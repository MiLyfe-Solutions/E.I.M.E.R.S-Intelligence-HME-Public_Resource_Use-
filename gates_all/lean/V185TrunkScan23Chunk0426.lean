import V185TrunkScan23Chunk0425

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2517914 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2517914 : Nat := 118140960795 + 2517914 * 2 ^ 59
def prefixEnd_2517914 : Nat := 4983230072969 + 3 ^ 40 * 2517914 * 2
def baseEnd_2517914 : Nat := 1292900128684966883595331

theorem tailTrace_2517914 : CollatzResearch.WordTrace tailWord_2517914 prefixEnd_2517914 1292900128684966883595331 := by
  unfold tailWord_2517914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22958967050008769580058199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61223912133356718880155197 22958967050008769580058199)
  ·
    refine ⟨34438450575013154370087299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22958967050008769580058199 34438450575013154370087299)
    ·
      refine ⟨51657675862519731555130949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34438450575013154370087299 51657675862519731555130949)
      ·
        refine ⟨9685814224222449666587053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51657675862519731555130949 9685814224222449666587053)
        ·
          refine ⟨3632180334083418624970145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9685814224222449666587053 3632180334083418624970145)
          ·
            refine ⟨2724135250562563968727609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632180334083418624970145 2724135250562563968727609)
            ·
              refine ⟨2043101437921922976545707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724135250562563968727609 2043101437921922976545707)
              ·
                refine ⟨3064652156882884464818561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043101437921922976545707 3064652156882884464818561)
                ·
                  refine ⟨2298489117662163348613921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064652156882884464818561 2298489117662163348613921)
                  ·
                    refine ⟨1723866838246622511460441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298489117662163348613921 1723866838246622511460441)
                    ·
                      refine ⟨1292900128684966883595331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723866838246622511460441 1292900128684966883595331)
                      ·
                        rfl

theorem cell23_2517914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2517914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517914 prefixEnd_2517914 := by exact prefixLift 2517914
  have htrace : WordTrace (prefixWord ++ tailWord_2517914) baseStart_2517914 baseEnd_2517914 := by
    simpa [prefixWord, tailWord_2517914, baseEnd_2517914] using wordTrace_append hprefix tailTrace_2517914
  have hstable : (prefixWord ++ tailWord_2517914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517914).length < 2 ^ (prefixWord ++ tailWord_2517914).sum := by decide
  have hdescent : baseEnd_2517914 < baseStart_2517914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517959 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 8]
def baseStart_2517959 : Nat := 118140960795 + 2517959 * 2 ^ 59
def prefixEnd_2517959 : Nat := 4983230072969 + 3 ^ 40 * 2517959 * 2
def baseEnd_2517959 : Nat := 143658137257157689725847

theorem tailTrace_2517959 : CollatzResearch.WordTrace tailWord_2517959 prefixEnd_2517959 143658137257157689725847 := by
  unfold tailWord_2517959
  simp only [CollatzResearch.WordTrace]
  refine ⟨91837509484872051005620931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61225006323248034003747287 91837509484872051005620931)
  ·
    refine ⟨137756264227308076508431397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91837509484872051005620931 137756264227308076508431397)
    ·
      refine ⟨25829299542620264345330887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137756264227308076508431397 25829299542620264345330887)
      ·
        refine ⟨38743949313930396517996331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25829299542620264345330887 38743949313930396517996331)
        ·
          refine ⟨58115923970895594776994497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38743949313930396517996331 58115923970895594776994497)
          ·
            refine ⟨43586942978171696082745873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58115923970895594776994497 43586942978171696082745873)
            ·
              refine ⟨32690207233628772062059405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43586942978171696082745873 32690207233628772062059405)
              ·
                refine ⟨12258827712610789523272277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32690207233628772062059405 12258827712610789523272277)
                ·
                  refine ⟨143658137257157689725847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12258827712610789523272277 143658137257157689725847)
                  ·
                    rfl

theorem cell23_2517959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 8].length) (baseStart_2517959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517959 prefixEnd_2517959 := by exact prefixLift 2517959
  have htrace : WordTrace (prefixWord ++ tailWord_2517959) baseStart_2517959 baseEnd_2517959 := by
    simpa [prefixWord, tailWord_2517959, baseEnd_2517959] using wordTrace_append hprefix tailTrace_2517959
  have hstable : (prefixWord ++ tailWord_2517959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517959).length < 2 ^ (prefixWord ++ tailWord_2517959).sum := by decide
  have hdescent : baseEnd_2517959 < baseStart_2517959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517970 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2517970 : Nat := 118140960795 + 2517970 * 2 ^ 59
def prefixEnd_2517970 : Nat := 4983230072969 + 3 ^ 40 * 2517970 * 2
def baseEnd_2517970 : Nat := 1292928883601618664495073

theorem tailTrace_2517970 : CollatzResearch.WordTrace tailWord_2517970 prefixEnd_2517970 1292928883601618664495073 := by
  unfold tailWord_2517970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22959477671958049971067841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61225273791888133256180909 22959477671958049971067841)
  ·
    refine ⟨17219608253968537478300881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22959477671958049971067841 17219608253968537478300881)
    ·
      refine ⟨12914706190476403108725661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17219608253968537478300881 12914706190476403108725661)
      ·
        refine ⟨4843014821428651165772123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12914706190476403108725661 4843014821428651165772123)
        ·
          refine ⟨7264522232142976748658185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843014821428651165772123 7264522232142976748658185)
          ·
            refine ⟨5448391674107232561493639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264522232142976748658185 5448391674107232561493639)
            ·
              refine ⟨8172587511160848842240459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448391674107232561493639 8172587511160848842240459)
              ·
                refine ⟨12258881266741273263360689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172587511160848842240459 12258881266741273263360689)
                ·
                  refine ⟨9194160950055954947520517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12258881266741273263360689 9194160950055954947520517)
                  ·
                    refine ⟨1723905178135491552660097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9194160950055954947520517 1723905178135491552660097)
                    ·
                      refine ⟨1292928883601618664495073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723905178135491552660097 1292928883601618664495073)
                      ·
                        rfl

theorem cell23_2517970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2517970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517970 prefixEnd_2517970 := by exact prefixLift 2517970
  have htrace : WordTrace (prefixWord ++ tailWord_2517970) baseStart_2517970 baseEnd_2517970 := by
    simpa [prefixWord, tailWord_2517970, baseEnd_2517970] using wordTrace_append hprefix tailTrace_2517970
  have hstable : (prefixWord ++ tailWord_2517970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517970).length < 2 ^ (prefixWord ++ tailWord_2517970).sum := by decide
  have hdescent : baseEnd_2517970 < baseStart_2517970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517976 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 6]
def baseStart_2517976 : Nat := 118140960795 + 2517976 * 2 ^ 59
def prefixEnd_2517976 : Nat := 4983230072969 + 3 ^ 40 * 2517976 * 2
def baseEnd_2517976 : Nat := 143659107165060626780005

theorem tailTrace_2517976 : CollatzResearch.WordTrace tailWord_2517976 prefixEnd_2517976 143659107165060626780005 := by
  unfold tailWord_2517976
  simp only [CollatzResearch.WordTrace]
  refine ⟨45919064762905231454494891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61225419683873641939326521 45919064762905231454494891)
  ·
    refine ⟨68878597144357847181742337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45919064762905231454494891 68878597144357847181742337)
    ·
      refine ⟨51658947858268385386306753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68878597144357847181742337 51658947858268385386306753)
      ·
        refine ⟨38744210893701289039730065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51658947858268385386306753 38744210893701289039730065)
        ·
          refine ⟨29058158170275966779797549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38744210893701289039730065 29058158170275966779797549)
          ·
            refine ⟨10896809313853487542424081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29058158170275966779797549 10896809313853487542424081)
            ·
              refine ⟨8172606985390115656818061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10896809313853487542424081 8172606985390115656818061)
              ·
                refine ⟨3064727619521293371306773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8172606985390115656818061 3064727619521293371306773)
                ·
                  refine ⟨143659107165060626780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3064727619521293371306773 143659107165060626780005)
                  ·
                    rfl

theorem cell23_2517976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_2517976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517976 prefixEnd_2517976 := by exact prefixLift 2517976
  have htrace : WordTrace (prefixWord ++ tailWord_2517976) baseStart_2517976 baseEnd_2517976 := by
    simpa [prefixWord, tailWord_2517976, baseEnd_2517976] using wordTrace_append hprefix tailTrace_2517976
  have hstable : (prefixWord ++ tailWord_2517976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517976).length < 2 ^ (prefixWord ++ tailWord_2517976).sum := by decide
  have hdescent : baseEnd_2517976 < baseStart_2517976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518013 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_2518013 : Nat := 118140960795 + 2518013 * 2 ^ 59
def prefixEnd_2518013 : Nat := 4983230072969 + 3 ^ 40 * 2518013 * 2
def baseEnd_2518013 : Nat := 1292950963269761996257375

theorem tailTrace_2518013 : CollatzResearch.WordTrace tailWord_2518013 prefixEnd_2518013 1292950963269761996257375 := by
  unfold tailWord_2518013
  simp only [CollatzResearch.WordTrace]
  refine ⟨91839479026676418228086693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61226319351117612152057795 91839479026676418228086693)
  ·
    refine ⟨17219902317501828417766255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91839479026676418228086693 17219902317501828417766255)
    ·
      refine ⟨25829853476252742626649383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17219902317501828417766255 25829853476252742626649383)
      ·
        refine ⟨38744780214379113939974075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25829853476252742626649383 38744780214379113939974075)
        ·
          refine ⟨58117170321568670909961113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38744780214379113939974075 58117170321568670909961113)
          ·
            refine ⟨43587877741176503182470835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58117170321568670909961113 43587877741176503182470835)
            ·
              refine ⟨65381816611764754773706253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43587877741176503182470835 65381816611764754773706253)
              ·
                refine ⟨24518181229411783040139845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65381816611764754773706253 24518181229411783040139845)
                ·
                  refine ⟨4597158980514709320026221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24518181229411783040139845 4597158980514709320026221)
                  ·
                    refine ⟨1723934617693015995009833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4597158980514709320026221 1723934617693015995009833)
                    ·
                      refine ⟨1292950963269761996257375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723934617693015995009833 1292950963269761996257375)
                      ·
                        rfl

theorem cell23_2518013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_2518013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518013 prefixEnd_2518013 := by exact prefixLift 2518013
  have htrace : WordTrace (prefixWord ++ tailWord_2518013) baseStart_2518013 baseEnd_2518013 := by
    simpa [prefixWord, tailWord_2518013, baseEnd_2518013] using wordTrace_append hprefix tailTrace_2518013
  have hstable : (prefixWord ++ tailWord_2518013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518013).length < 2 ^ (prefixWord ++ tailWord_2518013).sum := by decide
  have hdescent : baseEnd_2518013 < baseStart_2518013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518019 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 10]
def baseStart_2518019 : Nat := 118140960795 + 2518019 * 2 ^ 59
def prefixEnd_2518019 : Nat := 4983230072969 + 3 ^ 40 * 2518019 * 2
def baseEnd_2518019 : Nat := 430984681384562990927449

theorem tailTrace_2518019 : CollatzResearch.WordTrace tailWord_2518019 prefixEnd_2518019 430984681384562990927449 := by
  unfold tailWord_2518019
  simp only [CollatzResearch.WordTrace]
  refine ⟨91839697864654681252805111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61226465243103120835203407 91839697864654681252805111)
  ·
    refine ⟨137759546796982021879207667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91839697864654681252805111 137759546796982021879207667)
    ·
      refine ⟨206639320195473032818811501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137759546796982021879207667 206639320195473032818811501)
      ·
        refine ⟨77489745073302387307054313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206639320195473032818811501 77489745073302387307054313)
        ·
          refine ⟨58117308804976790480290735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77489745073302387307054313 58117308804976790480290735)
          ·
            refine ⟨87175963207465185720436103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58117308804976790480290735 87175963207465185720436103)
            ·
              refine ⟨130763944811197778580654155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87175963207465185720436103 130763944811197778580654155)
              ·
                refine ⟨196145917216796667870981233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130763944811197778580654155 196145917216796667870981233)
                ·
                  refine ⟨147109437912597500903235925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196145917216796667870981233 147109437912597500903235925)
                  ·
                    refine ⟨430984681384562990927449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 147109437912597500903235925 430984681384562990927449)
                    ·
                      rfl

theorem cell23_2518019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_2518019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518019 prefixEnd_2518019 := by exact prefixLift 2518019
  have htrace : WordTrace (prefixWord ++ tailWord_2518019) baseStart_2518019 baseEnd_2518019 := by
    simpa [prefixWord, tailWord_2518019, baseEnd_2518019] using wordTrace_append hprefix tailTrace_2518019
  have hstable : (prefixWord ++ tailWord_2518019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518019).length < 2 ^ (prefixWord ++ tailWord_2518019).sum := by decide
  have hdescent : baseEnd_2518019 < baseStart_2518019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518070 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2518070 : Nat := 118140960795 + 2518070 * 2 ^ 59
def prefixEnd_2518070 : Nat := 4983230072969 + 3 ^ 40 * 2518070 * 2
def baseEnd_2518070 : Nat := 430993410555689424414871

theorem tailTrace_2518070 : CollatzResearch.WordTrace tailWord_2518070 prefixEnd_2518070 430993410555689424414871 := by
  unfold tailWord_2518070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5740097374216869810181979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61227705324979944641941109 5740097374216869810181979)
  ·
    refine ⟨8610146061325304715272969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5740097374216869810181979 8610146061325304715272969)
    ·
      refine ⟨6457609545993978536454727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8610146061325304715272969 6457609545993978536454727)
      ·
        refine ⟨9686414318990967804682091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457609545993978536454727 9686414318990967804682091)
        ·
          refine ⟨14529621478486451707023137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686414318990967804682091 14529621478486451707023137)
          ·
            refine ⟨10897216108864838780267353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14529621478486451707023137 10897216108864838780267353)
            ·
              refine ⟨8172912081648629085200515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10897216108864838780267353 8172912081648629085200515)
              ·
                refine ⟨12259368122472943627800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172912081648629085200515 12259368122472943627800773)
                ·
                  refine ⟨2298631522963676930212645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12259368122472943627800773 2298631522963676930212645)
                  ·
                    refine ⟨430993410555689424414871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298631522963676930212645 430993410555689424414871)
                    ·
                      rfl

theorem cell23_2518070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2518070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518070 prefixEnd_2518070 := by exact prefixLift 2518070
  have htrace : WordTrace (prefixWord ++ tailWord_2518070) baseStart_2518070 baseEnd_2518070 := by
    simpa [prefixWord, tailWord_2518070, baseEnd_2518070] using wordTrace_append hprefix tailTrace_2518070
  have hstable : (prefixWord ++ tailWord_2518070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518070).length < 2 ^ (prefixWord ++ tailWord_2518070).sum := by decide
  have hdescent : baseEnd_2518070 < baseStart_2518070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518077 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2518077 : Nat := 118140960795 + 2518077 * 2 ^ 59
def prefixEnd_2518077 : Nat := 4983230072969 + 3 ^ 40 * 2518077 * 2
def baseEnd_2518077 : Nat := 1292983826031649745857081

theorem tailTrace_2518077 : CollatzResearch.WordTrace tailWord_2518077 prefixEnd_2518077 1292983826031649745857081 := by
  unfold tailWord_2518077
  simp only [CollatzResearch.WordTrace]
  refine ⟨91841813298444557158416485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61227875532296371438944323 91841813298444557158416485)
  ·
    refine ⟨17220339993458354467203091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91841813298444557158416485 17220339993458354467203091)
    ·
      refine ⟨25830509990187531700804637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17220339993458354467203091 25830509990187531700804637)
      ·
        refine ⟨9686441246320324387801739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25830509990187531700804637 9686441246320324387801739)
        ·
          refine ⟨14529661869480486581702609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686441246320324387801739 14529661869480486581702609)
          ·
            refine ⟨10897246402110364936276957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14529661869480486581702609 10897246402110364936276957)
            ·
              refine ⟨4086467400791386851103859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10897246402110364936276957 4086467400791386851103859)
              ·
                refine ⟨6129701101187080276655789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086467400791386851103859 6129701101187080276655789)
                ·
                  refine ⟨2298637912945155103745921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6129701101187080276655789 2298637912945155103745921)
                  ·
                    refine ⟨1723978434708866327809441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298637912945155103745921 1723978434708866327809441)
                    ·
                      refine ⟨1292983826031649745857081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723978434708866327809441 1292983826031649745857081)
                      ·
                        rfl

theorem cell23_2518077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2518077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518077 prefixEnd_2518077 := by exact prefixLift 2518077
  have htrace : WordTrace (prefixWord ++ tailWord_2518077) baseStart_2518077 baseEnd_2518077 := by
    simpa [prefixWord, tailWord_2518077, baseEnd_2518077] using wordTrace_append hprefix tailTrace_2518077
  have hstable : (prefixWord ++ tailWord_2518077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518077).length < 2 ^ (prefixWord ++ tailWord_2518077).sum := by decide
  have hdescent : baseEnd_2518077 < baseStart_2518077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518087 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 2, 4]
def baseStart_2518087 : Nat := 118140960795 + 2518087 * 2 ^ 59
def prefixEnd_2518087 : Nat := 4983230072969 + 3 ^ 40 * 2518087 * 2
def baseEnd_2518087 : Nat := 430996320279398235577345

theorem tailTrace_2518087 : CollatzResearch.WordTrace tailWord_2518087 prefixEnd_2518087 430996320279398235577345 := by
  unfold tailWord_2518087
  simp only [CollatzResearch.WordTrace]
  refine ⟨91842178028408328866280515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61228118685605552577520343 91842178028408328866280515)
  ·
    refine ⟨137763267042612493299420773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91842178028408328866280515 137763267042612493299420773)
    ·
      refine ⟨25830612570489842493641395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137763267042612493299420773 25830612570489842493641395)
      ·
        refine ⟨38745918855734763740462093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25830612570489842493641395 38745918855734763740462093)
        ·
          refine ⟨14529719570900536402673285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38745918855734763740462093 14529719570900536402673285)
          ·
            refine ⟨2724322419543850575501241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14529719570900536402673285 2724322419543850575501241)
            ·
              refine ⟨2043241814657887931625931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724322419543850575501241 2043241814657887931625931)
              ·
                refine ⟨3064862721986831897438897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043241814657887931625931 3064862721986831897438897)
                ·
                  refine ⟨2298647041490123923079173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064862721986831897438897 2298647041490123923079173)
                  ·
                    refine ⟨430996320279398235577345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298647041490123923079173 430996320279398235577345)
                    ·
                      rfl

theorem cell23_2518087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_2518087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518087 prefixEnd_2518087 := by exact prefixLift 2518087
  have htrace : WordTrace (prefixWord ++ tailWord_2518087) baseStart_2518087 baseEnd_2518087 := by
    simpa [prefixWord, tailWord_2518087, baseEnd_2518087] using wordTrace_append hprefix tailTrace_2518087
  have hstable : (prefixWord ++ tailWord_2518087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518087).length < 2 ^ (prefixWord ++ tailWord_2518087).sum := by decide
  have hdescent : baseEnd_2518087 < baseStart_2518087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518106 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2518106 : Nat := 118140960795 + 2518106 * 2 ^ 59
def prefixEnd_2518106 : Nat := 4983230072969 + 3 ^ 40 * 2518106 * 2
def baseEnd_2518106 : Nat := 1292998716970630132394447

theorem tailTrace_2518106 : CollatzResearch.WordTrace tailWord_2518106 prefixEnd_2518106 1292998716970630132394447 := by
  unfold tailWord_2518106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960717753834873777805543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61228580676892996740814781 22960717753834873777805543)
  ·
    refine ⟨34441076630752310666708315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22960717753834873777805543 34441076630752310666708315)
    ·
      refine ⟨51661614946128466000062473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34441076630752310666708315 51661614946128466000062473)
      ·
        refine ⟨38746211209596349500046855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51661614946128466000062473 38746211209596349500046855)
        ·
          refine ⟨58119316814394524250070283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38746211209596349500046855 58119316814394524250070283)
          ·
            refine ⟨87178975221591786375105425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58119316814394524250070283 87178975221591786375105425)
            ·
              refine ⟨65384231416193839781329069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87178975221591786375105425 65384231416193839781329069)
              ·
                refine ⟨24519086781072689917998401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65384231416193839781329069 24519086781072689917998401)
                ·
                  refine ⟨18389315085804517438498801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24519086781072689917998401 18389315085804517438498801)
                  ·
                    refine ⟨13791986314353388078874101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18389315085804517438498801 13791986314353388078874101)
                    ·
                      refine ⟨1292998716970630132394447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13791986314353388078874101 1292998716970630132394447)
                      ·
                        rfl

theorem cell23_2518106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2518106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518106 prefixEnd_2518106 := by exact prefixLift 2518106
  have htrace : WordTrace (prefixWord ++ tailWord_2518106) baseStart_2518106 baseEnd_2518106 := by
    simpa [prefixWord, tailWord_2518106, baseEnd_2518106] using wordTrace_append hprefix tailTrace_2518106
  have hstable : (prefixWord ++ tailWord_2518106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518106).length < 2 ^ (prefixWord ++ tailWord_2518106).sum := by decide
  have hdescent : baseEnd_2518106 < baseStart_2518106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518114 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2518114 : Nat := 118140960795 + 2518114 * 2 ^ 59
def prefixEnd_2518114 : Nat := 4983230072969 + 3 ^ 40 * 2518114 * 2
def baseEnd_2518114 : Nat := 1293002824815866101094411

theorem tailTrace_2518114 : CollatzResearch.WordTrace tailWord_2518114 prefixEnd_2518114 1293002824815866101094411 := by
  unfold tailWord_2518114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960790699827628119378349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61228775199540341651675597 22960790699827628119378349)
  ·
    refine ⟨8610296512435360544766881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22960790699827628119378349 8610296512435360544766881)
    ·
      refine ⟨6457722384326520408575161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8610296512435360544766881 6457722384326520408575161)
      ·
        refine ⟨4843291788244890306431371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6457722384326520408575161 4843291788244890306431371)
        ·
          refine ⟨7264937682367335459647057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843291788244890306431371 7264937682367335459647057)
          ·
            refine ⟨5448703261775501594735293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264937682367335459647057 5448703261775501594735293)
            ·
              refine ⟨2043263723165813098025735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448703261775501594735293 2043263723165813098025735)
              ·
                refine ⟨3064895584748719647038603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043263723165813098025735 3064895584748719647038603)
                ·
                  refine ⟨4597343377123079470557905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064895584748719647038603 4597343377123079470557905)
                  ·
                    refine ⟨3448007532842309602918429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4597343377123079470557905 3448007532842309602918429)
                    ·
                      refine ⟨1293002824815866101094411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448007532842309602918429 1293002824815866101094411)
                      ·
                        rfl

theorem cell23_2518114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2518114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518114 prefixEnd_2518114 := by exact prefixLift 2518114
  have htrace : WordTrace (prefixWord ++ tailWord_2518114) baseStart_2518114 baseEnd_2518114 := by
    simpa [prefixWord, tailWord_2518114, baseEnd_2518114] using wordTrace_append hprefix tailTrace_2518114
  have hstable : (prefixWord ++ tailWord_2518114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518114).length < 2 ^ (prefixWord ++ tailWord_2518114).sum := by decide
  have hdescent : baseEnd_2518114 < baseStart_2518114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518136 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2518136 : Nat := 118140960795 + 2518136 * 2 ^ 59
def prefixEnd_2518136 : Nat := 4983230072969 + 3 ^ 40 * 2518136 * 2
def baseEnd_2518136 : Nat := 1293014121390265015019309

theorem tailTrace_2518136 : CollatzResearch.WordTrace tailWord_2518136 prefixEnd_2518136 1293014121390265015019309 := by
  unfold tailWord_2518136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45921982602615405117407131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61229310136820540156542841 45921982602615405117407131)
  ·
    refine ⟨68882973903923107676110697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45921982602615405117407131 68882973903923107676110697)
    ·
      refine ⟨51662230427942330757083023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68882973903923107676110697 51662230427942330757083023)
      ·
        refine ⟨77493345641913496135624535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51662230427942330757083023 77493345641913496135624535)
        ·
          refine ⟨116240018462870244203436803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77493345641913496135624535 116240018462870244203436803)
          ·
            refine ⟨174360027694305366305155205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116240018462870244203436803 174360027694305366305155205)
            ·
              refine ⟨32692505192682256182216601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174360027694305366305155205 32692505192682256182216601)
              ·
                refine ⟨24519378894511692136662451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32692505192682256182216601 24519378894511692136662451)
                ·
                  refine ⟨36779068341767538204993677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24519378894511692136662451 36779068341767538204993677)
                  ·
                    refine ⟨13792150628162826826872629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36779068341767538204993677 13792150628162826826872629)
                    ·
                      refine ⟨1293014121390265015019309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13792150628162826826872629 1293014121390265015019309)
                      ·
                        rfl

theorem cell23_2518136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2518136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518136 prefixEnd_2518136 := by exact prefixLift 2518136
  have htrace : WordTrace (prefixWord ++ tailWord_2518136) baseStart_2518136 baseEnd_2518136 := by
    simpa [prefixWord, tailWord_2518136, baseEnd_2518136] using wordTrace_append hprefix tailTrace_2518136
  have hstable : (prefixWord ++ tailWord_2518136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518136).length < 2 ^ (prefixWord ++ tailWord_2518136).sum := by decide
  have hdescent : baseEnd_2518136 < baseStart_2518136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518237 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2518237 : Nat := 118140960795 + 2518237 * 2 ^ 59
def prefixEnd_2518237 : Nat := 4983230072969 + 3 ^ 40 * 2518237 * 2
def baseEnd_2518237 : Nat := 431021994312123039952115

theorem tailTrace_2518237 : CollatzResearch.WordTrace tailWord_2518237 prefixEnd_2518237 431021994312123039952115 := by
  unfold tailWord_2518237
  simp only [CollatzResearch.WordTrace]
  refine ⟨91847648977864904484240965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61231765985243269656160643 91847648977864904484240965)
  ·
    refine ⟨17221434183349669590795181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91847648977864904484240965 17221434183349669590795181)
    ·
      refine ⟨6458037818756126096548193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17221434183349669590795181 6458037818756126096548193)
      ·
        refine ⟨4843528364067094572411145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6458037818756126096548193 4843528364067094572411145)
        ·
          refine ⟨3632646273050320929308359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843528364067094572411145 3632646273050320929308359)
          ·
            refine ⟨5448969409575481393962539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632646273050320929308359 5448969409575481393962539)
            ·
              refine ⟨8173454114363222090943809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448969409575481393962539 8173454114363222090943809)
              ·
                refine ⟨6130090585772416568207857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173454114363222090943809 6130090585772416568207857)
                ·
                  refine ⟨4597567939329312426155893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130090585772416568207857 4597567939329312426155893)
                  ·
                    refine ⟨431021994312123039952115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4597567939329312426155893 431021994312123039952115)
                    ·
                      rfl

theorem cell23_2518237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2518237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518237 prefixEnd_2518237 := by exact prefixLift 2518237
  have htrace : WordTrace (prefixWord ++ tailWord_2518237) baseStart_2518237 baseEnd_2518237 := by
    simpa [prefixWord, tailWord_2518237, baseEnd_2518237] using wordTrace_append hprefix tailTrace_2518237
  have hstable : (prefixWord ++ tailWord_2518237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518237).length < 2 ^ (prefixWord ++ tailWord_2518237).sum := by decide
  have hdescent : baseEnd_2518237 < baseStart_2518237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518240 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2518240 : Nat := 118140960795 + 2518240 * 2 ^ 59
def prefixEnd_2518240 : Nat := 4983230072969 + 3 ^ 40 * 2518240 * 2
def baseEnd_2518240 : Nat := 1293067523378332608118831

theorem tailTrace_2518240 : CollatzResearch.WordTrace tailWord_2518240 prefixEnd_2518240 1293067523378332608118831 := by
  unfold tailWord_2518240
  simp only [CollatzResearch.WordTrace]
  refine ⟨45923879198427017998300087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61231838931236023997733449 45923879198427017998300087)
  ·
    refine ⟨68885818797640526997450131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45923879198427017998300087 68885818797640526997450131)
    ·
      refine ⟨103328728196460790496175197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68885818797640526997450131 103328728196460790496175197)
      ·
        refine ⟨38748273073672796436065699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103328728196460790496175197 38748273073672796436065699)
        ·
          refine ⟨58122409610509194654098549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38748273073672796436065699 58122409610509194654098549)
          ·
            refine ⟨5448975900985236998821739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58122409610509194654098549 5448975900985236998821739)
            ·
              refine ⟨8173463851477855498232609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448975900985236998821739 8173463851477855498232609)
              ·
                refine ⟨6130097888608391623674457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173463851477855498232609 6130097888608391623674457)
                ·
                  refine ⟨4597573416456293717755843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130097888608391623674457 4597573416456293717755843)
                  ·
                    refine ⟨6896360124684440576633765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597573416456293717755843 6896360124684440576633765)
                    ·
                      refine ⟨1293067523378332608118831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6896360124684440576633765 1293067523378332608118831)
                      ·
                        rfl

theorem cell23_2518240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2518240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518240 prefixEnd_2518240 := by exact prefixLift 2518240
  have htrace : WordTrace (prefixWord ++ tailWord_2518240) baseStart_2518240 baseEnd_2518240 := by
    simpa [prefixWord, tailWord_2518240, baseEnd_2518240] using wordTrace_append hprefix tailTrace_2518240
  have hstable : (prefixWord ++ tailWord_2518240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518240).length < 2 ^ (prefixWord ++ tailWord_2518240).sum := by decide
  have hdescent : baseEnd_2518240 < baseStart_2518240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518263 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 6]
def baseStart_2518263 : Nat := 118140960795 + 2518263 * 2 ^ 59
def prefixEnd_2518263 : Nat := 4983230072969 + 3 ^ 40 * 2518263 * 2
def baseEnd_2518263 : Nat := 143675481492598446459025

theorem tailTrace_2518263 : CollatzResearch.WordTrace tailWord_2518263 prefixEnd_2518263 143675481492598446459025 := by
  unfold tailWord_2518263
  simp only [CollatzResearch.WordTrace]
  refine ⟨91848597275770710924687443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61232398183847140616458295 91848597275770710924687443)
  ·
    refine ⟨137772895913656066387031165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91848597275770710924687443 137772895913656066387031165)
    ·
      refine ⟨51664835967621024895136687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137772895913656066387031165 51664835967621024895136687)
      ·
        refine ⟨77497253951431537342705031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51664835967621024895136687 77497253951431537342705031)
        ·
          refine ⟨116245880927147306014057547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77497253951431537342705031 116245880927147306014057547)
          ·
            refine ⟨174368821390720959021086321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116245880927147306014057547 174368821390720959021086321)
            ·
              refine ⟨130776616043040719265814741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174368821390720959021086321 130776616043040719265814741)
              ·
                refine ⟨3065076938508766857792533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130776616043040719265814741 3065076938508766857792533)
                ·
                  refine ⟨143675481492598446459025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3065076938508766857792533 143675481492598446459025)
                  ·
                    rfl

theorem cell23_2518263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 6].length) (baseStart_2518263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518263 prefixEnd_2518263 := by exact prefixLift 2518263
  have htrace : WordTrace (prefixWord ++ tailWord_2518263) baseStart_2518263 baseEnd_2518263 := by
    simpa [prefixWord, tailWord_2518263, baseEnd_2518263] using wordTrace_append hprefix tailTrace_2518263
  have hstable : (prefixWord ++ tailWord_2518263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518263).length < 2 ^ (prefixWord ++ tailWord_2518263).sum := by decide
  have hdescent : baseEnd_2518263 < baseStart_2518263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518274 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2518274 : Nat := 118140960795 + 2518274 * 2 ^ 59
def prefixEnd_2518274 : Nat := 4983230072969 + 3 ^ 40 * 2518274 * 2
def baseEnd_2518274 : Nat := 1293084981720585475093675

theorem tailTrace_2518274 : CollatzResearch.WordTrace tailWord_2518274 prefixEnd_2518274 1293084981720585475093675 := by
  unfold tailWord_2518274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962249619682714950834469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61232665652487239868891917 22962249619682714950834469)
  ·
    refine ⟨4305421803690509053281463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22962249619682714950834469 4305421803690509053281463)
    ·
      refine ⟨6458132705535763579922195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305421803690509053281463 6458132705535763579922195)
      ·
        refine ⟨9687199058303645369883293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458132705535763579922195 9687199058303645369883293)
        ·
          refine ⟨3632699646863867013706235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9687199058303645369883293 3632699646863867013706235)
          ·
            refine ⟨5449049470295800520559353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632699646863867013706235 5449049470295800520559353)
            ·
              refine ⟨4086787102721850390419515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449049470295800520559353 4086787102721850390419515)
              ·
                refine ⟨6130180654082775585629273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086787102721850390419515 6130180654082775585629273)
                ·
                  refine ⟨4597635490562081689221955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130180654082775585629273 4597635490562081689221955)
                  ·
                    refine ⟨6896453235843122533832933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597635490562081689221955 6896453235843122533832933)
                    ·
                      refine ⟨1293084981720585475093675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6896453235843122533832933 1293084981720585475093675)
                      ·
                        rfl

theorem cell23_2518274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2518274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518274 prefixEnd_2518274 := by exact prefixLift 2518274
  have htrace : WordTrace (prefixWord ++ tailWord_2518274) baseStart_2518274 baseEnd_2518274 := by
    simpa [prefixWord, tailWord_2518274, baseEnd_2518274] using wordTrace_append hprefix tailTrace_2518274
  have hstable : (prefixWord ++ tailWord_2518274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518274).length < 2 ^ (prefixWord ++ tailWord_2518274).sum := by decide
  have hdescent : baseEnd_2518274 < baseStart_2518274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518301 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2518301 : Nat := 118140960795 + 2518301 * 2 ^ 59
def prefixEnd_2518301 : Nat := 4983230072969 + 3 ^ 40 * 2518301 * 2
def baseEnd_2518301 : Nat := 431032948566085623152017

theorem tailTrace_2518301 : CollatzResearch.WordTrace tailWord_2518301 prefixEnd_2518301 431032948566085623152017 := by
  unfold tailWord_2518301
  simp only [CollatzResearch.WordTrace]
  refine ⟨91849983249633043414570757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61233322166422028943047171 91849983249633043414570757)
  ·
    refine ⟨17221871859306195640232017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91849983249633043414570757 17221871859306195640232017)
    ·
      refine ⟨12916403894479646730174013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17221871859306195640232017 12916403894479646730174013)
      ·
        refine ⟨4843651460429867523815255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12916403894479646730174013 4843651460429867523815255)
        ·
          refine ⟨7265477190644801285722883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843651460429867523815255 7265477190644801285722883)
          ·
            refine ⟨10898215785967201928584325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7265477190644801285722883 10898215785967201928584325)
            ·
              refine ⟨2043415459868850361609561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10898215785967201928584325 2043415459868850361609561)
              ·
                refine ⟨1532561594901637771207171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043415459868850361609561 1532561594901637771207171)
                ·
                  refine ⟨2298842392352456656810757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532561594901637771207171 2298842392352456656810757)
                  ·
                    refine ⟨431032948566085623152017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298842392352456656810757 431032948566085623152017)
                    ·
                      rfl

theorem cell23_2518301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2518301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518301 prefixEnd_2518301 := by exact prefixLift 2518301
  have htrace : WordTrace (prefixWord ++ tailWord_2518301) baseStart_2518301 baseEnd_2518301 := by
    simpa [prefixWord, tailWord_2518301, baseEnd_2518301] using wordTrace_append hprefix tailTrace_2518301
  have hstable : (prefixWord ++ tailWord_2518301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518301).length < 2 ^ (prefixWord ++ tailWord_2518301).sum := by decide
  have hdescent : baseEnd_2518301 < baseStart_2518301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518324 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2518324 : Nat := 118140960795 + 2518324 * 2 ^ 59
def prefixEnd_2518324 : Nat := 4983230072969 + 3 ^ 40 * 2518324 * 2
def baseEnd_2518324 : Nat := 1293110655753310279468445

theorem tailTrace_2518324 : CollatzResearch.WordTrace tailWord_2518324 prefixEnd_2518324 1293110655753310279468445 := by
  unfold tailWord_2518324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45925411064274859171329013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61233881419033145561772017 45925411064274859171329013)
  ·
    refine ⟨4305507287275768047312095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45925411064274859171329013 4305507287275768047312095)
    ·
      refine ⟨6458260930913652070968143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305507287275768047312095 6458260930913652070968143)
      ·
        refine ⟨9687391396370478106452215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458260930913652070968143 9687391396370478106452215)
        ·
          refine ⟨14531087094555717159678323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9687391396370478106452215 14531087094555717159678323)
          ·
            refine ⟨21796630641833575739517485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14531087094555717159678323 21796630641833575739517485)
            ·
              refine ⟨8173736490687590902319057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21796630641833575739517485 8173736490687590902319057)
              ·
                refine ⟨6130302368015693176739293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173736490687590902319057 6130302368015693176739293)
                ·
                  refine ⟨2298863388005884941277235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6130302368015693176739293 2298863388005884941277235)
                  ·
                    refine ⟨3448295082008827411915853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298863388005884941277235 3448295082008827411915853)
                    ·
                      refine ⟨1293110655753310279468445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448295082008827411915853 1293110655753310279468445)
                      ·
                        rfl

theorem cell23_2518324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2518324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518324 prefixEnd_2518324 := by exact prefixLift 2518324
  have htrace : WordTrace (prefixWord ++ tailWord_2518324) baseStart_2518324 baseEnd_2518324 := by
    simpa [prefixWord, tailWord_2518324, baseEnd_2518324] using wordTrace_append hprefix tailTrace_2518324
  have hstable : (prefixWord ++ tailWord_2518324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518324).length < 2 ^ (prefixWord ++ tailWord_2518324).sum := by decide
  have hdescent : baseEnd_2518324 < baseStart_2518324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518330 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_2518330 : Nat := 118140960795 + 2518330 * 2 ^ 59
def prefixEnd_2518330 : Nat := 4983230072969 + 3 ^ 40 * 2518330 * 2
def baseEnd_2518330 : Nat := 1293113736637237255993417

theorem tailTrace_2518330 : CollatzResearch.WordTrace tailWord_2518330 prefixEnd_2518330 1293113736637237255993417 := by
  unfold tailWord_2518330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962760241631995341844111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61234027311018654244917629 22962760241631995341844111)
  ·
    refine ⟨34444140362447993012766167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962760241631995341844111 34444140362447993012766167)
    ·
      refine ⟨51666210543671989519149251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34444140362447993012766167 51666210543671989519149251)
      ·
        refine ⟨77499315815507984278723877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51666210543671989519149251 77499315815507984278723877)
        ·
          refine ⟨14531121715407747052260727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77499315815507984278723877 14531121715407747052260727)
          ·
            refine ⟨21796682573111620578391091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14531121715407747052260727 21796682573111620578391091)
            ·
              refine ⟨32695023859667430867586637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21796682573111620578391091 32695023859667430867586637)
              ·
                refine ⟨12260633947375286575344989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32695023859667430867586637 12260633947375286575344989)
                ·
                  refine ⟨4597737730265732465754371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12260633947375286575344989 4597737730265732465754371)
                  ·
                    refine ⟨6896606595398598698631557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597737730265732465754371 6896606595398598698631557)
                    ·
                      refine ⟨1293113736637237255993417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6896606595398598698631557 1293113736637237255993417)
                      ·
                        rfl

theorem cell23_2518330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_2518330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518330 prefixEnd_2518330 := by exact prefixLift 2518330
  have htrace : WordTrace (prefixWord ++ tailWord_2518330) baseStart_2518330 baseEnd_2518330 := by
    simpa [prefixWord, tailWord_2518330, baseEnd_2518330] using wordTrace_append hprefix tailTrace_2518330
  have hstable : (prefixWord ++ tailWord_2518330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518330).length < 2 ^ (prefixWord ++ tailWord_2518330).sum := by decide
  have hdescent : baseEnd_2518330 < baseStart_2518330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518350 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2518350 : Nat := 118140960795 + 2518350 * 2 ^ 59
def prefixEnd_2518350 : Nat := 4983230072969 + 3 ^ 40 * 2518350 * 2
def baseEnd_2518350 : Nat := 1293124006250327177743325

theorem tailTrace_2518350 : CollatzResearch.WordTrace tailWord_2518350 prefixEnd_2518350 1293124006250327177743325 := by
  unfold tailWord_2518350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481471303306940597888063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61234513617637016522069669 11481471303306940597888063)
  ·
    refine ⟨17222206954960410896832095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11481471303306940597888063 17222206954960410896832095)
    ·
      refine ⟨25833310432440616345248143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17222206954960410896832095 25833310432440616345248143)
      ·
        refine ⟨38749965648660924517872215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25833310432440616345248143 38749965648660924517872215)
        ·
          refine ⟨58124948472991386776808323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38749965648660924517872215 58124948472991386776808323)
          ·
            refine ⟨87187422709487080165212485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58124948472991386776808323 87187422709487080165212485)
            ·
              refine ⟨16347641758028827530977341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87187422709487080165212485 16347641758028827530977341)
              ·
                refine ⟨6130365659260810324116503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16347641758028827530977341 6130365659260810324116503)
                ·
                  refine ⟨9195548488891215486174755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6130365659260810324116503 9195548488891215486174755)
                  ·
                    refine ⟨13793322733336823229262133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9195548488891215486174755 13793322733336823229262133)
                    ·
                      refine ⟨1293124006250327177743325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13793322733336823229262133 1293124006250327177743325)
                      ·
                        rfl

theorem cell23_2518350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2518350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518350 prefixEnd_2518350 := by exact prefixLift 2518350
  have htrace : WordTrace (prefixWord ++ tailWord_2518350) baseStart_2518350 baseEnd_2518350 := by
    simpa [prefixWord, tailWord_2518350, baseEnd_2518350] using wordTrace_append hprefix tailTrace_2518350
  have hstable : (prefixWord ++ tailWord_2518350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518350).length < 2 ^ (prefixWord ++ tailWord_2518350).sum := by decide
  have hdescent : baseEnd_2518350 < baseStart_2518350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518353 : List Nat := [1, 2, 2, 1, 4, 1, 12]
def baseStart_2518353 : Nat := 118140960795 + 2518353 * 2 ^ 59
def prefixEnd_2518353 : Nat := 4983230072969 + 3 ^ 40 * 2518353 * 2
def baseEnd_2518353 : Nat := 15964512922127045259331

theorem tailTrace_2518353 : CollatzResearch.WordTrace tailWord_2518353 prefixEnd_2518353 15964512922127045259331 := by
  unfold tailWord_2518353
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851879845444656295463713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61234586563629770863642475 91851879845444656295463713)
  ·
    refine ⟨68888909884083492221597785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91851879845444656295463713 68888909884083492221597785)
    ·
      refine ⟨51666682413062619166198339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68888909884083492221597785 51666682413062619166198339)
      ·
        refine ⟨77500023619593928749297509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51666682413062619166198339 77500023619593928749297509)
        ·
          refine ⟨14531254428673861640493283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77500023619593928749297509 14531254428673861640493283)
          ·
            refine ⟨21796881643010792460739925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14531254428673861640493283 21796881643010792460739925)
            ·
              refine ⟨15964512922127045259331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 21796881643010792460739925 15964512922127045259331)
              ·
                rfl

theorem cell23_2518353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 12].length) (baseStart_2518353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518353 prefixEnd_2518353 := by exact prefixLift 2518353
  have htrace : WordTrace (prefixWord ++ tailWord_2518353) baseStart_2518353 baseEnd_2518353 := by
    simpa [prefixWord, tailWord_2518353, baseEnd_2518353] using wordTrace_append hprefix tailTrace_2518353
  have hstable : (prefixWord ++ tailWord_2518353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518353).length < 2 ^ (prefixWord ++ tailWord_2518353).sum := by decide
  have hdescent : baseEnd_2518353 < baseStart_2518353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518357 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2518357 : Nat := 118140960795 + 2518357 * 2 ^ 59
def prefixEnd_2518357 : Nat := 4983230072969 + 3 ^ 40 * 2518357 * 2
def baseEnd_2518357 : Nat := 431042533538302883451931

theorem tailTrace_2518357 : CollatzResearch.WordTrace tailWord_2518357 prefixEnd_2518357 431042533538302883451931 := by
  unfold tailWord_2518357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91852025737430164978609325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61234683824953443319072883 91852025737430164978609325)
  ·
    refine ⟨34444509651536311866978497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91852025737430164978609325 34444509651536311866978497)
    ·
      refine ⟨25833382238652233900233873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34444509651536311866978497 25833382238652233900233873)
      ·
        refine ⟨19375036678989175425175405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25833382238652233900233873 19375036678989175425175405)
        ·
          refine ⟨7265638754620940784440777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19375036678989175425175405 7265638754620940784440777)
          ·
            refine ⟨5449229065965705588330583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7265638754620940784440777 5449229065965705588330583)
            ·
              refine ⟨8173843598948558382495875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449229065965705588330583 8173843598948558382495875)
              ·
                refine ⟨12260765398422837573743813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173843598948558382495875 12260765398422837573743813)
                ·
                  refine ⟨2298893512204282045076965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12260765398422837573743813 2298893512204282045076965)
                  ·
                    refine ⟨431042533538302883451931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298893512204282045076965 431042533538302883451931)
                    ·
                      rfl

theorem cell23_2518357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2518357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518357 prefixEnd_2518357 := by exact prefixLift 2518357
  have htrace : WordTrace (prefixWord ++ tailWord_2518357) baseStart_2518357 baseEnd_2518357 := by
    simpa [prefixWord, tailWord_2518357, baseEnd_2518357] using wordTrace_append hprefix tailTrace_2518357
  have hstable : (prefixWord ++ tailWord_2518357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518357).length < 2 ^ (prefixWord ++ tailWord_2518357).sum := by decide
  have hdescent : baseEnd_2518357 < baseStart_2518357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518370 : List Nat := [3, 3, 2, 1, 1, 1, 2, 10]
def baseStart_2518370 : Nat := 118140960795 + 2518370 * 2 ^ 59
def prefixEnd_2518370 : Nat := 4983230072969 + 3 ^ 40 * 2518370 * 2
def baseEnd_2518370 : Nat := 47893862069015448129379

theorem tailTrace_2518370 : CollatzResearch.WordTrace tailWord_2518370 prefixEnd_2518370 47893862069015448129379 := by
  unfold tailWord_2518370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963124971595767049708141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61234999924255378799221709 22963124971595767049708141)
  ·
    refine ⟨8611171864348412643640553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22963124971595767049708141 8611171864348412643640553)
    ·
      refine ⟨6458378898261309482730415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8611171864348412643640553 6458378898261309482730415)
      ·
        refine ⟨9687568347391964224095623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458378898261309482730415 9687568347391964224095623)
        ·
          refine ⟨14531352521087946336143435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9687568347391964224095623 14531352521087946336143435)
          ·
            refine ⟨21797028781631919504215153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14531352521087946336143435 21797028781631919504215153)
            ·
              refine ⟨16347771586223939628161365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21797028781631919504215153 16347771586223939628161365)
              ·
                refine ⟨47893862069015448129379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16347771586223939628161365 47893862069015448129379)
                ·
                  rfl

theorem cell23_2518370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_2518370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518370 prefixEnd_2518370 := by exact prefixLift 2518370
  have htrace : WordTrace (prefixWord ++ tailWord_2518370) baseStart_2518370 baseEnd_2518370 := by
    simpa [prefixWord, tailWord_2518370, baseEnd_2518370] using wordTrace_append hprefix tailTrace_2518370
  have hstable : (prefixWord ++ tailWord_2518370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518370).length < 2 ^ (prefixWord ++ tailWord_2518370).sum := by decide
  have hdescent : baseEnd_2518370 < baseStart_2518370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518397 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2518397 : Nat := 118140960795 + 2518397 * 2 ^ 59
def prefixEnd_2518397 : Nat := 4983230072969 + 3 ^ 40 * 2518397 * 2
def baseEnd_2518397 : Nat := 1293148139841088493855609

theorem tailTrace_2518397 : CollatzResearch.WordTrace tailWord_2518397 prefixEnd_2518397 1293148139841088493855609 := by
  unfold tailWord_2518397
  simp only [CollatzResearch.WordTrace]
  refine ⟨91853484657285251810065445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61235656438190167873376963 91853484657285251810065445)
  ·
    refine ⟨17222528373240984714387271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91853484657285251810065445 17222528373240984714387271)
    ·
      refine ⟨25833792559861477071580907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17222528373240984714387271 25833792559861477071580907)
      ·
        refine ⟨38750688839792215607371361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25833792559861477071580907 38750688839792215607371361)
        ·
          refine ⟨29063016629844161705528521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38750688839792215607371361 29063016629844161705528521)
          ·
            refine ⟨21797262472383121279146391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29063016629844161705528521 21797262472383121279146391)
            ·
              refine ⟨32695893708574681918719587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21797262472383121279146391 32695893708574681918719587)
              ·
                refine ⟨49043840562862022878079381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32695893708574681918719587 49043840562862022878079381)
                ·
                  refine ⟨2298930026384157322409971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49043840562862022878079381 2298930026384157322409971)
                  ·
                    refine ⟨3448395039576235983614957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298930026384157322409971 3448395039576235983614957)
                    ·
                      refine ⟨1293148139841088493855609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448395039576235983614957 1293148139841088493855609)
                      ·
                        rfl

theorem cell23_2518397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2518397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518397 prefixEnd_2518397 := by exact prefixLift 2518397
  have htrace : WordTrace (prefixWord ++ tailWord_2518397) baseStart_2518397 baseEnd_2518397 := by
    simpa [prefixWord, tailWord_2518397, baseEnd_2518397] using wordTrace_append hprefix tailTrace_2518397
  have hstable : (prefixWord ++ tailWord_2518397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518397).length < 2 ^ (prefixWord ++ tailWord_2518397).sum := by decide
  have hdescent : baseEnd_2518397 < baseStart_2518397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518431 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2518431 : Nat := 118140960795 + 2518431 * 2 ^ 59
def prefixEnd_2518431 : Nat := 4983230072969 + 3 ^ 40 * 2518431 * 2
def baseEnd_2518431 : Nat := 1293165598183341360830453

theorem tailTrace_2518431 : CollatzResearch.WordTrace tailWord_2518431 prefixEnd_2518431 1293165598183341360830453 := by
  unfold tailWord_2518431
  simp only [CollatzResearch.WordTrace]
  refine ⟨91854724739162075616803147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61236483159441383744535431 91854724739162075616803147)
  ·
    refine ⟨137782087108743113425204721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91854724739162075616803147 137782087108743113425204721)
    ·
      refine ⟨103336565331557335068903541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137782087108743113425204721 103336565331557335068903541)
      ·
        refine ⟨9687802999833500162709707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103336565331557335068903541 9687802999833500162709707)
        ·
          refine ⟨14531704499750250244064561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9687802999833500162709707 14531704499750250244064561)
          ·
            refine ⟨10898778374812687683048421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14531704499750250244064561 10898778374812687683048421)
            ·
              refine ⟨2043520945277378940571579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10898778374812687683048421 2043520945277378940571579)
              ·
                refine ⟨3065281417916068410857369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043520945277378940571579 3065281417916068410857369)
                ·
                  refine ⟨2298961063437051308143027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065281417916068410857369 2298961063437051308143027)
                  ·
                    refine ⟨3448441595155576962214541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298961063437051308143027 3448441595155576962214541)
                    ·
                      refine ⟨1293165598183341360830453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448441595155576962214541 1293165598183341360830453)
                      ·
                        rfl

theorem cell23_2518431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2518431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518431 prefixEnd_2518431 := by exact prefixLift 2518431
  have htrace : WordTrace (prefixWord ++ tailWord_2518431) baseStart_2518431 baseEnd_2518431 := by
    simpa [prefixWord, tailWord_2518431, baseEnd_2518431] using wordTrace_append hprefix tailTrace_2518431
  have hstable : (prefixWord ++ tailWord_2518431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518431).length < 2 ^ (prefixWord ++ tailWord_2518431).sum := by decide
  have hdescent : baseEnd_2518431 < baseStart_2518431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518450 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2518450 : Nat := 118140960795 + 2518450 * 2 ^ 59
def prefixEnd_2518450 : Nat := 4983230072969 + 3 ^ 40 * 2518450 * 2
def baseEnd_2518450 : Nat := 1293175354315776786492865

theorem tailTrace_2518450 : CollatzResearch.WordTrace tailWord_2518450 prefixEnd_2518450 1293175354315776786492865 := by
  unfold tailWord_2518450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963854431523310465436201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61236945150728827907829869 22963854431523310465436201)
  ·
    refine ⟨17222890823642482849077151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22963854431523310465436201 17222890823642482849077151)
    ·
      refine ⟨25834336235463724273615727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17222890823642482849077151 25834336235463724273615727)
      ·
        refine ⟨38751504353195586410423591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25834336235463724273615727 38751504353195586410423591)
        ·
          refine ⟨58127256529793379615635387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38751504353195586410423591 58127256529793379615635387)
          ·
            refine ⟨87190884794690069423453081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58127256529793379615635387 87190884794690069423453081)
            ·
              refine ⟨65393163596017552067589811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87190884794690069423453081 65393163596017552067589811)
              ·
                refine ⟨98089745394026328101384717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65393163596017552067589811 98089745394026328101384717)
                ·
                  refine ⟨36783654522759873038019269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98089745394026328101384717 36783654522759873038019269)
                  ·
                    refine ⟨6896935223017476194628613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36783654522759873038019269 6896935223017476194628613)
                    ·
                      refine ⟨1293175354315776786492865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6896935223017476194628613 1293175354315776786492865)
                      ·
                        rfl

theorem cell23_2518450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2518450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518450 prefixEnd_2518450 := by exact prefixLift 2518450
  have htrace : WordTrace (prefixWord ++ tailWord_2518450) baseStart_2518450 baseEnd_2518450 := by
    simpa [prefixWord, tailWord_2518450, baseEnd_2518450] using wordTrace_append hprefix tailTrace_2518450
  have hstable : (prefixWord ++ tailWord_2518450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518450).length < 2 ^ (prefixWord ++ tailWord_2518450).sum := by decide
  have hdescent : baseEnd_2518450 < baseStart_2518450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518471 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_2518471 : Nat := 118140960795 + 2518471 * 2 ^ 59
def prefixEnd_2518471 : Nat := 4983230072969 + 3 ^ 40 * 2518471 * 2
def baseEnd_2518471 : Nat := 1293186137409521204330269

theorem tailTrace_2518471 : CollatzResearch.WordTrace tailWord_2518471 prefixEnd_2518471 1293186137409521204330269 := by
  unfold tailWord_2518471
  simp only [CollatzResearch.WordTrace]
  refine ⟨91856183659017162448259267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61237455772678108298839511 91856183659017162448259267)
  ·
    refine ⟨137784275488525743672388901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91856183659017162448259267 137784275488525743672388901)
    ·
      refine ⟨25834551654098576938572919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137784275488525743672388901 25834551654098576938572919)
      ·
        refine ⟨38751827481147865407859379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25834551654098576938572919 38751827481147865407859379)
        ·
          refine ⟨58127741221721798111789069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38751827481147865407859379 58127741221721798111789069)
          ·
            refine ⟨21797902958145674291920901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58127741221721798111789069 21797902958145674291920901)
            ·
              refine ⟨4087106804652313929735169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21797902958145674291920901 4087106804652313929735169)
              ·
                refine ⟨3065330103489235447301377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087106804652313929735169 3065330103489235447301377)
                ·
                  refine ⟨2298997577616926585476033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065330103489235447301377 2298997577616926585476033)
                  ·
                    refine ⟨1724248183212694939107025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298997577616926585476033 1724248183212694939107025)
                    ·
                      refine ⟨1293186137409521204330269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724248183212694939107025 1293186137409521204330269)
                      ·
                        rfl

theorem cell23_2518471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_2518471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518471 prefixEnd_2518471 := by exact prefixLift 2518471
  have htrace : WordTrace (prefixWord ++ tailWord_2518471) baseStart_2518471 baseEnd_2518471 := by
    simpa [prefixWord, tailWord_2518471, baseEnd_2518471] using wordTrace_append hprefix tailTrace_2518471
  have hstable : (prefixWord ++ tailWord_2518471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518471).length < 2 ^ (prefixWord ++ tailWord_2518471).sum := by decide
  have hdescent : baseEnd_2518471 < baseStart_2518471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518484 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2518484 : Nat := 118140960795 + 2518484 * 2 ^ 59
def prefixEnd_2518484 : Nat := 4983230072969 + 3 ^ 40 * 2518484 * 2
def baseEnd_2518484 : Nat := 1293192812658029653467709

theorem tailTrace_2518484 : CollatzResearch.WordTrace tailWord_2518484 prefixEnd_2518484 1293192812658029653467709 := by
  unfold tailWord_2518484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928328903985032834241253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61237771871980043778988337 45928328903985032834241253)
  ·
    refine ⟨8611561669497193656420235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45928328903985032834241253 8611561669497193656420235)
    ·
      refine ⟨12917342504245790484630353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611561669497193656420235 12917342504245790484630353)
      ·
        refine ⟨9688006878184342863472765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12917342504245790484630353 9688006878184342863472765)
        ·
          refine ⟨3633002579319128573802287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9688006878184342863472765 3633002579319128573802287)
          ·
            refine ⟨5449503868978692860703431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633002579319128573802287 5449503868978692860703431)
            ·
              refine ⟨8174255803468039291055147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449503868978692860703431 8174255803468039291055147)
              ·
                refine ⟨12261383705202058936582721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174255803468039291055147 12261383705202058936582721)
                ·
                  refine ⟨9196037778901544202437041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12261383705202058936582721 9196037778901544202437041)
                  ·
                    refine ⟨6897028334176158151827781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196037778901544202437041 6897028334176158151827781)
                    ·
                      refine ⟨1293192812658029653467709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6897028334176158151827781 1293192812658029653467709)
                      ·
                        rfl

theorem cell23_2518484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2518484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518484 prefixEnd_2518484 := by exact prefixLift 2518484
  have htrace : WordTrace (prefixWord ++ tailWord_2518484) baseStart_2518484 baseEnd_2518484 := by
    simpa [prefixWord, tailWord_2518484, baseEnd_2518484] using wordTrace_append hprefix tailTrace_2518484
  have hstable : (prefixWord ++ tailWord_2518484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518484).length < 2 ^ (prefixWord ++ tailWord_2518484).sum := by decide
  have hdescent : baseEnd_2518484 < baseStart_2518484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518500 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2518500 : Nat := 118140960795 + 2518500 * 2 ^ 59
def prefixEnd_2518500 : Nat := 4983230072969 + 3 ^ 40 * 2518500 * 2
def baseEnd_2518500 : Nat := 1293201028348501590867635

theorem tailTrace_2518500 : CollatzResearch.WordTrace tailWord_2518500 prefixEnd_2518500 1293201028348501590867635 := by
  unfold tailWord_2518500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928620687956050200532477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61238160917274733600709969 45928620687956050200532477)
  ·
    refine ⟨17223232757983518825199679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45928620687956050200532477 17223232757983518825199679)
    ·
      refine ⟨25834849136975278237799519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17223232757983518825199679 25834849136975278237799519)
      ·
        refine ⟨38752273705462917356699279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25834849136975278237799519 38752273705462917356699279)
        ·
          refine ⟨58128410558194376035048919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38752273705462917356699279 58128410558194376035048919)
          ·
            refine ⟨87192615837291564052573379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58128410558194376035048919 87192615837291564052573379)
            ·
              refine ⟨130788923755937346078860069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87192615837291564052573379 130788923755937346078860069)
              ·
                refine ⟨24522923204238252389786263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130788923755937346078860069 24522923204238252389786263)
                ·
                  refine ⟨36784384806357378584679395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24522923204238252389786263 36784384806357378584679395)
                  ·
                    refine ⟨55176577209536067877019093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36784384806357378584679395 55176577209536067877019093)
                    ·
                      refine ⟨1293201028348501590867635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55176577209536067877019093 1293201028348501590867635)
                      ·
                        rfl

theorem cell23_2518500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2518500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518500 prefixEnd_2518500 := by exact prefixLift 2518500
  have htrace : WordTrace (prefixWord ++ tailWord_2518500) baseStart_2518500 baseEnd_2518500 := by
    simpa [prefixWord, tailWord_2518500, baseEnd_2518500] using wordTrace_append hprefix tailTrace_2518500
  have hstable : (prefixWord ++ tailWord_2518500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518500).length < 2 ^ (prefixWord ++ tailWord_2518500).sum := by decide
  have hdescent : baseEnd_2518500 < baseStart_2518500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518547 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3]
def baseStart_2518547 : Nat := 118140960795 + 2518547 * 2 ^ 59
def prefixEnd_2518547 : Nat := 4983230072969 + 3 ^ 40 * 2518547 * 2
def baseEnd_2518547 : Nat := 1293225161939262906979919

theorem tailTrace_2518547 : CollatzResearch.WordTrace tailWord_2518547 prefixEnd_2518547 1293225161939262906979919 := by
  unfold tailWord_2518547
  simp only [CollatzResearch.WordTrace]
  refine ⟨91858955606741827428025895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61239303737827884952017263 91858955606741827428025895)
  ·
    refine ⟨137788433410112741142038843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91858955606741827428025895 137788433410112741142038843)
    ·
      refine ⟨206682650115169111713058265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137788433410112741142038843 206682650115169111713058265)
      ·
        refine ⟨155011987586376833784793699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206682650115169111713058265 155011987586376833784793699)
        ·
          refine ⟨232517981379565250677190549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155011987586376833784793699 232517981379565250677190549)
          ·
            refine ⟨10899280377167121125493307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 232517981379565250677190549 10899280377167121125493307)
            ·
              refine ⟨16348920565750681688239961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899280377167121125493307 16348920565750681688239961)
              ·
                refine ⟨12261690424313011266179971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16348920565750681688239961 12261690424313011266179971)
                ·
                  refine ⟨18392535636469516899269957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12261690424313011266179971 18392535636469516899269957)
                  ·
                    refine ⟨3448600431838034418613117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18392535636469516899269957 3448600431838034418613117)
                    ·
                      refine ⟨1293225161939262906979919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448600431838034418613117 1293225161939262906979919)
                      ·
                        rfl

theorem cell23_2518547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_2518547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518547 prefixEnd_2518547 := by exact prefixLift 2518547
  have htrace : WordTrace (prefixWord ++ tailWord_2518547) baseStart_2518547 baseEnd_2518547 := by
    simpa [prefixWord, tailWord_2518547, baseEnd_2518547] using wordTrace_append hprefix tailTrace_2518547
  have hstable : (prefixWord ++ tailWord_2518547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518547).length < 2 ^ (prefixWord ++ tailWord_2518547).sum := by decide
  have hdescent : baseEnd_2518547 < baseStart_2518547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518557 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2518557 : Nat := 118140960795 + 2518557 * 2 ^ 59
def prefixEnd_2518557 : Nat := 4983230072969 + 3 ^ 40 * 2518557 * 2
def baseEnd_2518557 : Nat := 1293230296745807867854873

theorem tailTrace_2518557 : CollatzResearch.WordTrace tailWord_2518557 prefixEnd_2518557 1293230296745807867854873 := by
  unfold tailWord_2518557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91859320336705599135889925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61239546891137066090593283 91859320336705599135889925)
  ·
    refine ⟨17223622563132299837979361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91859320336705599135889925 17223622563132299837979361)
    ·
      refine ⟨12917716922349224878484521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17223622563132299837979361 12917716922349224878484521)
      ·
        refine ⟨9688287691761918658863391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12917716922349224878484521 9688287691761918658863391)
        ·
          refine ⟨14532431537642877988295087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688287691761918658863391 14532431537642877988295087)
          ·
            refine ⟨21798647306464316982442631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14532431537642877988295087 21798647306464316982442631)
            ·
              refine ⟨32697970959696475473663947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798647306464316982442631 32697970959696475473663947)
              ·
                refine ⟨49046956439544713210495921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32697970959696475473663947 49046956439544713210495921)
                ·
                  refine ⟨36785217329658534907871941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49046956439544713210495921 36785217329658534907871941)
                  ·
                    refine ⟨6897228249310975295225989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36785217329658534907871941 6897228249310975295225989)
                    ·
                      refine ⟨1293230296745807867854873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6897228249310975295225989 1293230296745807867854873)
                      ·
                        rfl

theorem cell23_2518557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2518557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518557 prefixEnd_2518557 := by exact prefixLift 2518557
  have htrace : WordTrace (prefixWord ++ tailWord_2518557) baseStart_2518557 baseEnd_2518557 := by
    simpa [prefixWord, tailWord_2518557, baseEnd_2518557] using wordTrace_append hprefix tailTrace_2518557
  have hstable : (prefixWord ++ tailWord_2518557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518557).length < 2 ^ (prefixWord ++ tailWord_2518557).sum := by decide
  have hdescent : baseEnd_2518557 < baseStart_2518557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518588 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_2518588 : Nat := 118140960795 + 2518588 * 2 ^ 59
def prefixEnd_2518588 : Nat := 4983230072969 + 3 ^ 40 * 2518588 * 2
def baseEnd_2518588 : Nat := 431082071548699082189077

theorem tailTrace_2518588 : CollatzResearch.WordTrace tailWord_2518588 prefixEnd_2518588 431082071548699082189077 := by
  unfold tailWord_2518588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45930225499796645715134209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61240300666395527620178945 45930225499796645715134209)
  ·
    refine ⟨34447669124847484286350657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45930225499796645715134209 34447669124847484286350657)
    ·
      refine ⟨25835751843635613214762993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34447669124847484286350657 25835751843635613214762993)
      ·
        refine ⟨19376813882726709911072245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25835751843635613214762993 19376813882726709911072245)
        ·
          refine ⟨1816576301505629054163023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19376813882726709911072245 1816576301505629054163023)
          ·
            refine ⟨2724864452258443581244535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816576301505629054163023 2724864452258443581244535)
            ·
              refine ⟨4087296678387665371866803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724864452258443581244535 4087296678387665371866803)
              ·
                refine ⟨6130945017581498057800205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087296678387665371866803 6130945017581498057800205)
                ·
                  refine ⟨2299104381593061771675077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6130945017581498057800205 2299104381593061771675077)
                  ·
                    refine ⟨431082071548699082189077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299104381593061771675077 431082071548699082189077)
                    ·
                      rfl

theorem cell23_2518588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_2518588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518588 prefixEnd_2518588 := by exact prefixLift 2518588
  have htrace : WordTrace (prefixWord ++ tailWord_2518588) baseStart_2518588 baseEnd_2518588 := by
    simpa [prefixWord, tailWord_2518588, baseEnd_2518588] using wordTrace_append hprefix tailTrace_2518588
  have hstable : (prefixWord ++ tailWord_2518588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518588).length < 2 ^ (prefixWord ++ tailWord_2518588).sum := by decide
  have hdescent : baseEnd_2518588 < baseStart_2518588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518597 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_2518597 : Nat := 118140960795 + 2518597 * 2 ^ 59
def prefixEnd_2518597 : Nat := 4983230072969 + 3 ^ 40 * 2518597 * 2
def baseEnd_2518597 : Nat := 431083611990662570451563

theorem tailTrace_2518597 : CollatzResearch.WordTrace tailWord_2518597 prefixEnd_2518597 431083611990662570451563 := by
  unfold tailWord_2518597
  simp only [CollatzResearch.WordTrace]
  refine ⟨91860779256560685967346045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61240519504373790644897363 91860779256560685967346045)
  ·
    refine ⟨34447792221210257237754767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91860779256560685967346045 34447792221210257237754767)
    ·
      refine ⟨51671688331815385856632151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34447792221210257237754767 51671688331815385856632151)
      ·
        refine ⟨77507532497723078784948227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51671688331815385856632151 77507532497723078784948227)
        ·
          refine ⟨116261298746584618177422341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77507532497723078784948227 116261298746584618177422341)
          ·
            refine ⟨21798993514984615908266689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116261298746584618177422341 21798993514984615908266689)
            ·
              refine ⟨16349245136238461931200017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21798993514984615908266689 16349245136238461931200017)
              ·
                refine ⟨12261933852178846448400013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16349245136238461931200017 12261933852178846448400013)
                ·
                  refine ⟨4598225194567067418150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12261933852178846448400013 4598225194567067418150005)
                  ·
                    refine ⟨431083611990662570451563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4598225194567067418150005 431083611990662570451563)
                    ·
                      rfl

theorem cell23_2518597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_2518597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518597 prefixEnd_2518597 := by exact prefixLift 2518597
  have htrace : WordTrace (prefixWord ++ tailWord_2518597) baseStart_2518597 baseEnd_2518597 := by
    simpa [prefixWord, tailWord_2518597, baseEnd_2518597] using wordTrace_append hprefix tailTrace_2518597
  have hstable : (prefixWord ++ tailWord_2518597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518597).length < 2 ^ (prefixWord ++ tailWord_2518597).sum := by decide
  have hdescent : baseEnd_2518597 < baseStart_2518597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518627 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 6]
def baseStart_2518627 : Nat := 118140960795 + 2518627 * 2 ^ 59
def prefixEnd_2518627 : Nat := 4983230072969 + 3 ^ 40 * 2518627 * 2
def baseEnd_2518627 : Nat := 431088746797207531326517

theorem tailTrace_2518627 : CollatzResearch.WordTrace tailWord_2518627 prefixEnd_2518627 431088746797207531326517 := by
  unfold tailWord_2518627
  simp only [CollatzResearch.WordTrace]
  refine ⟨91861873446452001090938135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61241248964301334060625423 91861873446452001090938135)
  ·
    refine ⟨137792810169678001636407203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91861873446452001090938135 137792810169678001636407203)
    ·
      refine ⟨206689215254517002454610805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137792810169678001636407203 206689215254517002454610805)
      ·
        refine ⟨19377113930110968980119763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206689215254517002454610805 19377113930110968980119763)
        ·
          refine ⟨29065670895166453470179645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19377113930110968980119763 29065670895166453470179645)
          ·
            refine ⟨10899626585687420051317367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29065670895166453470179645 10899626585687420051317367)
            ·
              refine ⟨16349439878531130076976051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899626585687420051317367 16349439878531130076976051)
              ·
                refine ⟨24524159817796695115464077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16349439878531130076976051 24524159817796695115464077)
                ·
                  refine ⟨9196559931673760668299029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24524159817796695115464077 9196559931673760668299029)
                  ·
                    refine ⟨431088746797207531326517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9196559931673760668299029 431088746797207531326517)
                    ·
                      rfl

theorem cell23_2518627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_2518627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518627 prefixEnd_2518627 := by exact prefixLift 2518627
  have htrace : WordTrace (prefixWord ++ tailWord_2518627) baseStart_2518627 baseEnd_2518627 := by
    simpa [prefixWord, tailWord_2518627, baseEnd_2518627] using wordTrace_append hprefix tailTrace_2518627
  have hstable : (prefixWord ++ tailWord_2518627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518627).length < 2 ^ (prefixWord ++ tailWord_2518627).sum := by decide
  have hdescent : baseEnd_2518627 < baseStart_2518627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518645 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2518645 : Nat := 118140960795 + 2518645 * 2 ^ 59
def prefixEnd_2518645 : Nat := 4983230072969 + 3 ^ 40 * 2518645 * 2
def baseEnd_2518645 : Nat := 1293275483043403523554469

theorem tailTrace_2518645 : CollatzResearch.WordTrace tailWord_2518645 prefixEnd_2518645 1293275483043403523554469 := by
  unfold tailWord_2518645
  simp only [CollatzResearch.WordTrace]
  refine ⟨91862529960386790165093389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61241686640257860110062259 91862529960386790165093389)
  ·
    refine ⟨34448448735145046311910021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91862529960386790165093389 34448448735145046311910021)
    ·
      refine ⟨6459084137839696183483129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34448448735145046311910021 6459084137839696183483129)
      ·
        refine ⟨4844313103379772137612347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6459084137839696183483129 4844313103379772137612347)
        ·
          refine ⟨7266469655069658206418521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844313103379772137612347 7266469655069658206418521)
          ·
            refine ⟨5449852241302243654813891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7266469655069658206418521 5449852241302243654813891)
            ·
              refine ⟨8174778361953365482220837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449852241302243654813891 8174778361953365482220837)
              ·
                refine ⟨1532770942866256027916407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8174778361953365482220837 1532770942866256027916407)
                ·
                  refine ⟨2299156414299384041874611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532770942866256027916407 2299156414299384041874611)
                  ·
                    refine ⟨3448734621449076062811917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2299156414299384041874611 3448734621449076062811917)
                    ·
                      refine ⟨1293275483043403523554469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448734621449076062811917 1293275483043403523554469)
                      ·
                        rfl

theorem cell23_2518645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2518645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518645 prefixEnd_2518645 := by exact prefixLift 2518645
  have htrace : WordTrace (prefixWord ++ tailWord_2518645) baseStart_2518645 baseEnd_2518645 := by
    simpa [prefixWord, tailWord_2518645, baseEnd_2518645] using wordTrace_append hprefix tailTrace_2518645
  have hstable : (prefixWord ++ tailWord_2518645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518645).length < 2 ^ (prefixWord ++ tailWord_2518645).sum := by decide
  have hdescent : baseEnd_2518645 < baseStart_2518645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518647 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2518647 : Nat := 118140960795 + 2518647 * 2 ^ 59
def prefixEnd_2518647 : Nat := 4983230072969 + 3 ^ 40 * 2518647 * 2
def baseEnd_2518647 : Nat := 1293276510004712515729459

theorem tailTrace_2518647 : CollatzResearch.WordTrace tailWord_2518647 prefixEnd_2518647 1293276510004712515729459 := by
  unfold tailWord_2518647
  simp only [CollatzResearch.WordTrace]
  refine ⟨91862602906379544506666195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61241735270919696337777463 91862602906379544506666195)
  ·
    refine ⟨137793904359569316759999293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91862602906379544506666195 137793904359569316759999293)
    ·
      refine ⟨51672714134838493784999735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137793904359569316759999293 51672714134838493784999735)
      ·
        refine ⟨77509071202257740677499603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51672714134838493784999735 77509071202257740677499603)
        ·
          refine ⟨116263606803386611016249405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77509071202257740677499603 116263606803386611016249405)
          ·
            refine ⟨43598852551269979131093527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116263606803386611016249405 43598852551269979131093527)
            ·
              refine ⟨65398278826904968696640291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43598852551269979131093527 65398278826904968696640291)
              ·
                refine ⟨98097418240357453044960437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65398278826904968696640291 98097418240357453044960437)
                ·
                  refine ⟨9196632960033511222965041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98097418240357453044960437 9196632960033511222965041)
                  ·
                    refine ⟨6897474720025133417223781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196632960033511222965041 6897474720025133417223781)
                    ·
                      refine ⟨1293276510004712515729459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6897474720025133417223781 1293276510004712515729459)
                      ·
                        rfl

theorem cell23_2518647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2518647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518647 prefixEnd_2518647 := by exact prefixLift 2518647
  have htrace : WordTrace (prefixWord ++ tailWord_2518647) baseStart_2518647 baseEnd_2518647 := by
    simpa [prefixWord, tailWord_2518647, baseEnd_2518647] using wordTrace_append hprefix tailTrace_2518647
  have hstable : (prefixWord ++ tailWord_2518647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518647).length < 2 ^ (prefixWord ++ tailWord_2518647).sum := by decide
  have hdescent : baseEnd_2518647 < baseStart_2518647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518651 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 3, 2, 2]
def baseStart_2518651 : Nat := 118140960795 + 2518651 * 2 ^ 59
def prefixEnd_2518651 : Nat := 4983230072969 + 3 ^ 40 * 2518651 * 2
def baseEnd_2518651 : Nat := 1293278563927330500079441

theorem tailTrace_2518651 : CollatzResearch.WordTrace tailWord_2518651 prefixEnd_2518651 1293278563927330500079441 := by
  unfold tailWord_2518651
  simp only [CollatzResearch.WordTrace]
  refine ⟨91862748798365053189811807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61241832532243368793207871 91862748798365053189811807)
  ·
    refine ⟨137794123197547579784717711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91862748798365053189811807 137794123197547579784717711)
    ·
      refine ⟨206691184796321369677076567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137794123197547579784717711 206691184796321369677076567)
      ·
        refine ⟨310036777194482054515614851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206691184796321369677076567 310036777194482054515614851)
        ·
          refine ⟨465055165791723081773422277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310036777194482054515614851 465055165791723081773422277)
          ·
            refine ⟨87197843585948077832516677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465055165791723081773422277 87197843585948077832516677)
            ·
              refine ⟨16349595672365264593596877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87197843585948077832516677 16349595672365264593596877)
              ·
                refine ⟨6131098377136974222598829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16349595672365264593596877 6131098377136974222598829)
                ·
                  refine ⟨2299161891426365333474561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6131098377136974222598829 2299161891426365333474561)
                  ·
                    refine ⟨1724371418569774000105921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2299161891426365333474561 1724371418569774000105921)
                    ·
                      refine ⟨1293278563927330500079441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724371418569774000105921 1293278563927330500079441)
                      ·
                        rfl

theorem cell23_2518651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2, 2].length) (baseStart_2518651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518651 prefixEnd_2518651 := by exact prefixLift 2518651
  have htrace : WordTrace (prefixWord ++ tailWord_2518651) baseStart_2518651 baseEnd_2518651 := by
    simpa [prefixWord, tailWord_2518651, baseEnd_2518651] using wordTrace_append hprefix tailTrace_2518651
  have hstable : (prefixWord ++ tailWord_2518651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518651).length < 2 ^ (prefixWord ++ tailWord_2518651).sum := by decide
  have hdescent : baseEnd_2518651 < baseStart_2518651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518688 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3]
def baseStart_2518688 : Nat := 118140960795 + 2518688 * 2 ^ 59
def prefixEnd_2518688 : Nat := 4983230072969 + 3 ^ 40 * 2518688 * 2
def baseEnd_2518688 : Nat := 1293297562711546855316771

theorem tailTrace_2518688 : CollatzResearch.WordTrace tailWord_2518688 prefixEnd_2518688 1293297562711546855316771 := by
  unfold tailWord_2518688
  simp only [CollatzResearch.WordTrace]
  refine ⟨45932049149615504254454359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61242732199487339005939145 45932049149615504254454359)
  ·
    refine ⟨68898073724423256381681539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45932049149615504254454359 68898073724423256381681539)
    ·
      refine ⟨103347110586634884572522309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68898073724423256381681539 103347110586634884572522309)
      ·
        refine ⟨19377583234994040857347933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103347110586634884572522309 19377583234994040857347933)
        ·
          refine ⟨7266593713122765321505475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19377583234994040857347933 7266593713122765321505475)
          ·
            refine ⟨10899890569684147982258213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266593713122765321505475 10899890569684147982258213)
            ·
              refine ⟨2043729481815777746673415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10899890569684147982258213 2043729481815777746673415)
              ·
                refine ⟨3065594222723666620010123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043729481815777746673415 3065594222723666620010123)
                ·
                  refine ⟨4598391334085499930015185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065594222723666620010123 4598391334085499930015185)
                  ·
                    refine ⟨3448793500564124947511389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598391334085499930015185 3448793500564124947511389)
                    ·
                      refine ⟨1293297562711546855316771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448793500564124947511389 1293297562711546855316771)
                      ·
                        rfl

theorem cell23_2518688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_2518688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518688 prefixEnd_2518688 := by exact prefixLift 2518688
  have htrace : WordTrace (prefixWord ++ tailWord_2518688) baseStart_2518688 baseEnd_2518688 := by
    simpa [prefixWord, tailWord_2518688, baseEnd_2518688] using wordTrace_append hprefix tailTrace_2518688
  have hstable : (prefixWord ++ tailWord_2518688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518688).length < 2 ^ (prefixWord ++ tailWord_2518688).sum := by decide
  have hdescent : baseEnd_2518688 < baseStart_2518688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518702 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2518702 : Nat := 118140960795 + 2518702 * 2 ^ 59
def prefixEnd_2518702 : Nat := 4983230072969 + 3 ^ 40 * 2518702 * 2
def baseEnd_2518702 : Nat := 1293304751440709800541707

theorem tailTrace_2518702 : CollatzResearch.WordTrace tailWord_2518702 prefixEnd_2518702 1293304751440709800541707 := by
  unfold tailWord_2518702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483076115147536112489795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61243072614120192599945573 11483076115147536112489795)
  ·
    refine ⟨17224614172721304168734693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11483076115147536112489795 17224614172721304168734693)
    ·
      refine ⟨3229615157385244531637755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17224614172721304168734693 3229615157385244531637755)
      ·
        refine ⟨4844422736077866797456633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229615157385244531637755 4844422736077866797456633)
        ·
          refine ⟨3633317052058400098092475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844422736077866797456633 3633317052058400098092475)
          ·
            refine ⟨5449975578087600147138713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633317052058400098092475 5449975578087600147138713)
            ·
              refine ⟨4087481683565700110354035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449975578087600147138713 4087481683565700110354035)
              ·
                refine ⟨6131222525348550165531053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087481683565700110354035 6131222525348550165531053)
                ·
                  refine ⟨2299208447005706312074145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6131222525348550165531053 2299208447005706312074145)
                  ·
                    refine ⟨1724406335254279734055609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2299208447005706312074145 1724406335254279734055609)
                    ·
                      refine ⟨1293304751440709800541707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724406335254279734055609 1293304751440709800541707)
                      ·
                        rfl

theorem cell23_2518702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2518702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518702 prefixEnd_2518702 := by exact prefixLift 2518702
  have htrace : WordTrace (prefixWord ++ tailWord_2518702) baseStart_2518702 baseEnd_2518702 := by
    simpa [prefixWord, tailWord_2518702, baseEnd_2518702] using wordTrace_append hprefix tailTrace_2518702
  have hstable : (prefixWord ++ tailWord_2518702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518702).length < 2 ^ (prefixWord ++ tailWord_2518702).sum := by decide
  have hdescent : baseEnd_2518702 < baseStart_2518702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518718 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2518718 : Nat := 118140960795 + 2518718 * 2 ^ 59
def prefixEnd_2518718 : Nat := 4983230072969 + 3 ^ 40 * 2518718 * 2
def baseEnd_2518718 : Nat := 1293312967131181737941633

theorem tailTrace_2518718 : CollatzResearch.WordTrace tailWord_2518718 prefixEnd_2518718 1293312967131181737941633 := by
  unfold tailWord_2518718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483149061140290454062601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61243461659414882421667205 11483149061140290454062601)
  ·
    refine ⟨8612361795855217840546951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11483149061140290454062601 8612361795855217840546951)
    ·
      refine ⟨12918542693782826760820427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8612361795855217840546951 12918542693782826760820427)
      ·
        refine ⟨19377814040674240141230641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12918542693782826760820427 19377814040674240141230641)
        ·
          refine ⟨14533360530505680105922981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19377814040674240141230641 14533360530505680105922981)
          ·
            refine ⟨2725005099469815019860559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14533360530505680105922981 2725005099469815019860559)
            ·
              refine ⟨4087507649204722529790839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725005099469815019860559 4087507649204722529790839)
              ·
                refine ⟨6131261473807083794686259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087507649204722529790839 6131261473807083794686259)
                ·
                  refine ⟨9196892210710625692029389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131261473807083794686259 9196892210710625692029389)
                  ·
                    refine ⟨3448834579016484634511021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9196892210710625692029389 3448834579016484634511021)
                    ·
                      refine ⟨1293312967131181737941633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3448834579016484634511021 1293312967131181737941633)
                      ·
                        rfl

theorem cell23_2518718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2518718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518718 prefixEnd_2518718 := by exact prefixLift 2518718
  have htrace : WordTrace (prefixWord ++ tailWord_2518718) baseStart_2518718 baseEnd_2518718 := by
    simpa [prefixWord, tailWord_2518718, baseEnd_2518718] using wordTrace_append hprefix tailTrace_2518718
  have hstable : (prefixWord ++ tailWord_2518718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518718).length < 2 ^ (prefixWord ++ tailWord_2518718).sum := by decide
  have hdescent : baseEnd_2518718 < baseStart_2518718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518728 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_2518728 : Nat := 118140960795 + 2518728 * 2 ^ 59
def prefixEnd_2518728 : Nat := 4983230072969 + 3 ^ 40 * 2518728 * 2
def baseEnd_2518728 : Nat := 1293318101937726698816587

theorem tailTrace_2518728 : CollatzResearch.WordTrace tailWord_2518728 prefixEnd_2518728 1293318101937726698816587 := by
  unfold tailWord_2518728
  simp only [CollatzResearch.WordTrace]
  refine ⟨45932778609543047670182419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61243704812724063560243225 45932778609543047670182419)
  ·
    refine ⟨68899167914314571505273629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45932778609543047670182419 68899167914314571505273629)
    ·
      refine ⟨25837187967867964314477611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68899167914314571505273629 25837187967867964314477611)
      ·
        refine ⟨38755781951801946471716417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25837187967867964314477611 38755781951801946471716417)
        ·
          refine ⟨29066836463851459853787313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38755781951801946471716417 29066836463851459853787313)
          ·
            refine ⟨21800127347888594890340485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29066836463851459853787313 21800127347888594890340485)
            ·
              refine ⟨4087523877729111541938841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21800127347888594890340485 4087523877729111541938841)
              ·
                refine ⟨3065642908296833656454131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087523877729111541938841 3065642908296833656454131)
                ·
                  refine ⟨4598464362445250484681197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065642908296833656454131 4598464362445250484681197)
                  ·
                    refine ⟨1724424135916968931755449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4598464362445250484681197 1724424135916968931755449)
                    ·
                      refine ⟨1293318101937726698816587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724424135916968931755449 1293318101937726698816587)
                      ·
                        rfl

theorem cell23_2518728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_2518728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518728 prefixEnd_2518728 := by exact prefixLift 2518728
  have htrace : WordTrace (prefixWord ++ tailWord_2518728) baseStart_2518728 baseEnd_2518728 := by
    simpa [prefixWord, tailWord_2518728, baseEnd_2518728] using wordTrace_append hprefix tailTrace_2518728
  have hstable : (prefixWord ++ tailWord_2518728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518728).length < 2 ^ (prefixWord ++ tailWord_2518728).sum := by decide
  have hdescent : baseEnd_2518728 < baseStart_2518728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518744 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2518744 : Nat := 118140960795 + 2518744 * 2 ^ 59
def prefixEnd_2518744 : Nat := 4983230072969 + 3 ^ 40 * 2518744 * 2
def baseEnd_2518744 : Nat := 1293326317628198636216513

theorem tailTrace_2518744 : CollatzResearch.WordTrace tailWord_2518744 prefixEnd_2518744 1293326317628198636216513 := by
  unfold tailWord_2518744
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933070393514065036473643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61244093858018753381964857 45933070393514065036473643)
  ·
    refine ⟨68899605590271097554710465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45933070393514065036473643 68899605590271097554710465)
    ·
      refine ⟨51674704192703323166032849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68899605590271097554710465 51674704192703323166032849)
      ·
        refine ⟨38756028144527492374524637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51674704192703323166032849 38756028144527492374524637)
        ·
          refine ⟨14533510554197809640446739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38756028144527492374524637 14533510554197809640446739)
          ·
            refine ⟨21800265831296714460670109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14533510554197809640446739 21800265831296714460670109)
            ·
              refine ⟨8175099686736267922751291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21800265831296714460670109 8175099686736267922751291)
              ·
                refine ⟨12262649530104401884126937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175099686736267922751291 12262649530104401884126937)
                ·
                  refine ⟨9196987147578301413095203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12262649530104401884126937 9196987147578301413095203)
                  ·
                    refine ⟨13795480721367452119642805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9196987147578301413095203 13795480721367452119642805)
                    ·
                      refine ⟨1293326317628198636216513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13795480721367452119642805 1293326317628198636216513)
                      ·
                        rfl

theorem cell23_2518744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2518744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518744 prefixEnd_2518744 := by exact prefixLift 2518744
  have htrace : WordTrace (prefixWord ++ tailWord_2518744) baseStart_2518744 baseEnd_2518744 := by
    simpa [prefixWord, tailWord_2518744, baseEnd_2518744] using wordTrace_append hprefix tailTrace_2518744
  have hstable : (prefixWord ++ tailWord_2518744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518744).length < 2 ^ (prefixWord ++ tailWord_2518744).sum := by decide
  have hdescent : baseEnd_2518744 < baseStart_2518744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518764 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 7]
def baseStart_2518764 : Nat := 118140960795 + 2518764 * 2 ^ 59
def prefixEnd_2518764 : Nat := 4983230072969 + 3 ^ 40 * 2518764 * 2
def baseEnd_2518764 : Nat := 143704065249032061996269

theorem tailTrace_2518764 : CollatzResearch.WordTrace tailWord_2518764 prefixEnd_2518764 143704065249032061996269 := by
  unfold tailWord_2518764
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933435123477836744337673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61244580164637115659116897 45933435123477836744337673)
  ·
    refine ⟨34450076342608377558253255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45933435123477836744337673 34450076342608377558253255)
    ·
      refine ⟨51675114513912566337379883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34450076342608377558253255 51675114513912566337379883)
      ·
        refine ⟨77512671770868849506069825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51675114513912566337379883 77512671770868849506069825)
        ·
          refine ⟨58134503828151637129552369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77512671770868849506069825 58134503828151637129552369)
          ·
            refine ⟨43600877871113727847164277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58134503828151637129552369 43600877871113727847164277)
            ·
              refine ⟨4087582300416911985671651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43600877871113727847164277 4087582300416911985671651)
              ·
                refine ⟨6131373450625367978507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087582300416911985671651 6131373450625367978507477)
                ·
                  refine ⟨143704065249032061996269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6131373450625367978507477 143704065249032061996269)
                  ·
                    rfl

theorem cell23_2518764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_2518764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518764 prefixEnd_2518764 := by exact prefixLift 2518764
  have htrace : WordTrace (prefixWord ++ tailWord_2518764) baseStart_2518764 baseEnd_2518764 := by
    simpa [prefixWord, tailWord_2518764, baseEnd_2518764] using wordTrace_append hprefix tailTrace_2518764
  have hstable : (prefixWord ++ tailWord_2518764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518764).length < 2 ^ (prefixWord ++ tailWord_2518764).sum := by decide
  have hdescent : baseEnd_2518764 < baseStart_2518764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518775 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_2518775 : Nat := 118140960795 + 2518775 * 2 ^ 59
def prefixEnd_2518775 : Nat := 4983230072969 + 3 ^ 40 * 2518775 * 2
def baseEnd_2518775 : Nat := 1293342235528488014928871

theorem tailTrace_2518775 : CollatzResearch.WordTrace tailWord_2518775 prefixEnd_2518775 1293342235528488014928871 := by
  unfold tailWord_2518775
  simp only [CollatzResearch.WordTrace]
  refine ⟨91867271449915822367325779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61244847633277214911550519 91867271449915822367325779)
  ·
    refine ⟨137800907174873733550988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91867271449915822367325779 137800907174873733550988669)
    ·
      refine ⟨51675340190577650081620751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137800907174873733550988669 51675340190577650081620751)
      ·
        refine ⟨77513010285866475122431127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51675340190577650081620751 77513010285866475122431127)
        ·
          refine ⟨116269515428799712683646691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77513010285866475122431127 116269515428799712683646691)
          ·
            refine ⟨174404273143199569025470037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116269515428799712683646691 174404273143199569025470037)
            ·
              refine ⟨2043800075896869949517227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 174404273143199569025470037 2043800075896869949517227)
              ·
                refine ⟨3065700113845304924275841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043800075896869949517227 3065700113845304924275841)
                ·
                  refine ⟨2299275085383978693206881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065700113845304924275841 2299275085383978693206881)
                  ·
                    refine ⟨1724456314037984019905161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2299275085383978693206881 1724456314037984019905161)
                    ·
                      refine ⟨1293342235528488014928871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724456314037984019905161 1293342235528488014928871)
                      ·
                        rfl

theorem cell23_2518775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_2518775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518775 prefixEnd_2518775 := by exact prefixLift 2518775
  have htrace : WordTrace (prefixWord ++ tailWord_2518775) baseStart_2518775 baseEnd_2518775 := by
    simpa [prefixWord, tailWord_2518775, baseEnd_2518775] using wordTrace_append hprefix tailTrace_2518775
  have hstable : (prefixWord ++ tailWord_2518775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518775).length < 2 ^ (prefixWord ++ tailWord_2518775).sum := by decide
  have hdescent : baseEnd_2518775 < baseStart_2518775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518831 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 4, 2]
def baseStart_2518831 : Nat := 118140960795 + 2518831 * 2 ^ 59
def prefixEnd_2518831 : Nat := 4983230072969 + 3 ^ 40 * 2518831 * 2
def baseEnd_2518831 : Nat := 1293370990445139795828613

theorem tailTrace_2518831 : CollatzResearch.WordTrace tailWord_2518831 prefixEnd_2518831 1293370990445139795828613 := by
  unfold tailWord_2518831
  simp only [CollatzResearch.WordTrace]
  refine ⟨91869313937712943931364347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61246209291808629287576231 91869313937712943931364347)
  ·
    refine ⟨137803970906569415897046521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91869313937712943931364347 137803970906569415897046521)
    ·
      refine ⟨103352978179927061922784891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137803970906569415897046521 103352978179927061922784891)
      ·
        refine ⟨155029467269890592884177337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103352978179927061922784891 155029467269890592884177337)
        ·
          refine ⟨116272100452417944663133003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155029467269890592884177337 116272100452417944663133003)
          ·
            refine ⟨174408150678626916994699505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116272100452417944663133003 174408150678626916994699505)
            ·
              refine ⟨130806113008970187746024629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174408150678626916994699505 130806113008970187746024629)
              ·
                refine ⟨12263073094590955101189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130806113008970187746024629 12263073094590955101189809)
                ·
                  refine ⟨9197304820943216325892357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12263073094590955101189809 9197304820943216325892357)
                  ·
                    refine ⟨1724494653926853061104817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9197304820943216325892357 1724494653926853061104817)
                    ·
                      refine ⟨1293370990445139795828613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724494653926853061104817 1293370990445139795828613)
                      ·
                        rfl

theorem cell23_2518831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4, 2].length) (baseStart_2518831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518831 prefixEnd_2518831 := by exact prefixLift 2518831
  have htrace : WordTrace (prefixWord ++ tailWord_2518831) baseStart_2518831 baseEnd_2518831 := by
    simpa [prefixWord, tailWord_2518831, baseEnd_2518831] using wordTrace_append hprefix tailTrace_2518831
  have hstable : (prefixWord ++ tailWord_2518831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518831).length < 2 ^ (prefixWord ++ tailWord_2518831).sum := by decide
  have hdescent : baseEnd_2518831 < baseStart_2518831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518851 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3]
def baseStart_2518851 : Nat := 118140960795 + 2518851 * 2 ^ 59
def prefixEnd_2518851 : Nat := 4983230072969 + 3 ^ 40 * 2518851 * 2
def baseEnd_2518851 : Nat := 1293381260058229717578521

theorem tailTrace_2518851 : CollatzResearch.WordTrace tailWord_2518851 prefixEnd_2518851 1293381260058229717578521 := by
  unfold tailWord_2518851
  simp only [CollatzResearch.WordTrace]
  refine ⟨91870043397640487347092407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61246695598426991564728271 91870043397640487347092407)
  ·
    refine ⟨137805065096460731020638611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91870043397640487347092407 137805065096460731020638611)
    ·
      refine ⟨206707597644691096530957917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137805065096460731020638611 206707597644691096530957917)
      ·
        refine ⟨77515349116759161199109219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206707597644691096530957917 77515349116759161199109219)
        ·
          refine ⟨116273023675138741798663829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77515349116759161199109219 116273023675138741798663829)
          ·
            refine ⟨5450297984772128521812367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116273023675138741798663829 5450297984772128521812367)
            ·
              refine ⟨8175446977158192782718551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450297984772128521812367 8175446977158192782718551)
              ·
                refine ⟨12263170465737289174077827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175446977158192782718551 12263170465737289174077827)
                ·
                  refine ⟨18394755698605933761116741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12263170465737289174077827 18394755698605933761116741)
                  ·
                    refine ⟨3449016693488612580209389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18394755698605933761116741 3449016693488612580209389)
                    ·
                      refine ⟨1293381260058229717578521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449016693488612580209389 1293381260058229717578521)
                      ·
                        rfl

theorem cell23_2518851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_2518851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518851 prefixEnd_2518851 := by exact prefixLift 2518851
  have htrace : WordTrace (prefixWord ++ tailWord_2518851) baseStart_2518851 baseEnd_2518851 := by
    simpa [prefixWord, tailWord_2518851, baseEnd_2518851] using wordTrace_append hprefix tailTrace_2518851
  have hstable : (prefixWord ++ tailWord_2518851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518851).length < 2 ^ (prefixWord ++ tailWord_2518851).sum := by decide
  have hdescent : baseEnd_2518851 < baseStart_2518851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518871 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 8]
def baseStart_2518871 : Nat := 118140960795 + 2518871 * 2 ^ 59
def prefixEnd_2518871 : Nat := 4983230072969 + 3 ^ 40 * 2518871 * 2
def baseEnd_2518871 : Nat := 143710169963479959925381

theorem tailTrace_2518871 : CollatzResearch.WordTrace tailWord_2518871 prefixEnd_2518871 143710169963479959925381 := by
  unfold tailWord_2518871
  simp only [CollatzResearch.WordTrace]
  refine ⟨91870772857568030762820467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61247181905045353841880311 91870772857568030762820467)
  ·
    refine ⟨137806159286352046144230701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91870772857568030762820467 137806159286352046144230701)
    ·
      refine ⟨51677309732382017304086513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137806159286352046144230701 51677309732382017304086513)
      ·
        refine ⟨38757982299286512978064885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51677309732382017304086513 38757982299286512978064885)
        ·
          refine ⟨3633560840558110591693583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38757982299286512978064885 3633560840558110591693583)
          ·
            refine ⟨5450341260837165887540375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633560840558110591693583 5450341260837165887540375)
            ·
              refine ⟨8175511891255748831310563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450341260837165887540375 8175511891255748831310563)
              ·
                refine ⟨12263267836883623246965845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175511891255748831310563 12263267836883623246965845)
                ·
                  refine ⟨143710169963479959925381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12263267836883623246965845 143710169963479959925381)
                  ·
                    rfl

theorem cell23_2518871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 8].length) (baseStart_2518871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518871 prefixEnd_2518871 := by exact prefixLift 2518871
  have htrace : WordTrace (prefixWord ++ tailWord_2518871) baseStart_2518871 baseEnd_2518871 := by
    simpa [prefixWord, tailWord_2518871, baseEnd_2518871] using wordTrace_append hprefix tailTrace_2518871
  have hstable : (prefixWord ++ tailWord_2518871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518871).length < 2 ^ (prefixWord ++ tailWord_2518871).sum := by decide
  have hdescent : baseEnd_2518871 < baseStart_2518871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518874 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2518874 : Nat := 118140960795 + 2518874 * 2 ^ 59
def prefixEnd_2518874 : Nat := 4983230072969 + 3 ^ 40 * 2518874 * 2
def baseEnd_2518874 : Nat := 1293393070113283127590915

theorem tailTrace_2518874 : CollatzResearch.WordTrace tailWord_2518874 prefixEnd_2518874 1293393070113283127590915 := by
  unfold tailWord_2518874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967720569139290568794919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61247254851038108183453117 22967720569139290568794919)
  ·
    refine ⟨34451580853708935853192379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22967720569139290568794919 34451580853708935853192379)
    ·
      refine ⟨51677371280563403779788569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34451580853708935853192379 51677371280563403779788569)
      ·
        refine ⟨38758028460422552834841427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51677371280563403779788569 38758028460422552834841427)
        ·
          refine ⟨58137042690633829252262141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38758028460422552834841427 58137042690633829252262141)
          ·
            refine ⟨21801391008987685969598303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58137042690633829252262141 21801391008987685969598303)
            ·
              refine ⟨32702086513481528954397455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21801391008987685969598303 32702086513481528954397455)
              ·
                refine ⟨49053129770222293431596183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32702086513481528954397455 49053129770222293431596183)
                ·
                  refine ⟨73579694655333440147394275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49053129770222293431596183 73579694655333440147394275)
                  ·
                    refine ⟨110369541983000160221091413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73579694655333440147394275 110369541983000160221091413)
                    ·
                      refine ⟨1293393070113283127590915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 110369541983000160221091413 1293393070113283127590915)
                      ·
                        rfl

theorem cell23_2518874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2518874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518874 prefixEnd_2518874 := by exact prefixLift 2518874
  have htrace : WordTrace (prefixWord ++ tailWord_2518874) baseStart_2518874 baseEnd_2518874 := by
    simpa [prefixWord, tailWord_2518874, baseEnd_2518874] using wordTrace_append hprefix tailTrace_2518874
  have hstable : (prefixWord ++ tailWord_2518874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518874).length < 2 ^ (prefixWord ++ tailWord_2518874).sum := by decide
  have hdescent : baseEnd_2518874 < baseStart_2518874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518888 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 6]
def baseStart_2518888 : Nat := 118140960795 + 2518888 * 2 ^ 59
def prefixEnd_2518888 : Nat := 4983230072969 + 3 ^ 40 * 2518888 * 2
def baseEnd_2518888 : Nat := 143711139871382896979539

theorem tailTrace_2518888 : CollatzResearch.WordTrace tailWord_2518888 prefixEnd_2518888 143711139871382896979539 := by
  unfold tailWord_2518888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45935696449253221333094659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61247595265670961777459545 45935696449253221333094659)
  ·
    refine ⟨68903544673879831999641989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45935696449253221333094659 68903544673879831999641989)
    ·
      refine ⟨12919414626352468499932873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68903544673879831999641989 12919414626352468499932873)
      ·
        refine ⟨9689560969764351374949655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12919414626352468499932873 9689560969764351374949655)
        ·
          refine ⟨14534341454646527062424483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689560969764351374949655 14534341454646527062424483)
          ·
            refine ⟨21801512181969790593636725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14534341454646527062424483 21801512181969790593636725)
            ·
              refine ⟨2043891767059667868153443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21801512181969790593636725 2043891767059667868153443)
              ·
                refine ⟨3065837650589501802230165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043891767059667868153443 3065837650589501802230165)
                ·
                  refine ⟨143711139871382896979539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3065837650589501802230165 143711139871382896979539)
                  ·
                    rfl

theorem cell23_2518888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_2518888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518888 prefixEnd_2518888 := by exact prefixLift 2518888
  have htrace : WordTrace (prefixWord ++ tailWord_2518888) baseStart_2518888 baseEnd_2518888 := by
    simpa [prefixWord, tailWord_2518888, baseEnd_2518888] using wordTrace_append hprefix tailTrace_2518888
  have hstable : (prefixWord ++ tailWord_2518888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518888).length < 2 ^ (prefixWord ++ tailWord_2518888).sum := by decide
  have hdescent : baseEnd_2518888 < baseStart_2518888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518932 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2518932 : Nat := 118140960795 + 2518932 * 2 ^ 59
def prefixEnd_2518932 : Nat := 4983230072969 + 3 ^ 40 * 2518932 * 2
def baseEnd_2518932 : Nat := 1293422851991243900665649

theorem tailTrace_2518932 : CollatzResearch.WordTrace tailWord_2518932 prefixEnd_2518932 1293422851991243900665649 := by
  unfold tailWord_2518932
  simp only [CollatzResearch.WordTrace]
  refine ⟨45936498855173519090395525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61248665140231358787194033 45936498855173519090395525)
  ·
    refine ⟨8613093535345034829449161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45936498855173519090395525 8613093535345034829449161)
    ·
      refine ⟨6459820151508776122086871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8613093535345034829449161 6459820151508776122086871)
      ·
        refine ⟨9689730227263164183130307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459820151508776122086871 9689730227263164183130307)
        ·
          refine ⟨14534595340894746274695461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689730227263164183130307 14534595340894746274695461)
          ·
            refine ⟨2725236626417764926505399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14534595340894746274695461 2725236626417764926505399)
            ·
              refine ⟨4087854939626647389758099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725236626417764926505399 4087854939626647389758099)
              ·
                refine ⟨6131782409439971084637149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087854939626647389758099 6131782409439971084637149)
                ·
                  refine ⟨2299418403539989156738931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6131782409439971084637149 2299418403539989156738931)
                  ·
                    refine ⟨3449127605309983735108397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2299418403539989156738931 3449127605309983735108397)
                    ·
                      refine ⟨1293422851991243900665649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449127605309983735108397 1293422851991243900665649)
                      ·
                        rfl

theorem cell23_2518932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2518932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518932 prefixEnd_2518932 := by exact prefixLift 2518932
  have htrace : WordTrace (prefixWord ++ tailWord_2518932) baseStart_2518932 baseEnd_2518932 := by
    simpa [prefixWord, tailWord_2518932, baseEnd_2518932] using wordTrace_append hprefix tailTrace_2518932
  have hstable : (prefixWord ++ tailWord_2518932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518932).length < 2 ^ (prefixWord ++ tailWord_2518932).sum := by decide
  have hdescent : baseEnd_2518932 < baseStart_2518932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518961 : List Nat := [1, 2, 2, 4, 2, 1, 2, 9]
def baseStart_2518961 : Nat := 118140960795 + 2518961 * 2 ^ 59
def prefixEnd_2518961 : Nat := 4983230072969 + 3 ^ 40 * 2518961 * 2
def baseEnd_2518961 : Nat := 47905101590008306933445

theorem tailTrace_2518961 : CollatzResearch.WordTrace tailWord_2518961 prefixEnd_2518961 47905101590008306933445 := by
  unfold tailWord_2518961
  simp only [CollatzResearch.WordTrace]
  refine ⟨91874055427241976133596737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61249370284827984089064491 91874055427241976133596737)
  ·
    refine ⟨68905541570431482100197553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91874055427241976133596737 68905541570431482100197553)
    ·
      refine ⟨51679156177823611575148165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68905541570431482100197553 51679156177823611575148165)
      ·
        refine ⟨9689841783341927170340281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51679156177823611575148165 9689841783341927170340281)
        ·
          refine ⟨7267381337506445377755211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9689841783341927170340281 7267381337506445377755211)
          ·
            refine ⟨10901072006259668066632817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267381337506445377755211 10901072006259668066632817)
            ·
              refine ⟨8175804004694751049974613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10901072006259668066632817 8175804004694751049974613)
              ·
                refine ⟨47905101590008306933445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8175804004694751049974613 47905101590008306933445)
                ·
                  rfl

theorem cell23_2518961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 9].length) (baseStart_2518961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518961 prefixEnd_2518961 := by exact prefixLift 2518961
  have htrace : WordTrace (prefixWord ++ tailWord_2518961) baseStart_2518961 baseEnd_2518961 := by
    simpa [prefixWord, tailWord_2518961, baseEnd_2518961] using wordTrace_append hprefix tailTrace_2518961
  have hstable : (prefixWord ++ tailWord_2518961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518961).length < 2 ^ (prefixWord ++ tailWord_2518961).sum := by decide
  have hdescent : baseEnd_2518961 < baseStart_2518961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3]
def baseStart_2518971 : Nat := 118140960795 + 2518971 * 2 ^ 59
def prefixEnd_2518971 : Nat := 4983230072969 + 3 ^ 40 * 2518971 * 2
def baseEnd_2518971 : Nat := 1293442877736769248077969

theorem tailTrace_2518971 : CollatzResearch.WordTrace tailWord_2518971 prefixEnd_2518971 1293442877736769248077969 := by
  unfold tailWord_2518971
  simp only [CollatzResearch.WordTrace]
  refine ⟨91874420157205747841460767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61249613438137165227640511 91874420157205747841460767)
  ·
    refine ⟨137811630235808621762191151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91874420157205747841460767 137811630235808621762191151)
    ·
      refine ⟨206717445353712932643286727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137811630235808621762191151 206717445353712932643286727)
      ·
        refine ⟨310076168030569398964930091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206717445353712932643286727 310076168030569398964930091)
        ·
          refine ⟨465114252045854098447395137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310076168030569398964930091 465114252045854098447395137)
          ·
            refine ⟨348835689034390573835546353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465114252045854098447395137 348835689034390573835546353)
            ·
              refine ⟨261626766775792930376659765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348835689034390573835546353 261626766775792930376659765)
              ·
                refine ⟨24527509385230587222811853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261626766775792930376659765 24527509385230587222811853)
                ·
                  refine ⟨9197816019461470208554445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24527509385230587222811853 9197816019461470208554445)
                  ·
                    refine ⟨3449181007298051328207917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9197816019461470208554445 3449181007298051328207917)
                    ·
                      refine ⟨1293442877736769248077969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449181007298051328207917 1293442877736769248077969)
                      ·
                        rfl

theorem cell23_2518971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].length) (baseStart_2518971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518971 prefixEnd_2518971 := by exact prefixLift 2518971
  have htrace : WordTrace (prefixWord ++ tailWord_2518971) baseStart_2518971 baseEnd_2518971 := by
    simpa [prefixWord, tailWord_2518971, baseEnd_2518971] using wordTrace_append hprefix tailTrace_2518971
  have hstable : (prefixWord ++ tailWord_2518971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518971).length < 2 ^ (prefixWord ++ tailWord_2518971).sum := by decide
  have hdescent : baseEnd_2518971 < baseStart_2518971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518975 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 1, 2, 3]
def baseStart_2518975 : Nat := 118140960795 + 2518975 * 2 ^ 59
def prefixEnd_2518975 : Nat := 4983230072969 + 3 ^ 40 * 2518975 * 2
def baseEnd_2518975 : Nat := 1293444931659387232427951

theorem tailTrace_2518975 : CollatzResearch.WordTrace tailWord_2518975 prefixEnd_2518975 1293444931659387232427951 := by
  unfold tailWord_2518975
  simp only [CollatzResearch.WordTrace]
  refine ⟨91874566049191256524606379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61249710699460837683070919 91874566049191256524606379)
  ·
    refine ⟨137811849073786884786909569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91874566049191256524606379 137811849073786884786909569)
    ·
      refine ⟨103358886805340163590182177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137811849073786884786909569 103358886805340163590182177)
      ·
        refine ⟨77519165104005122692636633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103358886805340163590182177 77519165104005122692636633)
        ·
          refine ⟨58139373828003842019477475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77519165104005122692636633 58139373828003842019477475)
          ·
            refine ⟨87209060742005763029216213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58139373828003842019477475 87209060742005763029216213)
            ·
              refine ⟨2043962361140760070997255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87209060742005763029216213 2043962361140760070997255)
              ·
                refine ⟨3065943541711140106495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043962361140760070997255 3065943541711140106495883)
                ·
                  refine ⟨4598915312566710159743825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065943541711140106495883 4598915312566710159743825)
                  ·
                    refine ⟨3449186484425032619807869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598915312566710159743825 3449186484425032619807869)
                    ·
                      refine ⟨1293444931659387232427951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449186484425032619807869 1293444931659387232427951)
                      ·
                        rfl

theorem cell23_2518975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_2518975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2518975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2518975 prefixEnd_2518975 := by exact prefixLift 2518975
  have htrace : WordTrace (prefixWord ++ tailWord_2518975) baseStart_2518975 baseEnd_2518975 := by
    simpa [prefixWord, tailWord_2518975, baseEnd_2518975] using wordTrace_append hprefix tailTrace_2518975
  have hstable : (prefixWord ++ tailWord_2518975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518975).length < 2 ^ (prefixWord ++ tailWord_2518975).sum := by decide
  have hdescent : baseEnd_2518975 < baseStart_2518975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519032 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_2519032 : Nat := 118140960795 + 2519032 * 2 ^ 59
def prefixEnd_2519032 : Nat := 4983230072969 + 3 ^ 40 * 2519032 * 2
def baseEnd_2519032 : Nat := 1293474200056693509415189

theorem tailTrace_2519032 : CollatzResearch.WordTrace tailWord_2519032 prefixEnd_2519032 1293474200056693509415189 := by
  unfold tailWord_2519032
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938322504992377629715675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61251096673323170172954233 45938322504992377629715675)
  ·
    refine ⟨68907483757488566444573513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45938322504992377629715675 68907483757488566444573513)
    ·
      refine ⟨51680612818116424833430135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68907483757488566444573513 51680612818116424833430135)
      ·
        refine ⟨77520919227174637250145203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51680612818116424833430135 77520919227174637250145203)
        ·
          refine ⟨116281378840761955875217805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77520919227174637250145203 116281378840761955875217805)
          ·
            refine ⟨43605517065285733453206677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116281378840761955875217805 43605517065285733453206677)
            ·
              refine ⟨2044008612435268755619063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43605517065285733453206677 2044008612435268755619063)
              ·
                refine ⟨3066012918652903133428595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044008612435268755619063 3066012918652903133428595)
                ·
                  refine ⟨4599019377979354700142893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066012918652903133428595 4599019377979354700142893)
                  ·
                    refine ⟨1724632266742258012553585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4599019377979354700142893 1724632266742258012553585)
                    ·
                      refine ⟨1293474200056693509415189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724632266742258012553585 1293474200056693509415189)
                      ·
                        rfl

theorem cell23_2519032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_2519032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519032 prefixEnd_2519032 := by exact prefixLift 2519032
  have htrace : WordTrace (prefixWord ++ tailWord_2519032) baseStart_2519032 baseEnd_2519032 := by
    simpa [prefixWord, tailWord_2519032, baseEnd_2519032] using wordTrace_append hprefix tailTrace_2519032
  have hstable : (prefixWord ++ tailWord_2519032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519032).length < 2 ^ (prefixWord ++ tailWord_2519032).sum := by decide
  have hdescent : baseEnd_2519032 < baseStart_2519032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519068 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 7]
def baseStart_2519068 : Nat := 118140960795 + 2519068 * 2 ^ 59
def prefixEnd_2519068 : Nat := 4983230072969 + 3 ^ 40 * 2519068 * 2
def baseEnd_2519068 : Nat := 143721409484472818729447

theorem tailTrace_2519068 : CollatzResearch.WordTrace tailWord_2519068 prefixEnd_2519068 143721409484472818729447 := by
  unfold tailWord_2519068
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938979018927166703870929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61251972025236222271827905 45938979018927166703870929)
  ·
    refine ⟨34454234264195375027903197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45938979018927166703870929 34454234264195375027903197)
    ·
      refine ⟨12920337849073265635463699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34454234264195375027903197 12920337849073265635463699)
      ·
        refine ⟨19380506773609898453195549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12920337849073265635463699 19380506773609898453195549)
        ·
          refine ⟨7267690040103711919948331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19380506773609898453195549 7267690040103711919948331)
          ·
            refine ⟨10901535060155567879922497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267690040103711919948331 10901535060155567879922497)
            ·
              refine ⟨8176151295116675909941873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10901535060155567879922497 8176151295116675909941873)
              ·
                refine ⟨6132113471337506932456405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176151295116675909941873 6132113471337506932456405)
                ·
                  refine ⟨143721409484472818729447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6132113471337506932456405 143721409484472818729447)
                  ·
                    rfl

theorem cell23_2519068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_2519068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519068 prefixEnd_2519068 := by exact prefixLift 2519068
  have htrace : WordTrace (prefixWord ++ tailWord_2519068) baseStart_2519068 baseEnd_2519068 := by
    simpa [prefixWord, tailWord_2519068, baseEnd_2519068] using wordTrace_append hprefix tailTrace_2519068
  have hstable : (prefixWord ++ tailWord_2519068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519068).length < 2 ^ (prefixWord ++ tailWord_2519068).sum := by decide
  have hdescent : baseEnd_2519068 < baseStart_2519068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519102 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2519102 : Nat := 118140960795 + 2519102 * 2 ^ 59
def prefixEnd_2519102 : Nat := 4983230072969 + 3 ^ 40 * 2519102 * 2
def baseEnd_2519102 : Nat := 143723349300278692837763

theorem tailTrace_2519102 : CollatzResearch.WordTrace tailWord_2519102 prefixEnd_2519102 143723349300278692837763 := by
  unfold tailWord_2519102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11484899764966394651809945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61252798746487438142986373 11484899764966394651809945)
  ·
    refine ⟨8613674823724795988857459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11484899764966394651809945 8613674823724795988857459)
    ·
      refine ⟨12920512235587193983286189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8613674823724795988857459 12920512235587193983286189)
      ·
        refine ⟨4845192088345197743732321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12920512235587193983286189 4845192088345197743732321)
        ·
          refine ⟨3633894066258898307799241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4845192088345197743732321 3633894066258898307799241)
          ·
            refine ⟨2725420549694173730849431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3633894066258898307799241 2725420549694173730849431)
            ·
              refine ⟨4088130824541260596274147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725420549694173730849431 4088130824541260596274147)
              ·
                refine ⟨6132196236811890894411221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088130824541260596274147 6132196236811890894411221)
                ·
                  refine ⟨143723349300278692837763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6132196236811890894411221 143723349300278692837763)
                  ·
                    rfl

theorem cell23_2519102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2519102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519102 prefixEnd_2519102 := by exact prefixLift 2519102
  have htrace : WordTrace (prefixWord ++ tailWord_2519102) baseStart_2519102 baseEnd_2519102 := by
    simpa [prefixWord, tailWord_2519102, baseEnd_2519102] using wordTrace_append hprefix tailTrace_2519102
  have hstable : (prefixWord ++ tailWord_2519102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519102).length < 2 ^ (prefixWord ++ tailWord_2519102).sum := by decide
  have hdescent : baseEnd_2519102 < baseStart_2519102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519168 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_2519168 : Nat := 118140960795 + 2519168 * 2 ^ 59
def prefixEnd_2519168 : Nat := 4983230072969 + 3 ^ 40 * 2519168 * 2
def baseEnd_2519168 : Nat := 1293544033425704977314563

theorem tailTrace_2519168 : CollatzResearch.WordTrace tailWord_2519168 prefixEnd_2519168 1293544033425704977314563 := by
  unfold tailWord_2519168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940802668746025243191079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61254403558328033657588105 45940802668746025243191079)
  ·
    refine ⟨68911204003119037864786619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45940802668746025243191079 68911204003119037864786619)
    ·
      refine ⟨103366806004678556797179929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68911204003119037864786619 103366806004678556797179929)
      ·
        refine ⟨77525104503508917597884947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103366806004678556797179929 77525104503508917597884947)
        ·
          refine ⟨116287656755263376396827421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77525104503508917597884947 116287656755263376396827421)
          ·
            refine ⟨43607871283223766148810283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116287656755263376396827421 43607871283223766148810283)
            ·
              refine ⟨65411806924835649223215425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43607871283223766148810283 65411806924835649223215425)
              ·
                refine ⟨49058855193626736917411569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65411806924835649223215425 49058855193626736917411569)
                ·
                  refine ⟨36794141395220052688058677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49058855193626736917411569 36794141395220052688058677)
                  ·
                    refine ⟨3449450755801879939505501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36794141395220052688058677 3449450755801879939505501)
                    ·
                      refine ⟨1293544033425704977314563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449450755801879939505501 1293544033425704977314563)
                      ·
                        rfl

theorem cell23_2519168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_2519168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519168 prefixEnd_2519168 := by exact prefixLift 2519168
  have htrace : WordTrace (prefixWord ++ tailWord_2519168) baseStart_2519168 baseEnd_2519168 := by
    simpa [prefixWord, tailWord_2519168, baseEnd_2519168] using wordTrace_append hprefix tailTrace_2519168
  have hstable : (prefixWord ++ tailWord_2519168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519168).length < 2 ^ (prefixWord ++ tailWord_2519168).sum := by decide
  have hdescent : baseEnd_2519168 < baseStart_2519168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519195 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 6, 3, 2]
def baseStart_2519195 : Nat := 118140960795 + 2519195 * 2 ^ 59
def prefixEnd_2519195 : Nat := 4983230072969 + 3 ^ 40 * 2519195 * 2
def baseEnd_2519195 : Nat := 1293557897403376371676939

theorem tailTrace_2519195 : CollatzResearch.WordTrace tailWord_2519195 prefixEnd_2519195 1293557897403376371676939 := by
  unfold tailWord_2519195
  simp only [CollatzResearch.WordTrace]
  refine ⟨91882590108394234097615039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61255060072262822731743359 91882590108394234097615039)
  ·
    refine ⟨137823885162591351146422559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91882590108394234097615039 137823885162591351146422559)
    ·
      refine ⟨206735827743887026719633839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137823885162591351146422559 206735827743887026719633839)
      ·
        refine ⟨310103741615830540079450759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206735827743887026719633839 310103741615830540079450759)
        ·
          refine ⟨465155612423745810119176139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310103741615830540079450759 465155612423745810119176139)
          ·
            refine ⟨697733418635618715178764209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465155612423745810119176139 697733418635618715178764209)
            ·
              refine ⟨523300063976714036384073157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697733418635618715178764209 523300063976714036384073157)
              ·
                refine ⟨98118761995633881822013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523300063976714036384073157 98118761995633881822013717)
                ·
                  refine ⟨4599316968545338210406893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98118761995633881822013717 4599316968545338210406893)
                  ·
                    refine ⟨1724743863204501828902585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4599316968545338210406893 1724743863204501828902585)
                    ·
                      refine ⟨1293557897403376371676939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724743863204501828902585 1293557897403376371676939)
                      ·
                        rfl

theorem cell23_2519195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3, 2].length) (baseStart_2519195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519195 prefixEnd_2519195 := by exact prefixLift 2519195
  have htrace : WordTrace (prefixWord ++ tailWord_2519195) baseStart_2519195 baseEnd_2519195 := by
    simpa [prefixWord, tailWord_2519195, baseEnd_2519195] using wordTrace_append hprefix tailTrace_2519195
  have hstable : (prefixWord ++ tailWord_2519195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519195).length < 2 ^ (prefixWord ++ tailWord_2519195).sum := by decide
  have hdescent : baseEnd_2519195 < baseStart_2519195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519205 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_2519205 : Nat := 118140960795 + 2519205 * 2 ^ 59
def prefixEnd_2519205 : Nat := 4983230072969 + 3 ^ 40 * 2519205 * 2
def baseEnd_2519205 : Nat := 431187677403307110850631

theorem tailTrace_2519205 : CollatzResearch.WordTrace tailWord_2519205 prefixEnd_2519205 431187677403307110850631 := by
  unfold tailWord_2519205
  simp only [CollatzResearch.WordTrace]
  refine ⟨91882954838358005805479069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61255303225572003870319379 91882954838358005805479069)
  ·
    refine ⟨34456108064384252177054651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91882954838358005805479069 34456108064384252177054651)
    ·
      refine ⟨51684162096576378265581977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34456108064384252177054651 51684162096576378265581977)
      ·
        refine ⟨38763121572432283699186483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51684162096576378265581977 38763121572432283699186483)
        ·
          refine ⟨58144682358648425548779725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38763121572432283699186483 58144682358648425548779725)
          ·
            refine ⟨21804255884493159580792397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58144682358648425548779725 21804255884493159580792397)
            ·
              refine ⟨8176595956684934842797149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21804255884493159580792397 8176595956684934842797149)
              ·
                refine ⟨3066223483756850566048931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8176595956684934842797149 3066223483756850566048931)
                ·
                  refine ⟨4599335225635275849073397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066223483756850566048931 4599335225635275849073397)
                  ·
                    refine ⟨431187677403307110850631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4599335225635275849073397 431187677403307110850631)
                    ·
                      rfl

theorem cell23_2519205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_2519205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519205 prefixEnd_2519205 := by exact prefixLift 2519205
  have htrace : WordTrace (prefixWord ++ tailWord_2519205) baseStart_2519205 baseEnd_2519205 := by
    simpa [prefixWord, tailWord_2519205, baseEnd_2519205] using wordTrace_append hprefix tailTrace_2519205
  have hstable : (prefixWord ++ tailWord_2519205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519205).length < 2 ^ (prefixWord ++ tailWord_2519205).sum := by decide
  have hdescent : baseEnd_2519205 < baseStart_2519205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519242 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_2519242 : Nat := 118140960795 + 2519242 * 2 ^ 59
def prefixEnd_2519242 : Nat := 4983230072969 + 3 ^ 40 * 2519242 * 2
def baseEnd_2519242 : Nat := 1293582030994137687789223

theorem tailTrace_2519242 : CollatzResearch.WordTrace tailWord_2519242 prefixEnd_2519242 1293582030994137687789223 := by
  unfold tailWord_2519242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22971076084805990281143995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61256202892815974083050653 22971076084805990281143995)
  ·
    refine ⟨34456614127208985421715993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22971076084805990281143995 34456614127208985421715993)
    ·
      refine ⟨25842460595406739066286995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34456614127208985421715993 25842460595406739066286995)
      ·
        refine ⟨38763690893110108599430493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25842460595406739066286995 38763690893110108599430493)
        ·
          refine ⟨14536384084916290724786435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38763690893110108599430493 14536384084916290724786435)
          ·
            refine ⟨21804576127374436087179653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14536384084916290724786435 21804576127374436087179653)
            ·
              refine ⟨4088358023882706766346185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21804576127374436087179653 4088358023882706766346185)
              ·
                refine ⟨3066268517912030074759639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088358023882706766346185 3066268517912030074759639)
                ·
                  refine ⟨4599402776868045112139459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066268517912030074759639 4599402776868045112139459)
                  ·
                    refine ⟨6899104165302067668209189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599402776868045112139459 6899104165302067668209189)
                    ·
                      refine ⟨1293582030994137687789223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6899104165302067668209189 1293582030994137687789223)
                      ·
                        rfl

theorem cell23_2519242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_2519242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519242 prefixEnd_2519242 := by exact prefixLift 2519242
  have htrace : WordTrace (prefixWord ++ tailWord_2519242) baseStart_2519242 baseEnd_2519242 := by
    simpa [prefixWord, tailWord_2519242, baseEnd_2519242] using wordTrace_append hprefix tailTrace_2519242
  have hstable : (prefixWord ++ tailWord_2519242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519242).length < 2 ^ (prefixWord ++ tailWord_2519242).sum := by decide
  have hdescent : baseEnd_2519242 < baseStart_2519242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519253 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2519253 : Nat := 118140960795 + 2519253 * 2 ^ 59
def prefixEnd_2519253 : Nat := 4983230072969 + 3 ^ 40 * 2519253 * 2
def baseEnd_2519253 : Nat := 1293587679281337144751673

theorem tailTrace_2519253 : CollatzResearch.WordTrace tailWord_2519253 prefixEnd_2519253 1293587679281337144751673 := by
  unfold tailWord_2519253
  simp only [CollatzResearch.WordTrace]
  refine ⟨91884705542184110003226413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61256470361456073335484275 91884705542184110003226413)
  ·
    refine ⟨34456764578319041251209905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91884705542184110003226413 34456764578319041251209905)
    ·
      refine ⟨25842573433739280938407429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34456764578319041251209905 25842573433739280938407429)
      ·
        refine ⟨4845482518826115175951393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25842573433739280938407429 4845482518826115175951393)
        ·
          refine ⟨3634111889119586381963545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4845482518826115175951393 3634111889119586381963545)
          ·
            refine ⟨2725583916839689786472659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634111889119586381963545 2725583916839689786472659)
            ·
              refine ⟨4088375875259534679708989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725583916839689786472659 4088375875259534679708989)
              ·
                refine ⟨1533140953222325504890871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088375875259534679708989 1533140953222325504890871)
                ·
                  refine ⟨2299711429833488257336307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533140953222325504890871 2299711429833488257336307)
                  ·
                    refine ⟨3449567144750232386004461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2299711429833488257336307 3449567144750232386004461)
                    ·
                      refine ⟨1293587679281337144751673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3449567144750232386004461 1293587679281337144751673)
                      ·
                        rfl

theorem cell23_2519253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2519253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519253 prefixEnd_2519253 := by exact prefixLift 2519253
  have htrace : WordTrace (prefixWord ++ tailWord_2519253) baseStart_2519253 baseEnd_2519253 := by
    simpa [prefixWord, tailWord_2519253, baseEnd_2519253] using wordTrace_append hprefix tailTrace_2519253
  have hstable : (prefixWord ++ tailWord_2519253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519253).length < 2 ^ (prefixWord ++ tailWord_2519253).sum := by decide
  have hdescent : baseEnd_2519253 < baseStart_2519253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519349 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_2519349 : Nat := 118140960795 + 2519349 * 2 ^ 59
def prefixEnd_2519349 : Nat := 4983230072969 + 3 ^ 40 * 2519349 * 2
def baseEnd_2519349 : Nat := 1293636973424168769151231

theorem tailTrace_2519349 : CollatzResearch.WordTrace tailWord_2519349 prefixEnd_2519349 1293636973424168769151231 := by
  unfold tailWord_2519349
  simp only [CollatzResearch.WordTrace]
  refine ⟨91888206949836318398721101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61258804633224212265814067 91888206949836318398721101)
  ·
    refine ⟨34458077606188619399520413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91888206949836318398721101 34458077606188619399520413)
    ·
      refine ⟨12921779102320732274820155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34458077606188619399520413 12921779102320732274820155)
      ·
        refine ⟨19382668653481098412230233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12921779102320732274820155 19382668653481098412230233)
        ·
          refine ⟨14537001490110823809172675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19382668653481098412230233 14537001490110823809172675)
          ·
            refine ⟨21805502235166235713759013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14537001490110823809172675 21805502235166235713759013)
            ·
              refine ⟨4088531669093669196329815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21805502235166235713759013 4088531669093669196329815)
              ·
                refine ⟨6132797503640503794494723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088531669093669196329815 6132797503640503794494723)
                ·
                  refine ⟨9199196255460755691742085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132797503640503794494723 9199196255460755691742085)
                  ·
                    refine ⟨1724849297898891692201641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9199196255460755691742085 1724849297898891692201641)
                    ·
                      refine ⟨1293636973424168769151231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724849297898891692201641 1293636973424168769151231)
                      ·
                        rfl

theorem cell23_2519349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_2519349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519349 prefixEnd_2519349 := by exact prefixLift 2519349
  have htrace : WordTrace (prefixWord ++ tailWord_2519349) baseStart_2519349 baseEnd_2519349 := by
    simpa [prefixWord, tailWord_2519349, baseEnd_2519349] using wordTrace_append hprefix tailTrace_2519349
  have hstable : (prefixWord ++ tailWord_2519349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519349).length < 2 ^ (prefixWord ++ tailWord_2519349).sum := by decide
  have hdescent : baseEnd_2519349 < baseStart_2519349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519385 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_2519385 : Nat := 118140960795 + 2519385 * 2 ^ 59
def prefixEnd_2519385 : Nat := 4983230072969 + 3 ^ 40 * 2519385 * 2
def baseEnd_2519385 : Nat := 431218486242576876100355

theorem tailTrace_2519385 : CollatzResearch.WordTrace tailWord_2519385 prefixEnd_2519385 431218486242576876100355 := by
  unfold tailWord_2519385
  simp only [CollatzResearch.WordTrace]
  refine ⟨91889519977705896547031609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61259679985137264364687739 91889519977705896547031609)
  ·
    refine ⟨68917139983279422410273707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91889519977705896547031609 68917139983279422410273707)
    ·
      refine ⟨103375709974919133615410561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68917139983279422410273707 103375709974919133615410561)
      ·
        refine ⟨77531782481189350211557921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103375709974919133615410561 77531782481189350211557921)
        ·
          refine ⟨58148836860892012658668441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77531782481189350211557921 58148836860892012658668441)
          ·
            refine ⟨43611627645669009494001331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58148836860892012658668441 43611627645669009494001331)
            ·
              refine ⟨65417441468503514241001997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43611627645669009494001331 65417441468503514241001997)
              ·
                refine ⟨24531540550688817840375749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65417441468503514241001997 24531540550688817840375749)
                ·
                  refine ⟨4599663853254153345070453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24531540550688817840375749 4599663853254153345070453)
                  ·
                    refine ⟨431218486242576876100355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4599663853254153345070453 431218486242576876100355)
                    ·
                      rfl

theorem cell23_2519385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_2519385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519385 prefixEnd_2519385 := by exact prefixLift 2519385
  have htrace : WordTrace (prefixWord ++ tailWord_2519385) baseStart_2519385 baseEnd_2519385 := by
    simpa [prefixWord, tailWord_2519385, baseEnd_2519385] using wordTrace_append hprefix tailTrace_2519385
  have hstable : (prefixWord ++ tailWord_2519385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519385).length < 2 ^ (prefixWord ++ tailWord_2519385).sum := by decide
  have hdescent : baseEnd_2519385 < baseStart_2519385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519395 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2519395 : Nat := 118140960795 + 2519395 * 2 ^ 59
def prefixEnd_2519395 : Nat := 4983230072969 + 3 ^ 40 * 2519395 * 2
def baseEnd_2519395 : Nat := 1293660593534275589176019

theorem tailTrace_2519395 : CollatzResearch.WordTrace tailWord_2519395 prefixEnd_2519395 1293660593534275589176019 := by
  unfold tailWord_2519395
  simp only [CollatzResearch.WordTrace]
  refine ⟨91889884707669668254895639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61259923138446445503263759 91889884707669668254895639)
  ·
    refine ⟨137834827061504502382343459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91889884707669668254895639 137834827061504502382343459)
    ·
      refine ⟨206752240592256753573515189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137834827061504502382343459 206752240592256753573515189)
      ·
        refine ⟨19383022555524070647517049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206752240592256753573515189 19383022555524070647517049)
        ·
          refine ⟨14537266916643052985637787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19383022555524070647517049 14537266916643052985637787)
          ·
            refine ⟨21805900374964579478456681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14537266916643052985637787 21805900374964579478456681)
            ·
              refine ⟨16354425281223434608842511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21805900374964579478456681 16354425281223434608842511)
              ·
                refine ⟨24531637921835151913263767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16354425281223434608842511 24531637921835151913263767)
                ·
                  refine ⟨36797456882752727869895651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24531637921835151913263767 36797456882752727869895651)
                  ·
                    refine ⟨55196185324129091804843477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36797456882752727869895651 55196185324129091804843477)
                    ·
                      refine ⟨1293660593534275589176019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55196185324129091804843477 1293660593534275589176019)
                      ·
                        rfl

theorem cell23_2519395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2519395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519395 prefixEnd_2519395 := by exact prefixLift 2519395
  have htrace : WordTrace (prefixWord ++ tailWord_2519395) baseStart_2519395 baseEnd_2519395 := by
    simpa [prefixWord, tailWord_2519395, baseEnd_2519395] using wordTrace_append hprefix tailTrace_2519395
  have hstable : (prefixWord ++ tailWord_2519395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519395).length < 2 ^ (prefixWord ++ tailWord_2519395).sum := by decide
  have hdescent : baseEnd_2519395 < baseStart_2519395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519402 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2519402 : Nat := 118140960795 + 2519402 * 2 ^ 59
def prefixEnd_2519402 : Nat := 4983230072969 + 3 ^ 40 * 2519402 * 2
def baseEnd_2519402 : Nat := 431221395966285687262829

theorem tailTrace_2519402 : CollatzResearch.WordTrace tailWord_2519402 prefixEnd_2519402 431221395966285687262829 := by
  unfold tailWord_2519402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22972535004661077112600115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61260093345762872300266973 22972535004661077112600115)
  ·
    refine ⟨34458802506991615668900173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22972535004661077112600115 34458802506991615668900173)
    ·
      refine ⟨12922050940121855875837565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34458802506991615668900173 12922050940121855875837565)
      ·
        refine ⟨4845769102545695953439087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12922050940121855875837565 4845769102545695953439087)
        ·
          refine ⟨7268653653818543930158631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845769102545695953439087 7268653653818543930158631)
          ·
            refine ⟨10902980480727815895237947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268653653818543930158631 10902980480727815895237947)
            ·
              refine ⟨16354470721091723842856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902980480727815895237947 16354470721091723842856921)
              ·
                refine ⟨12265853040818792882142691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16354470721091723842856921 12265853040818792882142691)
                ·
                  refine ⟨18398779561228189323214037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12265853040818792882142691 18398779561228189323214037)
                  ·
                    refine ⟨431221395966285687262829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18398779561228189323214037 431221395966285687262829)
                    ·
                      rfl

theorem cell23_2519402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2519402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519402 prefixEnd_2519402 := by exact prefixLift 2519402
  have htrace : WordTrace (prefixWord ++ tailWord_2519402) baseStart_2519402 baseEnd_2519402 := by
    simpa [prefixWord, tailWord_2519402, baseEnd_2519402] using wordTrace_append hprefix tailTrace_2519402
  have hstable : (prefixWord ++ tailWord_2519402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519402).length < 2 ^ (prefixWord ++ tailWord_2519402).sum := by decide
  have hdescent : baseEnd_2519402 < baseStart_2519402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519465 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_2519465 : Nat := 118140960795 + 2519465 * 2 ^ 59
def prefixEnd_2519465 : Nat := 4983230072969 + 3 ^ 40 * 2519465 * 2
def baseEnd_2519465 : Nat := 1293696537180090315300697

theorem tailTrace_2519465 : CollatzResearch.WordTrace tailWord_2519465 prefixEnd_2519465 1293696537180090315300697 := by
  unfold tailWord_2519465
  simp only [CollatzResearch.WordTrace]
  refine ⟨91892437817416070209943849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61261625211610713473295899 91892437817416070209943849)
  ·
    refine ⟨68919328363062052657457887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91892437817416070209943849 68919328363062052657457887)
    ·
      refine ⟨103378992544593078986186831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68919328363062052657457887 103378992544593078986186831)
      ·
        refine ⟨155068488816889618479280247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103378992544593078986186831 155068488816889618479280247)
        ·
          refine ⟨232602733225334427718920371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155068488816889618479280247 232602733225334427718920371)
          ·
            refine ⟨348904099838001641578380557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232602733225334427718920371 348904099838001641578380557)
            ·
              refine ⟨130839037439250615591892709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348904099838001641578380557 130839037439250615591892709)
              ·
                refine ⟨24532319519859490423479883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130839037439250615591892709 24532319519859490423479883)
                ·
                  refine ⟨36798479279789235635219825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24532319519859490423479883 36798479279789235635219825)
                  ·
                    refine ⟨27598859459841926726414869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36798479279789235635219825 27598859459841926726414869)
                    ·
                      refine ⟨1293696537180090315300697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27598859459841926726414869 1293696537180090315300697)
                      ·
                        rfl

theorem cell23_2519465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_2519465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519465 prefixEnd_2519465 := by exact prefixLift 2519465
  have htrace : WordTrace (prefixWord ++ tailWord_2519465) baseStart_2519465 baseEnd_2519465 := by
    simpa [prefixWord, tailWord_2519465, baseEnd_2519465] using wordTrace_append hprefix tailTrace_2519465
  have hstable : (prefixWord ++ tailWord_2519465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519465).length < 2 ^ (prefixWord ++ tailWord_2519465).sum := by decide
  have hdescent : baseEnd_2519465 < baseStart_2519465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519500 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_2519500 : Nat := 118140960795 + 2519500 * 2 ^ 59
def prefixEnd_2519500 : Nat := 4983230072969 + 3 ^ 40 * 2519500 * 2
def baseEnd_2519500 : Nat := 431238169667665892787679

theorem tailTrace_2519500 : CollatzResearch.WordTrace tailWord_2519500 prefixEnd_2519500 431238169667665892787679 := by
  unfold tailWord_2519500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45946857186144635593733977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61262476248192847458311969 45946857186144635593733977)
  ·
    refine ⟨34460142889608476695300483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45946857186144635593733977 34460142889608476695300483)
    ·
      refine ⟨51690214334412715042950725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34460142889608476695300483 51690214334412715042950725)
      ·
        refine ⟨9691915187702384070553261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51690214334412715042950725 9691915187702384070553261)
        ·
          refine ⟨3634468195388394026457473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9691915187702384070553261 3634468195388394026457473)
          ·
            refine ⟨2725851146541295519843105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634468195388394026457473 2725851146541295519843105)
            ·
              refine ⟨2044388359905971639882329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725851146541295519843105 2044388359905971639882329)
              ·
                refine ⟨1533291269929478729911747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044388359905971639882329 1533291269929478729911747)
                ·
                  refine ⟨2299936904894218094867621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533291269929478729911747 2299936904894218094867621)
                  ·
                    refine ⟨431238169667665892787679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299936904894218094867621 431238169667665892787679)
                    ·
                      rfl

theorem cell23_2519500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_2519500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519500 prefixEnd_2519500 := by exact prefixLift 2519500
  have htrace : WordTrace (prefixWord ++ tailWord_2519500) baseStart_2519500 baseEnd_2519500 := by
    simpa [prefixWord, tailWord_2519500, baseEnd_2519500] using wordTrace_append hprefix tailTrace_2519500
  have hstable : (prefixWord ++ tailWord_2519500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519500).length < 2 ^ (prefixWord ++ tailWord_2519500).sum := by decide
  have hdescent : baseEnd_2519500 < baseStart_2519500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519515 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_2519515 : Nat := 118140960795 + 2519515 * 2 ^ 59
def prefixEnd_2519515 : Nat := 4983230072969 + 3 ^ 40 * 2519515 * 2
def baseEnd_2519515 : Nat := 1293722211212815119675467

theorem tailTrace_2519515 : CollatzResearch.WordTrace tailWord_2519515 prefixEnd_2519515 1293722211212815119675467 := by
  unfold tailWord_2519515
  simp only [CollatzResearch.WordTrace]
  refine ⟨91894261467234928749263999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61262840978156619166175999 91894261467234928749263999)
  ·
    refine ⟨137841392200852393123895999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91894261467234928749263999 137841392200852393123895999)
    ·
      refine ⟨206762088301278589685843999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137841392200852393123895999 206762088301278589685843999)
      ·
        refine ⟨310143132451917884528765999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206762088301278589685843999 310143132451917884528765999)
        ·
          refine ⟨465214698677876826793148999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310143132451917884528765999 465214698677876826793148999)
          ·
            refine ⟨697822048016815240189723499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465214698677876826793148999 697822048016815240189723499)
            ·
              refine ⟨1046733072025222860284585249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697822048016815240189723499 1046733072025222860284585249)
              ·
                refine ⟨785049804018917145213438937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046733072025222860284585249 785049804018917145213438937)
                ·
                  refine ⟨588787353014187858910079203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785049804018917145213438937 588787353014187858910079203)
                  ·
                    refine ⟨883181029521281788365118805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588787353014187858910079203 883181029521281788365118805)
                    ·
                      refine ⟨1293722211212815119675467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 883181029521281788365118805 1293722211212815119675467)
                      ·
                        rfl

theorem cell23_2519515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_2519515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519515 prefixEnd_2519515 := by exact prefixLift 2519515
  have htrace : WordTrace (prefixWord ++ tailWord_2519515) baseStart_2519515 baseEnd_2519515 := by
    simpa [prefixWord, tailWord_2519515, baseEnd_2519515] using wordTrace_append hprefix tailTrace_2519515
  have hstable : (prefixWord ++ tailWord_2519515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519515).length < 2 ^ (prefixWord ++ tailWord_2519515).sum := by decide
  have hdescent : baseEnd_2519515 < baseStart_2519515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519533 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2519533 : Nat := 118140960795 + 2519533 * 2 ^ 59
def prefixEnd_2519533 : Nat := 4983230072969 + 3 ^ 40 * 2519533 * 2
def baseEnd_2519533 : Nat := 1293731453864596049250385

theorem tailTrace_2519533 : CollatzResearch.WordTrace tailWord_2519533 prefixEnd_2519533 1293731453864596049250385 := by
  unfold tailWord_2519533
  simp only [CollatzResearch.WordTrace]
  refine ⟨91894917981169717823419253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61263278654113145215612835 91894917981169717823419253)
  ·
    refine ⟨8615148560734661045945555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91894917981169717823419253 8615148560734661045945555)
    ·
      refine ⟨12922722841101991568918333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615148560734661045945555 12922722841101991568918333)
      ·
        refine ⟨4846021065413246838344375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12922722841101991568918333 4846021065413246838344375)
        ·
          refine ⟨7269031598119870257516563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846021065413246838344375 7269031598119870257516563)
          ·
            refine ⟨10903547397179805386274845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269031598119870257516563 10903547397179805386274845)
            ·
              refine ⟨4088830273942427019853067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10903547397179805386274845 4088830273942427019853067)
              ·
                refine ⟨6133245410913640529779601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088830273942427019853067 6133245410913640529779601)
                ·
                  refine ⟨4599934058185230397334701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6133245410913640529779601 4599934058185230397334701)
                  ·
                    refine ⟨1724975271819461399000513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4599934058185230397334701 1724975271819461399000513)
                    ·
                      refine ⟨1293731453864596049250385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724975271819461399000513 1293731453864596049250385)
                      ·
                        rfl

theorem cell23_2519533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2519533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519533 prefixEnd_2519533 := by exact prefixLift 2519533
  have htrace : WordTrace (prefixWord ++ tailWord_2519533) baseStart_2519533 baseEnd_2519533 := by
    simpa [prefixWord, tailWord_2519533, baseEnd_2519533] using wordTrace_append hprefix tailTrace_2519533
  have hstable : (prefixWord ++ tailWord_2519533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519533).length < 2 ^ (prefixWord ++ tailWord_2519533).sum := by decide
  have hdescent : baseEnd_2519533 < baseStart_2519533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519556 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_2519556 : Nat := 118140960795 + 2519556 * 2 ^ 59
def prefixEnd_2519556 : Nat := 4983230072969 + 3 ^ 40 * 2519556 * 2
def baseEnd_2519556 : Nat := 431247754639883153087593

theorem tailTrace_2519556 : CollatzResearch.WordTrace tailWord_2519556 prefixEnd_2519556 431247754639883153087593 := by
  unfold tailWord_2519556
  simp only [CollatzResearch.WordTrace]
  refine ⟨45947878430043196375753261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61263837906724261834337681 45947878430043196375753261)
  ·
    refine ⟨17230454411266198640907473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45947878430043196375753261 17230454411266198640907473)
    ·
      refine ⟨12922840808449648980680605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17230454411266198640907473 12922840808449648980680605)
      ·
        refine ⟨4846065303168618367755227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12922840808449648980680605 4846065303168618367755227)
        ·
          refine ⟨7269097954752927551632841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846065303168618367755227 7269097954752927551632841)
          ·
            refine ⟨5451823466064695663724631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7269097954752927551632841 5451823466064695663724631)
            ·
              refine ⟨8177735199097043495586947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5451823466064695663724631 8177735199097043495586947)
              ·
                refine ⟨12266602798645565243380421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8177735199097043495586947 12266602798645565243380421)
                ·
                  refine ⟨2299988024746043483133829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12266602798645565243380421 2299988024746043483133829)
                  ·
                    refine ⟨431247754639883153087593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299988024746043483133829 431247754639883153087593)
                    ·
                      rfl

theorem cell23_2519556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_2519556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519556 prefixEnd_2519556 := by exact prefixLift 2519556
  have htrace : WordTrace (prefixWord ++ tailWord_2519556) baseStart_2519556 baseEnd_2519556 := by
    simpa [prefixWord, tailWord_2519556, baseEnd_2519556] using wordTrace_append hprefix tailTrace_2519556
  have hstable : (prefixWord ++ tailWord_2519556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519556).length < 2 ^ (prefixWord ++ tailWord_2519556).sum := by decide
  have hdescent : baseEnd_2519556 < baseStart_2519556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519563 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 3, 2, 2]
def baseStart_2519563 : Nat := 118140960795 + 2519563 * 2 ^ 59
def prefixEnd_2519563 : Nat := 4983230072969 + 3 ^ 40 * 2519563 * 2
def baseEnd_2519563 : Nat := 1293746858284230931875247

theorem tailTrace_2519563 : CollatzResearch.WordTrace tailWord_2519563 prefixEnd_2519563 1293746858284230931875247 := by
  unfold tailWord_2519563
  simp only [CollatzResearch.WordTrace]
  refine ⟨91896012171061032947011343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61264008114040688631340895 91896012171061032947011343)
  ·
    refine ⟨137844018256591549420517015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91896012171061032947011343 137844018256591549420517015)
    ·
      refine ⟨206766027384887324130775523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137844018256591549420517015 206766027384887324130775523)
      ·
        refine ⟨310149041077330986196163285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206766027384887324130775523 310149041077330986196163285)
        ·
          refine ⟨7269118150249944988972577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 310149041077330986196163285 7269118150249944988972577)
          ·
            refine ⟨5451838612687458741729433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7269118150249944988972577 5451838612687458741729433)
            ·
              refine ⟨4088878959515594056297075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451838612687458741729433 4088878959515594056297075)
              ·
                refine ⟨6133318439273391084445613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088878959515594056297075 6133318439273391084445613)
                ·
                  refine ⟨2299994414727521656667105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6133318439273391084445613 2299994414727521656667105)
                  ·
                    refine ⟨1724995811045641242500329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2299994414727521656667105 1724995811045641242500329)
                    ·
                      refine ⟨1293746858284230931875247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1724995811045641242500329 1293746858284230931875247)
                      ·
                        rfl

theorem cell23_2519563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2, 2].length) (baseStart_2519563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519563 prefixEnd_2519563 := by exact prefixLift 2519563
  have htrace : WordTrace (prefixWord ++ tailWord_2519563) baseStart_2519563 baseEnd_2519563 := by
    simpa [prefixWord, tailWord_2519563, baseEnd_2519563] using wordTrace_append hprefix tailTrace_2519563
  have hstable : (prefixWord ++ tailWord_2519563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519563).length < 2 ^ (prefixWord ++ tailWord_2519563).sum := by decide
  have hdescent : baseEnd_2519563 < baseStart_2519563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519576 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2519576 : Nat := 118140960795 + 2519576 * 2 ^ 59
def prefixEnd_2519576 : Nat := 4983230072969 + 3 ^ 40 * 2519576 * 2
def baseEnd_2519576 : Nat := 1293753533532739381012687

theorem tailTrace_2519576 : CollatzResearch.WordTrace tailWord_2519576 prefixEnd_2519576 1293753533532739381012687 := by
  unfold tailWord_2519576
  simp only [CollatzResearch.WordTrace]
  refine ⟨45948243160006968083617291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61264324213342624111489721 45948243160006968083617291)
  ·
    refine ⟨68922364740010452125425937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45948243160006968083617291 68922364740010452125425937)
    ·
      refine ⟨51691773555007839094069453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68922364740010452125425937 51691773555007839094069453)
      ·
        refine ⟨19384415083127939660276045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51691773555007839094069453 19384415083127939660276045)
        ·
          refine ⟨7269155656172977372603517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19384415083127939660276045 7269155656172977372603517)
          ·
            refine ⟨2725933371064866514726319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7269155656172977372603517 2725933371064866514726319)
            ·
              refine ⟨4088900056597299772089479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725933371064866514726319 4088900056597299772089479)
              ·
                refine ⟨6133350084895949658134219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088900056597299772089479 6133350084895949658134219)
                ·
                  refine ⟨9200025127343924487201329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133350084895949658134219 9200025127343924487201329)
                  ·
                    refine ⟨6900018845507943365400997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9200025127343924487201329 6900018845507943365400997)
                    ·
                      refine ⟨1293753533532739381012687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6900018845507943365400997 1293753533532739381012687)
                      ·
                        rfl

theorem cell23_2519576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2519576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519576 prefixEnd_2519576 := by exact prefixLift 2519576
  have htrace : WordTrace (prefixWord ++ tailWord_2519576) baseStart_2519576 baseEnd_2519576 := by
    simpa [prefixWord, tailWord_2519576, baseEnd_2519576] using wordTrace_append hprefix tailTrace_2519576
  have hstable : (prefixWord ++ tailWord_2519576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519576).length < 2 ^ (prefixWord ++ tailWord_2519576).sum := by decide
  have hdescent : baseEnd_2519576 < baseStart_2519576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519614 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2519614 : Nat := 118140960795 + 2519614 * 2 ^ 59
def prefixEnd_2519614 : Nat := 4983230072969 + 3 ^ 40 * 2519614 * 2
def baseEnd_2519614 : Nat := 1293773045797610232337513

theorem tailTrace_2519614 : CollatzResearch.WordTrace tailWord_2519614 prefixEnd_2519614 1293773045797610232337513 := by
  unfold tailWord_2519614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487234036734533582139737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61265248195917512438078597 11487234036734533582139737)
  ·
    refine ⟨8615425527550900186604803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11487234036734533582139737 8615425527550900186604803)
    ·
      refine ⟨12923138291326350279907205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615425527550900186604803 12923138291326350279907205)
      ·
        refine ⟨2423088429623690677482601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12923138291326350279907205 2423088429623690677482601)
        ·
          refine ⟨1817316322217768008111951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423088429623690677482601 1817316322217768008111951)
          ·
            refine ⟨2725974483326652012167927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817316322217768008111951 2725974483326652012167927)
            ·
              refine ⟨4088961724989978018251891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725974483326652012167927 4088961724989978018251891)
              ·
                refine ⟨6133442587484967027377837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088961724989978018251891 6133442587484967027377837)
                ·
                  refine ⟨2300040970306862635266689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6133442587484967027377837 2300040970306862635266689)
                  ·
                    refine ⟨1725030727730146976450017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300040970306862635266689 1725030727730146976450017)
                    ·
                      refine ⟨1293773045797610232337513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725030727730146976450017 1293773045797610232337513)
                      ·
                        rfl

theorem cell23_2519614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2519614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519614 prefixEnd_2519614 := by exact prefixLift 2519614
  have htrace : WordTrace (prefixWord ++ tailWord_2519614) baseStart_2519614 baseEnd_2519614 := by
    simpa [prefixWord, tailWord_2519614, baseEnd_2519614] using wordTrace_append hprefix tailTrace_2519614
  have hstable : (prefixWord ++ tailWord_2519614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519614).length < 2 ^ (prefixWord ++ tailWord_2519614).sum := by decide
  have hdescent : baseEnd_2519614 < baseStart_2519614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519653 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_2519653 : Nat := 118140960795 + 2519653 * 2 ^ 59
def prefixEnd_2519653 : Nat := 4983230072969 + 3 ^ 40 * 2519653 * 2
def baseEnd_2519653 : Nat := 1293793071543135579749833

theorem tailTrace_2519653 : CollatzResearch.WordTrace tailWord_2519653 prefixEnd_2519653 1293793071543135579749833 := by
  unfold tailWord_2519653
  simp only [CollatzResearch.WordTrace]
  refine ⟨91899294740734978317787613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61266196493823318878525075 91899294740734978317787613)
  ·
    refine ⟨34462235527775616869170355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91899294740734978317787613 34462235527775616869170355)
    ·
      refine ⟨51693353291663425303755533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34462235527775616869170355 51693353291663425303755533)
      ·
        refine ⟨19385007484373784488908325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51693353291663425303755533 19385007484373784488908325)
        ·
          refine ⟨3634688903320084591670311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19385007484373784488908325 3634688903320084591670311)
          ·
            refine ⟨5452033354980126887505467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634688903320084591670311 5452033354980126887505467)
            ·
              refine ⟨8178050032470190331258201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452033354980126887505467 8178050032470190331258201)
              ·
                refine ⟨6133537524352642748443651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178050032470190331258201 6133537524352642748443651)
                ·
                  refine ⟨9200306286528964122665477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133537524352642748443651 9200306286528964122665477)
                  ·
                    refine ⟨1725057428724180772999777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9200306286528964122665477 1725057428724180772999777)
                    ·
                      refine ⟨1293793071543135579749833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725057428724180772999777 1293793071543135579749833)
                      ·
                        rfl

theorem cell23_2519653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_2519653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519653 prefixEnd_2519653 := by exact prefixLift 2519653
  have htrace : WordTrace (prefixWord ++ tailWord_2519653) baseStart_2519653 baseEnd_2519653 := by
    simpa [prefixWord, tailWord_2519653, baseEnd_2519653] using wordTrace_append hprefix tailTrace_2519653
  have hstable : (prefixWord ++ tailWord_2519653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519653).length < 2 ^ (prefixWord ++ tailWord_2519653).sum := by decide
  have hdescent : baseEnd_2519653 < baseStart_2519653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519799 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2519799 : Nat := 118140960795 + 2519799 * 2 ^ 59
def prefixEnd_2519799 : Nat := 4983230072969 + 3 ^ 40 * 2519799 * 2
def baseEnd_2519799 : Nat := 1293868039718692008524161

theorem tailTrace_2519799 : CollatzResearch.WordTrace tailWord_2519799 prefixEnd_2519799 1293868039718692008524161 := by
  unfold tailWord_2519799
  simp only [CollatzResearch.WordTrace]
  refine ⟨91904619798206045252602451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61269746532137363501734967 91904619798206045252602451)
  ·
    refine ⟨137856929697309067878903677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91904619798206045252602451 137856929697309067878903677)
    ·
      refine ⟨51696348636490900454588879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137856929697309067878903677 51696348636490900454588879)
      ·
        refine ⟨77544522954736350681883319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51696348636490900454588879 77544522954736350681883319)
        ·
          refine ⟨116316784432104526022824979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77544522954736350681883319 116316784432104526022824979)
          ·
            refine ⟨174475176648156789034237469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116316784432104526022824979 174475176648156789034237469)
            ·
              refine ⟨65428191243058795887839051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174475176648156789034237469 65428191243058795887839051)
              ·
                refine ⟨98142286864588193831758577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65428191243058795887839051 98142286864588193831758577)
                ·
                  refine ⟨73606715148441145373818933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98142286864588193831758577 73606715148441145373818933)
                  ·
                    refine ⟨6900629545166357378795525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73606715148441145373818933 6900629545166357378795525)
                    ·
                      refine ⟨1293868039718692008524161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6900629545166357378795525 1293868039718692008524161)
                      ·
                        rfl

theorem cell23_2519799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2519799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519799 prefixEnd_2519799 := by exact prefixLift 2519799
  have htrace : WordTrace (prefixWord ++ tailWord_2519799) baseStart_2519799 baseEnd_2519799 := by
    simpa [prefixWord, tailWord_2519799, baseEnd_2519799] using wordTrace_append hprefix tailTrace_2519799
  have hstable : (prefixWord ++ tailWord_2519799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519799).length < 2 ^ (prefixWord ++ tailWord_2519799).sum := by decide
  have hdescent : baseEnd_2519799 < baseStart_2519799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519833 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 7, 2, 2]
def baseStart_2519833 : Nat := 118140960795 + 2519833 * 2 ^ 59
def prefixEnd_2519833 : Nat := 4983230072969 + 3 ^ 40 * 2519833 * 2
def baseEnd_2519833 : Nat := 1293885498060944875499005

theorem tailTrace_2519833 : CollatzResearch.WordTrace tailWord_2519833 prefixEnd_2519833 1293885498060944875499005 := by
  unfold tailWord_2519833
  simp only [CollatzResearch.WordTrace]
  refine ⟨91905859880082869059340153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61270573253388579372893435 91905859880082869059340153)
  ·
    refine ⟨68929394910062151794505115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91905859880082869059340153 68929394910062151794505115)
    ·
      refine ⟨103394092365093227691757673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68929394910062151794505115 103394092365093227691757673)
      ·
        refine ⟨77545569273819920768818255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103394092365093227691757673 77545569273819920768818255)
        ·
          refine ⟨116318353910729881153227383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77545569273819920768818255 116318353910729881153227383)
          ·
            refine ⟨174477530866094821729841075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116318353910729881153227383 174477530866094821729841075)
            ·
              refine ⟨261716296299142232594761613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174477530866094821729841075 261716296299142232594761613)
              ·
                refine ⟨98143611112178337223035605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261716296299142232594761613 98143611112178337223035605)
                ·
                  refine ⟨2300240885441679778664897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98143611112178337223035605 2300240885441679778664897)
                  ·
                    refine ⟨1725180664081259833998673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300240885441679778664897 1725180664081259833998673)
                    ·
                      refine ⟨1293885498060944875499005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725180664081259833998673 1293885498060944875499005)
                      ·
                        rfl

theorem cell23_2519833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_2519833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519833 prefixEnd_2519833 := by exact prefixLift 2519833
  have htrace : WordTrace (prefixWord ++ tailWord_2519833) baseStart_2519833 baseEnd_2519833 := by
    simpa [prefixWord, tailWord_2519833, baseEnd_2519833] using wordTrace_append hprefix tailTrace_2519833
  have hstable : (prefixWord ++ tailWord_2519833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519833).length < 2 ^ (prefixWord ++ tailWord_2519833).sum := by decide
  have hdescent : baseEnd_2519833 < baseStart_2519833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519839 : List Nat := [1, 1, 2, 4, 2, 13]
def baseStart_2519839 : Nat := 118140960795 + 2519839 * 2 ^ 59
def prefixEnd_2519839 : Nat := 4983230072969 + 3 ^ 40 * 2519839 * 2
def baseEnd_2519839 : Nat := 5324644357797826551539

theorem tailTrace_2519839 : CollatzResearch.WordTrace tailWord_2519839 prefixEnd_2519839 5324644357797826551539 := by
  unfold tailWord_2519839
  simp only [CollatzResearch.WordTrace]
  refine ⟨91906078718061132084058571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61270719145374088056039047 91906078718061132084058571)
  ·
    refine ⟨137859118077091698126087857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91906078718061132084058571 137859118077091698126087857)
    ·
      refine ⟨103394338557818773594565893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137859118077091698126087857 103394338557818773594565893)
      ·
        refine ⟨19386438479591020048981105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103394338557818773594565893 19386438479591020048981105)
        ·
          refine ⟨14539828859693265036735829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19386438479591020048981105 14539828859693265036735829)
          ·
            refine ⟨5324644357797826551539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 14539828859693265036735829 5324644357797826551539)
            ·
              rfl

theorem cell23_2519839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 13].length) (baseStart_2519839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519839 prefixEnd_2519839 := by exact prefixLift 2519839
  have htrace : WordTrace (prefixWord ++ tailWord_2519839) baseStart_2519839 baseEnd_2519839 := by
    simpa [prefixWord, tailWord_2519839, baseEnd_2519839] using wordTrace_append hprefix tailTrace_2519839
  have hstable : (prefixWord ++ tailWord_2519839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519839).length < 2 ^ (prefixWord ++ tailWord_2519839).sum := by decide
  have hdescent : baseEnd_2519839 < baseStart_2519839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519860 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2519860 : Nat := 118140960795 + 2519860 * 2 ^ 59
def prefixEnd_2519860 : Nat := 4983230072969 + 3 ^ 40 * 2519860 * 2
def baseEnd_2519860 : Nat := 431299787346205423287127

theorem tailTrace_2519860 : CollatzResearch.WordTrace tailWord_2519860 prefixEnd_2519860 431299787346205423287127 := by
  unfold tailWord_2519860
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953422325492526335286517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61271229767323368447048689 45953422325492526335286517)
  ·
    refine ⟨4308133343014924343933111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45953422325492526335286517 4308133343014924343933111)
    ·
      refine ⟨6462200014522386515899667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4308133343014924343933111 6462200014522386515899667)
      ·
        refine ⟨9693300021783579773849501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462200014522386515899667 9693300021783579773849501)
        ·
          refine ⟨3634987508168842415193563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9693300021783579773849501 3634987508168842415193563)
          ·
            refine ⟨5452481262253263622790345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634987508168842415193563 5452481262253263622790345)
            ·
              refine ⟨4089360946689947717092759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5452481262253263622790345 4089360946689947717092759)
              ·
                refine ⟨6134041420034921575639139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089360946689947717092759 6134041420034921575639139)
                ·
                  refine ⟨9201062130052382363458709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134041420034921575639139 9201062130052382363458709)
                  ·
                    refine ⟨431299787346205423287127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9201062130052382363458709 431299787346205423287127)
                    ·
                      rfl

theorem cell23_2519860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2519860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519860 prefixEnd_2519860 := by exact prefixLift 2519860
  have htrace : WordTrace (prefixWord ++ tailWord_2519860) baseStart_2519860 baseEnd_2519860 := by
    simpa [prefixWord, tailWord_2519860, baseEnd_2519860] using wordTrace_append hprefix tailTrace_2519860
  have hstable : (prefixWord ++ tailWord_2519860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519860).length < 2 ^ (prefixWord ++ tailWord_2519860).sum := by decide
  have hdescent : baseEnd_2519860 < baseStart_2519860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519884 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2519884 : Nat := 118140960795 + 2519884 * 2 ^ 59
def prefixEnd_2519884 : Nat := 4983230072969 + 3 ^ 40 * 2519884 * 2
def baseEnd_2519884 : Nat := 1293911685574324175961271

theorem tailTrace_2519884 : CollatzResearch.WordTrace tailWord_2519884 prefixEnd_2519884 1293911685574324175961271 := by
  unfold tailWord_2519884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953860001449052384723353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61271813335265403179631137 45953860001449052384723353)
  ·
    refine ⟨34465395001086789288542515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45953860001449052384723353 34465395001086789288542515)
    ·
      refine ⟨51698092501630183932813773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34465395001086789288542515 51698092501630183932813773)
      ·
        refine ⟨19386784688111318974805165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51698092501630183932813773 19386784688111318974805165)
        ·
          refine ⟨7270044258041744615551937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19386784688111318974805165 7270044258041744615551937)
          ·
            refine ⟨5452533193531308461663953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270044258041744615551937 5452533193531308461663953)
            ·
              refine ⟨4089399895148481346247965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5452533193531308461663953 4089399895148481346247965)
              ·
                refine ⟨1533524960680680504842987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4089399895148481346247965 1533524960680680504842987)
                ·
                  refine ⟨2300287441021020757264481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533524960680680504842987 2300287441021020757264481)
                  ·
                    refine ⟨1725215580765765567948361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300287441021020757264481 1725215580765765567948361)
                    ·
                      refine ⟨1293911685574324175961271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725215580765765567948361 1293911685574324175961271)
                      ·
                        rfl

theorem cell23_2519884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2519884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519884 prefixEnd_2519884 := by exact prefixLift 2519884
  have htrace : WordTrace (prefixWord ++ tailWord_2519884) baseStart_2519884 baseEnd_2519884 := by
    simpa [prefixWord, tailWord_2519884, baseEnd_2519884] using wordTrace_append hprefix tailTrace_2519884
  have hstable : (prefixWord ++ tailWord_2519884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519884).length < 2 ^ (prefixWord ++ tailWord_2519884).sum := by decide
  have hdescent : baseEnd_2519884 < baseStart_2519884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519916 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_2519916 : Nat := 118140960795 + 2519916 * 2 ^ 59
def prefixEnd_2519916 : Nat := 4983230072969 + 3 ^ 40 * 2519916 * 2
def baseEnd_2519916 : Nat := 431309372318422683587041

theorem tailTrace_2519916 : CollatzResearch.WordTrace tailWord_2519916 prefixEnd_2519916 431309372318422683587041 := by
  unfold tailWord_2519916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45954443569391087117305801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61272591425854782823074401 45954443569391087117305801)
  ·
    refine ⟨34465832677043315337979351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45954443569391087117305801 34465832677043315337979351)
    ·
      refine ⟨51698749015564973006969027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34465832677043315337979351 51698749015564973006969027)
      ·
        refine ⟨77548123523347459510453541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51698749015564973006969027 77548123523347459510453541)
        ·
          refine ⟨14540273160627648658210039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77548123523347459510453541 14540273160627648658210039)
          ·
            refine ⟨21810409740941472987315059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14540273160627648658210039 21810409740941472987315059)
            ·
              refine ⟨32715614611412209480972589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21810409740941472987315059 32715614611412209480972589)
              ·
                refine ⟨12268355479279578555364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32715614611412209480972589 12268355479279578555364721)
                ·
                  refine ⟨9201266609459683916523541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12268355479279578555364721 9201266609459683916523541)
                  ·
                    refine ⟨431309372318422683587041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9201266609459683916523541 431309372318422683587041)
                    ·
                      rfl

theorem cell23_2519916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_2519916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519916 prefixEnd_2519916 := by exact prefixLift 2519916
  have htrace : WordTrace (prefixWord ++ tailWord_2519916) baseStart_2519916 baseEnd_2519916 := by
    simpa [prefixWord, tailWord_2519916, baseEnd_2519916] using wordTrace_append hprefix tailTrace_2519916
  have hstable : (prefixWord ++ tailWord_2519916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519916).length < 2 ^ (prefixWord ++ tailWord_2519916).sum := by decide
  have hdescent : baseEnd_2519916 < baseStart_2519916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519936 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2519936 : Nat := 118140960795 + 2519936 * 2 ^ 59
def prefixEnd_2519936 : Nat := 4983230072969 + 3 ^ 40 * 2519936 * 2
def baseEnd_2519936 : Nat := 1293938386568357972511031

theorem tailTrace_2519936 : CollatzResearch.WordTrace tailWord_2519936 prefixEnd_2519936 1293938386568357972511031 := by
  unfold tailWord_2519936
  simp only [CollatzResearch.WordTrace]
  refine ⟨45954808299354858825169831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61273077732473145100226441 45954808299354858825169831)
  ·
    refine ⟨68932212449032288237754747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45954808299354858825169831 68932212449032288237754747)
    ·
      refine ⟨103398318673548432356632121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68932212449032288237754747 103398318673548432356632121)
      ·
        refine ⟨77548739005161324267474091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103398318673548432356632121 77548739005161324267474091)
        ·
          refine ⟨116323108507741986401211137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77548739005161324267474091 116323108507741986401211137)
          ·
            refine ⟨87242331380806489800908353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116323108507741986401211137 87242331380806489800908353)
            ·
              refine ⟨65431748535604867350681265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87242331380806489800908353 65431748535604867350681265)
              ·
                refine ⟨49073811401703650513010949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65431748535604867350681265 49073811401703650513010949)
                ·
                  refine ⟨9201339637819434471189553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49073811401703650513010949 9201339637819434471189553)
                  ·
                    refine ⟨6901004728364575853392165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9201339637819434471189553 6901004728364575853392165)
                    ·
                      refine ⟨1293938386568357972511031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6901004728364575853392165 1293938386568357972511031)
                      ·
                        rfl

theorem cell23_2519936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2519936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519936 prefixEnd_2519936 := by exact prefixLift 2519936
  have htrace : WordTrace (prefixWord ++ tailWord_2519936) baseStart_2519936 baseEnd_2519936 := by
    simpa [prefixWord, tailWord_2519936, baseEnd_2519936] using wordTrace_append hprefix tailTrace_2519936
  have hstable : (prefixWord ++ tailWord_2519936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519936).length < 2 ^ (prefixWord ++ tailWord_2519936).sum := by decide
  have hdescent : baseEnd_2519936 < baseStart_2519936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519943 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2519943 : Nat := 118140960795 + 2519943 * 2 ^ 59
def prefixEnd_2519943 : Nat := 4983230072969 + 3 ^ 40 * 2519943 * 2
def baseEnd_2519943 : Nat := 1293941980932939445123499

theorem tailTrace_2519943 : CollatzResearch.WordTrace tailWord_2519943 prefixEnd_2519943 1293941980932939445123499 := by
  unfold tailWord_2519943
  simp only [CollatzResearch.WordTrace]
  refine ⟨91909871909684357845844483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61273247939789571897229655 91909871909684357845844483)
  ·
    refine ⟨137864807864526536768766725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91909871909684357845844483 137864807864526536768766725)
    ·
      refine ⟨25849651474598725644143761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137864807864526536768766725 25849651474598725644143761)
      ·
        refine ⟨19387238605949044233107821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25849651474598725644143761 19387238605949044233107821)
        ·
          refine ⟨7270214477230891587415433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19387238605949044233107821 7270214477230891587415433)
          ·
            refine ⟨5452660857923168690561575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270214477230891587415433 5452660857923168690561575)
            ·
              refine ⟨8178991286884753035842363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452660857923168690561575 8178991286884753035842363)
              ·
                refine ⟨12268486930327129553763545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178991286884753035842363 12268486930327129553763545)
                ·
                  refine ⟨9201365197745347165322659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12268486930327129553763545 9201365197745347165322659)
                  ·
                    refine ⟨13802047796618020747983989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9201365197745347165322659 13802047796618020747983989)
                    ·
                      refine ⟨1293941980932939445123499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13802047796618020747983989 1293941980932939445123499)
                      ·
                        rfl

theorem cell23_2519943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2519943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519943 prefixEnd_2519943 := by exact prefixLift 2519943
  have htrace : WordTrace (prefixWord ++ tailWord_2519943) baseStart_2519943 baseEnd_2519943 := by
    simpa [prefixWord, tailWord_2519943, baseEnd_2519943] using wordTrace_append hprefix tailTrace_2519943
  have hstable : (prefixWord ++ tailWord_2519943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519943).length < 2 ^ (prefixWord ++ tailWord_2519943).sum := by decide
  have hdescent : baseEnd_2519943 < baseStart_2519943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519983 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 5, 2]
def baseStart_2519983 : Nat := 118140960795 + 2519983 * 2 ^ 59
def prefixEnd_2519983 : Nat := 4983230072969 + 3 ^ 40 * 2519983 * 2
def baseEnd_2519983 : Nat := 1293962520159119288623315

theorem tailTrace_2519983 : CollatzResearch.WordTrace tailWord_2519983 prefixEnd_2519983 1293962520159119288623315 := by
  unfold tailWord_2519983
  simp only [CollatzResearch.WordTrace]
  refine ⟨91911330829539444677300603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61274220553026296451533735 91911330829539444677300603)
  ·
    refine ⟨137866996244309167015950905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91911330829539444677300603 137866996244309167015950905)
    ·
      refine ⟨103400247183231875261963179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137866996244309167015950905 103400247183231875261963179)
      ·
        refine ⟨155100370774847812892944769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103400247183231875261963179 155100370774847812892944769)
        ·
          refine ⟨116325278081135859669708577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155100370774847812892944769 116325278081135859669708577)
          ·
            refine ⟨87243958560851894752281433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116325278081135859669708577 87243958560851894752281433)
            ·
              refine ⟨65432968920638921064211075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87243958560851894752281433 65432968920638921064211075)
              ·
                refine ⟨98149453380958381596316613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65432968920638921064211075 98149453380958381596316613)
                ·
                  refine ⟨18403022508929696549309365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98149453380958381596316613 18403022508929696549309365)
                  ·
                    refine ⟨1725283360212159051497753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18403022508929696549309365 1725283360212159051497753)
                    ·
                      refine ⟨1293962520159119288623315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725283360212159051497753 1293962520159119288623315)
                      ·
                        rfl

theorem cell23_2519983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5, 2].length) (baseStart_2519983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519983 prefixEnd_2519983 := by exact prefixLift 2519983
  have htrace : WordTrace (prefixWord ++ tailWord_2519983) baseStart_2519983 baseEnd_2519983 := by
    simpa [prefixWord, tailWord_2519983, baseEnd_2519983] using wordTrace_append hprefix tailTrace_2519983
  have hstable : (prefixWord ++ tailWord_2519983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519983).length < 2 ^ (prefixWord ++ tailWord_2519983).sum := by decide
  have hdescent : baseEnd_2519983 < baseStart_2519983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519993 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_2519993 : Nat := 118140960795 + 2519993 * 2 ^ 59
def prefixEnd_2519993 : Nat := 4983230072969 + 3 ^ 40 * 2519993 * 2
def baseEnd_2519993 : Nat := 431322551655221416499423

theorem tailTrace_2519993 : CollatzResearch.WordTrace tailWord_2519993 prefixEnd_2519993 431322551655221416499423 := by
  unfold tailWord_2519993
  simp only [CollatzResearch.WordTrace]
  refine ⟨91911695559503216385164633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61274463706335477590109755 91911695559503216385164633)
  ·
    refine ⟨68933771669627412288873475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91911695559503216385164633 68933771669627412288873475)
    ·
      refine ⟨103400657504441118433310213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68933771669627412288873475 103400657504441118433310213)
      ·
        refine ⟨19387623282082709706245665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103400657504441118433310213 19387623282082709706245665)
        ·
          refine ⟨14540717461562032279684249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19387623282082709706245665 14540717461562032279684249)
          ·
            refine ⟨10905538096171524209763187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14540717461562032279684249 10905538096171524209763187)
            ·
              refine ⟨16358307144257286314644781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905538096171524209763187 16358307144257286314644781)
              ·
                refine ⟨6134365179096482367991793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16358307144257286314644781 6134365179096482367991793)
                ·
                  refine ⟨4600773884322361775993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134365179096482367991793 4600773884322361775993845)
                  ·
                    refine ⟨431322551655221416499423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4600773884322361775993845 431322551655221416499423)
                    ·
                      rfl

theorem cell23_2519993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_2519993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2519993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2519993 prefixEnd_2519993 := by exact prefixLift 2519993
  have htrace : WordTrace (prefixWord ++ tailWord_2519993) baseStart_2519993 baseEnd_2519993 := by
    simpa [prefixWord, tailWord_2519993, baseEnd_2519993] using wordTrace_append hprefix tailTrace_2519993
  have hstable : (prefixWord ++ tailWord_2519993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519993).length < 2 ^ (prefixWord ++ tailWord_2519993).sum := by decide
  have hdescent : baseEnd_2519993 < baseStart_2519993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520016 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_2520016 : Nat := 118140960795 + 2520016 * 2 ^ 59
def prefixEnd_2520016 : Nat := 4983230072969 + 3 ^ 40 * 2520016 * 2
def baseEnd_2520016 : Nat := 1293979465020717659510663

theorem tailTrace_2520016 : CollatzResearch.WordTrace tailWord_2520016 prefixEnd_2520016 1293979465020717659510663 := by
  unfold tailWord_2520016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45956267219209945656625951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61275022958946594208834601 45956267219209945656625951)
  ·
    refine ⟨68934400828814918484938927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45956267219209945656625951 68934400828814918484938927)
    ·
      refine ⟨103401601243222377727408391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68934400828814918484938927 103401601243222377727408391)
      ·
        refine ⟨155102401864833566591112587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103401601243222377727408391 155102401864833566591112587)
        ·
          refine ⟨232653602797250349886668881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155102401864833566591112587 232653602797250349886668881)
          ·
            refine ⟨174490202097937762415001661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232653602797250349886668881 174490202097937762415001661)
            ·
              refine ⟨65433825786726660905625623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174490202097937762415001661 65433825786726660905625623)
              ·
                refine ⟨98150738680089991358438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65433825786726660905625623 98150738680089991358438435)
                ·
                  refine ⟨147226108020134987037657653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98150738680089991358438435 147226108020134987037657653)
                  ·
                    refine ⟨13802447626887655034780405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147226108020134987037657653 13802447626887655034780405)
                    ·
                      refine ⟨1293979465020717659510663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13802447626887655034780405 1293979465020717659510663)
                      ·
                        rfl

theorem cell23_2520016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_2520016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520016 prefixEnd_2520016 := by exact prefixLift 2520016
  have htrace : WordTrace (prefixWord ++ tailWord_2520016) baseStart_2520016 baseEnd_2520016 := by
    simpa [prefixWord, tailWord_2520016, baseEnd_2520016] using wordTrace_append hprefix tailTrace_2520016
  have hstable : (prefixWord ++ tailWord_2520016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520016).length < 2 ^ (prefixWord ++ tailWord_2520016).sum := by decide
  have hdescent : baseEnd_2520016 < baseStart_2520016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520033 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_2520033 : Nat := 118140960795 + 2520033 * 2 ^ 59
def prefixEnd_2520033 : Nat := 4983230072969 + 3 ^ 40 * 2520033 * 2
def baseEnd_2520033 : Nat := 1293988194191844092998085

theorem tailTrace_2520033 : CollatzResearch.WordTrace tailWord_2520033 prefixEnd_2520033 1293988194191844092998085 := by
  unfold tailWord_2520033
  simp only [CollatzResearch.WordTrace]
  refine ⟨91913154479358303216620753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61275436319572202144413835 91913154479358303216620753)
  ·
    refine ⟨68934865859518727412465565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91913154479358303216620753 68934865859518727412465565)
    ·
      refine ⟨25850574697319522779674587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68934865859518727412465565 25850574697319522779674587)
      ·
        refine ⟨38775862045979284169511881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25850574697319522779674587 38775862045979284169511881)
        ·
          refine ⟨29081896534484463127133911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38775862045979284169511881 29081896534484463127133911)
          ·
            refine ⟨43622844801726694690700867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29081896534484463127133911 43622844801726694690700867)
            ·
              refine ⟨65434267202590042036051301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43622844801726694690700867 65434267202590042036051301)
              ·
                refine ⟨12268925100485632881759619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65434267202590042036051301 12268925100485632881759619)
                ·
                  refine ⟨18403387650728449322639429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12268925100485632881759619 18403387650728449322639429)
                  ·
                    refine ⟨3450635184511584247994893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18403387650728449322639429 3450635184511584247994893)
                    ·
                      refine ⟨1293988194191844092998085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3450635184511584247994893 1293988194191844092998085)
                      ·
                        rfl

theorem cell23_2520033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_2520033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520033 prefixEnd_2520033 := by exact prefixLift 2520033
  have htrace : WordTrace (prefixWord ++ tailWord_2520033) baseStart_2520033 baseEnd_2520033 := by
    simpa [prefixWord, tailWord_2520033, baseEnd_2520033] using wordTrace_append hprefix tailTrace_2520033
  have hstable : (prefixWord ++ tailWord_2520033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520033).length < 2 ^ (prefixWord ++ tailWord_2520033).sum := by decide
  have hdescent : baseEnd_2520033 < baseStart_2520033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520057 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 1, 4]
def baseStart_2520057 : Nat := 118140960795 + 2520057 * 2 ^ 59
def prefixEnd_2520057 : Nat := 4983230072969 + 3 ^ 40 * 2520057 * 2
def baseEnd_2520057 : Nat := 431333505909183999699325

theorem tailTrace_2520057 : CollatzResearch.WordTrace tailWord_2520057 prefixEnd_2520057 431333505909183999699325 := by
  unfold tailWord_2520057
  simp only [CollatzResearch.WordTrace]
  refine ⟨91914029831271355315494425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61276019887514236876996283 91914029831271355315494425)
  ·
    refine ⟨68935522373453516486620819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91914029831271355315494425 68935522373453516486620819)
    ·
      refine ⟨103403283560180274729931229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68935522373453516486620819 103403283560180274729931229)
      ·
        refine ⟨38776231335067603023724211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103403283560180274729931229 38776231335067603023724211)
        ·
          refine ⟨58164347002601404535586317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38776231335067603023724211 58164347002601404535586317)
          ·
            refine ⟨21811630125975526700844869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58164347002601404535586317 21811630125975526700844869)
            ·
              refine ⟨4089680648620411256408413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21811630125975526700844869 4089680648620411256408413)
              ·
                refine ⟨1533630243232654221153155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4089680648620411256408413 1533630243232654221153155)
                ·
                  refine ⟨2300445364848981331729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533630243232654221153155 2300445364848981331729733)
                  ·
                    refine ⟨431333505909183999699325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2300445364848981331729733 431333505909183999699325)
                    ·
                      rfl

theorem cell23_2520057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_2520057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520057 prefixEnd_2520057 := by exact prefixLift 2520057
  have htrace : WordTrace (prefixWord ++ tailWord_2520057) baseStart_2520057 baseEnd_2520057 := by
    simpa [prefixWord, tailWord_2520057, baseEnd_2520057] using wordTrace_append hprefix tailTrace_2520057
  have hstable : (prefixWord ++ tailWord_2520057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520057).length < 2 ^ (prefixWord ++ tailWord_2520057).sum := by decide
  have hdescent : baseEnd_2520057 < baseStart_2520057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520087 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 6]
def baseStart_2520087 : Nat := 118140960795 + 2520087 * 2 ^ 59
def prefixEnd_2520087 : Nat := 4983230072969 + 3 ^ 40 * 2520087 * 2
def baseEnd_2520087 : Nat := 143779546905242986858093

theorem tailTrace_2520087 : CollatzResearch.WordTrace tailWord_2520087 prefixEnd_2520087 143779546905242986858093 := by
  unfold tailWord_2520087
  simp only [CollatzResearch.WordTrace]
  refine ⟨91915124021162670439086515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61276749347441780292724343 91915124021162670439086515)
  ·
    refine ⟨137872686031744005658629773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91915124021162670439086515 137872686031744005658629773)
    ·
      refine ⟨51702257261904002121986165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137872686031744005658629773 51702257261904002121986165)
      ·
        refine ⟨4847086618303500198936203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51702257261904002121986165 4847086618303500198936203)
        ·
          refine ⟨7270629927455250298404305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847086618303500198936203 7270629927455250298404305)
          ·
            refine ⟨5452972445591437723803229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270629927455250298404305 5452972445591437723803229)
            ·
              refine ⟨2044864667096789146426211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5452972445591437723803229 2044864667096789146426211)
              ·
                refine ⟨3067297000645183719639317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044864667096789146426211 3067297000645183719639317)
                ·
                  refine ⟨143779546905242986858093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3067297000645183719639317 143779546905242986858093)
                  ·
                    rfl

theorem cell23_2520087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 6].length) (baseStart_2520087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520087 prefixEnd_2520087 := by exact prefixLift 2520087
  have htrace : WordTrace (prefixWord ++ tailWord_2520087) baseStart_2520087 baseEnd_2520087 := by
    simpa [prefixWord, tailWord_2520087, baseEnd_2520087] using wordTrace_append hprefix tailTrace_2520087
  have hstable : (prefixWord ++ tailWord_2520087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520087).length < 2 ^ (prefixWord ++ tailWord_2520087).sum := by decide
  have hdescent : baseEnd_2520087 < baseStart_2520087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520090 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_2520090 : Nat := 118140960795 + 2520090 * 2 ^ 59
def prefixEnd_2520090 : Nat := 4983230072969 + 3 ^ 40 * 2520090 * 2
def baseEnd_2520090 : Nat := 1294017462589150369985323

theorem tailTrace_2520090 : CollatzResearch.WordTrace tailWord_2520090 prefixEnd_2520090 1294017462589150369985323 := by
  unfold tailWord_2520090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22978808360037950487861431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61276822293434534634297149 22978808360037950487861431)
  ·
    refine ⟨34468212540056925731792147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22978808360037950487861431 34468212540056925731792147)
    ·
      refine ⟨51702318810085388597688221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34468212540056925731792147 51702318810085388597688221)
      ·
        refine ⟨19388369553782020724133083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51702318810085388597688221 19388369553782020724133083)
        ·
          refine ⟨29082554330673031086199625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388369553782020724133083 29082554330673031086199625)
          ·
            refine ⟨21811915748004773314649719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29082554330673031086199625 21811915748004773314649719)
            ·
              refine ⟨32717873622007159971974579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21811915748004773314649719 32717873622007159971974579)
              ·
                refine ⟨49076810433010739957961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32717873622007159971974579 49076810433010739957961869)
                ·
                  refine ⟨18403803912379027484235701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49076810433010739957961869 18403803912379027484235701)
                  ·
                    refine ⟨1725356616785533826647097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18403803912379027484235701 1725356616785533826647097)
                    ·
                      refine ⟨1294017462589150369985323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725356616785533826647097 1294017462589150369985323)
                      ·
                        rfl

theorem cell23_2520090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_2520090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520090 prefixEnd_2520090 := by exact prefixLift 2520090
  have htrace : WordTrace (prefixWord ++ tailWord_2520090) baseStart_2520090 baseEnd_2520090 := by
    simpa [prefixWord, tailWord_2520090, baseEnd_2520090] using wordTrace_append hprefix tailTrace_2520090
  have hstable : (prefixWord ++ tailWord_2520090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520090).length < 2 ^ (prefixWord ++ tailWord_2520090).sum := by decide
  have hdescent : baseEnd_2520090 < baseStart_2520090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520097 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2520097 : Nat := 118140960795 + 2520097 * 2 ^ 59
def prefixEnd_2520097 : Nat := 4983230072969 + 3 ^ 40 * 2520097 * 2
def baseEnd_2520097 : Nat := 1294021056953731842597791

theorem tailTrace_2520097 : CollatzResearch.WordTrace tailWord_2520097 prefixEnd_2520097 1294021056953731842597791 := by
  unfold tailWord_2520097
  simp only [CollatzResearch.WordTrace]
  refine ⟨91915488751126442146950545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61276992500750961431300363 91915488751126442146950545)
  ·
    refine ⟨68936616563344831610212909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91915488751126442146950545 68936616563344831610212909)
    ·
      refine ⟨25851231211254311853829841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68936616563344831610212909 25851231211254311853829841)
      ·
        refine ⟨19388423408440733890372381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25851231211254311853829841 19388423408440733890372381)
        ·
          refine ⟨7270658778165275208889643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19388423408440733890372381 7270658778165275208889643)
          ·
            refine ⟨10905988167247912813334465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270658778165275208889643 10905988167247912813334465)
            ·
              refine ⟨8179491125435934610000849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10905988167247912813334465 8179491125435934610000849)
              ·
                refine ⟨6134618344076950957500637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8179491125435934610000849 6134618344076950957500637)
                ·
                  refine ⟨2300481879028856609062739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6134618344076950957500637 2300481879028856609062739)
                  ·
                    refine ⟨3450722818543284913594109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2300481879028856609062739 3450722818543284913594109)
                    ·
                      refine ⟨1294021056953731842597791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3450722818543284913594109 1294021056953731842597791)
                      ·
                        rfl

theorem cell23_2520097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2520097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520097 prefixEnd_2520097 := by exact prefixLift 2520097
  have htrace : WordTrace (prefixWord ++ tailWord_2520097) baseStart_2520097 baseEnd_2520097 := by
    simpa [prefixWord, tailWord_2520097, baseEnd_2520097] using wordTrace_append hprefix tailTrace_2520097
  have hstable : (prefixWord ++ tailWord_2520097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520097).length < 2 ^ (prefixWord ++ tailWord_2520097).sum := by decide
  have hdescent : baseEnd_2520097 < baseStart_2520097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520113 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2520113 : Nat := 118140960795 + 2520113 * 2 ^ 59
def prefixEnd_2520113 : Nat := 4983230072969 + 3 ^ 40 * 2520113 * 2
def baseEnd_2520113 : Nat := 431343090881401259999239

theorem tailTrace_2520113 : CollatzResearch.WordTrace tailWord_2520113 prefixEnd_2520113 431343090881401259999239 := by
  unfold tailWord_2520113
  simp only [CollatzResearch.WordTrace]
  refine ⟨91916072319068476879532993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61277381546045651253021995 91916072319068476879532993)
  ·
    refine ⟨68937054239301357659649745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91916072319068476879532993 68937054239301357659649745)
    ·
      refine ⟨51702790679476018244737309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68937054239301357659649745 51702790679476018244737309)
      ·
        refine ⟨19388546504803506841776491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51702790679476018244737309 19388546504803506841776491)
        ·
          refine ⟨29082819757205260262664737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388546504803506841776491 29082819757205260262664737)
          ·
            refine ⟨21812114817903945196998553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29082819757205260262664737 21812114817903945196998553)
            ·
              refine ⟨16359086113427958897748915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21812114817903945196998553 16359086113427958897748915)
              ·
                refine ⟨24538629170141938346623373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16359086113427958897748915 24538629170141938346623373)
                ·
                  refine ⟨9201985938803226879983765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24538629170141938346623373 9201985938803226879983765)
                  ·
                    refine ⟨431343090881401259999239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9201985938803226879983765 431343090881401259999239)
                    ·
                      rfl

theorem cell23_2520113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2520113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520113 prefixEnd_2520113 := by exact prefixLift 2520113
  have htrace : WordTrace (prefixWord ++ tailWord_2520113) baseStart_2520113 baseEnd_2520113 := by
    simpa [prefixWord, tailWord_2520113, baseEnd_2520113] using wordTrace_append hprefix tailTrace_2520113
  have hstable : (prefixWord ++ tailWord_2520113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520113).length < 2 ^ (prefixWord ++ tailWord_2520113).sum := by decide
  have hdescent : baseEnd_2520113 < baseStart_2520113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520133 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_2520133 : Nat := 118140960795 + 2520133 * 2 ^ 59
def prefixEnd_2520133 : Nat := 4983230072969 + 3 ^ 40 * 2520133 * 2
def baseEnd_2520133 : Nat := 1294039542257293701747625

theorem tailTrace_2520133 : CollatzResearch.WordTrace tailWord_2520133 prefixEnd_2520133 1294039542257293701747625 := by
  unfold tailWord_2520133
  simp only [CollatzResearch.WordTrace]
  refine ⟨91916801778996020295261053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61277867852664013530174035 91916801778996020295261053)
  ·
    refine ⟨34468800667123507610722895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91916801778996020295261053 34468800667123507610722895)
    ·
      refine ⟨51703201000685261416084343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34468800667123507610722895 51703201000685261416084343)
      ·
        refine ⟨77554801501027892124126515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51703201000685261416084343 77554801501027892124126515)
        ·
          refine ⟨116332202251541838186189773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77554801501027892124126515 116332202251541838186189773)
          ·
            refine ⟨43624575844328189319821165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116332202251541838186189773 43624575844328189319821165)
            ·
              refine ⟨16359215941623070994932937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43624575844328189319821165 16359215941623070994932937)
              ·
                refine ⟨12269411956217303246199703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16359215941623070994932937 12269411956217303246199703)
                ·
                  refine ⟨18404117934325954869299555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12269411956217303246199703 18404117934325954869299555)
                  ·
                    refine ⟨27606176901488932303949333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18404117934325954869299555 27606176901488932303949333)
                    ·
                      refine ⟨1294039542257293701747625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27606176901488932303949333 1294039542257293701747625)
                      ·
                        rfl

theorem cell23_2520133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_2520133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520133 prefixEnd_2520133 := by exact prefixLift 2520133
  have htrace : WordTrace (prefixWord ++ tailWord_2520133) baseStart_2520133 baseEnd_2520133 := by
    simpa [prefixWord, tailWord_2520133, baseEnd_2520133] using wordTrace_append hprefix tailTrace_2520133
  have hstable : (prefixWord ++ tailWord_2520133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520133).length < 2 ^ (prefixWord ++ tailWord_2520133).sum := by decide
  have hdescent : baseEnd_2520133 < baseStart_2520133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520137 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 3, 2, 2]
def baseStart_2520137 : Nat := 118140960795 + 2520137 * 2 ^ 59
def prefixEnd_2520137 : Nat := 4983230072969 + 3 ^ 40 * 2520137 * 2
def baseEnd_2520137 : Nat := 1294041596179911686097607

theorem tailTrace_2520137 : CollatzResearch.WordTrace tailWord_2520137 prefixEnd_2520137 1294041596179911686097607 := by
  unfold tailWord_2520137
  simp only [CollatzResearch.WordTrace]
  refine ⟨91916947670981528978406665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61277965113987685985604443 91916947670981528978406665)
  ·
    refine ⟨68937710753236146733804999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91916947670981528978406665 68937710753236146733804999)
    ·
      refine ⟨103406566129854220100707499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68937710753236146733804999 103406566129854220100707499)
      ·
        refine ⟨155109849194781330151061249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103406566129854220100707499 155109849194781330151061249)
        ·
          refine ⟨116332386896085997613295937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155109849194781330151061249 116332386896085997613295937)
          ·
            refine ⟨87249290172064498209971953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116332386896085997613295937 87249290172064498209971953)
            ·
              refine ⟨65436967629048373657478965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87249290172064498209971953 65436967629048373657478965)
              ·
                refine ⟨6134715715223285030388653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65436967629048373657478965 6134715715223285030388653)
                ·
                  refine ⟨2300518393208731886395745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6134715715223285030388653 2300518393208731886395745)
                  ·
                    refine ⟨1725388794906548914796809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300518393208731886395745 1725388794906548914796809)
                    ·
                      refine ⟨1294041596179911686097607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725388794906548914796809 1294041596179911686097607)
                      ·
                        rfl

theorem cell23_2520137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2, 2].length) (baseStart_2520137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520137 prefixEnd_2520137 := by exact prefixLift 2520137
  have htrace : WordTrace (prefixWord ++ tailWord_2520137) baseStart_2520137 baseEnd_2520137 := by
    simpa [prefixWord, tailWord_2520137, baseEnd_2520137] using wordTrace_append hprefix tailTrace_2520137
  have hstable : (prefixWord ++ tailWord_2520137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520137).length < 2 ^ (prefixWord ++ tailWord_2520137).sum := by decide
  have hdescent : baseEnd_2520137 < baseStart_2520137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520140 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2520140 : Nat := 118140960795 + 2520140 * 2 ^ 59
def prefixEnd_2520140 : Nat := 4983230072969 + 3 ^ 40 * 2520140 * 2
def baseEnd_2520140 : Nat := 1294043136621875174360093

theorem tailTrace_2520140 : CollatzResearch.WordTrace tailWord_2520140 prefixEnd_2520140 1294043136621875174360093 := by
  unfold tailWord_2520140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45958528544985330245382937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61278038059980440327177249 45958528544985330245382937)
  ·
    refine ⟨34468896408738997684037203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45958528544985330245382937 34468896408738997684037203)
    ·
      refine ⟨51703344613108496526055805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34468896408738997684037203 51703344613108496526055805)
      ·
        refine ⟨19388754229915686197270927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51703344613108496526055805 19388754229915686197270927)
        ·
          refine ⟨29083131344873529295906391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388754229915686197270927 29083131344873529295906391)
          ·
            refine ⟨43624697017310293943859587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29083131344873529295906391 43624697017310293943859587)
            ·
              refine ⟨65437045525965440915789381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43624697017310293943859587 65437045525965440915789381)
              ·
                refine ⟨12269446036118520171710509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65437045525965440915789381 12269446036118520171710509)
                ·
                  refine ⟨4601042263544445064391441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12269446036118520171710509 4601042263544445064391441)
                  ·
                    refine ⟨3450781697658333798293581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601042263544445064391441 3450781697658333798293581)
                    ·
                      refine ⟨1294043136621875174360093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3450781697658333798293581 1294043136621875174360093)
                      ·
                        rfl

theorem cell23_2520140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2520140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520140 prefixEnd_2520140 := by exact prefixLift 2520140
  have htrace : WordTrace (prefixWord ++ tailWord_2520140) baseStart_2520140 baseEnd_2520140 := by
    simpa [prefixWord, tailWord_2520140, baseEnd_2520140] using wordTrace_append hprefix tailTrace_2520140
  have hstable : (prefixWord ++ tailWord_2520140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520140).length < 2 ^ (prefixWord ++ tailWord_2520140).sum := by decide
  have hdescent : baseEnd_2520140 < baseStart_2520140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520158 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2520158 : Nat := 118140960795 + 2520158 * 2 ^ 59
def prefixEnd_2520158 : Nat := 4983230072969 + 3 ^ 40 * 2520158 * 2
def baseEnd_2520158 : Nat := 1294052379273656103935011

theorem tailTrace_2520158 : CollatzResearch.WordTrace tailWord_2520158 prefixEnd_2520158 1294052379273656103935011 := by
  unfold tailWord_2520158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489714200488181195615141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61278475735936966376614085 11489714200488181195615141)
  ·
    refine ⟨2154321412591533974177839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11489714200488181195615141 2154321412591533974177839)
    ·
      refine ⟨3231482118887300961266759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154321412591533974177839 3231482118887300961266759)
      ·
        refine ⟨4847223178330951441900139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231482118887300961266759 4847223178330951441900139)
        ·
          refine ⟨7270834767496427162850209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847223178330951441900139 7270834767496427162850209)
          ·
            refine ⟨5453126075622320372137657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270834767496427162850209 5453126075622320372137657)
            ·
              refine ⟨4089844556716740279103243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5453126075622320372137657 4089844556716740279103243)
              ·
                refine ⟨6134766835075110418654865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089844556716740279103243 6134766835075110418654865)
                ·
                  refine ⟨4601075126306332813991149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134766835075110418654865 4601075126306332813991149)
                  ·
                    refine ⟨1725403172364874805246681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4601075126306332813991149 1725403172364874805246681)
                    ·
                      refine ⟨1294052379273656103935011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725403172364874805246681 1294052379273656103935011)
                      ·
                        rfl

theorem cell23_2520158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2520158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520158 prefixEnd_2520158 := by exact prefixLift 2520158
  have htrace : WordTrace (prefixWord ++ tailWord_2520158) baseStart_2520158 baseEnd_2520158 := by
    simpa [prefixWord, tailWord_2520158, baseEnd_2520158] using wordTrace_append hprefix tailTrace_2520158
  have hstable : (prefixWord ++ tailWord_2520158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520158).length < 2 ^ (prefixWord ++ tailWord_2520158).sum := by decide
  have hdescent : baseEnd_2520158 < baseStart_2520158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520181 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2520181 : Nat := 118140960795 + 2520181 * 2 ^ 59
def prefixEnd_2520181 : Nat := 4983230072969 + 3 ^ 40 * 2520181 * 2
def baseEnd_2520181 : Nat := 431354729776236504649135

theorem tailTrace_2520181 : CollatzResearch.WordTrace tailWord_2520181 prefixEnd_2520181 431354729776236504649135 := by
  unfold tailWord_2520181
  simp only [CollatzResearch.WordTrace]
  refine ⟨91918552482822124493008397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61279034988548082995338931 91918552482822124493008397)
  ·
    refine ⟨34469457181058296684878149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91918552482822124493008397 34469457181058296684878149)
    ·
      refine ⟨6463023221448430628414653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34469457181058296684878149 6463023221448430628414653)
      ·
        refine ⟨2423633708043161485655495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6463023221448430628414653 2423633708043161485655495)
        ·
          refine ⟨3635450562064742228483243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423633708043161485655495 3635450562064742228483243)
          ·
            refine ⟨5453175843097113342724865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635450562064742228483243 5453175843097113342724865)
            ·
              refine ⟨4089881882322835007043649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5453175843097113342724865 4089881882322835007043649)
              ·
                refine ⟨3067411411742126255282737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4089881882322835007043649 3067411411742126255282737)
                ·
                  refine ⟨2300558558806594691462053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067411411742126255282737 2300558558806594691462053)
                  ·
                    refine ⟨431354729776236504649135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2300558558806594691462053 431354729776236504649135)
                    ·
                      rfl

theorem cell23_2520181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2520181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520181 prefixEnd_2520181 := by exact prefixLift 2520181
  have htrace : WordTrace (prefixWord ++ tailWord_2520181) baseStart_2520181 baseEnd_2520181 := by
    simpa [prefixWord, tailWord_2520181, baseEnd_2520181] using wordTrace_append hprefix tailTrace_2520181
  have hstable : (prefixWord ++ tailWord_2520181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520181).length < 2 ^ (prefixWord ++ tailWord_2520181).sum := by decide
  have hdescent : baseEnd_2520181 < baseStart_2520181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520231 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2520231 : Nat := 118140960795 + 2520231 * 2 ^ 59
def prefixEnd_2520231 : Nat := 4983230072969 + 3 ^ 40 * 2520231 * 2
def baseEnd_2520231 : Nat := 1294089863361434318322175

theorem tailTrace_2520231 : CollatzResearch.WordTrace tailWord_2520231 prefixEnd_2520231 1294089863361434318322175 := by
  unfold tailWord_2520231
  simp only [CollatzResearch.WordTrace]
  refine ⟨91920376132640983032328547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61280250755093988688219031 91920376132640983032328547)
  ·
    refine ⟨137880564198961474548492821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91920376132640983032328547 137880564198961474548492821)
    ·
      refine ⟨6463151446826319119460601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137880564198961474548492821 6463151446826319119460601)
      ·
        refine ⟨4847363585119739339595451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6463151446826319119460601 4847363585119739339595451)
        ·
          refine ⟨7271045377679609009393177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847363585119739339595451 7271045377679609009393177)
          ·
            refine ⟨5453284033259706757044883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271045377679609009393177 5453284033259706757044883)
            ·
              refine ⟨8179926049889560135567325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453284033259706757044883 8179926049889560135567325)
              ·
                refine ⟨3067472268708585050837747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8179926049889560135567325 3067472268708585050837747)
                ·
                  refine ⟨4601208403062877576256621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067472268708585050837747 4601208403062877576256621)
                  ·
                    refine ⟨1725453151148579091096233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4601208403062877576256621 1725453151148579091096233)
                    ·
                      refine ⟨1294089863361434318322175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725453151148579091096233 1294089863361434318322175)
                      ·
                        rfl

theorem cell23_2520231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2520231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520231 prefixEnd_2520231 := by exact prefixLift 2520231
  have htrace : WordTrace (prefixWord ++ tailWord_2520231) baseStart_2520231 baseEnd_2520231 := by
    simpa [prefixWord, tailWord_2520231, baseEnd_2520231] using wordTrace_append hprefix tailTrace_2520231
  have hstable : (prefixWord ++ tailWord_2520231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520231).length < 2 ^ (prefixWord ++ tailWord_2520231).sum := by decide
  have hdescent : baseEnd_2520231 < baseStart_2520231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520301 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2520301 : Nat := 118140960795 + 2520301 * 2 ^ 59
def prefixEnd_2520301 : Nat := 4983230072969 + 3 ^ 40 * 2520301 * 2
def baseEnd_2520301 : Nat := 143791756334138782716317

theorem tailTrace_2520301 : CollatzResearch.WordTrace tailWord_2520301 prefixEnd_2520301 143791756334138782716317 := by
  unfold tailWord_2520301
  simp only [CollatzResearch.WordTrace]
  refine ⟨91922929242387384987376757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61281952828258256658251171 91922929242387384987376757)
  ·
    refine ⟨8617774616473817342566571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91922929242387384987376757 8617774616473817342566571)
    ·
      refine ⟨12926661924710726013849857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8617774616473817342566571 12926661924710726013849857)
      ·
        refine ⟨9694996443533044510387393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12926661924710726013849857 9694996443533044510387393)
        ·
          refine ⟨7271247332649783382790545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9694996443533044510387393 7271247332649783382790545)
          ·
            refine ⟨5453435499487337537092909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271247332649783382790545 5453435499487337537092909)
            ·
              refine ⟨2045038312307751576409841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453435499487337537092909 2045038312307751576409841)
              ·
                refine ⟨1533778734230813682307381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045038312307751576409841 1533778734230813682307381)
                ·
                  refine ⟨143791756334138782716317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1533778734230813682307381 143791756334138782716317)
                  ·
                    rfl

theorem cell23_2520301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2520301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520301 prefixEnd_2520301 := by exact prefixLift 2520301
  have htrace : WordTrace (prefixWord ++ tailWord_2520301) baseStart_2520301 baseEnd_2520301 := by
    simpa [prefixWord, tailWord_2520301, baseEnd_2520301] using wordTrace_append hprefix tailTrace_2520301
  have hstable : (prefixWord ++ tailWord_2520301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520301).length < 2 ^ (prefixWord ++ tailWord_2520301).sum := by decide
  have hdescent : baseEnd_2520301 < baseStart_2520301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520330 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2520330 : Nat := 118140960795 + 2520330 * 2 ^ 59
def prefixEnd_2520330 : Nat := 4983230072969 + 3 ^ 40 * 2520330 * 2
def baseEnd_2520330 : Nat := 1294140697946229430984219

theorem tailTrace_2520330 : CollatzResearch.WordTrace tailWord_2520330 prefixEnd_2520330 1294140697946229430984219 := by
  unfold tailWord_2520330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22980996739820580735045611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61282657972854881960121629 22980996739820580735045611)
  ·
    refine ⟨34471495109730871102568417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22980996739820580735045611 34471495109730871102568417)
    ·
      refine ⟨25853621332298153326926313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34471495109730871102568417 25853621332298153326926313)
      ·
        refine ⟨19390215999223614995194735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25853621332298153326926313 19390215999223614995194735)
        ·
          refine ⟨29085323998835422492792103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19390215999223614995194735 29085323998835422492792103)
          ·
            refine ⟨43627985998253133739188155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29085323998835422492792103 43627985998253133739188155)
            ·
              refine ⟨65441978997379700608782233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43627985998253133739188155 65441978997379700608782233)
              ·
                refine ⟨49081484248034775456586675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65441978997379700608782233 49081484248034775456586675)
                ·
                  refine ⟨73622226372052163184880013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49081484248034775456586675 73622226372052163184880013)
                  ·
                    refine ⟨27608334889519561194330005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73622226372052163184880013 27608334889519561194330005)
                    ·
                      refine ⟨1294140697946229430984219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27608334889519561194330005 1294140697946229430984219)
                      ·
                        rfl

theorem cell23_2520330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2520330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520330 prefixEnd_2520330 := by exact prefixLift 2520330
  have htrace : WordTrace (prefixWord ++ tailWord_2520330) baseStart_2520330 baseEnd_2520330 := by
    simpa [prefixWord, tailWord_2520330, baseEnd_2520330] using wordTrace_append hprefix tailTrace_2520330
  have hstable : (prefixWord ++ tailWord_2520330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520330).length < 2 ^ (prefixWord ++ tailWord_2520330).sum := by decide
  have hdescent : baseEnd_2520330 < baseStart_2520330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520334 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2520334 : Nat := 118140960795 + 2520334 * 2 ^ 59
def prefixEnd_2520334 : Nat := 4983230072969 + 3 ^ 40 * 2520334 * 2
def baseEnd_2520334 : Nat := 1294142751868847415334201

theorem tailTrace_2520334 : CollatzResearch.WordTrace tailWord_2520334 prefixEnd_2520334 1294142751868847415334201 := by
  unfold tailWord_2520334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11490516606408478952916007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61282755234178554415552037 11490516606408478952916007)
  ·
    refine ⟨17235774909612718429374011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11490516606408478952916007 17235774909612718429374011)
    ·
      refine ⟨25853662364419077644061017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17235774909612718429374011 25853662364419077644061017)
      ·
        refine ⟨19390246773314308233045763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25853662364419077644061017 19390246773314308233045763)
        ·
          refine ⟨29085370159971462349568645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19390246773314308233045763 29085370159971462349568645)
          ·
            refine ⟨5453506904994649190544121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29085370159971462349568645 5453506904994649190544121)
            ·
              refine ⟨4090130178745986892908091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5453506904994649190544121 4090130178745986892908091)
              ·
                refine ⟨6135195268118980339362137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090130178745986892908091 6135195268118980339362137)
                ·
                  refine ⟨4601396451089235254521603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135195268118980339362137 4601396451089235254521603)
                  ·
                    refine ⟨6902094676633852881782405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4601396451089235254521603 6902094676633852881782405)
                    ·
                      refine ⟨1294142751868847415334201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6902094676633852881782405 1294142751868847415334201)
                      ·
                        rfl

theorem cell23_2520334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2520334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520334 prefixEnd_2520334 := by exact prefixLift 2520334
  have htrace : WordTrace (prefixWord ++ tailWord_2520334) baseStart_2520334 baseEnd_2520334 := by
    simpa [prefixWord, tailWord_2520334, baseEnd_2520334] using wordTrace_append hprefix tailTrace_2520334
  have hstable : (prefixWord ++ tailWord_2520334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520334).length < 2 ^ (prefixWord ++ tailWord_2520334).sum := by decide
  have hdescent : baseEnd_2520334 < baseStart_2520334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520357 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 6]
def baseStart_2520357 : Nat := 118140960795 + 2520357 * 2 ^ 59
def prefixEnd_2520357 : Nat := 4983230072969 + 3 ^ 40 * 2520357 * 2
def baseEnd_2520357 : Nat := 143794951324877869482955

theorem tailTrace_2520357 : CollatzResearch.WordTrace tailWord_2520357 prefixEnd_2520357 143794951324877869482955 := by
  unfold tailWord_2520357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91924971730184506551415325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61283314486789671034276883 91924971730184506551415325)
  ·
    refine ⟨34471864398819189956780747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91924971730184506551415325 34471864398819189956780747)
    ·
      refine ⟨51707796598228784935171121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34471864398819189956780747 51707796598228784935171121)
      ·
        refine ⟨38780847448671588701378341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51707796598228784935171121 38780847448671588701378341)
        ·
          refine ⟨7271408896625922881508439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38780847448671588701378341 7271408896625922881508439)
          ·
            refine ⟨10907113344938884322262659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7271408896625922881508439 10907113344938884322262659)
            ·
              refine ⟨16360670017408326483393989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10907113344938884322262659 16360670017408326483393989)
              ·
                refine ⟨3067625628264061215636373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16360670017408326483393989 3067625628264061215636373)
                ·
                  refine ⟨143794951324877869482955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3067625628264061215636373 143794951324877869482955)
                  ·
                    rfl

theorem cell23_2520357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_2520357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520357 prefixEnd_2520357 := by exact prefixLift 2520357
  have htrace : WordTrace (prefixWord ++ tailWord_2520357) baseStart_2520357 baseEnd_2520357 := by
    simpa [prefixWord, tailWord_2520357, baseEnd_2520357] using wordTrace_append hprefix tailTrace_2520357
  have hstable : (prefixWord ++ tailWord_2520357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520357).length < 2 ^ (prefixWord ++ tailWord_2520357).sum := by decide
  have hdescent : baseEnd_2520357 < baseStart_2520357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520384 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_2520384 : Nat := 118140960795 + 2520384 * 2 ^ 59
def prefixEnd_2520384 : Nat := 4983230072969 + 3 ^ 40 * 2520384 * 2
def baseEnd_2520384 : Nat := 1294168425901572219708971

theorem tailTrace_2520384 : CollatzResearch.WordTrace tailWord_2520384 prefixEnd_2520384 1294168425901572219708971 := by
  unfold tailWord_2520384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45962978250543345081324103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61283971000724460108432137 45962978250543345081324103)
  ·
    refine ⟨68944467375815017621986155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45962978250543345081324103 68944467375815017621986155)
    ·
      refine ⟨103416701063722526432979233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68944467375815017621986155 103416701063722526432979233)
      ·
        refine ⟨77562525797791894824734425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103416701063722526432979233 77562525797791894824734425)
        ·
          refine ⟨58171894348343921118550819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77562525797791894824734425 58171894348343921118550819)
          ·
            refine ⟨87257841522515881677826229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58171894348343921118550819 87257841522515881677826229)
            ·
              refine ⟨8180422642735863907296209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87257841522515881677826229 8180422642735863907296209)
              ·
                refine ⟨6135316982051897930472157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8180422642735863907296209 6135316982051897930472157)
                ·
                  refine ⟨2300743868269461723927059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6135316982051897930472157 2300743868269461723927059)
                  ·
                    refine ⟨3451115802404192585890589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2300743868269461723927059 3451115802404192585890589)
                    ·
                      refine ⟨1294168425901572219708971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451115802404192585890589 1294168425901572219708971)
                      ·
                        rfl

theorem cell23_2520384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_2520384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520384 prefixEnd_2520384 := by exact prefixLift 2520384
  have htrace : WordTrace (prefixWord ++ tailWord_2520384) baseStart_2520384 baseEnd_2520384 := by
    simpa [prefixWord, tailWord_2520384, baseEnd_2520384] using wordTrace_append hprefix tailTrace_2520384
  have hstable : (prefixWord ++ tailWord_2520384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520384).length < 2 ^ (prefixWord ++ tailWord_2520384).sum := by decide
  have hdescent : baseEnd_2520384 < baseStart_2520384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520387 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 1, 5]
def baseStart_2520387 : Nat := 118140960795 + 2520387 * 2 ^ 59
def prefixEnd_2520387 : Nat := 4983230072969 + 3 ^ 40 * 2520387 * 2
def baseEnd_2520387 : Nat := 431389988781178569323819

theorem tailTrace_2520387 : CollatzResearch.WordTrace tailWord_2520387 prefixEnd_2520387 431389988781178569323819 := by
  unfold tailWord_2520387
  simp only [CollatzResearch.WordTrace]
  refine ⟨91926065920075821675007415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61284043946717214450004943 91926065920075821675007415)
  ·
    refine ⟨137889098880113732512511123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91926065920075821675007415 137889098880113732512511123)
    ·
      refine ⟨206833648320170598768766685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137889098880113732512511123 206833648320170598768766685)
      ·
        refine ⟨77562618120063974538287507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206833648320170598768766685 77562618120063974538287507)
        ·
          refine ⟨116343927180095961807431261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77562618120063974538287507 116343927180095961807431261)
          ·
            refine ⟨43628972692535985677786723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116343927180095961807431261 43628972692535985677786723)
            ·
              refine ⟨65443459038803978516680085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43628972692535985677786723 65443459038803978516680085)
              ·
                refine ⟨3067662142443936492969379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65443459038803978516680085 3067662142443936492969379)
                ·
                  refine ⟨4601493213665904739454069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067662142443936492969379 4601493213665904739454069)
                  ·
                    refine ⟨431389988781178569323819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4601493213665904739454069 431389988781178569323819)
                    ·
                      rfl

theorem cell23_2520387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 5].length) (baseStart_2520387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520387 prefixEnd_2520387 := by exact prefixLift 2520387
  have htrace : WordTrace (prefixWord ++ tailWord_2520387) baseStart_2520387 baseEnd_2520387 := by
    simpa [prefixWord, tailWord_2520387, baseEnd_2520387] using wordTrace_append hprefix tailTrace_2520387
  have hstable : (prefixWord ++ tailWord_2520387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520387).length < 2 ^ (prefixWord ++ tailWord_2520387).sum := by decide
  have hdescent : baseEnd_2520387 < baseStart_2520387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520388 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2520388 : Nat := 118140960795 + 2520388 * 2 ^ 59
def prefixEnd_2520388 : Nat := 4983230072969 + 3 ^ 40 * 2520388 * 2
def baseEnd_2520388 : Nat := 1294170479824190204058953

theorem tailTrace_2520388 : CollatzResearch.WordTrace tailWord_2520388 prefixEnd_2520388 1294170479824190204058953 := by
  unfold tailWord_2520388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45963051196536099422896909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61284068262048132563862545 45963051196536099422896909)
  ·
    refine ⟨17236144198701037283586341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45963051196536099422896909 17236144198701037283586341)
    ·
      refine ⟨3231777037256444490672439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17236144198701037283586341 3231777037256444490672439)
      ·
        refine ⟨4847665555884666736008659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231777037256444490672439 4847665555884666736008659)
        ·
          refine ⟨7271498333827000104012989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847665555884666736008659 7271498333827000104012989)
          ·
            refine ⟨2726811875185125039004871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7271498333827000104012989 2726811875185125039004871)
            ·
              refine ⟨4090217812777687558507307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726811875185125039004871 4090217812777687558507307)
              ·
                refine ⟨6135326719166531337760961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090217812777687558507307 6135326719166531337760961)
                ·
                  refine ⟨4601495039374898503320721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135326719166531337760961 4601495039374898503320721)
                  ·
                    refine ⟨3451121279531173877490541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601495039374898503320721 3451121279531173877490541)
                    ·
                      refine ⟨1294170479824190204058953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451121279531173877490541 1294170479824190204058953)
                      ·
                        rfl

theorem cell23_2520388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2520388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520388 prefixEnd_2520388 := by exact prefixLift 2520388
  have htrace : WordTrace (prefixWord ++ tailWord_2520388) baseStart_2520388 baseEnd_2520388 := by
    simpa [prefixWord, tailWord_2520388, baseEnd_2520388] using wordTrace_append hprefix tailTrace_2520388
  have hstable : (prefixWord ++ tailWord_2520388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520388).length < 2 ^ (prefixWord ++ tailWord_2520388).sum := by decide
  have hdescent : baseEnd_2520388 < baseStart_2520388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520404 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2520404 : Nat := 118140960795 + 2520404 * 2 ^ 59
def prefixEnd_2520404 : Nat := 4983230072969 + 3 ^ 40 * 2520404 * 2
def baseEnd_2520404 : Nat := 431392898504887380486293

theorem tailTrace_2520404 : CollatzResearch.WordTrace tailWord_2520404 prefixEnd_2520404 431392898504887380486293 := by
  unfold tailWord_2520404
  simp only [CollatzResearch.WordTrace]
  refine ⟨45963342980507116789188133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61284457307342822385584177 45963342980507116789188133)
  ·
    refine ⟨8618126808845084397972775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45963342980507116789188133 8618126808845084397972775)
    ·
      refine ⟨12927190213267626596959163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618126808845084397972775 12927190213267626596959163)
      ·
        refine ⟨19390785319901439895438745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12927190213267626596959163 19390785319901439895438745)
        ·
          refine ⟨14543088989926079921579059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19390785319901439895438745 14543088989926079921579059)
          ·
            refine ⟨21814633484889119882368589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543088989926079921579059 21814633484889119882368589)
            ·
              refine ⟨8180487556833419955888221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21814633484889119882368589 8180487556833419955888221)
              ·
                refine ⟨3067682833812532483458083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8180487556833419955888221 3067682833812532483458083)
                ·
                  refine ⟨4601524250718798725187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067682833812532483458083 4601524250718798725187125)
                  ·
                    refine ⟨431392898504887380486293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4601524250718798725187125 431392898504887380486293)
                    ·
                      rfl

theorem cell23_2520404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2520404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520404 prefixEnd_2520404 := by exact prefixLift 2520404
  have htrace : WordTrace (prefixWord ++ tailWord_2520404) baseStart_2520404 baseEnd_2520404 := by
    simpa [prefixWord, tailWord_2520404, baseEnd_2520404] using wordTrace_append hprefix tailTrace_2520404
  have hstable : (prefixWord ++ tailWord_2520404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520404).length < 2 ^ (prefixWord ++ tailWord_2520404).sum := by decide
  have hdescent : baseEnd_2520404 < baseStart_2520404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520418 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2520418 : Nat := 118140960795 + 2520418 * 2 ^ 59
def prefixEnd_2520418 : Nat := 4983230072969 + 3 ^ 40 * 2520418 * 2
def baseEnd_2520418 : Nat := 1294185884243825086683815

theorem tailTrace_2520418 : CollatzResearch.WordTrace tailWord_2520418 prefixEnd_2520418 1294185884243825086683815 := by
  unfold tailWord_2520418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22981799145740878492346477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61284797721975675979590605 22981799145740878492346477)
  ·
    refine ⟨8618174679652829434629929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22981799145740878492346477 8618174679652829434629929)
    ·
      refine ⟨6463631009739622075972447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8618174679652829434629929 6463631009739622075972447)
      ·
        refine ⟨9695446514609433113958671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463631009739622075972447 9695446514609433113958671)
        ·
          refine ⟨14543169771914149670938007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695446514609433113958671 14543169771914149670938007)
          ·
            refine ⟨21814754657871224506407011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543169771914149670938007 21814754657871224506407011)
            ·
              refine ⟨32722131986806836759610517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21814754657871224506407011 32722131986806836759610517)
              ·
                refine ⟨1533849936881570473106743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32722131986806836759610517 1533849936881570473106743)
                ·
                  refine ⟨2300774905322355709660115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533849936881570473106743 2300774905322355709660115)
                  ·
                    refine ⟨3451162357983533564490173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2300774905322355709660115 3451162357983533564490173)
                    ·
                      refine ⟨1294185884243825086683815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451162357983533564490173 1294185884243825086683815)
                      ·
                        rfl

theorem cell23_2520418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2520418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520418 prefixEnd_2520418 := by exact prefixLift 2520418
  have htrace : WordTrace (prefixWord ++ tailWord_2520418) baseStart_2520418 baseEnd_2520418 := by
    simpa [prefixWord, tailWord_2520418, baseEnd_2520418] using wordTrace_append hprefix tailTrace_2520418
  have hstable : (prefixWord ++ tailWord_2520418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520418).length < 2 ^ (prefixWord ++ tailWord_2520418).sum := by decide
  have hdescent : baseEnd_2520418 < baseStart_2520418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520441 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 3, 2, 2]
def baseStart_2520441 : Nat := 118140960795 + 2520441 * 2 ^ 59
def prefixEnd_2520441 : Nat := 4983230072969 + 3 ^ 40 * 2520441 * 2
def baseEnd_2520441 : Nat := 1294197694298878496696209

theorem tailTrace_2520441 : CollatzResearch.WordTrace tailWord_2520441 prefixEnd_2520441 1294197694298878496696209 := by
  unfold tailWord_2520441
  simp only [CollatzResearch.WordTrace]
  refine ⟨91928035461880188897473177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61285356974586792598315451 91928035461880188897473177)
  ·
    refine ⟨68946026596410141673104883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91928035461880188897473177 68946026596410141673104883)
    ·
      refine ⟨103419039894615212509657325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68946026596410141673104883 103419039894615212509657325)
      ·
        refine ⟨38782139960480704691121497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103419039894615212509657325 38782139960480704691121497)
        ·
          refine ⟨29086604970360528518341123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38782139960480704691121497 29086604970360528518341123)
          ·
            refine ⟨43629907455540792777511685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29086604970360528518341123 43629907455540792777511685)
            ·
              refine ⟨8180607647913898645783441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43629907455540792777511685 8180607647913898645783441)
              ·
                refine ⟨6135455735935423984337581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8180607647913898645783441 6135455735935423984337581)
                ·
                  refine ⟨2300795900975783994126593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6135455735935423984337581 2300795900975783994126593)
                  ·
                    refine ⟨1725596925731837995594945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300795900975783994126593 1725596925731837995594945)
                    ·
                      refine ⟨1294197694298878496696209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725596925731837995594945 1294197694298878496696209)
                      ·
                        rfl

theorem cell23_2520441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_2520441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520441 prefixEnd_2520441 := by exact prefixLift 2520441
  have htrace : WordTrace (prefixWord ++ tailWord_2520441) baseStart_2520441 baseEnd_2520441 := by
    simpa [prefixWord, tailWord_2520441, baseEnd_2520441] using wordTrace_append hprefix tailTrace_2520441
  have hstable : (prefixWord ++ tailWord_2520441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520441).length < 2 ^ (prefixWord ++ tailWord_2520441).sum := by decide
  have hdescent : baseEnd_2520441 < baseStart_2520441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520484 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_2520484 : Nat := 118140960795 + 2520484 * 2 ^ 59
def prefixEnd_2520484 : Nat := 4983230072969 + 3 ^ 40 * 2520484 * 2
def baseEnd_2520484 : Nat := 1294219773967021828458511

theorem tailTrace_2520484 : CollatzResearch.WordTrace tailWord_2520484 prefixEnd_2520484 1294219773967021828458511 := by
  unfold tailWord_2520484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45964801900362203620644253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61286402533816271494192337 45964801900362203620644253)
  ·
    refine ⟨17236800712635826357741595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45964801900362203620644253 17236800712635826357741595)
    ·
      refine ⟨25855201068953739536612393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17236800712635826357741595 25855201068953739536612393)
      ·
        refine ⟨19391400801715304652459295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25855201068953739536612393 19391400801715304652459295)
        ·
          refine ⟨29087101202572956978688943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19391400801715304652459295 29087101202572956978688943)
          ·
            refine ⟨43630651803859435468033415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29087101202572956978688943 43630651803859435468033415)
            ·
              refine ⟨65445977705789153202050123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43630651803859435468033415 65445977705789153202050123)
              ·
                refine ⟨98168966558683729803075185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65445977705789153202050123 98168966558683729803075185)
                ·
                  refine ⟨73626724919012797352306389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98168966558683729803075185 73626724919012797352306389)
                  ·
                    refine ⟨1725626365289362437944681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73626724919012797352306389 1725626365289362437944681)
                    ·
                      refine ⟨1294219773967021828458511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725626365289362437944681 1294219773967021828458511)
                      ·
                        rfl

theorem cell23_2520484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_2520484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520484 prefixEnd_2520484 := by exact prefixLift 2520484
  have htrace : WordTrace (prefixWord ++ tailWord_2520484) baseStart_2520484 baseEnd_2520484 := by
    simpa [prefixWord, tailWord_2520484, baseEnd_2520484] using wordTrace_append hprefix tailTrace_2520484
  have hstable : (prefixWord ++ tailWord_2520484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520484).length < 2 ^ (prefixWord ++ tailWord_2520484).sum := by decide
  have hdescent : baseEnd_2520484 < baseStart_2520484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520584 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2520584 : Nat := 118140960795 + 2520584 * 2 ^ 59
def prefixEnd_2520584 : Nat := 4983230072969 + 3 ^ 40 * 2520584 * 2
def baseEnd_2520584 : Nat := 431423707344157145736017

theorem tailTrace_2520584 : CollatzResearch.WordTrace tailWord_2520584 prefixEnd_2520584 431423707344157145736017 := by
  unfold tailWord_2520584
  simp only [CollatzResearch.WordTrace]
  refine ⟨45966625550181062159964403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61288834066908082879952537 45966625550181062159964403)
  ·
    refine ⟨68949938325271593239946605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45966625550181062159964403 68949938325271593239946605)
    ·
      refine ⟨25856226871976847464979977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68949938325271593239946605 25856226871976847464979977)
      ·
        refine ⟨19392170153982635598734983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25856226871976847464979977 19392170153982635598734983)
        ·
          refine ⟨29088255230973953398102475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19392170153982635598734983 29088255230973953398102475)
          ·
            refine ⟨43632382846460930097153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29088255230973953398102475 43632382846460930097153713)
            ·
              refine ⟨32724287134845697572865285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43632382846460930097153713 32724287134845697572865285)
              ·
                refine ⟨6135803837783568294912241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32724287134845697572865285 6135803837783568294912241)
                ·
                  refine ⟨4601852878337676221184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135803837783568294912241 4601852878337676221184181)
                  ·
                    refine ⟨431423707344157145736017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4601852878337676221184181 431423707344157145736017)
                    ·
                      rfl

theorem cell23_2520584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2520584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520584 prefixEnd_2520584 := by exact prefixLift 2520584
  have htrace : WordTrace (prefixWord ++ tailWord_2520584) baseStart_2520584 baseEnd_2520584 := by
    simpa [prefixWord, tailWord_2520584, baseEnd_2520584] using wordTrace_append hprefix tailTrace_2520584
  have hstable : (prefixWord ++ tailWord_2520584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520584).length < 2 ^ (prefixWord ++ tailWord_2520584).sum := by decide
  have hdescent : baseEnd_2520584 < baseStart_2520584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520604 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2520604 : Nat := 118140960795 + 2520604 * 2 ^ 59
def prefixEnd_2520604 : Nat := 4983230072969 + 3 ^ 40 * 2520604 * 2
def baseEnd_2520604 : Nat := 1294281391645561358957959

theorem tailTrace_2520604 : CollatzResearch.WordTrace tailWord_2520604 prefixEnd_2520604 1294281391645561358957959 := by
  unfold tailWord_2520604
  simp only [CollatzResearch.WordTrace]
  refine ⟨45966990280144833867828433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61289320373526445157104577 45966990280144833867828433)
  ·
    refine ⟨34475242710108625400871325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45966990280144833867828433 34475242710108625400871325)
    ·
      refine ⟨12928216016290734525326747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34475242710108625400871325 12928216016290734525326747)
      ·
        refine ⟨19392324024436101787990121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12928216016290734525326747 19392324024436101787990121)
        ·
          refine ⟨14544243018327076340992591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19392324024436101787990121 14544243018327076340992591)
          ·
            refine ⟨21816364527490614511488887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14544243018327076340992591 21816364527490614511488887)
            ·
              refine ⟨32724546791235921767233331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21816364527490614511488887 32724546791235921767233331)
              ·
                refine ⟨49086820186853882650849997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32724546791235921767233331 49086820186853882650849997)
                ·
                  refine ⟨18407557570070205994068749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49086820186853882650849997 18407557570070205994068749)
                  ·
                    refine ⟨6902834088776327247775781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18407557570070205994068749 6902834088776327247775781)
                    ·
                      refine ⟨1294281391645561358957959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6902834088776327247775781 1294281391645561358957959)
                      ·
                        rfl

theorem cell23_2520604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2520604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520604 prefixEnd_2520604 := by exact prefixLift 2520604
  have htrace : WordTrace (prefixWord ++ tailWord_2520604) baseStart_2520604 baseEnd_2520604 := by
    simpa [prefixWord, tailWord_2520604, baseEnd_2520604] using wordTrace_append hprefix tailTrace_2520604
  have hstable : (prefixWord ++ tailWord_2520604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520604).length < 2 ^ (prefixWord ++ tailWord_2520604).sum := by decide
  have hdescent : baseEnd_2520604 < baseStart_2520604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520681 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 5, 2]
def baseStart_2520681 : Nat := 118140960795 + 2520681 * 2 ^ 59
def prefixEnd_2520681 : Nat := 4983230072969 + 3 ^ 40 * 2520681 * 2
def baseEnd_2520681 : Nat := 1294320929655957557695105

theorem tailTrace_2520681 : CollatzResearch.WordTrace tailWord_2520681 prefixEnd_2520681 1294320929655957557695105 := by
  unfold tailWord_2520681
  simp only [CollatzResearch.WordTrace]
  refine ⟨91936788981010709886209897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61291192654007139924139931 91936788981010709886209897)
  ·
    refine ⟨68952591735758032414657423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91936788981010709886209897 68952591735758032414657423)
    ·
      refine ⟨103428887603637048621986135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68952591735758032414657423 103428887603637048621986135)
      ·
        refine ⟨155143331405455572932979203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103428887603637048621986135 155143331405455572932979203)
        ·
          refine ⟨232714997108183359399468805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155143331405455572932979203 232714997108183359399468805)
          ·
            refine ⟨43634061957784379887400401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232714997108183359399468805 43634061957784379887400401)
            ·
              refine ⟨32725546468338284915550301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43634061957784379887400401 32725546468338284915550301)
              ·
                refine ⟨12272079925626856843331363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32725546468338284915550301 12272079925626856843331363)
                ·
                  refine ⟨18408119888440285264997045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12272079925626856843331363 18408119888440285264997045)
                  ·
                    refine ⟨1725761239541276743593473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18408119888440285264997045 1725761239541276743593473)
                    ·
                      refine ⟨1294320929655957557695105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725761239541276743593473 1294320929655957557695105)
                      ·
                        rfl

theorem cell23_2520681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5, 2].length) (baseStart_2520681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520681 prefixEnd_2520681 := by exact prefixLift 2520681
  have htrace : WordTrace (prefixWord ++ tailWord_2520681) baseStart_2520681 baseEnd_2520681 := by
    simpa [prefixWord, tailWord_2520681, baseEnd_2520681] using wordTrace_append hprefix tailTrace_2520681
  have hstable : (prefixWord ++ tailWord_2520681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520681).length < 2 ^ (prefixWord ++ tailWord_2520681).sum := by decide
  have hdescent : baseEnd_2520681 < baseStart_2520681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520704 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_2520704 : Nat := 118140960795 + 2520704 * 2 ^ 59
def prefixEnd_2520704 : Nat := 4983230072969 + 3 ^ 40 * 2520704 * 2
def baseEnd_2520704 : Nat := 431444246570336989235833

theorem tailTrace_2520704 : CollatzResearch.WordTrace tailWord_2520704 prefixEnd_2520704 431444246570336989235833 := by
  unfold tailWord_2520704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45968813929963692407148583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61291751906618256542864777 45968813929963692407148583)
  ·
    refine ⟨68953220894945538610722875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45968813929963692407148583 68953220894945538610722875)
    ·
      refine ⟨103429831342418307916084313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68953220894945538610722875 103429831342418307916084313)
      ·
        refine ⟨77572373506813730937063235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103429831342418307916084313 77572373506813730937063235)
        ·
          refine ⟨116358560260220596405594853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77572373506813730937063235 116358560260220596405594853)
          ·
            refine ⟨21817230048791361826049035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116358560260220596405594853 21817230048791361826049035)
            ·
              refine ⟨32725845073187042739073553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21817230048791361826049035 32725845073187042739073553)
              ·
                refine ⟨24544383804890282054305165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32725845073187042739073553 24544383804890282054305165)
                ·
                  refine ⟨9204143926833855770364437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24544383804890282054305165 9204143926833855770364437)
                  ·
                    refine ⟨431444246570336989235833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9204143926833855770364437 431444246570336989235833)
                    ·
                      rfl

theorem cell23_2520704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_2520704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520704 prefixEnd_2520704 := by exact prefixLift 2520704
  have htrace : WordTrace (prefixWord ++ tailWord_2520704) baseStart_2520704 baseEnd_2520704 := by
    simpa [prefixWord, tailWord_2520704, baseEnd_2520704] using wordTrace_append hprefix tailTrace_2520704
  have hstable : (prefixWord ++ tailWord_2520704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520704).length < 2 ^ (prefixWord ++ tailWord_2520704).sum := by decide
  have hdescent : baseEnd_2520704 < baseStart_2520704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520711 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2520711 : Nat := 118140960795 + 2520711 * 2 ^ 59
def prefixEnd_2520711 : Nat := 4983230072969 + 3 ^ 40 * 2520711 * 2
def baseEnd_2520711 : Nat := 1294336334075592440319967

theorem tailTrace_2520711 : CollatzResearch.WordTrace tailWord_2520711 prefixEnd_2520711 1294336334075592440319967 := by
  unfold tailWord_2520711
  simp only [CollatzResearch.WordTrace]
  refine ⟨91937883170902025009801987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61291922113934683339867991 91937883170902025009801987)
  ·
    refine ⟨137906824756353037514702981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91937883170902025009801987 137906824756353037514702981)
    ·
      refine ⟨25857529641816194534006809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137906824756353037514702981 25857529641816194534006809)
      ·
        refine ⟨19393147231362145900505107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25857529641816194534006809 19393147231362145900505107)
        ·
          refine ⟨29089720847043218850757661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393147231362145900505107 29089720847043218850757661)
          ·
            refine ⟨10908645317641207069034123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29089720847043218850757661 10908645317641207069034123)
            ·
              refine ⟨16362967976461810603551185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908645317641207069034123 16362967976461810603551185)
              ·
                refine ⟨12272225982346357952663389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16362967976461810603551185 12272225982346357952663389)
                ·
                  refine ⟨4602084743379884232248771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12272225982346357952663389 4602084743379884232248771)
                  ·
                    refine ⟨6903127115069826348373157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602084743379884232248771 6903127115069826348373157)
                    ·
                      refine ⟨1294336334075592440319967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6903127115069826348373157 1294336334075592440319967)
                      ·
                        rfl

theorem cell23_2520711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2520711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520711 prefixEnd_2520711 := by exact prefixLift 2520711
  have htrace : WordTrace (prefixWord ++ tailWord_2520711) baseStart_2520711 baseEnd_2520711 := by
    simpa [prefixWord, tailWord_2520711, baseEnd_2520711] using wordTrace_append hprefix tailTrace_2520711
  have hstable : (prefixWord ++ tailWord_2520711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520711).length < 2 ^ (prefixWord ++ tailWord_2520711).sum := by decide
  have hdescent : baseEnd_2520711 < baseStart_2520711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520732 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2520732 : Nat := 118140960795 + 2520732 * 2 ^ 59
def prefixEnd_2520732 : Nat := 4983230072969 + 3 ^ 40 * 2520732 * 2
def baseEnd_2520732 : Nat := 1294347117169336858157371

theorem tailTrace_2520732 : CollatzResearch.WordTrace tailWord_2520732 prefixEnd_2520732 1294347117169336858157371 := by
  unfold tailWord_2520732
  simp only [CollatzResearch.WordTrace]
  refine ⟨45969324551912972798158225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61292432735883963730877633 45969324551912972798158225)
  ·
    refine ⟨34476993413934729598618669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45969324551912972798158225 34476993413934729598618669)
    ·
      refine ⟨12928872530225523599482001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34476993413934729598618669 12928872530225523599482001)
      ·
        refine ⟨9696654397669142699611501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12928872530225523599482001 9696654397669142699611501)
        ·
          refine ⟨3636245399125928512354313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9696654397669142699611501 3636245399125928512354313)
          ·
            refine ⟨2727184049344446384265735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3636245399125928512354313 2727184049344446384265735)
            ·
              refine ⟨4090776074016669576398603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727184049344446384265735 4090776074016669576398603)
              ·
                refine ⟨6136164111025004364597905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090776074016669576398603 6136164111025004364597905)
                ·
                  refine ⟨4602123083268753273448429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6136164111025004364597905 4602123083268753273448429)
                  ·
                    refine ⟨1725796156225782477543161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4602123083268753273448429 1725796156225782477543161)
                    ·
                      refine ⟨1294347117169336858157371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725796156225782477543161 1294347117169336858157371)
                      ·
                        rfl

theorem cell23_2520732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2520732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520732 prefixEnd_2520732 := by exact prefixLift 2520732
  have htrace : WordTrace (prefixWord ++ tailWord_2520732) baseStart_2520732 baseEnd_2520732 := by
    simpa [prefixWord, tailWord_2520732, baseEnd_2520732] using wordTrace_append hprefix tailTrace_2520732
  have hstable : (prefixWord ++ tailWord_2520732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520732).length < 2 ^ (prefixWord ++ tailWord_2520732).sum := by decide
  have hdescent : baseEnd_2520732 < baseStart_2520732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520741 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2520741 : Nat := 118140960795 + 2520741 * 2 ^ 59
def prefixEnd_2520741 : Nat := 4983230072969 + 3 ^ 40 * 2520741 * 2
def baseEnd_2520741 : Nat := 1294351738495227322944829

theorem tailTrace_2520741 : CollatzResearch.WordTrace tailWord_2520741 prefixEnd_2520741 1294351738495227322944829 := by
  unfold tailWord_2520741
  simp only [CollatzResearch.WordTrace]
  refine ⟨91938977360793340133394077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61292651573862226755596051 91938977360793340133394077)
  ·
    refine ⟨34477116510297502550022779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91938977360793340133394077 34477116510297502550022779)
    ·
      refine ⟨51715674765446253825034169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34477116510297502550022779 51715674765446253825034169)
      ·
        refine ⟨38786756074084690368775627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51715674765446253825034169 38786756074084690368775627)
        ·
          refine ⟨58180134111127035553163441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38786756074084690368775627 58180134111127035553163441)
          ·
            refine ⟨43635100583345276664872581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58180134111127035553163441 43635100583345276664872581)
            ·
              refine ⟨8181581359377239374663609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43635100583345276664872581 8181581359377239374663609)
              ·
                refine ⟨6136186019532929530997707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8181581359377239374663609 6136186019532929530997707)
                ·
                  refine ⟨9204279029299394296496561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6136186019532929530997707 9204279029299394296496561)
                  ·
                    refine ⟨6903209271974545722372421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9204279029299394296496561 6903209271974545722372421)
                    ·
                      refine ⟨1294351738495227322944829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6903209271974545722372421 1294351738495227322944829)
                      ·
                        rfl

theorem cell23_2520741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2520741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520741 prefixEnd_2520741 := by exact prefixLift 2520741
  have htrace : WordTrace (prefixWord ++ tailWord_2520741) baseStart_2520741 baseEnd_2520741 := by
    simpa [prefixWord, tailWord_2520741, baseEnd_2520741] using wordTrace_append hprefix tailTrace_2520741
  have hstable : (prefixWord ++ tailWord_2520741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520741).length < 2 ^ (prefixWord ++ tailWord_2520741).sum := by decide
  have hdescent : baseEnd_2520741 < baseStart_2520741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520761 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2520761 : Nat := 118140960795 + 2520761 * 2 ^ 59
def prefixEnd_2520761 : Nat := 4983230072969 + 3 ^ 40 * 2520761 * 2
def baseEnd_2520761 : Nat := 1294362008108317244694737

theorem tailTrace_2520761 : CollatzResearch.WordTrace tailWord_2520761 prefixEnd_2520761 1294362008108317244694737 := by
  unfold tailWord_2520761
  simp only [CollatzResearch.WordTrace]
  refine ⟨91939706820720883549122137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61293137880480589032748091 91939706820720883549122137)
  ·
    refine ⟨68954780115540662661841603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91939706820720883549122137 68954780115540662661841603)
    ·
      refine ⟨103432170173310993992762405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68954780115540662661841603 103432170173310993992762405)
      ·
        refine ⟨19393531907495811373642951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103432170173310993992762405 19393531907495811373642951)
        ·
          refine ⟨29090297861243717060464427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393531907495811373642951 29090297861243717060464427)
          ·
            refine ⟨43635446791865575590696641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29090297861243717060464427 43635446791865575590696641)
            ·
              refine ⟨32726585093899181693022481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43635446791865575590696641 32726585093899181693022481)
              ·
                refine ⟨24544938820424386269766861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32726585093899181693022481 24544938820424386269766861)
                ·
                  refine ⟨9204352057659144851162573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24544938820424386269766861 9204352057659144851162573)
                  ·
                    refine ⟨3451632021622179319185965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9204352057659144851162573 3451632021622179319185965)
                    ·
                      refine ⟨1294362008108317244694737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451632021622179319185965 1294362008108317244694737)
                      ·
                        rfl

theorem cell23_2520761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2520761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520761 prefixEnd_2520761 := by exact prefixLift 2520761
  have htrace : WordTrace (prefixWord ++ tailWord_2520761) baseStart_2520761 baseEnd_2520761 := by
    simpa [prefixWord, tailWord_2520761, baseEnd_2520761] using wordTrace_append hprefix tailTrace_2520761
  have hstable : (prefixWord ++ tailWord_2520761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520761).length < 2 ^ (prefixWord ++ tailWord_2520761).sum := by decide
  have hdescent : baseEnd_2520761 < baseStart_2520761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520762 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_2520762 : Nat := 118140960795 + 2520762 * 2 ^ 59
def prefixEnd_2520762 : Nat := 4983230072969 + 3 ^ 40 * 2520762 * 2
def baseEnd_2520762 : Nat := 1294362521588971740782233

theorem tailTrace_2520762 : CollatzResearch.WordTrace tailWord_2520762 prefixEnd_2520762 1294362521588971740782233 := by
  unfold tailWord_2520762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984935823429315179977135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61293162195811507146605693 22984935823429315179977135)
  ·
    refine ⟨34477403735143972769965703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22984935823429315179977135 34477403735143972769965703)
    ·
      refine ⟨51716105602715959154948555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34477403735143972769965703 51716105602715959154948555)
      ·
        refine ⟨77574158404073938732422833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51716105602715959154948555 77574158404073938732422833)
        ·
          refine ⟨58180618803055454049317125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77574158404073938732422833 58180618803055454049317125)
          ·
            refine ⟨10908866025572897634246961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58180618803055454049317125 10908866025572897634246961)
            ·
              refine ⟨8181649519179673225685221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10908866025572897634246961 8181649519179673225685221)
              ·
                refine ⟨1534059284846188729815979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8181649519179673225685221 1534059284846188729815979)
                ·
                  refine ⟨2301088927269283094723969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534059284846188729815979 2301088927269283094723969)
                  ·
                    refine ⟨1725816695451962321042977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2301088927269283094723969 1725816695451962321042977)
                    ·
                      refine ⟨1294362521588971740782233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725816695451962321042977 1294362521588971740782233)
                      ·
                        rfl

theorem cell23_2520762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_2520762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520762 prefixEnd_2520762 := by exact prefixLift 2520762
  have htrace : WordTrace (prefixWord ++ tailWord_2520762) baseStart_2520762 baseEnd_2520762 := by
    simpa [prefixWord, tailWord_2520762, baseEnd_2520762] using wordTrace_append hprefix tailTrace_2520762
  have hstable : (prefixWord ++ tailWord_2520762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520762).length < 2 ^ (prefixWord ++ tailWord_2520762).sum := by decide
  have hdescent : baseEnd_2520762 < baseStart_2520762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520784 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_2520784 : Nat := 118140960795 + 2520784 * 2 ^ 59
def prefixEnd_2520784 : Nat := 4983230072969 + 3 ^ 40 * 2520784 * 2
def baseEnd_2520784 : Nat := 1294373818163370654707131

theorem tailTrace_2520784 : CollatzResearch.WordTrace tailWord_2520784 prefixEnd_2520784 1294373818163370654707131 := by
  unfold tailWord_2520784
  simp only [CollatzResearch.WordTrace]
  refine ⟨45970272849818779238604703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61293697133091705651472937 45970272849818779238604703)
  ·
    refine ⟨68955409274728168857907055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45970272849818779238604703 68955409274728168857907055)
    ·
      refine ⟨103433113912092253286860583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68955409274728168857907055 103433113912092253286860583)
      ·
        refine ⟨155149670868138379930290875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103433113912092253286860583 155149670868138379930290875)
        ·
          refine ⟨232724506302207569895436313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155149670868138379930290875 232724506302207569895436313)
          ·
            refine ⟨174543379726655677421577235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232724506302207569895436313 174543379726655677421577235)
            ·
              refine ⟨261815069589983516132365853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174543379726655677421577235 261815069589983516132365853)
              ·
                refine ⟨98180651096243818549637195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261815069589983516132365853 98180651096243818549637195)
                ·
                  refine ⟨147270976644365727824455793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98180651096243818549637195 147270976644365727824455793)
                  ·
                    refine ⟨110453232483274295868341845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147270976644365727824455793 110453232483274295868341845)
                    ·
                      refine ⟨1294373818163370654707131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 110453232483274295868341845 1294373818163370654707131)
                      ·
                        rfl

theorem cell23_2520784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_2520784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520784 prefixEnd_2520784 := by exact prefixLift 2520784
  have htrace : WordTrace (prefixWord ++ tailWord_2520784) baseStart_2520784 baseEnd_2520784 := by
    simpa [prefixWord, tailWord_2520784, baseEnd_2520784] using wordTrace_append hprefix tailTrace_2520784
  have hstable : (prefixWord ++ tailWord_2520784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520784).length < 2 ^ (prefixWord ++ tailWord_2520784).sum := by decide
  have hdescent : baseEnd_2520784 < baseStart_2520784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520805 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2520805 : Nat := 118140960795 + 2520805 * 2 ^ 59
def prefixEnd_2520805 : Nat := 4983230072969 + 3 ^ 40 * 2520805 * 2
def baseEnd_2520805 : Nat := 1294384601257115072544535

theorem tailTrace_2520805 : CollatzResearch.WordTrace tailWord_2520805 prefixEnd_2520805 1294384601257115072544535 := by
  unfold tailWord_2520805
  simp only [CollatzResearch.WordTrace]
  refine ⟨91941311632561479063723869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61294207755040986042482579 91941311632561479063723869)
  ·
    refine ⟨34477991862210554648896451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91941311632561479063723869 34477991862210554648896451)
    ·
      refine ⟨51716987793315831973344677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34477991862210554648896451 51716987793315831973344677)
      ·
        refine ⟨9696935211246718495002127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51716987793315831973344677 9696935211246718495002127)
        ·
          refine ⟨14545402816870077742503191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9696935211246718495002127 14545402816870077742503191)
          ·
            refine ⟨21818104225305116613754787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14545402816870077742503191 21818104225305116613754787)
            ·
              refine ⟨32727156337957674920632181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21818104225305116613754787 32727156337957674920632181)
              ·
                refine ⟨3068170906683532023809267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32727156337957674920632181 3068170906683532023809267)
                ·
                  refine ⟨4602256360025298035713901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068170906683532023809267 4602256360025298035713901)
                  ·
                    refine ⟨1725846135009486763392713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4602256360025298035713901 1725846135009486763392713)
                    ·
                      refine ⟨1294384601257115072544535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725846135009486763392713 1294384601257115072544535)
                      ·
                        rfl

theorem cell23_2520805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2520805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520805 prefixEnd_2520805 := by exact prefixLift 2520805
  have htrace : WordTrace (prefixWord ++ tailWord_2520805) baseStart_2520805 baseEnd_2520805 := by
    simpa [prefixWord, tailWord_2520805, baseEnd_2520805] using wordTrace_append hprefix tailTrace_2520805
  have hstable : (prefixWord ++ tailWord_2520805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520805).length < 2 ^ (prefixWord ++ tailWord_2520805).sum := by decide
  have hdescent : baseEnd_2520805 < baseStart_2520805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520831 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_2520831 : Nat := 118140960795 + 2520831 * 2 ^ 59
def prefixEnd_2520831 : Nat := 4983230072969 + 3 ^ 40 * 2520831 * 2
def baseEnd_2520831 : Nat := 1294397951754131970819415

theorem tailTrace_2520831 : CollatzResearch.WordTrace tailWord_2520831 prefixEnd_2520831 1294397951754131970819415 := by
  unfold tailWord_2520831
  simp only [CollatzResearch.WordTrace]
  refine ⟨91942259930467285504170347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61294839953644857002780231 91942259930467285504170347)
  ·
    refine ⟨137913389895700928256255521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91942259930467285504170347 137913389895700928256255521)
    ·
      refine ⟨103435042421775696192191641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137913389895700928256255521 103435042421775696192191641)
      ·
        refine ⟨77576281816331772144143731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103435042421775696192191641 77576281816331772144143731)
        ·
          refine ⟨116364422724497658216215597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77576281816331772144143731 116364422724497658216215597)
          ·
            refine ⟨43636658521686621831080849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116364422724497658216215597 43636658521686621831080849)
            ·
              refine ⟨32727493891264966373310637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43636658521686621831080849 32727493891264966373310637)
              ·
                refine ⟨12272810209224362389991489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32727493891264966373310637 12272810209224362389991489)
                ·
                  refine ⟨9204607656918271792493617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12272810209224362389991489 9204607656918271792493617)
                  ·
                    refine ⟨6903455742688703844370213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9204607656918271792493617 6903455742688703844370213)
                    ·
                      refine ⟨1294397951754131970819415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6903455742688703844370213 1294397951754131970819415)
                      ·
                        rfl

theorem cell23_2520831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_2520831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520831 prefixEnd_2520831 := by exact prefixLift 2520831
  have htrace : WordTrace (prefixWord ++ tailWord_2520831) baseStart_2520831 baseEnd_2520831 := by
    simpa [prefixWord, tailWord_2520831, baseEnd_2520831] using wordTrace_append hprefix tailTrace_2520831
  have hstable : (prefixWord ++ tailWord_2520831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520831).length < 2 ^ (prefixWord ++ tailWord_2520831).sum := by decide
  have hdescent : baseEnd_2520831 < baseStart_2520831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520839 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2520839 : Nat := 118140960795 + 2520839 * 2 ^ 59
def prefixEnd_2520839 : Nat := 4983230072969 + 3 ^ 40 * 2520839 * 2
def baseEnd_2520839 : Nat := 1294402059599367939519379

theorem tailTrace_2520839 : CollatzResearch.WordTrace tailWord_2520839 prefixEnd_2520839 1294402059599367939519379 := by
  unfold tailWord_2520839
  simp only [CollatzResearch.WordTrace]
  refine ⟨91942551714438302870461571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61295034476292201913641047 91942551714438302870461571)
  ·
    refine ⟨137913827571657454305692357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91942551714438302870461571 137913827571657454305692357)
    ·
      refine ⟨25858842669685772682317317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137913827571657454305692357 25858842669685772682317317)
      ·
        refine ⟨4848533000566082377934497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25858842669685772682317317 4848533000566082377934497)
        ·
          refine ⟨3636399750424561783450873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4848533000566082377934497 3636399750424561783450873)
          ·
            refine ⟨2727299812818421337588155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3636399750424561783450873 2727299812818421337588155)
            ·
              refine ⟨4090949719227632006382233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727299812818421337588155 4090949719227632006382233)
              ·
                refine ⟨3068212289420724004786675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090949719227632006382233 3068212289420724004786675)
                ·
                  refine ⟨4602318434131086007180013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068212289420724004786675 4602318434131086007180013)
                  ·
                    refine ⟨1725869412799157252692505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4602318434131086007180013 1725869412799157252692505)
                    ·
                      refine ⟨1294402059599367939519379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725869412799157252692505 1294402059599367939519379)
                      ·
                        rfl

theorem cell23_2520839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2520839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520839 prefixEnd_2520839 := by exact prefixLift 2520839
  have htrace : WordTrace (prefixWord ++ tailWord_2520839) baseStart_2520839 baseEnd_2520839 := by
    simpa [prefixWord, tailWord_2520839, baseEnd_2520839] using wordTrace_append hprefix tailTrace_2520839
  have hstable : (prefixWord ++ tailWord_2520839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520839).length < 2 ^ (prefixWord ++ tailWord_2520839).sum := by decide
  have hdescent : baseEnd_2520839 < baseStart_2520839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520851 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3]
def baseStart_2520851 : Nat := 118140960795 + 2520851 * 2 ^ 59
def prefixEnd_2520851 : Nat := 4983230072969 + 3 ^ 40 * 2520851 * 2
def baseEnd_2520851 : Nat := 1294408221367221892569323

theorem tailTrace_2520851 : CollatzResearch.WordTrace tailWord_2520851 prefixEnd_2520851 1294408221367221892569323 := by
  unfold tailWord_2520851
  simp only [CollatzResearch.WordTrace]
  refine ⟨91942989390394828919898407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61295326260263219279932271 91942989390394828919898407)
  ·
    refine ⟨137914484085592243379847611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91942989390394828919898407 137914484085592243379847611)
    ·
      refine ⟨206871726128388365069771417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137914484085592243379847611 206871726128388365069771417)
      ·
        refine ⟨155153794596291273802328563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206871726128388365069771417 155153794596291273802328563)
        ·
          refine ⟨232730691894436910703492845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155153794596291273802328563 232730691894436910703492845)
          ·
            refine ⟨87274009460413841513809817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232730691894436910703492845 87274009460413841513809817)
            ·
              refine ⟨65455507095310381135357363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87274009460413841513809817 65455507095310381135357363)
              ·
                refine ⟨98183260642965571703036045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65455507095310381135357363 98183260642965571703036045)
                ·
                  refine ⟨36818722741112089388638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98183260642965571703036045 36818722741112089388638517)
                  ·
                    refine ⟨3451755256979258380184861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36818722741112089388638517 3451755256979258380184861)
                    ·
                      refine ⟨1294408221367221892569323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451755256979258380184861 1294408221367221892569323)
                      ·
                        rfl

theorem cell23_2520851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_2520851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520851 prefixEnd_2520851 := by exact prefixLift 2520851
  have htrace : WordTrace (prefixWord ++ tailWord_2520851) baseStart_2520851 baseEnd_2520851 := by
    simpa [prefixWord, tailWord_2520851, baseEnd_2520851] using wordTrace_append hprefix tailTrace_2520851
  have hstable : (prefixWord ++ tailWord_2520851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520851).length < 2 ^ (prefixWord ++ tailWord_2520851).sum := by decide
  have hdescent : baseEnd_2520851 < baseStart_2520851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520885 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2520885 : Nat := 118140960795 + 2520885 * 2 ^ 59
def prefixEnd_2520885 : Nat := 4983230072969 + 3 ^ 40 * 2520885 * 2
def baseEnd_2520885 : Nat := 1294425679709474759544167

theorem tailTrace_2520885 : CollatzResearch.WordTrace tailWord_2520885 prefixEnd_2520885 1294425679709474759544167 := by
  unfold tailWord_2520885
  simp only [CollatzResearch.WordTrace]
  refine ⟨91944229472271652726636109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61296152981514435151090739 91944229472271652726636109)
  ·
    refine ⟨34479086052101869772488541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91944229472271652726636109 34479086052101869772488541)
    ·
      refine ⟨12929657269538201164683203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34479086052101869772488541 12929657269538201164683203)
      ·
        refine ⟨19394485904307301747024805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929657269538201164683203 19394485904307301747024805)
        ·
          refine ⟨3636466107057619077567151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19394485904307301747024805 3636466107057619077567151)
          ·
            refine ⟨5454699160586428616350727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636466107057619077567151 5454699160586428616350727)
            ·
              refine ⟨8182048740879642924526091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5454699160586428616350727 8182048740879642924526091)
              ·
                refine ⟨12273073111319464386789137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8182048740879642924526091 12273073111319464386789137)
                ·
                  refine ⟨9204804833489598290091853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12273073111319464386789137 9204804833489598290091853)
                  ·
                    refine ⟨3451801812558599358784445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9204804833489598290091853 3451801812558599358784445)
                    ·
                      refine ⟨1294425679709474759544167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3451801812558599358784445 1294425679709474759544167)
                      ·
                        rfl

theorem cell23_2520885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2520885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520885 prefixEnd_2520885 := by exact prefixLift 2520885
  have htrace : WordTrace (prefixWord ++ tailWord_2520885) baseStart_2520885 baseEnd_2520885 := by
    simpa [prefixWord, tailWord_2520885, baseEnd_2520885] using wordTrace_append hprefix tailTrace_2520885
  have hstable : (prefixWord ++ tailWord_2520885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520885).length < 2 ^ (prefixWord ++ tailWord_2520885).sum := by decide
  have hdescent : baseEnd_2520885 < baseStart_2520885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520921 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2520921 : Nat := 118140960795 + 2520921 * 2 ^ 59
def prefixEnd_2520921 : Nat := 4983230072969 + 3 ^ 40 * 2520921 * 2
def baseEnd_2520921 : Nat := 1294444165013036618694001

theorem tailTrace_2520921 : CollatzResearch.WordTrace tailWord_2520921 prefixEnd_2520921 1294444165013036618694001 := by
  unfold tailWord_2520921
  simp only [CollatzResearch.WordTrace]
  refine ⟨91945542500141230874946617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61297028333427487249964411 91945542500141230874946617)
  ·
    refine ⟨68959156875105923156209963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91945542500141230874946617 68959156875105923156209963)
    ·
      refine ⟨103438735312658884734314945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68959156875105923156209963 103438735312658884734314945)
      ·
        refine ⟨77579051484494163550736209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103438735312658884734314945 77579051484494163550736209)
        ·
          refine ⟨58184288613370622663052157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77579051484494163550736209 58184288613370622663052157)
          ·
            refine ⟨21819108230013983498644559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58184288613370622663052157 21819108230013983498644559)
            ·
              refine ⟨32728662345020975247966839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21819108230013983498644559 32728662345020975247966839)
              ·
                refine ⟨49092993517531462871950259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32728662345020975247966839 49092993517531462871950259)
                ·
                  refine ⟨73639490276297194307925389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49092993517531462871950259 73639490276297194307925389)
                  ·
                    refine ⟨27614808853611447865472021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73639490276297194307925389 27614808853611447865472021)
                    ·
                      refine ⟨1294444165013036618694001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27614808853611447865472021 1294444165013036618694001)
                      ·
                        rfl

theorem cell23_2520921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2520921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520921 prefixEnd_2520921 := by exact prefixLift 2520921
  have htrace : WordTrace (prefixWord ++ tailWord_2520921) baseStart_2520921 baseEnd_2520921 := by
    simpa [prefixWord, tailWord_2520921, baseEnd_2520921] using wordTrace_append hprefix tailTrace_2520921
  have hstable : (prefixWord ++ tailWord_2520921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520921).length < 2 ^ (prefixWord ++ tailWord_2520921).sum := by decide
  have hdescent : baseEnd_2520921 < baseStart_2520921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520935 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 3, 4]
def baseStart_2520935 : Nat := 118140960795 + 2520935 * 2 ^ 59
def prefixEnd_2520935 : Nat := 4983230072969 + 3 ^ 40 * 2520935 * 2
def baseEnd_2520935 : Nat := 431483784580733187972979

theorem tailTrace_2520935 : CollatzResearch.WordTrace tailWord_2520935 prefixEnd_2520935 431483784580733187972979 := by
  unfold tailWord_2520935
  simp only [CollatzResearch.WordTrace]
  refine ⟨91946053122090511265956259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61297368748060340843970839 91946053122090511265956259)
  ·
    refine ⟨137919079683135766898934389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91946053122090511265956259 137919079683135766898934389)
    ·
      refine ⟨12929913720293978146775099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137919079683135766898934389 12929913720293978146775099)
      ·
        refine ⟨19394870580440967220162649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929913720293978146775099 19394870580440967220162649)
        ·
          refine ⟨14546152935330725415121987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19394870580440967220162649 14546152935330725415121987)
          ·
            refine ⟨21819229402996088122682981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14546152935330725415121987 21819229402996088122682981)
            ·
              refine ⟨4091105513061766523003059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21819229402996088122682981 4091105513061766523003059)
              ·
                refine ⟨6136658269592649784504589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091105513061766523003059 6136658269592649784504589)
                ·
                  refine ⟨2301246851097243669189221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6136658269592649784504589 2301246851097243669189221)
                  ·
                    refine ⟨431483784580733187972979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2301246851097243669189221 431483784580733187972979)
                    ·
                      rfl

theorem cell23_2520935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_2520935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520935 prefixEnd_2520935 := by exact prefixLift 2520935
  have htrace : WordTrace (prefixWord ++ tailWord_2520935) baseStart_2520935 baseEnd_2520935 := by
    simpa [prefixWord, tailWord_2520935, baseEnd_2520935] using wordTrace_append hprefix tailTrace_2520935
  have hstable : (prefixWord ++ tailWord_2520935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520935).length < 2 ^ (prefixWord ++ tailWord_2520935).sum := by decide
  have hdescent : baseEnd_2520935 < baseStart_2520935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520942 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2520942 : Nat := 118140960795 + 2520942 * 2 ^ 59
def prefixEnd_2520942 : Nat := 4983230072969 + 3 ^ 40 * 2520942 * 2
def baseEnd_2520942 : Nat := 1294454948106781036531405

theorem tailTrace_2520942 : CollatzResearch.WordTrace tailWord_2520942 prefixEnd_2520942 1294454948106781036531405 := by
  unfold tailWord_2520942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493288554133143932682635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61297538955376767640974053 11493288554133143932682635)
  ·
    refine ⟨17239932831199715899023953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493288554133143932682635 17239932831199715899023953)
    ·
      refine ⟨12929949623399786924267965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17239932831199715899023953 12929949623399786924267965)
      ·
        refine ⟨4848731108774920096600487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12929949623399786924267965 4848731108774920096600487)
        ·
          refine ⟨7273096663162380144900731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4848731108774920096600487 7273096663162380144900731)
          ·
            refine ⟨10909644994743570217351097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273096663162380144900731 10909644994743570217351097)
            ·
              refine ⟨8182233746057677663013323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10909644994743570217351097 8182233746057677663013323)
              ·
                refine ⟨12273350619086516494519985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8182233746057677663013323 12273350619086516494519985)
                ·
                  refine ⟨9205012964314887370889989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12273350619086516494519985 9205012964314887370889989)
                  ·
                    refine ⟨1725939930809041382041873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9205012964314887370889989 1725939930809041382041873)
                    ·
                      refine ⟨1294454948106781036531405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725939930809041382041873 1294454948106781036531405)
                      ·
                        rfl

theorem cell23_2520942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2520942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520942 prefixEnd_2520942 := by exact prefixLift 2520942
  have htrace : WordTrace (prefixWord ++ tailWord_2520942) baseStart_2520942 baseEnd_2520942 := by
    simpa [prefixWord, tailWord_2520942, baseEnd_2520942] using wordTrace_append hprefix tailTrace_2520942
  have hstable : (prefixWord ++ tailWord_2520942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520942).length < 2 ^ (prefixWord ++ tailWord_2520942).sum := by decide
  have hdescent : baseEnd_2520942 < baseStart_2520942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520985 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 4, 3, 2]
def baseStart_2520985 : Nat := 118140960795 + 2520985 * 2 ^ 59
def prefixEnd_2520985 : Nat := 4983230072969 + 3 ^ 40 * 2520985 * 2
def baseEnd_2520985 : Nat := 1294477027774924368293707

theorem tailTrace_2520985 : CollatzResearch.WordTrace tailWord_2520985 prefixEnd_2520985 1294477027774924368293707 := by
  unfold tailWord_2520985
  simp only [CollatzResearch.WordTrace]
  refine ⟨91947876771909369805276409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61298584514606246536850939 91947876771909369805276409)
  ·
    refine ⟨68960907578932027353957307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91947876771909369805276409 68960907578932027353957307)
    ·
      refine ⟨103441361368398041030935961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68960907578932027353957307 103441361368398041030935961)
      ·
        refine ⟨77581021026298530773201971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103441361368398041030935961 77581021026298530773201971)
        ·
          refine ⟨116371531539447796159802957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77581021026298530773201971 116371531539447796159802957)
          ·
            refine ⟨43639324327292923559926109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116371531539447796159802957 43639324327292923559926109)
            ·
              refine ⟨16364746622734846334972291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43639324327292923559926109 16364746622734846334972291)
              ·
                refine ⟨24547119934102269502458437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16364746622734846334972291 24547119934102269502458437)
                ·
                  refine ⟨4602584987644175531710957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24547119934102269502458437 4602584987644175531710957)
                  ·
                    refine ⟨1725969370366565824391609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4602584987644175531710957 1725969370366565824391609)
                    ·
                      refine ⟨1294477027774924368293707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1725969370366565824391609 1294477027774924368293707)
                      ·
                        rfl

theorem cell23_2520985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_2520985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2520985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2520985 prefixEnd_2520985 := by exact prefixLift 2520985
  have htrace : WordTrace (prefixWord ++ tailWord_2520985) baseStart_2520985 baseEnd_2520985 := by
    simpa [prefixWord, tailWord_2520985, baseEnd_2520985] using wordTrace_append hprefix tailTrace_2520985
  have hstable : (prefixWord ++ tailWord_2520985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520985).length < 2 ^ (prefixWord ++ tailWord_2520985).sum := by decide
  have hdescent : baseEnd_2520985 < baseStart_2520985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521055 : List Nat := [1, 1, 2, 3, 4, 3, 1, 8]
def baseStart_2521055 : Nat := 118140960795 + 2521055 * 2 ^ 59
def prefixEnd_2521055 : Nat := 4983230072969 + 3 ^ 40 * 2521055 * 2
def baseEnd_2521055 : Nat := 47944924867434781274755

theorem tailTrace_2521055 : CollatzResearch.WordTrace tailWord_2521055 prefixEnd_2521055 47944924867434781274755 := by
  unfold tailWord_2521055
  simp only [CollatzResearch.WordTrace]
  refine ⟨91950429881655771760324619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61300286587770514506883079 91950429881655771760324619)
  ·
    refine ⟨137925644822483657640486929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91950429881655771760324619 137925644822483657640486929)
    ·
      refine ⟨103444233616862743230365197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137925644822483657640486929 103444233616862743230365197)
      ·
        refine ⟨38791587606323528711386949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103444233616862743230365197 38791587606323528711386949)
        ·
          refine ⟨7273422676185661633385053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38791587606323528711386949 7273422676185661633385053)
          ·
            refine ⟨2727533503569623112519395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7273422676185661633385053 2727533503569623112519395)
            ·
              refine ⟨4091300255354434668779093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727533503569623112519395 4091300255354434668779093)
              ·
                refine ⟨47944924867434781274755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4091300255354434668779093 47944924867434781274755)
                ·
                  rfl

theorem cell23_2521055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 8].length) (baseStart_2521055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521055 prefixEnd_2521055 := by exact prefixLift 2521055
  have htrace : WordTrace (prefixWord ++ tailWord_2521055) baseStart_2521055 baseEnd_2521055 := by
    simpa [prefixWord, tailWord_2521055, baseEnd_2521055] using wordTrace_append hprefix tailTrace_2521055
  have hstable : (prefixWord ++ tailWord_2521055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521055).length < 2 ^ (prefixWord ++ tailWord_2521055).sum := by decide
  have hdescent : baseEnd_2521055 < baseStart_2521055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521086 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2521086 : Nat := 118140960795 + 2521086 * 2 ^ 59
def prefixEnd_2521086 : Nat := 4983230072969 + 3 ^ 40 * 2521086 * 2
def baseEnd_2521086 : Nat := 1294528889321028473130743

theorem tailTrace_2521086 : CollatzResearch.WordTrace tailWord_2521086 prefixEnd_2521086 1294528889321028473130743 := by
  unfold tailWord_2521086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493945068067933006837889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61301040363028976036468741 11493945068067933006837889)
  ·
    refine ⟨8620458801050949755128417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11493945068067933006837889 8620458801050949755128417)
    ·
      refine ⟨6465344100788212316346313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8620458801050949755128417 6465344100788212316346313)
      ·
        refine ⟨4849008075591159237259735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6465344100788212316346313 4849008075591159237259735)
        ·
          refine ⟨7273512113386738855889603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849008075591159237259735 7273512113386738855889603)
          ·
            refine ⟨10910268170080108283834405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273512113386738855889603 10910268170080108283834405)
            ·
              refine ⟨2045675281890020303218951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10910268170080108283834405 2045675281890020303218951)
              ·
                refine ⟨3068512922835030454828427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045675281890020303218951 3068512922835030454828427)
                ·
                  refine ⟨4602769384252545682242641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068512922835030454828427 4602769384252545682242641)
                  ·
                    refine ⟨3452077038189409261681981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602769384252545682242641 3452077038189409261681981)
                    ·
                      refine ⟨1294528889321028473130743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452077038189409261681981 1294528889321028473130743)
                      ·
                        rfl

theorem cell23_2521086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2521086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521086 prefixEnd_2521086 := by exact prefixLift 2521086
  have htrace : WordTrace (prefixWord ++ tailWord_2521086) baseStart_2521086 baseEnd_2521086 := by
    simpa [prefixWord, tailWord_2521086, baseEnd_2521086] using wordTrace_append hprefix tailTrace_2521086
  have hstable : (prefixWord ++ tailWord_2521086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521086).length < 2 ^ (prefixWord ++ tailWord_2521086).sum := by decide
  have hdescent : baseEnd_2521086 < baseStart_2521086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521088 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2521088 : Nat := 118140960795 + 2521088 * 2 ^ 59
def prefixEnd_2521088 : Nat := 4983230072969 + 3 ^ 40 * 2521088 * 2
def baseEnd_2521088 : Nat := 1294529916282337465305733

theorem tailTrace_2521088 : CollatzResearch.WordTrace tailWord_2521088 prefixEnd_2521088 1294529916282337465305733 := by
  unfold tailWord_2521088
  simp only [CollatzResearch.WordTrace]
  refine ⟨45975816745268109198137959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61301088993690812264183945 45975816745268109198137959)
  ·
    refine ⟨68963725117902163797206939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45975816745268109198137959 68963725117902163797206939)
    ·
      refine ⟨103445587676853245695810409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68963725117902163797206939 103445587676853245695810409)
      ·
        refine ⟨77584190757639934271857807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103445587676853245695810409 77584190757639934271857807)
        ·
          refine ⟨116376286136459901407786711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77584190757639934271857807 116376286136459901407786711)
          ·
            refine ⟨174564429204689852111680067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116376286136459901407786711 174564429204689852111680067)
            ·
              refine ⟨261846643807034778167520101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174564429204689852111680067 261846643807034778167520101)
              ·
                refine ⟨49096245713819020906410019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261846643807034778167520101 49096245713819020906410019)
                ·
                  refine ⟨73644368570728531359615029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49096245713819020906410019 73644368570728531359615029)
                  ·
                    refine ⟨6904159553505799814963909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73644368570728531359615029 6904159553505799814963909)
                    ·
                      refine ⟨1294529916282337465305733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6904159553505799814963909 1294529916282337465305733)
                      ·
                        rfl

theorem cell23_2521088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2521088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521088 prefixEnd_2521088 := by exact prefixLift 2521088
  have htrace : WordTrace (prefixWord ++ tailWord_2521088) baseStart_2521088 baseEnd_2521088 := by
    simpa [prefixWord, tailWord_2521088, baseEnd_2521088] using wordTrace_append hprefix tailTrace_2521088
  have hstable : (prefixWord ++ tailWord_2521088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521088).length < 2 ^ (prefixWord ++ tailWord_2521088).sum := by decide
  have hdescent : baseEnd_2521088 < baseStart_2521088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521105 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_2521105 : Nat := 118140960795 + 2521105 * 2 ^ 59
def prefixEnd_2521105 : Nat := 4983230072969 + 3 ^ 40 * 2521105 * 2
def baseEnd_2521105 : Nat := 1294538645453463898793155

theorem tailTrace_2521105 : CollatzResearch.WordTrace tailWord_2521105 prefixEnd_2521105 1294538645453463898793155 := by
  unfold tailWord_2521105
  simp only [CollatzResearch.WordTrace]
  refine ⟨91952253531474630299644769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61301502354316420199763179 91952253531474630299644769)
  ·
    refine ⟨68964190148605972724733577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91952253531474630299644769 68964190148605972724733577)
    ·
      refine ⟨51723142611454479543550183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68964190148605972724733577 51723142611454479543550183)
      ·
        refine ⟨77584713917181719315325275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51723142611454479543550183 77584713917181719315325275)
        ·
          refine ⟨116377070875772578972987913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77584713917181719315325275 116377070875772578972987913)
          ·
            refine ⟨87282803156829434229740935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116377070875772578972987913 87282803156829434229740935)
            ·
              refine ⟨130924204735244151344611403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87282803156829434229740935 130924204735244151344611403)
              ·
                refine ⟨196386307102866227016917105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130924204735244151344611403 196386307102866227016917105)
                ·
                  refine ⟨147289730327149670262687829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196386307102866227016917105 147289730327149670262687829)
                  ·
                    refine ⟨1726051527271285198390873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 147289730327149670262687829 1726051527271285198390873)
                    ·
                      refine ⟨1294538645453463898793155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726051527271285198390873 1294538645453463898793155)
                      ·
                        rfl

theorem cell23_2521105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_2521105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521105 prefixEnd_2521105 := by exact prefixLift 2521105
  have htrace : WordTrace (prefixWord ++ tailWord_2521105) baseStart_2521105 baseEnd_2521105 := by
    simpa [prefixWord, tailWord_2521105, baseEnd_2521105] using wordTrace_append hprefix tailTrace_2521105
  have hstable : (prefixWord ++ tailWord_2521105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521105).length < 2 ^ (prefixWord ++ tailWord_2521105).sum := by decide
  have hdescent : baseEnd_2521105 < baseStart_2521105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521116 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2521116 : Nat := 118140960795 + 2521116 * 2 ^ 59
def prefixEnd_2521116 : Nat := 4983230072969 + 3 ^ 40 * 2521116 * 2
def baseEnd_2521116 : Nat := 1294544293740663355755605

theorem tailTrace_2521116 : CollatzResearch.WordTrace tailWord_2521116 prefixEnd_2521116 1294544293740663355755605 := by
  unfold tailWord_2521116
  simp only [CollatzResearch.WordTrace]
  refine ⟨45976327367217389589147601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61301769822956519452196801 45976327367217389589147601)
  ·
    refine ⟨34482245525413042191860701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45976327367217389589147601 34482245525413042191860701)
    ·
      refine ⟨12930842072029890821947763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34482245525413042191860701 12930842072029890821947763)
      ·
        refine ⟨19396263108044836232921645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12930842072029890821947763 19396263108044836232921645)
        ·
          refine ⟨7273598665516813587345617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19396263108044836232921645 7273598665516813587345617)
          ·
            refine ⟨5455198999137610190509213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7273598665516813587345617 5455198999137610190509213)
            ·
              refine ⟨2045699624676603821440955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5455198999137610190509213 2045699624676603821440955)
              ·
                refine ⟨3068549437014905732161433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045699624676603821440955 3068549437014905732161433)
                ·
                  refine ⟨2301412077761179299121075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068549437014905732161433 2301412077761179299121075)
                  ·
                    refine ⟨3452118116641768948681613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301412077761179299121075 3452118116641768948681613)
                    ·
                      refine ⟨1294544293740663355755605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452118116641768948681613 1294544293740663355755605)
                      ·
                        rfl

theorem cell23_2521116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2521116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521116 prefixEnd_2521116 := by exact prefixLift 2521116
  have htrace : WordTrace (prefixWord ++ tailWord_2521116) baseStart_2521116 baseEnd_2521116 := by
    simpa [prefixWord, tailWord_2521116, baseEnd_2521116] using wordTrace_append hprefix tailTrace_2521116
  have hstable : (prefixWord ++ tailWord_2521116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521116).length < 2 ^ (prefixWord ++ tailWord_2521116).sum := by decide
  have hdescent : baseEnd_2521116 < baseStart_2521116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521142 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2521142 : Nat := 118140960795 + 2521142 * 2 ^ 59
def prefixEnd_2521142 : Nat := 4983230072969 + 3 ^ 40 * 2521142 * 2
def baseEnd_2521142 : Nat := 1294557644237680254030485

theorem tailTrace_2521142 : CollatzResearch.WordTrace tailWord_2521142 prefixEnd_2521142 1294557644237680254030485 := by
  unfold tailWord_2521142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747100189521286601171355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61302402021560390412494453 5747100189521286601171355)
  ·
    refine ⟨8620650284281929901757033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747100189521286601171355 8620650284281929901757033)
    ·
      refine ⟨6465487713211447426317775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8620650284281929901757033 6465487713211447426317775)
      ·
        refine ⟨9698231569817171139476663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465487713211447426317775 9698231569817171139476663)
        ·
          refine ⟨14547347354725756709214995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9698231569817171139476663 14547347354725756709214995)
          ·
            refine ⟨21821021032088635063822493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14547347354725756709214995 21821021032088635063822493)
            ·
              refine ⟨8182882887033238148933435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21821021032088635063822493 8182882887033238148933435)
              ·
                refine ⟨12274324330549857223400153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8182882887033238148933435 12274324330549857223400153)
                ·
                  refine ⟨9205743247912392917550115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12274324330549857223400153 9205743247912392917550115)
                  ·
                    refine ⟨13808614871868589376325173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9205743247912392917550115 13808614871868589376325173)
                    ·
                      refine ⟨1294557644237680254030485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13808614871868589376325173 1294557644237680254030485)
                      ·
                        rfl

theorem cell23_2521142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2521142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521142 prefixEnd_2521142 := by exact prefixLift 2521142
  have htrace : WordTrace (prefixWord ++ tailWord_2521142) baseStart_2521142 baseEnd_2521142 := by
    simpa [prefixWord, tailWord_2521142, baseEnd_2521142] using wordTrace_append hprefix tailTrace_2521142
  have hstable : (prefixWord ++ tailWord_2521142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521142).length < 2 ^ (prefixWord ++ tailWord_2521142).sum := by decide
  have hdescent : baseEnd_2521142 < baseStart_2521142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521155 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3]
def baseStart_2521155 : Nat := 118140960795 + 2521155 * 2 ^ 59
def prefixEnd_2521155 : Nat := 4983230072969 + 3 ^ 40 * 2521155 * 2
def baseEnd_2521155 : Nat := 1294564319486188703167925

theorem tailTrace_2521155 : CollatzResearch.WordTrace tailWord_2521155 prefixEnd_2521155 1294564319486188703167925 := by
  unfold tailWord_2521155
  simp only [CollatzResearch.WordTrace]
  refine ⟨91954077181293488838964919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61302718120862325892643279 91954077181293488838964919)
  ·
    refine ⟨137931115771940233258447379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91954077181293488838964919 137931115771940233258447379)
    ·
      refine ⟨206896673657910349887671069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137931115771940233258447379 206896673657910349887671069)
      ·
        refine ⟨77586252621716381207876651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206896673657910349887671069 77586252621716381207876651)
        ·
          refine ⟨116379378932574571811814977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77586252621716381207876651 116379378932574571811814977)
          ·
            refine ⟨87284534199430928858861233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116379378932574571811814977 87284534199430928858861233)
            ·
              refine ⟨65463400649573196644145925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87284534199430928858861233 65463400649573196644145925)
              ·
                refine ⟨12274387621794974370777361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65463400649573196644145925 12274387621794974370777361)
                ·
                  refine ⟨9205790716346230778083021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12274387621794974370777361 9205790716346230778083021)
                  ·
                    refine ⟨3452171518629836541781133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9205790716346230778083021 3452171518629836541781133)
                    ·
                      refine ⟨1294564319486188703167925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452171518629836541781133 1294564319486188703167925)
                      ·
                        rfl

theorem cell23_2521155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_2521155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521155 prefixEnd_2521155 := by exact prefixLift 2521155
  have htrace : WordTrace (prefixWord ++ tailWord_2521155) baseStart_2521155 baseEnd_2521155 := by
    simpa [prefixWord, tailWord_2521155, baseEnd_2521155] using wordTrace_append hprefix tailTrace_2521155
  have hstable : (prefixWord ++ tailWord_2521155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521155).length < 2 ^ (prefixWord ++ tailWord_2521155).sum := by decide
  have hdescent : baseEnd_2521155 < baseStart_2521155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521173 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2521173 : Nat := 118140960795 + 2521173 * 2 ^ 59
def prefixEnd_2521173 : Nat := 4983230072969 + 3 ^ 40 * 2521173 * 2
def baseEnd_2521173 : Nat := 1294573562137969632742843

theorem tailTrace_2521173 : CollatzResearch.WordTrace tailWord_2521173 prefixEnd_2521173 1294573562137969632742843 := by
  unfold tailWord_2521173
  simp only [CollatzResearch.WordTrace]
  refine ⟨91954733695228277913120173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61303155796818851942080115 91954733695228277913120173)
  ·
    refine ⟨34483025135710604217420065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91954733695228277913120173 34483025135710604217420065)
    ·
      refine ⟨25862268851782953163065049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34483025135710604217420065 25862268851782953163065049)
      ·
        refine ⟨19396701638837214872298787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25862268851782953163065049 19396701638837214872298787)
        ·
          refine ⟨29095052458255822308448181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19396701638837214872298787 29095052458255822308448181)
          ·
            refine ⟨2727661167961483341417017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29095052458255822308448181 2727661167961483341417017)
            ·
              refine ⟨2045745875971112506062763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2727661167961483341417017 2045745875971112506062763)
              ·
                refine ⟨3068618813956668759094145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045745875971112506062763 3068618813956668759094145)
                ·
                  refine ⟨2301464110467501569320609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068618813956668759094145 2301464110467501569320609)
                  ·
                    refine ⟨1726098082850626176990457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2301464110467501569320609 1726098082850626176990457)
                    ·
                      refine ⟨1294573562137969632742843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726098082850626176990457 1294573562137969632742843)
                      ·
                        rfl

theorem cell23_2521173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2521173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521173 prefixEnd_2521173 := by exact prefixLift 2521173
  have htrace : WordTrace (prefixWord ++ tailWord_2521173) baseStart_2521173 baseEnd_2521173 := by
    simpa [prefixWord, tailWord_2521173, baseEnd_2521173] using wordTrace_append hprefix tailTrace_2521173
  have hstable : (prefixWord ++ tailWord_2521173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521173).length < 2 ^ (prefixWord ++ tailWord_2521173).sum := by decide
  have hdescent : baseEnd_2521173 < baseStart_2521173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521212 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2521212 : Nat := 118140960795 + 2521212 * 2 ^ 59
def prefixEnd_2521212 : Nat := 4983230072969 + 3 ^ 40 * 2521212 * 2
def baseEnd_2521212 : Nat := 1294593587883494980155163

theorem tailTrace_2521212 : CollatzResearch.WordTrace tailWord_2521212 prefixEnd_2521212 1294593587883494980155163 := by
  unfold tailWord_2521212
  simp only [CollatzResearch.WordTrace]
  refine ⟨45978078071043493786894945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61304104094724658382526593 45978078071043493786894945)
  ·
    refine ⟨34483558553282620340171209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45978078071043493786894945 34483558553282620340171209)
    ·
      refine ⟨25862668914961965255128407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34483558553282620340171209 25862668914961965255128407)
      ·
        refine ⟨38794003372442947882692611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25862668914961965255128407 38794003372442947882692611)
        ·
          refine ⟨58191005058664421824038917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38794003372442947882692611 58191005058664421824038917)
          ·
            refine ⟨10910813448499579092007297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58191005058664421824038917 10910813448499579092007297)
            ·
              refine ⟨8183110086374684319005473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10910813448499579092007297 8183110086374684319005473)
              ·
                refine ⟨6137332564781013239254105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183110086374684319005473 6137332564781013239254105)
                ·
                  refine ⟨4602999423585759929440579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137332564781013239254105 4602999423585759929440579)
                  ·
                    refine ⟨6904499135378639894160869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602999423585759929440579 6904499135378639894160869)
                    ·
                      refine ⟨1294593587883494980155163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6904499135378639894160869 1294593587883494980155163)
                      ·
                        rfl

theorem cell23_2521212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2521212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521212 prefixEnd_2521212 := by exact prefixLift 2521212
  have htrace : WordTrace (prefixWord ++ tailWord_2521212) baseStart_2521212 baseEnd_2521212 := by
    simpa [prefixWord, tailWord_2521212, baseEnd_2521212] using wordTrace_append hprefix tailTrace_2521212
  have hstable : (prefixWord ++ tailWord_2521212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521212).length < 2 ^ (prefixWord ++ tailWord_2521212).sum := by decide
  have hdescent : baseEnd_2521212 < baseStart_2521212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521239 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 3, 4]
def baseStart_2521239 : Nat := 118140960795 + 2521239 * 2 ^ 59
def prefixEnd_2521239 : Nat := 4983230072969 + 3 ^ 40 * 2521239 * 2
def baseEnd_2521239 : Nat := 431535817287055458172513

theorem tailTrace_2521239 : CollatzResearch.WordTrace tailWord_2521239 prefixEnd_2521239 431535817287055458172513 := by
  unfold tailWord_2521239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91957140912989171185022771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61304760608659447456681847 91957140912989171185022771)
  ·
    refine ⟨137935711369483756777534157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91957140912989171185022771 137935711369483756777534157)
    ·
      refine ⟨51725891763556408791575309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137935711369483756777534157 51725891763556408791575309)
      ·
        refine ⟨19397209411333653296840741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51725891763556408791575309 19397209411333653296840741)
        ·
          refine ⟨3636976764625059993157639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19397209411333653296840741 3636976764625059993157639)
          ·
            refine ⟨5455465146937589989736459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636976764625059993157639 5455465146937589989736459)
            ·
              refine ⟨8183197720406384984604689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455465146937589989736459 8183197720406384984604689)
              ·
                refine ⟨6137398290304788738453517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183197720406384984604689 6137398290304788738453517)
                ·
                  refine ⟨2301524358864295776920069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6137398290304788738453517 2301524358864295776920069)
                  ·
                    refine ⟨431535817287055458172513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2301524358864295776920069 431535817287055458172513)
                    ·
                      rfl

theorem cell23_2521239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_2521239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521239 prefixEnd_2521239 := by exact prefixLift 2521239
  have htrace : WordTrace (prefixWord ++ tailWord_2521239) baseStart_2521239 baseEnd_2521239 := by
    simpa [prefixWord, tailWord_2521239, baseEnd_2521239] using wordTrace_append hprefix tailTrace_2521239
  have hstable : (prefixWord ++ tailWord_2521239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521239).length < 2 ^ (prefixWord ++ tailWord_2521239).sum := by decide
  have hdescent : baseEnd_2521239 < baseStart_2521239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521249 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2521249 : Nat := 118140960795 + 2521249 * 2 ^ 59
def prefixEnd_2521249 : Nat := 4983230072969 + 3 ^ 40 * 2521249 * 2
def baseEnd_2521249 : Nat := 1294612586667711335392493

theorem tailTrace_2521249 : CollatzResearch.WordTrace tailWord_2521249 prefixEnd_2521249 1294612586667711335392493 := by
  unfold tailWord_2521249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91957505642952942892886801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61305003761968628595257867 91957505642952942892886801)
  ·
    refine ⟨68968129232214707169665101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91957505642952942892886801 68968129232214707169665101)
    ·
      refine ⟨25863048462080515188624413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68968129232214707169665101 25863048462080515188624413)
      ·
        refine ⟨9698643173280193195734155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25863048462080515188624413 9698643173280193195734155)
        ·
          refine ⟨14547964759920289793601233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9698643173280193195734155 14547964759920289793601233)
          ·
            refine ⟨10910973569940217345200925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14547964759920289793601233 10910973569940217345200925)
            ·
              refine ⟨4091615088727581504450347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10910973569940217345200925 4091615088727581504450347)
              ·
                refine ⟨6137422633091372256675521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091615088727581504450347 6137422633091372256675521)
                ·
                  refine ⟨4603066974818529192506641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137422633091372256675521 4603066974818529192506641)
                  ·
                    refine ⟨3452300231113896894379981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603066974818529192506641 3452300231113896894379981)
                    ·
                      refine ⟨1294612586667711335392493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452300231113896894379981 1294612586667711335392493)
                      ·
                        rfl

theorem cell23_2521249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2521249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521249 prefixEnd_2521249 := by exact prefixLift 2521249
  have htrace : WordTrace (prefixWord ++ tailWord_2521249) baseStart_2521249 baseEnd_2521249 := by
    simpa [prefixWord, tailWord_2521249, baseEnd_2521249] using wordTrace_append hprefix tailTrace_2521249
  have hstable : (prefixWord ++ tailWord_2521249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521249).length < 2 ^ (prefixWord ++ tailWord_2521249).sum := by decide
  have hdescent : baseEnd_2521249 < baseStart_2521249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521269 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 8]
def baseStart_2521269 : Nat := 118140960795 + 2521269 * 2 ^ 59
def prefixEnd_2521269 : Nat := 4983230072969 + 3 ^ 40 * 2521269 * 2
def baseEnd_2521269 : Nat := 143846984031200139682489

theorem tailTrace_2521269 : CollatzResearch.WordTrace tailWord_2521269 prefixEnd_2521269 143846984031200139682489 := by
  unfold tailWord_2521269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91958235102880486308614861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61305490068586990872409907 91958235102880486308614861)
  ·
    refine ⟨34484338163580182365730573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91958235102880486308614861 34484338163580182365730573)
    ·
      refine ⟨12931626811342568387148965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34484338163580182365730573 12931626811342568387148965)
      ·
        refine ⟨2424680027126731572590431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12931626811342568387148965 2424680027126731572590431)
        ·
          refine ⟨3637020040690097358885647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424680027126731572590431 3637020040690097358885647)
          ·
            refine ⟨5455530061035146038328471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637020040690097358885647 5455530061035146038328471)
            ·
              refine ⟨8183295091552719057492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455530061035146038328471 8183295091552719057492707)
              ·
                refine ⟨12274942637329078586239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8183295091552719057492707 12274942637329078586239061)
                ·
                  refine ⟨143846984031200139682489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12274942637329078586239061 143846984031200139682489)
                  ·
                    rfl

theorem cell23_2521269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_2521269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521269 prefixEnd_2521269 := by exact prefixLift 2521269
  have htrace : WordTrace (prefixWord ++ tailWord_2521269) baseStart_2521269 baseEnd_2521269 := by
    simpa [prefixWord, tailWord_2521269, baseEnd_2521269] using wordTrace_append hprefix tailTrace_2521269
  have hstable : (prefixWord ++ tailWord_2521269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521269).length < 2 ^ (prefixWord ++ tailWord_2521269).sum := by decide
  have hdescent : baseEnd_2521269 < baseStart_2521269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521312 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_2521312 : Nat := 118140960795 + 2521312 * 2 ^ 59
def prefixEnd_2521312 : Nat := 4983230072969 + 3 ^ 40 * 2521312 * 2
def baseEnd_2521312 : Nat := 431548311982981529634901

theorem tailTrace_2521312 : CollatzResearch.WordTrace tailWord_2521312 prefixEnd_2521312 431548311982981529634901 := by
  unfold tailWord_2521312
  simp only [CollatzResearch.WordTrace]
  refine ⟨45979901720862352326215095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61306535627816469768286793 45979901720862352326215095)
  ·
    refine ⟨68969852581293528489322643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45979901720862352326215095 68969852581293528489322643)
    ·
      refine ⟨103454778871940292733983965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68969852581293528489322643 103454778871940292733983965)
      ·
        refine ⟨38795542076977609775243987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103454778871940292733983965 38795542076977609775243987)
        ·
          refine ⟨58193313115466414662865981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38795542076977609775243987 58193313115466414662865981)
          ·
            refine ⟨21822492418299905498574743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58193313115466414662865981 21822492418299905498574743)
            ·
              refine ⟨32733738627449858247862115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21822492418299905498574743 32733738627449858247862115)
              ·
                refine ⟨49100607941174787371793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32733738627449858247862115 49100607941174787371793173)
                ·
                  refine ⟨2301590997242568158052805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49100607941174787371793173 2301590997242568158052805)
                  ·
                    refine ⟨431548311982981529634901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2301590997242568158052805 431548311982981529634901)
                    ·
                      rfl

theorem cell23_2521312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_2521312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521312 prefixEnd_2521312 := by exact prefixLift 2521312
  have htrace : WordTrace (prefixWord ++ tailWord_2521312) baseStart_2521312 baseEnd_2521312 := by
    simpa [prefixWord, tailWord_2521312, baseEnd_2521312] using wordTrace_append hprefix tailTrace_2521312
  have hstable : (prefixWord ++ tailWord_2521312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521312).length < 2 ^ (prefixWord ++ tailWord_2521312).sum := by decide
  have hdescent : baseEnd_2521312 < baseStart_2521312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521330 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2521330 : Nat := 118140960795 + 2521330 * 2 ^ 59
def prefixEnd_2521330 : Nat := 4983230072969 + 3 ^ 40 * 2521330 * 2
def baseEnd_2521330 : Nat := 1294654178600725518479621

theorem tailTrace_2521330 : CollatzResearch.WordTrace tailWord_2521330 prefixEnd_2521330 1294654178600725518479621 := by
  unfold tailWord_2521330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990114988914873431646361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61306973303772995817723629 22990114988914873431646361)
  ·
    refine ⟨17242586241686155073734771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22990114988914873431646361 17242586241686155073734771)
    ·
      refine ⟨25863879362529232610602157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17242586241686155073734771 25863879362529232610602157)
      ·
        refine ⟨9698954760948462228975809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25863879362529232610602157 9698954760948462228975809)
        ·
          refine ⟨7274216070711346671731857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9698954760948462228975809 7274216070711346671731857)
          ·
            refine ⟨5455662053033510003798893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274216070711346671731857 5455662053033510003798893)
            ·
              refine ⟨2045873269887566251424585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5455662053033510003798893 2045873269887566251424585)
              ·
                refine ⟨1534404952415674688568439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045873269887566251424585 1534404952415674688568439)
                ·
                  refine ⟨2301607428623512032852659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534404952415674688568439 2301607428623512032852659)
                  ·
                    refine ⟨3452411142935268049278989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301607428623512032852659 3452411142935268049278989)
                    ·
                      refine ⟨1294654178600725518479621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452411142935268049278989 1294654178600725518479621)
                      ·
                        rfl

theorem cell23_2521330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2521330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521330 prefixEnd_2521330 := by exact prefixLift 2521330
  have htrace : WordTrace (prefixWord ++ tailWord_2521330) baseStart_2521330 baseEnd_2521330 := by
    simpa [prefixWord, tailWord_2521330, baseEnd_2521330] using wordTrace_append hprefix tailTrace_2521330
  have hstable : (prefixWord ++ tailWord_2521330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521330).length < 2 ^ (prefixWord ++ tailWord_2521330).sum := by decide
  have hdescent : baseEnd_2521330 < baseStart_2521330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521335 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2521335 : Nat := 118140960795 + 2521335 * 2 ^ 59
def prefixEnd_2521335 : Nat := 4983230072969 + 3 ^ 40 * 2521335 * 2
def baseEnd_2521335 : Nat := 1294656746003997998917097

theorem tailTrace_2521335 : CollatzResearch.WordTrace tailWord_2521335 prefixEnd_2521335 1294656746003997998917097 := by
  unfold tailWord_2521335
  simp only [CollatzResearch.WordTrace]
  refine ⟨91960642320641379580517459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61307094880427586387011639 91960642320641379580517459)
  ·
    refine ⟨137940963480962069370776189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91960642320641379580517459 137940963480962069370776189)
    ·
      refine ⟨51727861305360776014041071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137940963480962069370776189 51727861305360776014041071)
      ·
        refine ⟨77591791958041164021061607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51727861305360776014041071 77591791958041164021061607)
        ·
          refine ⟨116387687937061746031592411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77591791958041164021061607 116387687937061746031592411)
          ·
            refine ⟨174581531905592619047388617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116387687937061746031592411 174581531905592619047388617)
            ·
              refine ⟨130936148929194464285541463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174581531905592619047388617 130936148929194464285541463)
              ·
                refine ⟨196404223393791696428312195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130936148929194464285541463 196404223393791696428312195)
                ·
                  refine ⟨294606335090687544642468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196404223393791696428312195 294606335090687544642468293)
                  ·
                    refine ⟨55238687829503914620462805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294606335090687544642468293 55238687829503914620462805)
                    ·
                      refine ⟨1294656746003997998917097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55238687829503914620462805 1294656746003997998917097)
                      ·
                        rfl

theorem cell23_2521335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2521335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521335 prefixEnd_2521335 := by exact prefixLift 2521335
  have htrace : WordTrace (prefixWord ++ tailWord_2521335) baseStart_2521335 baseEnd_2521335 := by
    simpa [prefixWord, tailWord_2521335, baseEnd_2521335] using wordTrace_append hprefix tailTrace_2521335
  have hstable : (prefixWord ++ tailWord_2521335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521335).length < 2 ^ (prefixWord ++ tailWord_2521335).sum := by decide
  have hdescent : baseEnd_2521335 < baseStart_2521335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521373 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2521373 : Nat := 118140960795 + 2521373 * 2 ^ 59
def prefixEnd_2521373 : Nat := 4983230072969 + 3 ^ 40 * 2521373 * 2
def baseEnd_2521373 : Nat := 1294676258268868850241923

theorem tailTrace_2521373 : CollatzResearch.WordTrace tailWord_2521373 prefixEnd_2521373 1294676258268868850241923 := by
  unfold tailWord_2521373
  simp only [CollatzResearch.WordTrace]
  refine ⟨91962028294503712070400773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61308018863002474713600515 91962028294503712070400773)
  ·
    refine ⟨17242880305219446013200145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91962028294503712070400773 17242880305219446013200145)
    ·
      refine ⟨12932160228914584509900109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17242880305219446013200145 12932160228914584509900109)
      ·
        refine ⟨4849560085842969191212541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12932160228914584509900109 4849560085842969191212541)
        ·
          refine ⟨1818585032191113446704703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4849560085842969191212541 1818585032191113446704703)
          ·
            refine ⟨2727877548286670170057055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818585032191113446704703 2727877548286670170057055)
            ·
              refine ⟨4091816322430005255085583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727877548286670170057055 4091816322430005255085583)
              ·
                refine ⟨6137724483645007882628375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091816322430005255085583 6137724483645007882628375)
                ·
                  refine ⟨9206586725467511823942563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137724483645007882628375 9206586725467511823942563)
                  ·
                    refine ⟨13809880088201267735913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9206586725467511823942563 13809880088201267735913845)
                    ·
                      refine ⟨1294676258268868850241923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13809880088201267735913845 1294676258268868850241923)
                      ·
                        rfl

theorem cell23_2521373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2521373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521373 prefixEnd_2521373 := by exact prefixLift 2521373
  have htrace : WordTrace (prefixWord ++ tailWord_2521373) baseStart_2521373 baseEnd_2521373 := by
    simpa [prefixWord, tailWord_2521373, baseEnd_2521373] using wordTrace_append hprefix tailTrace_2521373
  have hstable : (prefixWord ++ tailWord_2521373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521373).length < 2 ^ (prefixWord ++ tailWord_2521373).sum := by decide
  have hdescent : baseEnd_2521373 < baseStart_2521373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521402 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_2521402 : Nat := 118140960795 + 2521402 * 2 ^ 59
def prefixEnd_2521402 : Nat := 4983230072969 + 3 ^ 40 * 2521402 * 2
def baseEnd_2521402 : Nat := 431563716402616412259763

theorem tailTrace_2521402 : CollatzResearch.WordTrace tailWord_2521402 prefixEnd_2521402 431563716402616412259763 := by
  unfold tailWord_2521402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990771502849662505801615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61308724007599100015470973 22990771502849662505801615)
  ·
    refine ⟨34486157254274493758702423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22990771502849662505801615 34486157254274493758702423)
    ·
      refine ⟨51729235881411740638053635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34486157254274493758702423 51729235881411740638053635)
      ·
        refine ⟨77593853822117610957080453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51729235881411740638053635 77593853822117610957080453)
        ·
          refine ⟨14548847591647052054452585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77593853822117610957080453 14548847591647052054452585)
          ·
            refine ⟨10911635693735289040839439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548847591647052054452585 10911635693735289040839439)
            ·
              refine ⟨16367453540602933561259159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10911635693735289040839439 16367453540602933561259159)
              ·
                refine ⟨24551180310904400341888739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16367453540602933561259159 24551180310904400341888739)
                ·
                  refine ⟨36826770466356600512833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24551180310904400341888739 36826770466356600512833109)
                  ·
                    refine ⟨431563716402616412259763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36826770466356600512833109 431563716402616412259763)
                    ·
                      rfl

theorem cell23_2521402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_2521402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521402 prefixEnd_2521402 := by exact prefixLift 2521402
  have htrace : WordTrace (prefixWord ++ tailWord_2521402) baseStart_2521402 baseEnd_2521402 := by
    simpa [prefixWord, tailWord_2521402, baseEnd_2521402] using wordTrace_append hprefix tailTrace_2521402
  have hstable : (prefixWord ++ tailWord_2521402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521402).length < 2 ^ (prefixWord ++ tailWord_2521402).sum := by decide
  have hdescent : baseEnd_2521402 < baseStart_2521402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521426 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_2521426 : Nat := 118140960795 + 2521426 * 2 ^ 59
def prefixEnd_2521426 : Nat := 4983230072969 + 3 ^ 40 * 2521426 * 2
def baseEnd_2521426 : Nat := 1294703472743557142879179

theorem tailTrace_2521426 : CollatzResearch.WordTrace tailWord_2521426 prefixEnd_2521426 1294703472743557142879179 := by
  unfold tailWord_2521426
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990990340827925530520033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61309307575541134748053421 22990990340827925530520033)
  ·
    refine ⟨17243242755620944147890025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22990990340827925530520033 17243242755620944147890025)
    ·
      refine ⟨12932432066715708110917519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17243242755620944147890025 12932432066715708110917519)
      ·
        refine ⟨19398648100073562166376279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932432066715708110917519 19398648100073562166376279)
        ·
          refine ⟨29097972150110343249564419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398648100073562166376279 29097972150110343249564419)
          ·
            refine ⟨43646958225165514874346629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29097972150110343249564419 43646958225165514874346629)
            ·
              refine ⟨8183804667218534038939993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43646958225165514874346629 8183804667218534038939993)
              ·
                refine ⟨6137853500413900529204995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183804667218534038939993 6137853500413900529204995)
                ·
                  refine ⟨9206780250620850793807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137853500413900529204995 9206780250620850793807493)
                  ·
                    refine ⟨1726271296991409523838905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9206780250620850793807493 1726271296991409523838905)
                    ·
                      refine ⟨1294703472743557142879179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726271296991409523838905 1294703472743557142879179)
                      ·
                        rfl

theorem cell23_2521426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_2521426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521426 prefixEnd_2521426 := by exact prefixLift 2521426
  have htrace : WordTrace (prefixWord ++ tailWord_2521426) baseStart_2521426 baseEnd_2521426 := by
    simpa [prefixWord, tailWord_2521426, baseEnd_2521426] using wordTrace_append hprefix tailTrace_2521426
  have hstable : (prefixWord ++ tailWord_2521426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521426).length < 2 ^ (prefixWord ++ tailWord_2521426).sum := by decide
  have hdescent : baseEnd_2521426 < baseStart_2521426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521449 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 5]
def baseStart_2521449 : Nat := 118140960795 + 2521449 * 2 ^ 59
def prefixEnd_2521449 : Nat := 4983230072969 + 3 ^ 40 * 2521449 * 2
def baseEnd_2521449 : Nat := 143857253644290061432397

theorem tailTrace_2521449 : CollatzResearch.WordTrace tailWord_2521449 prefixEnd_2521449 143857253644290061432397 := by
  unfold tailWord_2521449
  simp only [CollatzResearch.WordTrace]
  refine ⟨91964800242228377050167401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61309866828152251366778267 91964800242228377050167401)
  ·
    refine ⟨68973600181671282787625551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91964800242228377050167401 68973600181671282787625551)
    ·
      refine ⟨103460400272506924181438327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68973600181671282787625551 103460400272506924181438327)
      ·
        refine ⟨155190600408760386272157491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103460400272506924181438327 155190600408760386272157491)
        ·
          refine ⟨232785900613140579408236237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155190600408760386272157491 232785900613140579408236237)
          ·
            refine ⟨87294712729927717278088589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232785900613140579408236237 87294712729927717278088589)
            ·
              refine ⟨32735517273722893979283221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87294712729927717278088589 32735517273722893979283221)
              ·
                refine ⟨1534477372205760655278901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32735517273722893979283221 1534477372205760655278901)
                ·
                  refine ⟨143857253644290061432397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1534477372205760655278901 143857253644290061432397)
                  ·
                    rfl

theorem cell23_2521449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 5].length) (baseStart_2521449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521449 prefixEnd_2521449 := by exact prefixLift 2521449
  have htrace : WordTrace (prefixWord ++ tailWord_2521449) baseStart_2521449 baseEnd_2521449 := by
    simpa [prefixWord, tailWord_2521449, baseEnd_2521449] using wordTrace_append hprefix tailTrace_2521449
  have hstable : (prefixWord ++ tailWord_2521449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521449).length < 2 ^ (prefixWord ++ tailWord_2521449).sum := by decide
  have hdescent : baseEnd_2521449 < baseStart_2521449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521472 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2521472 : Nat := 118140960795 + 2521472 * 2 ^ 59
def prefixEnd_2521472 : Nat := 4983230072969 + 3 ^ 40 * 2521472 * 2
def baseEnd_2521472 : Nat := 1294727092853663962903967

theorem tailTrace_2521472 : CollatzResearch.WordTrace tailWord_2521472 prefixEnd_2521472 1294727092853663962903967 := by
  unfold tailWord_2521472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45982819560572525989127335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61310426080763367985503113 45982819560572525989127335)
  ·
    refine ⟨68974229340858788983691003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45982819560572525989127335 68974229340858788983691003)
    ·
      refine ⟨103461344011288183475536505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68974229340858788983691003 103461344011288183475536505)
      ·
        refine ⟨77596008008466137606652379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103461344011288183475536505 77596008008466137606652379)
        ·
          refine ⟨116394012012699206409978569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77596008008466137606652379 116394012012699206409978569)
          ·
            refine ⟨87295509009524404807483927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116394012012699206409978569 87295509009524404807483927)
            ·
              refine ⟨130943263514286607211225891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87295509009524404807483927 130943263514286607211225891)
              ·
                refine ⟨196414895271429910816838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130943263514286607211225891 196414895271429910816838837)
                ·
                  refine ⟨18413896431696554139078641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196414895271429910816838837 18413896431696554139078641)
                  ·
                    refine ⟨13810422323772415604308981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18413896431696554139078641 13810422323772415604308981)
                    ·
                      refine ⟨1294727092853663962903967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13810422323772415604308981 1294727092853663962903967)
                      ·
                        rfl

theorem cell23_2521472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2521472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521472 prefixEnd_2521472 := by exact prefixLift 2521472
  have htrace : WordTrace (prefixWord ++ tailWord_2521472) baseStart_2521472 baseEnd_2521472 := by
    simpa [prefixWord, tailWord_2521472, baseEnd_2521472] using wordTrace_append hprefix tailTrace_2521472
  have hstable : (prefixWord ++ tailWord_2521472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521472).length < 2 ^ (prefixWord ++ tailWord_2521472).sum := by decide
  have hdescent : baseEnd_2521472 < baseStart_2521472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521479 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 2, 5]
def baseStart_2521479 : Nat := 118140960795 + 2521479 * 2 ^ 59
def prefixEnd_2521479 : Nat := 4983230072969 + 3 ^ 40 * 2521479 * 2
def baseEnd_2521479 : Nat := 431576895739415145172145

theorem tailTrace_2521479 : CollatzResearch.WordTrace tailWord_2521479 prefixEnd_2521479 431576895739415145172145 := by
  unfold tailWord_2521479
  simp only [CollatzResearch.WordTrace]
  refine ⟨91965894432119692173759491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61310596288079794782506327 91965894432119692173759491)
  ·
    refine ⟨137948841648179538260639237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91965894432119692173759491 137948841648179538260639237)
    ·
      refine ⟨25865407809033663423869857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137948841648179538260639237 25865407809033663423869857)
      ·
        refine ⟨19399055856775247567902393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25865407809033663423869857 19399055856775247567902393)
        ·
          refine ⟨14549291892581435675926795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19399055856775247567902393 14549291892581435675926795)
          ·
            refine ⟨21823937838872153513890193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14549291892581435675926795 21823937838872153513890193)
            ·
              refine ⟨16367953379154115135417645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21823937838872153513890193 16367953379154115135417645)
              ·
                refine ⟨6137982517182793175781617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16367953379154115135417645 6137982517182793175781617)
                ·
                  refine ⟨4603486887887094881836213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137982517182793175781617 4603486887887094881836213)
                  ·
                    refine ⟨431576895739415145172145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4603486887887094881836213 431576895739415145172145)
                    ·
                      rfl

theorem cell23_2521479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_2521479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521479 prefixEnd_2521479 := by exact prefixLift 2521479
  have htrace : WordTrace (prefixWord ++ tailWord_2521479) baseStart_2521479 baseEnd_2521479 := by
    simpa [prefixWord, tailWord_2521479, baseEnd_2521479] using wordTrace_append hprefix tailTrace_2521479
  have hstable : (prefixWord ++ tailWord_2521479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521479).length < 2 ^ (prefixWord ++ tailWord_2521479).sum := by decide
  have hdescent : baseEnd_2521479 < baseStart_2521479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521496 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_2521496 : Nat := 118140960795 + 2521496 * 2 ^ 59
def prefixEnd_2521496 : Nat := 4983230072969 + 3 ^ 40 * 2521496 * 2
def baseEnd_2521496 : Nat := 431579805463123956334619

theorem tailTrace_2521496 : CollatzResearch.WordTrace tailWord_2521496 prefixEnd_2521496 431579805463123956334619 := by
  unfold tailWord_2521496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45983257236529052038564171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61311009648705402718085561 45983257236529052038564171)
  ·
    refine ⟨68974885854793578057846257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45983257236529052038564171 68974885854793578057846257)
    ·
      refine ⟨51731164391095183543384693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68974885854793578057846257 51731164391095183543384693)
      ·
        refine ⟨4849796661665173457192315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51731164391095183543384693 4849796661665173457192315)
        ·
          refine ⟨7274694992497760185788473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849796661665173457192315 7274694992497760185788473)
          ·
            refine ⟨5456021244373320139341355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274694992497760185788473 5456021244373320139341355)
            ·
              refine ⟨8184031866559980209012033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456021244373320139341355 8184031866559980209012033)
              ·
                refine ⟨6138023899919985156759025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8184031866559980209012033 6138023899919985156759025)
                ·
                  refine ⟨4603517924939988867569269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138023899919985156759025 4603517924939988867569269)
                  ·
                    refine ⟨431579805463123956334619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4603517924939988867569269 431579805463123956334619)
                    ·
                      rfl

theorem cell23_2521496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_2521496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521496 prefixEnd_2521496 := by exact prefixLift 2521496
  have htrace : WordTrace (prefixWord ++ tailWord_2521496) baseStart_2521496 baseEnd_2521496 := by
    simpa [prefixWord, tailWord_2521496, baseEnd_2521496] using wordTrace_append hprefix tailTrace_2521496
  have hstable : (prefixWord ++ tailWord_2521496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521496).length < 2 ^ (prefixWord ++ tailWord_2521496).sum := by decide
  have hdescent : baseEnd_2521496 < baseStart_2521496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 10, 2]
def baseStart_2521499 : Nat := 118140960795 + 2521499 * 2 ^ 59
def prefixEnd_2521499 : Nat := 4983230072969 + 3 ^ 40 * 2521499 * 2
def baseEnd_2521499 : Nat := 1294740956831335357266343

theorem tailTrace_2521499 : CollatzResearch.WordTrace tailWord_2521499 prefixEnd_2521499 1294740956831335357266343 := by
  unfold tailWord_2521499
  simp only [CollatzResearch.WordTrace]
  refine ⟨91966623892047235589487551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61311082594698157059658367 91966623892047235589487551)
  ·
    refine ⟨137949935838070853384231327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91966623892047235589487551 137949935838070853384231327)
    ·
      refine ⟨206924903757106280076346991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137949935838070853384231327 206924903757106280076346991)
      ·
        refine ⟨310387355635659420114520487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206924903757106280076346991 310387355635659420114520487)
        ·
          refine ⟨465581033453489130171780731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310387355635659420114520487 465581033453489130171780731)
          ·
            refine ⟨698371550180233695257671097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465581033453489130171780731 698371550180233695257671097)
            ·
              refine ⟨523778662635175271443253323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698371550180233695257671097 523778662635175271443253323)
              ·
                refine ⟨785667993952762907164879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523778662635175271443253323 785667993952762907164879985)
                ·
                  refine ⟨589250995464572180373659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785667993952762907164879985 589250995464572180373659989)
                  ·
                    refine ⟨1726321275775113809688457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 589250995464572180373659989 1726321275775113809688457)
                    ·
                      refine ⟨1294740956831335357266343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726321275775113809688457 1294740956831335357266343)
                      ·
                        rfl

theorem cell23_2521499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10, 2].length) (baseStart_2521499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521499 prefixEnd_2521499 := by exact prefixLift 2521499
  have htrace : WordTrace (prefixWord ++ tailWord_2521499) baseStart_2521499 baseEnd_2521499 := by
    simpa [prefixWord, tailWord_2521499, baseEnd_2521499] using wordTrace_append hprefix tailTrace_2521499
  have hstable : (prefixWord ++ tailWord_2521499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521499).length < 2 ^ (prefixWord ++ tailWord_2521499).sum := by decide
  have hdescent : baseEnd_2521499 < baseStart_2521499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521556 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2521556 : Nat := 118140960795 + 2521556 * 2 ^ 59
def prefixEnd_2521556 : Nat := 4983230072969 + 3 ^ 40 * 2521556 * 2
def baseEnd_2521556 : Nat := 143863358358737959361509

theorem tailTrace_2521556 : CollatzResearch.WordTrace tailWord_2521556 prefixEnd_2521556 143863358358737959361509 := by
  unfold tailWord_2521556
  simp only [CollatzResearch.WordTrace]
  refine ⟨45984351426420367162156261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61312468568560489549541681 45984351426420367162156261)
  ·
    refine ⟨8622065892453818842904299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45984351426420367162156261 8622065892453818842904299)
    ·
      refine ⟨12933098838680728264356449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622065892453818842904299 12933098838680728264356449)
      ·
        refine ⟨9699824129010546198267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12933098838680728264356449 9699824129010546198267337)
        ·
          refine ⟨7274868096757909648700503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9699824129010546198267337 7274868096757909648700503)
          ·
            refine ⟨10912302145136864473050755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7274868096757909648700503 10912302145136864473050755)
            ·
              refine ⟨16368453217705296709576133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912302145136864473050755 16368453217705296709576133)
              ·
                refine ⟨3069084978319743133045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16368453217705296709576133 3069084978319743133045525)
                ·
                  refine ⟨143863358358737959361509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3069084978319743133045525 143863358358737959361509)
                  ·
                    rfl

theorem cell23_2521556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2521556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521556 prefixEnd_2521556 := by exact prefixLift 2521556
  have htrace : WordTrace (prefixWord ++ tailWord_2521556) baseStart_2521556 baseEnd_2521556 := by
    simpa [prefixWord, tailWord_2521556, baseEnd_2521556] using wordTrace_append hprefix tailTrace_2521556
  have hstable : (prefixWord ++ tailWord_2521556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521556).length < 2 ^ (prefixWord ++ tailWord_2521556).sum := by decide
  have hdescent : baseEnd_2521556 < baseStart_2521556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521569 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2521569 : Nat := 118140960795 + 2521569 * 2 ^ 59
def prefixEnd_2521569 : Nat := 4983230072969 + 3 ^ 40 * 2521569 * 2
def baseEnd_2521569 : Nat := 431592300159050027797007

theorem tailTrace_2521569 : CollatzResearch.WordTrace tailWord_2521569 prefixEnd_2521569 431592300159050027797007 := by
  unfold tailWord_2521569
  simp only [CollatzResearch.WordTrace]
  refine ⟨91969177001793637544535761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61312784667862425029690507 91969177001793637544535761)
  ·
    refine ⟨68976882751345228158401821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91969177001793637544535761 68976882751345228158401821)
    ·
      refine ⟨25866331031754460559400683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68976882751345228158401821 25866331031754460559400683)
      ·
        refine ⟨38799496547631690839101025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25866331031754460559400683 38799496547631690839101025)
        ·
          refine ⟨29099622410723768129325769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38799496547631690839101025 29099622410723768129325769)
          ·
            refine ⟨21824716808042826096994327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29099622410723768129325769 21824716808042826096994327)
            ·
              refine ⟨32737075212064239145491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21824716808042826096994327 32737075212064239145491491)
              ·
                refine ⟨49105612818096358718237237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32737075212064239145491491 49105612818096358718237237)
                ·
                  refine ⟨4603651201696533629834741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49105612818096358718237237 4603651201696533629834741)
                  ·
                    refine ⟨431592300159050027797007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4603651201696533629834741 431592300159050027797007)
                    ·
                      rfl

theorem cell23_2521569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2521569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521569 prefixEnd_2521569 := by exact prefixLift 2521569
  have htrace : WordTrace (prefixWord ++ tailWord_2521569) baseStart_2521569 baseEnd_2521569 := by
    simpa [prefixWord, tailWord_2521569, baseEnd_2521569] using wordTrace_append hprefix tailTrace_2521569
  have hstable : (prefixWord ++ tailWord_2521569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521569).length < 2 ^ (prefixWord ++ tailWord_2521569).sum := by decide
  have hdescent : baseEnd_2521569 < baseStart_2521569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521593 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2521593 : Nat := 118140960795 + 2521593 * 2 ^ 59
def prefixEnd_2521593 : Nat := 4983230072969 + 3 ^ 40 * 2521593 * 2
def baseEnd_2521593 : Nat := 1294789224012857989490911

theorem tailTrace_2521593 : CollatzResearch.WordTrace tailWord_2521593 prefixEnd_2521593 1294789224012857989490911 := by
  unfold tailWord_2521593
  simp only [CollatzResearch.WordTrace]
  refine ⟨91970052353706689643409433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61313368235804459762272955 91970052353706689643409433)
  ·
    refine ⟨68977539265280017232557075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91970052353706689643409433 68977539265280017232557075)
    ·
      refine ⟨103466308897920025848835613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68977539265280017232557075 103466308897920025848835613)
      ·
        refine ⟨38799865836720009693313355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103466308897920025848835613 38799865836720009693313355)
        ·
          refine ⟨58199798755080014539970033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38799865836720009693313355 58199798755080014539970033)
          ·
            refine ⟨43649849066310010904977525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58199798755080014539970033 43649849066310010904977525)
            ·
              refine ⟨4092173349966563522341643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43649849066310010904977525 4092173349966563522341643)
              ·
                refine ⟨6138260024949845283512465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092173349966563522341643 6138260024949845283512465)
                ·
                  refine ⟨4603695018712383962634349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138260024949845283512465 4603695018712383962634349)
                  ·
                    refine ⟨1726385632017143985987881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4603695018712383962634349 1726385632017143985987881)
                    ·
                      refine ⟨1294789224012857989490911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726385632017143985987881 1294789224012857989490911)
                      ·
                        rfl

theorem cell23_2521593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2521593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521593 prefixEnd_2521593 := by exact prefixLift 2521593
  have htrace : WordTrace (prefixWord ++ tailWord_2521593) baseStart_2521593 baseEnd_2521593 := by
    simpa [prefixWord, tailWord_2521593, baseEnd_2521593] using wordTrace_append hprefix tailTrace_2521593
  have hstable : (prefixWord ++ tailWord_2521593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521593).length < 2 ^ (prefixWord ++ tailWord_2521593).sum := by decide
  have hdescent : baseEnd_2521593 < baseStart_2521593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521599 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 6]
def baseStart_2521599 : Nat := 118140960795 + 2521599 * 2 ^ 59
def prefixEnd_2521599 : Nat := 4983230072969 + 3 ^ 40 * 2521599 * 2
def baseEnd_2521599 : Nat := 431597434965594988671961

theorem tailTrace_2521599 : CollatzResearch.WordTrace tailWord_2521599 prefixEnd_2521599 431597434965594988671961 := by
  unfold tailWord_2521599
  simp only [CollatzResearch.WordTrace]
  refine ⟨91970271191684952668127851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61313514127789968445418567 91970271191684952668127851)
  ·
    refine ⟨137955406787527429002191777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91970271191684952668127851 137955406787527429002191777)
    ·
      refine ⟨103466555090645571751643833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137955406787527429002191777 103466555090645571751643833)
      ·
        refine ⟨77599916317984178813732875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103466555090645571751643833 77599916317984178813732875)
        ·
          refine ⟨116399874476976268220599313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77599916317984178813732875 116399874476976268220599313)
          ·
            refine ⟨87299905857732201165449485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116399874476976268220599313 87299905857732201165449485)
            ·
              refine ⟨32737464696649575437043557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87299905857732201165449485 32737464696649575437043557)
              ·
                refine ⟨6138274630621795394445667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32737464696649575437043557 6138274630621795394445667)
                ·
                  refine ⟨9207411945932693091668501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138274630621795394445667 9207411945932693091668501)
                  ·
                    refine ⟨431597434965594988671961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9207411945932693091668501 431597434965594988671961)
                    ·
                      rfl

theorem cell23_2521599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_2521599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521599 prefixEnd_2521599 := by exact prefixLift 2521599
  have htrace : WordTrace (prefixWord ++ tailWord_2521599) baseStart_2521599 baseEnd_2521599 := by
    simpa [prefixWord, tailWord_2521599, baseEnd_2521599] using wordTrace_append hprefix tailTrace_2521599
  have hstable : (prefixWord ++ tailWord_2521599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521599).length < 2 ^ (prefixWord ++ tailWord_2521599).sum := by decide
  have hdescent : baseEnd_2521599 < baseStart_2521599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521619 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_2521619 : Nat := 118140960795 + 2521619 * 2 ^ 59
def prefixEnd_2521619 : Nat := 4983230072969 + 3 ^ 40 * 2521619 * 2
def baseEnd_2521619 : Nat := 1294802574509874887765791

theorem tailTrace_2521619 : CollatzResearch.WordTrace tailWord_2521619 prefixEnd_2521619 1294802574509874887765791 := by
  unfold tailWord_2521619
  simp only [CollatzResearch.WordTrace]
  refine ⟨91971000651612496083855911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61314000434408330722570607 91971000651612496083855911)
  ·
    refine ⟨137956500977418744125783867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91971000651612496083855911 137956500977418744125783867)
    ·
      refine ⟨206934751466128116188675801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137956500977418744125783867 206934751466128116188675801)
      ·
        refine ⟨155201063599596087141506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206934751466128116188675801 155201063599596087141506851)
        ·
          refine ⟨232801595399394130712260277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155201063599596087141506851 232801595399394130712260277)
          ·
            refine ⟨21825149568693199754274401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232801595399394130712260277 21825149568693199754274401)
            ·
              refine ⟨16368862176519899815705801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21825149568693199754274401 16368862176519899815705801)
              ·
                refine ⟨12276646632389924861779351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16368862176519899815705801 12276646632389924861779351)
                ·
                  refine ⟨18414969948584887292669027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12276646632389924861779351 18414969948584887292669027)
                  ·
                    refine ⟨27622454922877330939003541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18414969948584887292669027 27622454922877330939003541)
                    ·
                      refine ⟨1294802574509874887765791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27622454922877330939003541 1294802574509874887765791)
                      ·
                        rfl

theorem cell23_2521619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_2521619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521619 prefixEnd_2521619 := by exact prefixLift 2521619
  have htrace : WordTrace (prefixWord ++ tailWord_2521619) baseStart_2521619 baseEnd_2521619 := by
    simpa [prefixWord, tailWord_2521619, baseEnd_2521619] using wordTrace_append hprefix tailTrace_2521619
  have hstable : (prefixWord ++ tailWord_2521619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521619).length < 2 ^ (prefixWord ++ tailWord_2521619).sum := by decide
  have hdescent : baseEnd_2521619 < baseStart_2521619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521626 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2521626 : Nat := 118140960795 + 2521626 * 2 ^ 59
def prefixEnd_2521626 : Nat := 4983230072969 + 3 ^ 40 * 2521626 * 2
def baseEnd_2521626 : Nat := 1294806168874456360378259

theorem tailTrace_2521626 : CollatzResearch.WordTrace tailWord_2521626 prefixEnd_2521626 1294806168874456360378259 := by
  unfold tailWord_2521626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22992813990646784069840183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61314170641724757519573821 22992813990646784069840183)
  ·
    refine ⟨34489220985970176104760275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22992813990646784069840183 34489220985970176104760275)
    ·
      refine ⟨51733831478955264157140413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34489220985970176104760275 51733831478955264157140413)
      ·
        refine ⟨19400186804608224058927655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51733831478955264157140413 19400186804608224058927655)
        ·
          refine ⟨29100280206912336088391483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19400186804608224058927655 29100280206912336088391483)
          ·
            refine ⟨43650420310368504132587225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29100280206912336088391483 43650420310368504132587225)
            ·
              refine ⟨32737815232776378099440419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43650420310368504132587225 32737815232776378099440419)
              ·
                refine ⟨49106722849164567149160629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32737815232776378099440419 49106722849164567149160629)
                ·
                  refine ⟨4603755267109178170233809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49106722849164567149160629 4603755267109178170233809)
                  ·
                    refine ⟨3452816450331883627675357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603755267109178170233809 3452816450331883627675357)
                    ·
                      refine ⟨1294806168874456360378259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452816450331883627675357 1294806168874456360378259)
                      ·
                        rfl

theorem cell23_2521626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2521626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521626 prefixEnd_2521626 := by exact prefixLift 2521626
  have htrace : WordTrace (prefixWord ++ tailWord_2521626) baseStart_2521626 baseEnd_2521626 := by
    simpa [prefixWord, tailWord_2521626, baseEnd_2521626] using wordTrace_append hprefix tailTrace_2521626
  have hstable : (prefixWord ++ tailWord_2521626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521626).length < 2 ^ (prefixWord ++ tailWord_2521626).sum := by decide
  have hdescent : baseEnd_2521626 < baseStart_2521626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521640 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2521640 : Nat := 118140960795 + 2521640 * 2 ^ 59
def prefixEnd_2521640 : Nat := 4983230072969 + 3 ^ 40 * 2521640 * 2
def baseEnd_2521640 : Nat := 1294813357603619305603195

theorem tailTrace_2521640 : CollatzResearch.WordTrace tailWord_2521640 prefixEnd_2521640 1294813357603619305603195 := by
  unfold tailWord_2521640
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985883292268208335185187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61314511056357611113580249 45985883292268208335185187)
  ·
    refine ⟨68978824938402312502777781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45985883292268208335185187 68978824938402312502777781)
    ·
      refine ⟨6466764837975216797135417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68978824938402312502777781 6466764837975216797135417)
      ·
        refine ⟨4850073628481412597851563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6466764837975216797135417 4850073628481412597851563)
        ·
          refine ⟨7275110442722118896777345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850073628481412597851563 7275110442722118896777345)
          ·
            refine ⟨5456332832041589172583009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7275110442722118896777345 5456332832041589172583009)
            ·
              refine ⟨4092249624031191879437257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5456332832041589172583009 4092249624031191879437257)
              ·
                refine ⟨3069187218023393909577943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092249624031191879437257 3069187218023393909577943)
                ·
                  refine ⟨4603780827035090864366915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069187218023393909577943 4603780827035090864366915)
                  ·
                    refine ⟨6905671240552636296550373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603780827035090864366915 6905671240552636296550373)
                    ·
                      refine ⟨1294813357603619305603195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6905671240552636296550373 1294813357603619305603195)
                      ·
                        rfl

theorem cell23_2521640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2521640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521640 prefixEnd_2521640 := by exact prefixLift 2521640
  have htrace : WordTrace (prefixWord ++ tailWord_2521640) baseStart_2521640 baseEnd_2521640 := by
    simpa [prefixWord, tailWord_2521640, baseEnd_2521640] using wordTrace_append hprefix tailTrace_2521640
  have hstable : (prefixWord ++ tailWord_2521640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521640).length < 2 ^ (prefixWord ++ tailWord_2521640).sum := by decide
  have hdescent : baseEnd_2521640 < baseStart_2521640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521656 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2521656 : Nat := 118140960795 + 2521656 * 2 ^ 59
def prefixEnd_2521656 : Nat := 4983230072969 + 3 ^ 40 * 2521656 * 2
def baseEnd_2521656 : Nat := 1294821573294091243003121

theorem tailTrace_2521656 : CollatzResearch.WordTrace tailWord_2521656 prefixEnd_2521656 1294821573294091243003121 := by
  unfold tailWord_2521656
  simp only [CollatzResearch.WordTrace]
  refine ⟨45986175076239225701476411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61314900101652300935301881 45986175076239225701476411)
  ·
    refine ⟨68979262614358838552214617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45986175076239225701476411 68979262614358838552214617)
    ·
      refine ⟨51734446960769128914160963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68979262614358838552214617 51734446960769128914160963)
      ·
        refine ⟨77601670441153693371241445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51734446960769128914160963 77601670441153693371241445)
        ·
          refine ⟨14550313207716317507107771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77601670441153693371241445 14550313207716317507107771)
          ·
            refine ⟨21825469811574476260661657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14550313207716317507107771 21825469811574476260661657)
            ·
              refine ⟨16369102358680857195496243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21825469811574476260661657 16369102358680857195496243)
              ·
                refine ⟨24553653538021285793244365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16369102358680857195496243 24553653538021285793244365)
                ·
                  refine ⟨9207620076757982172466637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24553653538021285793244365 9207620076757982172466637)
                  ·
                    refine ⟨3452857528784243314674989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9207620076757982172466637 3452857528784243314674989)
                    ·
                      refine ⟨1294821573294091243003121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452857528784243314674989 1294821573294091243003121)
                      ·
                        rfl

theorem cell23_2521656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2521656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521656 prefixEnd_2521656 := by exact prefixLift 2521656
  have htrace : WordTrace (prefixWord ++ tailWord_2521656) baseStart_2521656 baseEnd_2521656 := by
    simpa [prefixWord, tailWord_2521656, baseEnd_2521656] using wordTrace_append hprefix tailTrace_2521656
  have hstable : (prefixWord ++ tailWord_2521656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521656).length < 2 ^ (prefixWord ++ tailWord_2521656).sum := by decide
  have hdescent : baseEnd_2521656 < baseStart_2521656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521668 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2521668 : Nat := 118140960795 + 2521668 * 2 ^ 59
def prefixEnd_2521668 : Nat := 4983230072969 + 3 ^ 40 * 2521668 * 2
def baseEnd_2521668 : Nat := 1294827735061945196053067

theorem tailTrace_2521668 : CollatzResearch.WordTrace tailWord_2521668 prefixEnd_2521668 1294827735061945196053067 := by
  unfold tailWord_2521668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45986393914217488726194829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61315191885623318301593105 45986393914217488726194829)
  ·
    refine ⟨17244897717831558272323061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45986393914217488726194829 17244897717831558272323061)
    ·
      refine ⟨1616709161046708588030287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17244897717831558272323061 1616709161046708588030287)
      ·
        refine ⟨2425063741570062882045431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616709161046708588030287 2425063741570062882045431)
        ·
          refine ⟨3637595612355094323068147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425063741570062882045431 3637595612355094323068147)
          ·
            refine ⟨5456393418532641484602221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637595612355094323068147 5456393418532641484602221)
            ·
              refine ⟨2046147531949740556725833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5456393418532641484602221 2046147531949740556725833)
              ·
                refine ⟨1534610648962305417544375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046147531949740556725833 1534610648962305417544375)
                ·
                  refine ⟨2301915973443458126316563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534610648962305417544375 2301915973443458126316563)
                  ·
                    refine ⟨3452873960165187189474845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301915973443458126316563 3452873960165187189474845)
                    ·
                      refine ⟨1294827735061945196053067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452873960165187189474845 1294827735061945196053067)
                      ·
                        rfl

theorem cell23_2521668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2521668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521668 prefixEnd_2521668 := by exact prefixLift 2521668
  have htrace : WordTrace (prefixWord ++ tailWord_2521668) baseStart_2521668 baseEnd_2521668 := by
    simpa [prefixWord, tailWord_2521668, baseEnd_2521668] using wordTrace_append hprefix tailTrace_2521668
  have hstable : (prefixWord ++ tailWord_2521668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521668).length < 2 ^ (prefixWord ++ tailWord_2521668).sum := by decide
  have hdescent : baseEnd_2521668 < baseStart_2521668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521674 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_2521674 : Nat := 118140960795 + 2521674 * 2 ^ 59
def prefixEnd_2521674 : Nat := 4983230072969 + 3 ^ 40 * 2521674 * 2
def baseEnd_2521674 : Nat := 1294830815945872172578039

theorem tailTrace_2521674 : CollatzResearch.WordTrace tailWord_2521674 prefixEnd_2521674 1294830815945872172578039 := by
  unfold tailWord_2521674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22993251666603310119277019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61315337777608826984738717 22993251666603310119277019)
  ·
    refine ⟨34489877499904965178915529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22993251666603310119277019 34489877499904965178915529)
    ·
      refine ⟨25867408124928723884186647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34489877499904965178915529 25867408124928723884186647)
      ·
        refine ⟨38801112187393085826279971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25867408124928723884186647 38801112187393085826279971)
        ·
          refine ⟨58201668281089628739419957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38801112187393085826279971 58201668281089628739419957)
          ·
            refine ⟨5456406401352152694320621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58201668281089628739419957 5456406401352152694320621)
            ·
              refine ⟨2046152400507057260370233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5456406401352152694320621 2046152400507057260370233)
              ·
                refine ⟨1534614300380292945277675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046152400507057260370233 1534614300380292945277675)
                ·
                  refine ⟨2301921450570439417916513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534614300380292945277675 2301921450570439417916513)
                  ·
                    refine ⟨1726441087927829563437385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2301921450570439417916513 1726441087927829563437385)
                    ·
                      refine ⟨1294830815945872172578039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726441087927829563437385 1294830815945872172578039)
                      ·
                        rfl

theorem cell23_2521674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_2521674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521674 prefixEnd_2521674 := by exact prefixLift 2521674
  have htrace : WordTrace (prefixWord ++ tailWord_2521674) baseStart_2521674 baseEnd_2521674 := by
    simpa [prefixWord, tailWord_2521674, baseEnd_2521674] using wordTrace_append hprefix tailTrace_2521674
  have hstable : (prefixWord ++ tailWord_2521674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521674).length < 2 ^ (prefixWord ++ tailWord_2521674).sum := by decide
  have hdescent : baseEnd_2521674 < baseStart_2521674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521694 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2521694 : Nat := 118140960795 + 2521694 * 2 ^ 59
def prefixEnd_2521694 : Nat := 4983230072969 + 3 ^ 40 * 2521694 * 2
def baseEnd_2521694 : Nat := 1294841085558962094327947

theorem tailTrace_2521694 : CollatzResearch.WordTrace tailWord_2521694 prefixEnd_2521694 1294841085558962094327947 := by
  unfold tailWord_2521694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496717015792597986604517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61315824084227189261890757 11496717015792597986604517)
  ·
    refine ⟨2155634440461112122488347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11496717015792597986604517 2155634440461112122488347)
    ·
      refine ⟨3233451660691668183732521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155634440461112122488347 3233451660691668183732521)
      ·
        refine ⟨2425088745518751137799391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3233451660691668183732521 2425088745518751137799391)
        ·
          refine ⟨3637633118278126706699087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425088745518751137799391 3637633118278126706699087)
          ·
            refine ⟨5456449677417190060048631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637633118278126706699087 5456449677417190060048631)
            ·
              refine ⟨8184674516125785090072947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456449677417190060048631 8184674516125785090072947)
              ·
                refine ⟨12277011774188677635109421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8184674516125785090072947 12277011774188677635109421)
                ·
                  refine ⟨4603879415320754113166033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12277011774188677635109421 4603879415320754113166033)
                  ·
                    refine ⟨3452909561490565584874525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603879415320754113166033 3452909561490565584874525)
                    ·
                      refine ⟨1294841085558962094327947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3452909561490565584874525 1294841085558962094327947)
                      ·
                        rfl

theorem cell23_2521694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2521694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521694 prefixEnd_2521694 := by exact prefixLift 2521694
  have htrace : WordTrace (prefixWord ++ tailWord_2521694) baseStart_2521694 baseEnd_2521694 := by
    simpa [prefixWord, tailWord_2521694, baseEnd_2521694] using wordTrace_append hprefix tailTrace_2521694
  have hstable : (prefixWord ++ tailWord_2521694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521694).length < 2 ^ (prefixWord ++ tailWord_2521694).sum := by decide
  have hdescent : baseEnd_2521694 < baseStart_2521694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521798 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2521798 : Nat := 118140960795 + 2521798 * 2 ^ 59
def prefixEnd_2521798 : Nat := 4983230072969 + 3 ^ 40 * 2521798 * 2
def baseEnd_2521798 : Nat := 1294894487547029687427469

theorem tailTrace_2521798 : CollatzResearch.WordTrace tailWord_2521798 prefixEnd_2521798 1294894487547029687427469 := by
  unfold tailWord_2521798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874297791186375301706939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61318352878642673103081365 2874297791186375301706939)
  ·
    refine ⟨4311446686779562952560409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874297791186375301706939 4311446686779562952560409)
    ·
      refine ⟨3233585015084672214420307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4311446686779562952560409 3233585015084672214420307)
      ·
        refine ⟨4850377522627008321630461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233585015084672214420307 4850377522627008321630461)
        ·
          refine ⟨1818891570985128120611423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4850377522627008321630461 1818891570985128120611423)
          ·
            refine ⟨2728337356477692180917135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818891570985128120611423 2728337356477692180917135)
            ·
              refine ⟨4092506034716538271375703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728337356477692180917135 4092506034716538271375703)
              ·
                refine ⟨6138759052074807407063555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092506034716538271375703 6138759052074807407063555)
                ·
                  refine ⟨9208138578112211110595333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138759052074807407063555 9208138578112211110595333)
                  ·
                    refine ⟨1726525983396039583236625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9208138578112211110595333 1726525983396039583236625)
                    ·
                      refine ⟨1294894487547029687427469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726525983396039583236625 1294894487547029687427469)
                      ·
                        rfl

theorem cell23_2521798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2521798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521798 prefixEnd_2521798 := by exact prefixLift 2521798
  have htrace : WordTrace (prefixWord ++ tailWord_2521798) baseStart_2521798 baseEnd_2521798 := by
    simpa [prefixWord, tailWord_2521798, baseEnd_2521798] using wordTrace_append hprefix tailTrace_2521798
  have hstable : (prefixWord ++ tailWord_2521798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521798).length < 2 ^ (prefixWord ++ tailWord_2521798).sum := by decide
  have hdescent : baseEnd_2521798 < baseStart_2521798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521820 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2521820 : Nat := 118140960795 + 2521820 * 2 ^ 59
def prefixEnd_2521820 : Nat := 4983230072969 + 3 ^ 40 * 2521820 * 2
def baseEnd_2521820 : Nat := 1294905784121428601352367

theorem tailTrace_2521820 : CollatzResearch.WordTrace tailWord_2521820 prefixEnd_2521820 1294905784121428601352367 := by
  unfold tailWord_2521820
  simp only [CollatzResearch.WordTrace]
  refine ⟨45989165861942153705961457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61318887815922871607948609 45989165861942153705961457)
  ·
    refine ⟨34491874396456615279471093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45989165861942153705961457 34491874396456615279471093)
    ·
      refine ⟨3233613224667807682450415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34491874396456615279471093 3233613224667807682450415)
      ·
        refine ⟨4850419837001711523675623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233613224667807682450415 4850419837001711523675623)
        ·
          refine ⟨7275629755502567285513435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850419837001711523675623 7275629755502567285513435)
          ·
            refine ⟨10913444633253850928270153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275629755502567285513435 10913444633253850928270153)
            ·
              refine ⟨8185083474940388196202615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10913444633253850928270153 8185083474940388196202615)
              ·
                refine ⟨12277625212410582294303923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185083474940388196202615 12277625212410582294303923)
                ·
                  refine ⟨18416437818615873441455885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12277625212410582294303923 18416437818615873441455885)
                  ·
                    refine ⟨6906164181980952540545957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18416437818615873441455885 6906164181980952540545957)
                    ·
                      refine ⟨1294905784121428601352367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6906164181980952540545957 1294905784121428601352367)
                      ·
                        rfl

theorem cell23_2521820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2521820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521820 prefixEnd_2521820 := by exact prefixLift 2521820
  have htrace : WordTrace (prefixWord ++ tailWord_2521820) baseStart_2521820 baseEnd_2521820 := by
    simpa [prefixWord, tailWord_2521820, baseEnd_2521820] using wordTrace_append hprefix tailTrace_2521820
  have hstable : (prefixWord ++ tailWord_2521820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521820).length < 2 ^ (prefixWord ++ tailWord_2521820).sum := by decide
  have hdescent : baseEnd_2521820 < baseStart_2521820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521823 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_2521823 : Nat := 118140960795 + 2521823 * 2 ^ 59
def prefixEnd_2521823 : Nat := 4983230072969 + 3 ^ 40 * 2521823 * 2
def baseEnd_2521823 : Nat := 1294907324563392089614853

theorem tailTrace_2521823 : CollatzResearch.WordTrace tailWord_2521823 prefixEnd_2521823 1294907324563392089614853 := by
  unfold tailWord_2521823
  simp only [CollatzResearch.WordTrace]
  refine ⟨91978441142873438924282123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61318960761915625949521415 91978441142873438924282123)
  ·
    refine ⟨137967661714310158386423185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91978441142873438924282123 137967661714310158386423185)
    ·
      refine ⟨103475746285732618789817389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137967661714310158386423185 103475746285732618789817389)
      ·
        refine ⟨38803404857149732046181521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103475746285732618789817389 38803404857149732046181521)
        ·
          refine ⟨29102553642862299034636141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38803404857149732046181521 29102553642862299034636141)
          ·
            refine ⟨10913457616073362137988553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29102553642862299034636141 10913457616073362137988553)
            ·
              refine ⟨8185093212055021603491415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10913457616073362137988553 8185093212055021603491415)
              ·
                refine ⟨12277639818082532405237123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185093212055021603491415 12277639818082532405237123)
                ·
                  refine ⟨18416459727123798607855685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12277639818082532405237123 18416459727123798607855685)
                  ·
                    refine ⟨3453086198835712238972941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18416459727123798607855685 3453086198835712238972941)
                    ·
                      refine ⟨1294907324563392089614853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453086198835712238972941 1294907324563392089614853)
                      ·
                        rfl

theorem cell23_2521823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_2521823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521823 prefixEnd_2521823 := by exact prefixLift 2521823
  have htrace : WordTrace (prefixWord ++ tailWord_2521823) baseStart_2521823 baseEnd_2521823 := by
    simpa [prefixWord, tailWord_2521823, baseEnd_2521823] using wordTrace_append hprefix tailTrace_2521823
  have hstable : (prefixWord ++ tailWord_2521823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521823).length < 2 ^ (prefixWord ++ tailWord_2521823).sum := by decide
  have hdescent : baseEnd_2521823 < baseStart_2521823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521870 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2521870 : Nat := 118140960795 + 2521870 * 2 ^ 59
def prefixEnd_2521870 : Nat := 4983230072969 + 3 ^ 40 * 2521870 * 2
def baseEnd_2521870 : Nat := 1294931458154153405727137

theorem tailTrace_2521870 : CollatzResearch.WordTrace tailWord_2521870 prefixEnd_2521870 1294931458154153405727137 := by
  unfold tailWord_2521870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497519421712895743905383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61320103582468777300828709 11497519421712895743905383)
  ·
    refine ⟨17246279132569343615858075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11497519421712895743905383 17246279132569343615858075)
    ·
      refine ⟨25869418698854015423787113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17246279132569343615858075 25869418698854015423787113)
      ·
        refine ⟨19402064024140511567840335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25869418698854015423787113 19402064024140511567840335)
        ·
          refine ⟨29103096036210767351760503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19402064024140511567840335 29103096036210767351760503)
          ·
            refine ⟨43654644054316151027640755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29103096036210767351760503 43654644054316151027640755)
            ·
              refine ⟨65481966081474226541461133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43654644054316151027640755 65481966081474226541461133)
              ·
                refine ⟨24555737280552834953047925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65481966081474226541461133 24555737280552834953047925)
                ·
                  refine ⟨2302100370051828276848243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24555737280552834953047925 2302100370051828276848243)
                  ·
                    refine ⟨3453150555077742415272365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302100370051828276848243 3453150555077742415272365)
                    ·
                      refine ⟨1294931458154153405727137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453150555077742415272365 1294931458154153405727137)
                      ·
                        rfl

theorem cell23_2521870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2521870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521870 prefixEnd_2521870 := by exact prefixLift 2521870
  have htrace : WordTrace (prefixWord ++ tailWord_2521870) baseStart_2521870 baseEnd_2521870 := by
    simpa [prefixWord, tailWord_2521870, baseEnd_2521870] using wordTrace_append hprefix tailTrace_2521870
  have hstable : (prefixWord ++ tailWord_2521870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521870).length < 2 ^ (prefixWord ++ tailWord_2521870).sum := by decide
  have hdescent : baseEnd_2521870 < baseStart_2521870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521874 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2521874 : Nat := 118140960795 + 2521874 * 2 ^ 59
def prefixEnd_2521874 : Nat := 4983230072969 + 3 ^ 40 * 2521874 * 2
def baseEnd_2521874 : Nat := 1294933512076771390077119

theorem tailTrace_2521874 : CollatzResearch.WordTrace tailWord_2521874 prefixEnd_2521874 1294933512076771390077119 := by
  unfold tailWord_2521874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22995075316422168658597169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61320200843792449756259117 22995075316422168658597169)
  ·
    refine ⟨17246306487316626493947877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22995075316422168658597169 17246306487316626493947877)
    ·
      refine ⟨3233682466371867467615227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17246306487316626493947877 3233682466371867467615227)
      ·
        refine ⟨4850523699557801201422841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233682466371867467615227 4850523699557801201422841)
        ·
          refine ⟨3637892774668350901067131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850523699557801201422841 3637892774668350901067131)
          ·
            refine ⟨5456839162002526351600697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637892774668350901067131 5456839162002526351600697)
            ·
              refine ⟨4092629371501894763700523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5456839162002526351600697 4092629371501894763700523)
              ·
                refine ⟨6138944057252842145550785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092629371501894763700523 6138944057252842145550785)
                ·
                  refine ⟨4604208042939631609163089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138944057252842145550785 4604208042939631609163089)
                  ·
                    refine ⟨3453156032204723706872317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604208042939631609163089 3453156032204723706872317)
                    ·
                      refine ⟨1294933512076771390077119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453156032204723706872317 1294933512076771390077119)
                      ·
                        rfl

theorem cell23_2521874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2521874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521874 prefixEnd_2521874 := by exact prefixLift 2521874
  have htrace : WordTrace (prefixWord ++ tailWord_2521874) baseStart_2521874 baseEnd_2521874 := by
    simpa [prefixWord, tailWord_2521874, baseEnd_2521874] using wordTrace_append hprefix tailTrace_2521874
  have hstable : (prefixWord ++ tailWord_2521874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521874).length < 2 ^ (prefixWord ++ tailWord_2521874).sum := by decide
  have hdescent : baseEnd_2521874 < baseStart_2521874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521898 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2521898 : Nat := 118140960795 + 2521898 * 2 ^ 59
def prefixEnd_2521898 : Nat := 4983230072969 + 3 ^ 40 * 2521898 * 2
def baseEnd_2521898 : Nat := 431648611870826432059003

theorem tailTrace_2521898 : CollatzResearch.WordTrace tailWord_2521898 prefixEnd_2521898 431648611870826432059003 := by
  unfold tailWord_2521898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22995294154400431683315587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61320784411734484488841565 22995294154400431683315587)
  ·
    refine ⟨34492941231600647524973381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22995294154400431683315587 34492941231600647524973381)
    ·
      refine ⟨6467426480925121410932509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34492941231600647524973381 6467426480925121410932509)
      ·
        refine ⟨2425284930346920529099691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6467426480925121410932509 2425284930346920529099691)
        ·
          refine ⟨3637927395520380793649537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425284930346920529099691 3637927395520380793649537)
          ·
            refine ⟨2728445546640285595237153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3637927395520380793649537 2728445546640285595237153)
            ·
              refine ⟨2046334159980214196427865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728445546640285595237153 2046334159980214196427865)
              ·
                refine ⟨1534750619985160647320899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046334159980214196427865 1534750619985160647320899)
                ·
                  refine ⟨2302125929977740970981349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534750619985160647320899 2302125929977740970981349)
                  ·
                    refine ⟨431648611870826432059003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302125929977740970981349 431648611870826432059003)
                    ·
                      rfl

theorem cell23_2521898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2521898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521898 prefixEnd_2521898 := by exact prefixLift 2521898
  have htrace : WordTrace (prefixWord ++ tailWord_2521898) baseStart_2521898 baseEnd_2521898 := by
    simpa [prefixWord, tailWord_2521898, baseEnd_2521898] using wordTrace_append hprefix tailTrace_2521898
  have hstable : (prefixWord ++ tailWord_2521898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521898).length < 2 ^ (prefixWord ++ tailWord_2521898).sum := by decide
  have hdescent : baseEnd_2521898 < baseStart_2521898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521974 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2521974 : Nat := 118140960795 + 2521974 * 2 ^ 59
def prefixEnd_2521974 : Nat := 4983230072969 + 3 ^ 40 * 2521974 * 2
def baseEnd_2521974 : Nat := 1294984860142220998826659

theorem tailTrace_2521974 : CollatzResearch.WordTrace tailWord_2521974 prefixEnd_2521974 1294984860142220998826659 := by
  unfold tailWord_2521974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748996785332899482064311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61322632376884261142019317 5748996785332899482064311)
  ·
    refine ⟨8623495177999349223096467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748996785332899482064311 8623495177999349223096467)
    ·
      refine ⟨12935242766999023834644701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623495177999349223096467 12935242766999023834644701)
      ·
        refine ⟨4850716037624633937991763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12935242766999023834644701 4850716037624633937991763)
        ·
          refine ⟨7276074056436950906987645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850716037624633937991763 7276074056436950906987645)
          ·
            refine ⟨2728527771163856590120367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7276074056436950906987645 2728527771163856590120367)
            ·
              refine ⟨4092791656745784885180551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728527771163856590120367 4092791656745784885180551)
              ·
                refine ⟨6139187485118677327770827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092791656745784885180551 6139187485118677327770827)
                ·
                  refine ⟨9208781227678015991656241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139187485118677327770827 9208781227678015991656241)
                  ·
                    refine ⟨6906585920758511993742181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9208781227678015991656241 6906585920758511993742181)
                    ·
                      refine ⟨1294984860142220998826659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6906585920758511993742181 1294984860142220998826659)
                      ·
                        rfl

theorem cell23_2521974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2521974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521974 prefixEnd_2521974 := by exact prefixLift 2521974
  have htrace : WordTrace (prefixWord ++ tailWord_2521974) baseStart_2521974 baseEnd_2521974 := by
    simpa [prefixWord, tailWord_2521974, baseEnd_2521974] using wordTrace_append hprefix tailTrace_2521974
  have hstable : (prefixWord ++ tailWord_2521974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521974).length < 2 ^ (prefixWord ++ tailWord_2521974).sum := by decide
  have hdescent : baseEnd_2521974 < baseStart_2521974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521977 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2521977 : Nat := 118140960795 + 2521977 * 2 ^ 59
def prefixEnd_2521977 : Nat := 4983230072969 + 3 ^ 40 * 2521977 * 2
def baseEnd_2521977 : Nat := 1294986400584184487089145

theorem tailTrace_2521977 : CollatzResearch.WordTrace tailWord_2521977 prefixEnd_2521977 1294986400584184487089145 := by
  unfold tailWord_2521977
  simp only [CollatzResearch.WordTrace]
  refine ⟨91984057984315523225388185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61322705322877015483592123 91984057984315523225388185)
  ·
    refine ⟨68988043488236642419041139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91984057984315523225388185 68988043488236642419041139)
    ·
      refine ⟨103482065232354963628561709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68988043488236642419041139 103482065232354963628561709)
      ·
        refine ⟨38805774462133111360710641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103482065232354963628561709 38805774462133111360710641)
        ·
          refine ⟨29104330846599833520532981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38805774462133111360710641 29104330846599833520532981)
          ·
            refine ⟨2728531016868734392549967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29104330846599833520532981 2728531016868734392549967)
            ·
              refine ⟨4092796525303101588824951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728531016868734392549967 4092796525303101588824951)
              ·
                refine ⟨6139194787954652383237427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092796525303101588824951 6139194787954652383237427)
                ·
                  refine ⟨9208792181931978574856141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139194787954652383237427 9208792181931978574856141)
                  ·
                    refine ⟨3453297068224491965571053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9208792181931978574856141 3453297068224491965571053)
                    ·
                      refine ⟨1294986400584184487089145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453297068224491965571053 1294986400584184487089145)
                      ·
                        rfl

theorem cell23_2521977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2521977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521977 prefixEnd_2521977 := by exact prefixLift 2521977
  have htrace : WordTrace (prefixWord ++ tailWord_2521977) baseStart_2521977 baseEnd_2521977 := by
    simpa [prefixWord, tailWord_2521977, baseEnd_2521977] using wordTrace_append hprefix tailTrace_2521977
  have hstable : (prefixWord ++ tailWord_2521977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521977).length < 2 ^ (prefixWord ++ tailWord_2521977).sum := by decide
  have hdescent : baseEnd_2521977 < baseStart_2521977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521983 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_2521983 : Nat := 118140960795 + 2521983 * 2 ^ 59
def prefixEnd_2521983 : Nat := 4983230072969 + 3 ^ 40 * 2521983 * 2
def baseEnd_2521983 : Nat := 1294989481468111463614117

theorem tailTrace_2521983 : CollatzResearch.WordTrace tailWord_2521983 prefixEnd_2521983 1294989481468111463614117 := by
  unfold tailWord_2521983
  simp only [CollatzResearch.WordTrace]
  refine ⟨91984276822293786250106603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61322851214862524166737735 91984276822293786250106603)
  ·
    refine ⟨137976415233440679375159905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91984276822293786250106603 137976415233440679375159905)
    ·
      refine ⟨103482311425080509531369929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137976415233440679375159905 103482311425080509531369929)
      ·
        refine ⟨77611733568810382148527447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103482311425080509531369929 77611733568810382148527447)
        ·
          refine ⟨116417600353215573222791171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77611733568810382148527447 116417600353215573222791171)
          ·
            refine ⟨174626400529823359834186757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116417600353215573222791171 174626400529823359834186757)
            ·
              refine ⟨32742450099341879968910017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174626400529823359834186757 32742450099341879968910017)
              ·
                refine ⟨24556837574506409976682513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32742450099341879968910017 24556837574506409976682513)
                ·
                  refine ⟨18417628180879807482511885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24556837574506409976682513 18417628180879807482511885)
                  ·
                    refine ⟨6906610567829927805941957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18417628180879807482511885 6906610567829927805941957)
                    ·
                      refine ⟨1294989481468111463614117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6906610567829927805941957 1294989481468111463614117)
                      ·
                        rfl

theorem cell23_2521983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_2521983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2521983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2521983 prefixEnd_2521983 := by exact prefixLift 2521983
  have htrace : WordTrace (prefixWord ++ tailWord_2521983) baseStart_2521983 baseEnd_2521983 := by
    simpa [prefixWord, tailWord_2521983, baseEnd_2521983] using wordTrace_append hprefix tailTrace_2521983
  have hstable : (prefixWord ++ tailWord_2521983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521983).length < 2 ^ (prefixWord ++ tailWord_2521983).sum := by decide
  have hdescent : baseEnd_2521983 < baseStart_2521983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522004 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2522004 : Nat := 118140960795 + 2522004 * 2 ^ 59
def prefixEnd_2522004 : Nat := 4983230072969 + 3 ^ 40 * 2522004 * 2
def baseEnd_2522004 : Nat := 1295000264561855881451521

theorem tailTrace_2522004 : CollatzResearch.WordTrace tailWord_2522004 prefixEnd_2522004 1295000264561855881451521 := by
  unfold tailWord_2522004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45992521377608853418310533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61323361836811804557747377 45992521377608853418310533)
  ·
    refine ⟨8623597758301660015933225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45992521377608853418310533 8623597758301660015933225)
    ·
      refine ⟨6467698318726245011949919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8623597758301660015933225 6467698318726245011949919)
      ·
        refine ⟨9701547478089367517924879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6467698318726245011949919 9701547478089367517924879)
        ·
          refine ⟨14552321217134051276887319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9701547478089367517924879 14552321217134051276887319)
          ·
            refine ⟨21828481825701076915330979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14552321217134051276887319 21828481825701076915330979)
            ·
              refine ⟨32742722738551615372996469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21828481825701076915330979 32742722738551615372996469)
              ·
                refine ⟨3069630256739213941218419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32742722738551615372996469 3069630256739213941218419)
                ·
                  refine ⟨4604445385108820911827629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069630256739213941218419 4604445385108820911827629)
                  ·
                    refine ⟨1726667019415807841935361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4604445385108820911827629 1726667019415807841935361)
                    ·
                      refine ⟨1295000264561855881451521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726667019415807841935361 1295000264561855881451521)
                      ·
                        rfl

theorem cell23_2522004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2522004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522004 prefixEnd_2522004 := by exact prefixLift 2522004
  have htrace : WordTrace (prefixWord ++ tailWord_2522004) baseStart_2522004 baseEnd_2522004 := by
    simpa [prefixWord, tailWord_2522004, baseEnd_2522004] using wordTrace_append hprefix tailTrace_2522004
  have hstable : (prefixWord ++ tailWord_2522004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522004).length < 2 ^ (prefixWord ++ tailWord_2522004).sum := by decide
  have hdescent : baseEnd_2522004 < baseStart_2522004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522020 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_2522020 : Nat := 118140960795 + 2522020 * 2 ^ 59
def prefixEnd_2522020 : Nat := 4983230072969 + 3 ^ 40 * 2522020 * 2
def baseEnd_2522020 : Nat := 1295008480252327818851447

theorem tailTrace_2522020 : CollatzResearch.WordTrace tailWord_2522020 prefixEnd_2522020 1295008480252327818851447 := by
  unfold tailWord_2522020
  simp only [CollatzResearch.WordTrace]
  refine ⟨45992813161579870784601757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61323750882106494379469009 45992813161579870784601757)
  ·
    refine ⟨17247304935592451544225659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45992813161579870784601757 17247304935592451544225659)
    ·
      refine ⟨25870957403388677316338489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17247304935592451544225659 25870957403388677316338489)
      ·
        refine ⟨19403218052541507987253867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25870957403388677316338489 19403218052541507987253867)
        ·
          refine ⟨29104827078812261980880801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403218052541507987253867 29104827078812261980880801)
          ·
            refine ⟨21828620309109196485660601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29104827078812261980880801 21828620309109196485660601)
            ·
              refine ⟨16371465231831897364245451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21828620309109196485660601 16371465231831897364245451)
              ·
                refine ⟨24557197847747846046368177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16371465231831897364245451 24557197847747846046368177)
                ·
                  refine ⟨18417898385810884534776133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24557197847747846046368177 18417898385810884534776133)
                  ·
                    refine ⟨3453355947339540850270525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18417898385810884534776133 3453355947339540850270525)
                    ·
                      refine ⟨1295008480252327818851447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453355947339540850270525 1295008480252327818851447)
                      ·
                        rfl

theorem cell23_2522020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_2522020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522020 prefixEnd_2522020 := by exact prefixLift 2522020
  have htrace : WordTrace (prefixWord ++ tailWord_2522020) baseStart_2522020 baseEnd_2522020 := by
    simpa [prefixWord, tailWord_2522020, baseEnd_2522020] using wordTrace_append hprefix tailTrace_2522020
  have hstable : (prefixWord ++ tailWord_2522020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522020).length < 2 ^ (prefixWord ++ tailWord_2522020).sum := by decide
  have hdescent : baseEnd_2522020 < baseStart_2522020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522053 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_2522053 : Nat := 118140960795 + 2522053 * 2 ^ 59
def prefixEnd_2522053 : Nat := 4983230072969 + 3 ^ 40 * 2522053 * 2
def baseEnd_2522053 : Nat := 431675141704642063246265

theorem tailTrace_2522053 : CollatzResearch.WordTrace tailWord_2522053 prefixEnd_2522053 431675141704642063246265 := by
  unfold tailWord_2522053
  simp only [CollatzResearch.WordTrace]
  refine ⟨91986829932040188205154813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61324553288026792136769875 91986829932040188205154813)
  ·
    refine ⟨34495061224515070576933055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91986829932040188205154813 34495061224515070576933055)
    ·
      refine ⟨51742591836772605865399583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34495061224515070576933055 51742591836772605865399583)
      ·
        refine ⟨77613887755158908798099375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51742591836772605865399583 77613887755158908798099375)
        ·
          refine ⟨116420831632738363197149063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77613887755158908798099375 116420831632738363197149063)
          ·
            refine ⟨174631247449107544795723595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116420831632738363197149063 174631247449107544795723595)
            ·
              refine ⟨261946871173661317193585393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174631247449107544795723595 261946871173661317193585393)
              ·
                refine ⟨196460153380245987895189045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261946871173661317193585393 196460153380245987895189045)
                ·
                  refine ⟨18418139379398061365173973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196460153380245987895189045 18418139379398061365173973)
                  ·
                    refine ⟨431675141704642063246265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18418139379398061365173973 431675141704642063246265)
                    ·
                      rfl

theorem cell23_2522053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_2522053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522053 prefixEnd_2522053 := by exact prefixLift 2522053
  have htrace : WordTrace (prefixWord ++ tailWord_2522053) baseStart_2522053 baseEnd_2522053 := by
    simpa [prefixWord, tailWord_2522053, baseEnd_2522053] using wordTrace_append hprefix tailTrace_2522053
  have hstable : (prefixWord ++ tailWord_2522053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522053).length < 2 ^ (prefixWord ++ tailWord_2522053).sum := by decide
  have hdescent : baseEnd_2522053 < baseStart_2522053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522074 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_2522074 : Nat := 118140960795 + 2522074 * 2 ^ 59
def prefixEnd_2522074 : Nat := 4983230072969 + 3 ^ 40 * 2522074 * 2
def baseEnd_2522074 : Nat := 143892912023074511952911

theorem tailTrace_2522074 : CollatzResearch.WordTrace tailWord_2522074 prefixEnd_2522074 143892912023074511952911 := by
  unfold tailWord_2522074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996898966241027197917319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61325063909976072527779517 22996898966241027197917319)
  ·
    refine ⟨34495348449361540796875979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22996898966241027197917319 34495348449361540796875979)
    ·
      refine ⟨51743022674042311195313969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34495348449361540796875979 51743022674042311195313969)
      ·
        refine ⟨38807267005531733396485477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51743022674042311195313969 38807267005531733396485477)
        ·
          refine ⟨7276362563537200011841027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38807267005531733396485477 7276362563537200011841027)
          ·
            refine ⟨10914543845305800017761541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276362563537200011841027 10914543845305800017761541)
            ·
              refine ⟨2046476970994837503330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10914543845305800017761541 2046476970994837503330289)
              ·
                refine ⟨1534857728246128127497717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046476970994837503330289 1534857728246128127497717)
                ·
                  refine ⟨143892912023074511952911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1534857728246128127497717 143892912023074511952911)
                  ·
                    rfl

theorem cell23_2522074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_2522074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522074 prefixEnd_2522074 := by exact prefixLift 2522074
  have htrace : WordTrace (prefixWord ++ tailWord_2522074) baseStart_2522074 baseEnd_2522074 := by
    simpa [prefixWord, tailWord_2522074, baseEnd_2522074] using wordTrace_append hprefix tailTrace_2522074
  have hstable : (prefixWord ++ tailWord_2522074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522074).length < 2 ^ (prefixWord ++ tailWord_2522074).sum := by decide
  have hdescent : baseEnd_2522074 < baseStart_2522074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522120 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2522120 : Nat := 118140960795 + 2522120 * 2 ^ 59
def prefixEnd_2522120 : Nat := 4983230072969 + 3 ^ 40 * 2522120 * 2
def baseEnd_2522120 : Nat := 1295059828317777427600987

theorem tailTrace_2522120 : CollatzResearch.WordTrace tailWord_2522120 prefixEnd_2522120 1295059828317777427600987 := by
  unfold tailWord_2522120
  simp only [CollatzResearch.WordTrace]
  refine ⟨45994636811398729323921907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61326182415198305765229209 45994636811398729323921907)
  ·
    refine ⟨68991955217098093985882861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45994636811398729323921907 68991955217098093985882861)
    ·
      refine ⟨25871983206411785244706073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68991955217098093985882861 25871983206411785244706073)
      ·
        refine ⟨19403987404808838933529555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25871983206411785244706073 19403987404808838933529555)
        ·
          refine ⟨29105981107213258400294333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403987404808838933529555 29105981107213258400294333)
          ·
            refine ⟨10914742915204971900110375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29105981107213258400294333 10914742915204971900110375)
            ·
              refine ⟨16372114372807457850165563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914742915204971900110375 16372114372807457850165563)
              ·
                refine ⟨24558171559211186775248345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16372114372807457850165563 24558171559211186775248345)
                ·
                  refine ⟨18418628669408390081436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24558171559211186775248345 18418628669408390081436259)
                  ·
                    refine ⟨27627943004112585122154389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18418628669408390081436259 27627943004112585122154389)
                    ·
                      refine ⟨1295059828317777427600987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27627943004112585122154389 1295059828317777427600987)
                      ·
                        rfl

theorem cell23_2522120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2522120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522120 prefixEnd_2522120 := by exact prefixLift 2522120
  have htrace : WordTrace (prefixWord ++ tailWord_2522120) baseStart_2522120 baseEnd_2522120 := by
    simpa [prefixWord, tailWord_2522120, baseEnd_2522120] using wordTrace_append hprefix tailTrace_2522120
  have hstable : (prefixWord ++ tailWord_2522120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522120).length < 2 ^ (prefixWord ++ tailWord_2522120).sum := by decide
  have hdescent : baseEnd_2522120 < baseStart_2522120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522184 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_2522184 : Nat := 118140960795 + 2522184 * 2 ^ 59
def prefixEnd_2522184 : Nat := 4983230072969 + 3 ^ 40 * 2522184 * 2
def baseEnd_2522184 : Nat := 1295092691079665177200693

theorem tailTrace_2522184 : CollatzResearch.WordTrace tailWord_2522184 prefixEnd_2522184 1295092691079665177200693 := by
  unfold tailWord_2522184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45995803947282798789086803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61327738596377065052115737 45995803947282798789086803)
  ·
    refine ⟨68993705920924198183630205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45995803947282798789086803 68993705920924198183630205)
    ·
      refine ⟨25872639720346574318861327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68993705920924198183630205 25872639720346574318861327)
      ·
        refine ⟨38808959580519861478291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25872639720346574318861327 38808959580519861478291991)
        ·
          refine ⟨58213439370779792217437987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38808959580519861478291991 58213439370779792217437987)
          ·
            refine ⟨87320159056169688326156981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58213439370779792217437987 87320159056169688326156981)
            ·
              refine ⟨8186264911515908280577217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87320159056169688326156981 8186264911515908280577217)
              ·
                refine ⟨6139698683636931210432913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8186264911515908280577217 6139698683636931210432913)
                ·
                  refine ⟨4604774012727698407824685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6139698683636931210432913 4604774012727698407824685)
                  ·
                    refine ⟨1726790254772886902934257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4604774012727698407824685 1726790254772886902934257)
                    ·
                      refine ⟨1295092691079665177200693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726790254772886902934257 1295092691079665177200693)
                      ·
                        rfl

theorem cell23_2522184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_2522184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522184 prefixEnd_2522184 := by exact prefixLift 2522184
  have htrace : WordTrace (prefixWord ++ tailWord_2522184) baseStart_2522184 baseEnd_2522184 := by
    simpa [prefixWord, tailWord_2522184, baseEnd_2522184] using wordTrace_append hprefix tailTrace_2522184
  have hstable : (prefixWord ++ tailWord_2522184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522184).length < 2 ^ (prefixWord ++ tailWord_2522184).sum := by decide
  have hdescent : baseEnd_2522184 < baseStart_2522184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522197 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2522197 : Nat := 118140960795 + 2522197 * 2 ^ 59
def prefixEnd_2522197 : Nat := 4983230072969 + 3 ^ 40 * 2522197 * 2
def baseEnd_2522197 : Nat := 1295099366328173626338133

theorem tailTrace_2522197 : CollatzResearch.WordTrace tailWord_2522197 prefixEnd_2522197 1295099366328173626338133 := by
  unfold tailWord_2522197
  simp only [CollatzResearch.WordTrace]
  refine ⟨91992082043518500798396845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61328054695679000532264563 91992082043518500798396845)
  ·
    refine ⟨34497030766319437799398817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91992082043518500798396845 34497030766319437799398817)
    ·
      refine ⟨25872773074739578349549113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34497030766319437799398817 25872773074739578349549113)
      ·
        refine ⟨19404579806054683762161835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25872773074739578349549113 19404579806054683762161835)
        ·
          refine ⟨29106869709082025643242753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19404579806054683762161835 29106869709082025643242753)
          ·
            refine ⟨21830152281811519232432065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29106869709082025643242753 21830152281811519232432065)
            ·
              refine ⟨16372614211358639424324049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21830152281811519232432065 16372614211358639424324049)
              ·
                refine ⟨12279460658518979568243037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16372614211358639424324049 12279460658518979568243037)
                ·
                  refine ⟨4604797746944617338091139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12279460658518979568243037 4604797746944617338091139)
                  ·
                    refine ⟨6907196620416926007136709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604797746944617338091139 6907196620416926007136709)
                    ·
                      refine ⟨1295099366328173626338133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6907196620416926007136709 1295099366328173626338133)
                      ·
                        rfl

theorem cell23_2522197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2522197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522197 prefixEnd_2522197 := by exact prefixLift 2522197
  have htrace : WordTrace (prefixWord ++ tailWord_2522197) baseStart_2522197 baseEnd_2522197 := by
    simpa [prefixWord, tailWord_2522197, baseEnd_2522197] using wordTrace_append hprefix tailTrace_2522197
  have hstable : (prefixWord ++ tailWord_2522197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522197).length < 2 ^ (prefixWord ++ tailWord_2522197).sum := by decide
  have hdescent : baseEnd_2522197 < baseStart_2522197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522220 : List Nat := [2, 2, 1, 1, 3, 2, 1, 11]
def baseStart_2522220 : Nat := 118140960795 + 2522220 * 2 ^ 59
def prefixEnd_2522220 : Nat := 4983230072969 + 3 ^ 40 * 2522220 * 2
def baseEnd_2522220 : Nat := 47967080606786186531501

theorem tailTrace_2522220 : CollatzResearch.WordTrace tailWord_2522220 prefixEnd_2522220 47967080606786186531501 := by
  unfold tailWord_2522220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45996460461217587863242057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61328613948290117150989409 45996460461217587863242057)
  ·
    refine ⟨34497345345913190897431543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45996460461217587863242057 34497345345913190897431543)
    ·
      refine ⟨51746018018869786346147315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34497345345913190897431543 51746018018869786346147315)
      ·
        refine ⟨77619027028304679519220973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51746018018869786346147315 77619027028304679519220973)
        ·
          refine ⟨29107135135614254819707865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77619027028304679519220973 29107135135614254819707865)
          ·
            refine ⟨21830351351710691114780899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29107135135614254819707865 21830351351710691114780899)
            ·
              refine ⟨32745527027566036672171349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21830351351710691114780899 32745527027566036672171349)
              ·
                refine ⟨47967080606786186531501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32745527027566036672171349 47967080606786186531501)
                ·
                  rfl

theorem cell23_2522220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 11].length) (baseStart_2522220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522220 prefixEnd_2522220 := by exact prefixLift 2522220
  have htrace : WordTrace (prefixWord ++ tailWord_2522220) baseStart_2522220 baseEnd_2522220 := by
    simpa [prefixWord, tailWord_2522220, baseEnd_2522220] using wordTrace_append hprefix tailTrace_2522220
  have hstable : (prefixWord ++ tailWord_2522220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522220).length < 2 ^ (prefixWord ++ tailWord_2522220).sum := by decide
  have hdescent : baseEnd_2522220 < baseStart_2522220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522241 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2522241 : Nat := 118140960795 + 2522241 * 2 ^ 59
def prefixEnd_2522241 : Nat := 4983230072969 + 3 ^ 40 * 2522241 * 2
def baseEnd_2522241 : Nat := 431707319825657151395977

theorem tailTrace_2522241 : CollatzResearch.WordTrace tailWord_2522241 prefixEnd_2522241 431707319825657151395977 := by
  unfold tailWord_2522241
  simp only [CollatzResearch.WordTrace]
  refine ⟨91993686855359096312998577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61329124570239397541999051 91993686855359096312998577)
  ·
    refine ⟨68995265141519322234748933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91993686855359096312998577 68995265141519322234748933)
    ·
      refine ⟨12936612214034872919015425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68995265141519322234748933 12936612214034872919015425)
      ·
        refine ⟨9702459160526154689261569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12936612214034872919015425 9702459160526154689261569)
        ·
          refine ⟨7276844370394616016946177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702459160526154689261569 7276844370394616016946177)
          ·
            refine ⟨5457633277795962012709633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7276844370394616016946177 5457633277795962012709633)
            ·
              refine ⟨4093224958346971509532225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457633277795962012709633 4093224958346971509532225)
              ·
                refine ⟨3069918718760228632149169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093224958346971509532225 3069918718760228632149169)
                ·
                  refine ⟨2302439039070171474111877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3069918718760228632149169 2302439039070171474111877)
                  ·
                    refine ⟨431707319825657151395977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302439039070171474111877 431707319825657151395977)
                    ·
                      rfl

theorem cell23_2522241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2522241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522241 prefixEnd_2522241 := by exact prefixLift 2522241
  have htrace : WordTrace (prefixWord ++ tailWord_2522241) baseStart_2522241 baseEnd_2522241 := by
    simpa [prefixWord, tailWord_2522241, baseEnd_2522241] using wordTrace_append hprefix tailTrace_2522241
  have hstable : (prefixWord ++ tailWord_2522241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522241).length < 2 ^ (prefixWord ++ tailWord_2522241).sum := by decide
  have hdescent : baseEnd_2522241 < baseStart_2522241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522247 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2522247 : Nat := 118140960795 + 2522247 * 2 ^ 59
def prefixEnd_2522247 : Nat := 4983230072969 + 3 ^ 40 * 2522247 * 2
def baseEnd_2522247 : Nat := 1295125040360898430712903

theorem tailTrace_2522247 : CollatzResearch.WordTrace tailWord_2522247 prefixEnd_2522247 1295125040360898430712903 := by
  unfold tailWord_2522247
  simp only [CollatzResearch.WordTrace]
  refine ⟨91993905693337359337716995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61329270462224906225144663 91993905693337359337716995)
  ·
    refine ⟨137990858540006039006575493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91993905693337359337716995 137990858540006039006575493)
    ·
      refine ⟨25873285976251132313732905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137990858540006039006575493 25873285976251132313732905)
      ·
        refine ⟨19404964482188349235299679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25873285976251132313732905 19404964482188349235299679)
        ·
          refine ⟨29107446723282523852949519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19404964482188349235299679 29107446723282523852949519)
          ·
            refine ⟨43661170084923785779424279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29107446723282523852949519 43661170084923785779424279)
            ·
              refine ⟨65491755127385678669136419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43661170084923785779424279 65491755127385678669136419)
              ·
                refine ⟨98237632691078518003704629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65491755127385678669136419 98237632691078518003704629)
                ·
                  refine ⟨9209778064788611062847309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98237632691078518003704629 9209778064788611062847309)
                  ·
                    refine ⟨3453666774295729148567741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9209778064788611062847309 3453666774295729148567741)
                    ·
                      refine ⟨1295125040360898430712903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453666774295729148567741 1295125040360898430712903)
                      ·
                        rfl

theorem cell23_2522247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2522247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522247 prefixEnd_2522247 := by exact prefixLift 2522247
  have htrace : WordTrace (prefixWord ++ tailWord_2522247) baseStart_2522247 baseEnd_2522247 := by
    simpa [prefixWord, tailWord_2522247, baseEnd_2522247] using wordTrace_append hprefix tailTrace_2522247
  have hstable : (prefixWord ++ tailWord_2522247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522247).length < 2 ^ (prefixWord ++ tailWord_2522247).sum := by decide
  have hdescent : baseEnd_2522247 < baseStart_2522247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522254 : List Nat := [4, 1, 1, 3, 2, 3, 1, 8]
def baseStart_2522254 : Nat := 118140960795 + 2522254 * 2 ^ 59
def prefixEnd_2522254 : Nat := 4983230072969 + 3 ^ 40 * 2522254 * 2
def baseEnd_2522254 : Nat := 47967727212054811234273

theorem tailTrace_2522254 : CollatzResearch.WordTrace tailWord_2522254 prefixEnd_2522254 47967727212054811234273 := by
  unfold tailWord_2522254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499270125538999941652727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61329440669541333022147877 11499270125538999941652727)
  ·
    refine ⟨17248905188308499912479091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11499270125538999941652727 17248905188308499912479091)
    ·
      refine ⟨25873357782462749868718637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248905188308499912479091 25873357782462749868718637)
      ·
        refine ⟨9702509168423531200769489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25873357782462749868718637 9702509168423531200769489)
        ·
          refine ⟨7276881876317648400577117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702509168423531200769489 7276881876317648400577117)
          ·
            refine ⟨2728830703619118150216419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7276881876317648400577117 2728830703619118150216419)
            ·
              refine ⟨4093246055428677225324629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728830703619118150216419 4093246055428677225324629)
              ·
                refine ⟨47967727212054811234273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4093246055428677225324629 47967727212054811234273)
                ·
                  rfl

theorem cell23_2522254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_2522254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522254 prefixEnd_2522254 := by exact prefixLift 2522254
  have htrace : WordTrace (prefixWord ++ tailWord_2522254) baseStart_2522254 baseEnd_2522254 := by
    simpa [prefixWord, tailWord_2522254, baseEnd_2522254] using wordTrace_append hprefix tailTrace_2522254
  have hstable : (prefixWord ++ tailWord_2522254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522254).length < 2 ^ (prefixWord ++ tailWord_2522254).sum := by decide
  have hdescent : baseEnd_2522254 < baseStart_2522254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522264 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2522264 : Nat := 118140960795 + 2522264 * 2 ^ 59
def prefixEnd_2522264 : Nat := 4983230072969 + 3 ^ 40 * 2522264 * 2
def baseEnd_2522264 : Nat := 1295133769532024864200325

theorem tailTrace_2522264 : CollatzResearch.WordTrace tailWord_2522264 prefixEnd_2522264 1295133769532024864200325 := by
  unfold tailWord_2522264
  simp only [CollatzResearch.WordTrace]
  refine ⟨45997262867137885620542923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61329683822850514160723897 45997262867137885620542923)
  ·
    refine ⟨68995894300706828430814385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45997262867137885620542923 68995894300706828430814385)
    ·
      refine ⟨51746920725530121323110789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68995894300706828430814385 51746920725530121323110789)
      ·
        refine ⟨9702547636036897748083273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51746920725530121323110789 9702547636036897748083273)
        ·
          refine ⟨7276910727027673311062455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702547636036897748083273 7276910727027673311062455)
          ·
            refine ⟨10915366090541509966593683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276910727027673311062455 10915366090541509966593683)
            ·
              refine ⟨16373049135812264949890525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10915366090541509966593683 16373049135812264949890525)
              ·
                refine ⟨6139893425929599356208947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16373049135812264949890525 6139893425929599356208947)
                ·
                  refine ⟨9209840138894399034313421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139893425929599356208947 9209840138894399034313421)
                  ·
                    refine ⟨3453690052085399637867533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9209840138894399034313421 3453690052085399637867533)
                    ·
                      refine ⟨1295133769532024864200325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453690052085399637867533 1295133769532024864200325)
                      ·
                        rfl

theorem cell23_2522264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2522264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522264 prefixEnd_2522264 := by exact prefixLift 2522264
  have htrace : WordTrace (prefixWord ++ tailWord_2522264) baseStart_2522264 baseEnd_2522264 := by
    simpa [prefixWord, tailWord_2522264, baseEnd_2522264] using wordTrace_append hprefix tailTrace_2522264
  have hstable : (prefixWord ++ tailWord_2522264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522264).length < 2 ^ (prefixWord ++ tailWord_2522264).sum := by decide
  have hdescent : baseEnd_2522264 < baseStart_2522264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522282 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2522282 : Nat := 118140960795 + 2522282 * 2 ^ 59
def prefixEnd_2522282 : Nat := 4983230072969 + 3 ^ 40 * 2522282 * 2
def baseEnd_2522282 : Nat := 1295143012183805793775243

theorem tailTrace_2522282 : CollatzResearch.WordTrace tailWord_2522282 prefixEnd_2522282 1295143012183805793775243 := by
  unfold tailWord_2522282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22998795562052640078810275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61330121498807040210160733 22998795562052640078810275)
  ·
    refine ⟨34498193343078960118215413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22998795562052640078810275 34498193343078960118215413)
    ·
      refine ⟨3234205625913652511082695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34498193343078960118215413 3234205625913652511082695)
      ·
        refine ⟨4851308438870478766624043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234205625913652511082695 4851308438870478766624043)
        ·
          refine ⟨7276962658305718149936065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851308438870478766624043 7276962658305718149936065)
          ·
            refine ⟨5457721993729288612452049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7276962658305718149936065 5457721993729288612452049)
            ·
              refine ⟨4093291495296966459339037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457721993729288612452049 4093291495296966459339037)
              ·
                refine ⟨1534984310736362422252139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4093291495296966459339037 1534984310736362422252139)
                ·
                  refine ⟨2302476466104543633378209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534984310736362422252139 2302476466104543633378209)
                  ·
                    refine ⟨1726857349578407725033657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302476466104543633378209 1726857349578407725033657)
                    ·
                      refine ⟨1295143012183805793775243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726857349578407725033657 1295143012183805793775243)
                      ·
                        rfl

theorem cell23_2522282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2522282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522282 prefixEnd_2522282 := by exact prefixLift 2522282
  have htrace : WordTrace (prefixWord ++ tailWord_2522282) baseStart_2522282 baseEnd_2522282 := by
    simpa [prefixWord, tailWord_2522282, baseEnd_2522282] using wordTrace_append hprefix tailTrace_2522282
  have hstable : (prefixWord ++ tailWord_2522282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522282).length < 2 ^ (prefixWord ++ tailWord_2522282).sum := by decide
  have hdescent : baseEnd_2522282 < baseStart_2522282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522285 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_2522285 : Nat := 118140960795 + 2522285 * 2 ^ 59
def prefixEnd_2522285 : Nat := 4983230072969 + 3 ^ 40 * 2522285 * 2
def baseEnd_2522285 : Nat := 1295144552625769282037729

theorem tailTrace_2522285 : CollatzResearch.WordTrace tailWord_2522285 prefixEnd_2522285 1295144552625769282037729 := by
  unfold tailWord_2522285
  simp only [CollatzResearch.WordTrace]
  refine ⟨91995291667199691827600309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61330194444799794551733539 91995291667199691827600309)
  ·
    refine ⟨8624558593799971108837529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91995291667199691827600309 8624558593799971108837529)
    ·
      refine ⟨6468418945349978331628147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8624558593799971108837529 6468418945349978331628147)
      ·
        refine ⟨9702628418024967497442221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468418945349978331628147 9702628418024967497442221)
        ·
          refine ⟨3638485656759362811540833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9702628418024967497442221 3638485656759362811540833)
          ·
            refine ⟨2728864242569522108655625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3638485656759362811540833 2728864242569522108655625)
            ·
              refine ⟨2046648181927141581491719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728864242569522108655625 2046648181927141581491719)
              ·
                refine ⟨3069972272890712372237579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046648181927141581491719 3069972272890712372237579)
                ·
                  refine ⟨4604958409336068558356369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069972272890712372237579 4604958409336068558356369)
                  ·
                    refine ⟨3453718807002051418767277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604958409336068558356369 3453718807002051418767277)
                    ·
                      refine ⟨1295144552625769282037729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453718807002051418767277 1295144552625769282037729)
                      ·
                        rfl

theorem cell23_2522285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_2522285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522285 prefixEnd_2522285 := by exact prefixLift 2522285
  have htrace : WordTrace (prefixWord ++ tailWord_2522285) baseStart_2522285 baseEnd_2522285 := by
    simpa [prefixWord, tailWord_2522285, baseEnd_2522285] using wordTrace_append hprefix tailTrace_2522285
  have hstable : (prefixWord ++ tailWord_2522285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522285).length < 2 ^ (prefixWord ++ tailWord_2522285).sum := by decide
  have hdescent : baseEnd_2522285 < baseStart_2522285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522297 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_2522297 : Nat := 118140960795 + 2522297 * 2 ^ 59
def prefixEnd_2522297 : Nat := 4983230072969 + 3 ^ 40 * 2522297 * 2
def baseEnd_2522297 : Nat := 431716904797874411695891

theorem tailTrace_2522297 : CollatzResearch.WordTrace tailWord_2522297 prefixEnd_2522297 431716904797874411695891 := by
  unfold tailWord_2522297
  simp only [CollatzResearch.WordTrace]
  refine ⟨91995729343156217877037145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61330486228770811918024763 91995729343156217877037145)
  ·
    refine ⟨68996797007367163407777859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91995729343156217877037145 68996797007367163407777859)
    ·
      refine ⟨103495195511050745111666789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68996797007367163407777859 103495195511050745111666789)
      ·
        refine ⟨19405349158322014708437523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103495195511050745111666789 19405349158322014708437523)
        ·
          refine ⟨29108023737483022062656285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19405349158322014708437523 29108023737483022062656285)
          ·
            refine ⟨10915508901556133273496107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29108023737483022062656285 10915508901556133273496107)
            ·
              refine ⟨16373263352334199910244161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10915508901556133273496107 16373263352334199910244161)
              ·
                refine ⟨12279947514250649932683121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16373263352334199910244161 12279947514250649932683121)
                ·
                  refine ⟨9209960635687987449512341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12279947514250649932683121 9209960635687987449512341)
                  ·
                    refine ⟨431716904797874411695891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9209960635687987449512341 431716904797874411695891)
                    ·
                      rfl

theorem cell23_2522297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_2522297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522297 prefixEnd_2522297 := by exact prefixLift 2522297
  have htrace : WordTrace (prefixWord ++ tailWord_2522297) baseStart_2522297 baseEnd_2522297 := by
    simpa [prefixWord, tailWord_2522297, baseEnd_2522297] using wordTrace_append hprefix tailTrace_2522297
  have hstable : (prefixWord ++ tailWord_2522297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522297).length < 2 ^ (prefixWord ++ tailWord_2522297).sum := by decide
  have hdescent : baseEnd_2522297 < baseStart_2522297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522307 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3]
def baseStart_2522307 : Nat := 118140960795 + 2522307 * 2 ^ 59
def prefixEnd_2522307 : Nat := 4983230072969 + 3 ^ 40 * 2522307 * 2
def baseEnd_2522307 : Nat := 1295155849200168195962627

theorem tailTrace_2522307 : CollatzResearch.WordTrace tailWord_2522307 prefixEnd_2522307 1295155849200168195962627 := by
  unfold tailWord_2522307
  simp only [CollatzResearch.WordTrace]
  refine ⟨91996094073119989584901175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61330729382079993056600783 91996094073119989584901175)
  ·
    refine ⟨137994141109679984377351763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91996094073119989584901175 137994141109679984377351763)
    ·
      refine ⟨206991211664519976566027645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137994141109679984377351763 206991211664519976566027645)
      ·
        refine ⟨77621704374194991212260367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206991211664519976566027645 77621704374194991212260367)
        ·
          refine ⟨116432556561292486818390551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77621704374194991212260367 116432556561292486818390551)
          ·
            refine ⟨174648834841938730227585827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116432556561292486818390551 174648834841938730227585827)
            ·
              refine ⟨261973252262908095341378741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174648834841938730227585827 261973252262908095341378741)
              ·
                refine ⟨24559992399647633938254257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261973252262908095341378741 24559992399647633938254257)
                ·
                  refine ⟨18419994299735725453690693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24559992399647633938254257 18419994299735725453690693)
                  ·
                    refine ⟨3453748931200448522567005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18419994299735725453690693 3453748931200448522567005)
                    ·
                      refine ⟨1295155849200168195962627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3453748931200448522567005 1295155849200168195962627)
                      ·
                        rfl

theorem cell23_2522307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_2522307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522307 prefixEnd_2522307 := by exact prefixLift 2522307
  have htrace : WordTrace (prefixWord ++ tailWord_2522307) baseStart_2522307 baseEnd_2522307 := by
    simpa [prefixWord, tailWord_2522307, baseEnd_2522307] using wordTrace_append hprefix tailTrace_2522307
  have hstable : (prefixWord ++ tailWord_2522307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522307).length < 2 ^ (prefixWord ++ tailWord_2522307).sum := by decide
  have hdescent : baseEnd_2522307 < baseStart_2522307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522327 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 7]
def baseStart_2522327 : Nat := 118140960795 + 2522327 * 2 ^ 59
def prefixEnd_2522327 : Nat := 4983230072969 + 3 ^ 40 * 2522327 * 2
def baseEnd_2522327 : Nat := 143907346534806457523615

theorem tailTrace_2522327 : CollatzResearch.WordTrace tailWord_2522327 prefixEnd_2522327 143907346534806457523615 := by
  unfold tailWord_2522327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91996823533047533000629235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61331215688698355333752823 91996823533047533000629235)
  ·
    refine ⟨137995235299571299500943853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91996823533047533000629235 137995235299571299500943853)
    ·
      refine ⟨51748213237339237312853945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137995235299571299500943853 51748213237339237312853945)
      ·
        refine ⟨38811159928004427984640459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51748213237339237312853945 38811159928004427984640459)
        ·
          refine ⟨58216739892006641976960689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38811159928004427984640459 58216739892006641976960689)
          ·
            refine ⟨43662554919004981482720517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58216739892006641976960689 43662554919004981482720517)
            ·
              refine ⟨8186729047313434028010097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43662554919004981482720517 8186729047313434028010097)
              ·
                refine ⟨6140046785485075521007573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8186729047313434028010097 6140046785485075521007573)
                ·
                  refine ⟨143907346534806457523615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6140046785485075521007573 143907346534806457523615)
                  ·
                    rfl

theorem cell23_2522327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 7].length) (baseStart_2522327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522327 prefixEnd_2522327 := by exact prefixLift 2522327
  have htrace : WordTrace (prefixWord ++ tailWord_2522327) baseStart_2522327 baseEnd_2522327 := by
    simpa [prefixWord, tailWord_2522327, baseEnd_2522327] using wordTrace_append hprefix tailTrace_2522327
  have hstable : (prefixWord ++ tailWord_2522327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522327).length < 2 ^ (prefixWord ++ tailWord_2522327).sum := by decide
  have hdescent : baseEnd_2522327 < baseStart_2522327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522361 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 5]
def baseStart_2522361 : Nat := 118140960795 + 2522361 * 2 ^ 59
def prefixEnd_2522361 : Nat := 4983230072969 + 3 ^ 40 * 2522361 * 2
def baseEnd_2522361 : Nat := 143909286350612331631931

theorem tailTrace_2522361 : CollatzResearch.WordTrace tailWord_2522361 prefixEnd_2522361 143909286350612331631931 := by
  unfold tailWord_2522361
  simp only [CollatzResearch.WordTrace]
  refine ⟨91998063614924356807366937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61332042409949571204911291 91998063614924356807366937)
  ·
    refine ⟨68998547711193267605525203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91998063614924356807366937 68998547711193267605525203)
    ·
      refine ⟨103497821566789901408287805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68998547711193267605525203 103497821566789901408287805)
      ·
        refine ⟨38811683087546213028107927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103497821566789901408287805 38811683087546213028107927)
        ·
          refine ⟨58217524631319319542161891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38811683087546213028107927 58217524631319319542161891)
          ·
            refine ⟨87326286946978979313242837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58217524631319319542161891 87326286946978979313242837)
            ·
              refine ⟨2046709850319819827654129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87326286946978979313242837 2046709850319819827654129)
              ·
                refine ⟨1535032387739864870740597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046709850319819827654129 1535032387739864870740597)
                ·
                  refine ⟨143909286350612331631931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535032387739864870740597 143909286350612331631931)
                  ·
                    rfl

theorem cell23_2522361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 5].length) (baseStart_2522361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522361 prefixEnd_2522361 := by exact prefixLift 2522361
  have htrace : WordTrace (prefixWord ++ tailWord_2522361) baseStart_2522361 baseEnd_2522361 := by
    simpa [prefixWord, tailWord_2522361, baseEnd_2522361] using wordTrace_append hprefix tailTrace_2522361
  have hstable : (prefixWord ++ tailWord_2522361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522361).length < 2 ^ (prefixWord ++ tailWord_2522361).sum := by decide
  have hdescent : baseEnd_2522361 < baseStart_2522361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522367 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_2522367 : Nat := 118140960795 + 2522367 * 2 ^ 59
def prefixEnd_2522367 : Nat := 4983230072969 + 3 ^ 40 * 2522367 * 2
def baseEnd_2522367 : Nat := 1295186658039437961212351

theorem tailTrace_2522367 : CollatzResearch.WordTrace tailWord_2522367 prefixEnd_2522367 1295186658039437961212351 := by
  unfold tailWord_2522367
  simp only [CollatzResearch.WordTrace]
  refine ⟨91998282452902619832085355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61332188301935079888056903 91998282452902619832085355)
  ·
    refine ⟨137997423679353929748128033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91998282452902619832085355 137997423679353929748128033)
    ·
      refine ⟨103498067759515447311096025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137997423679353929748128033 103498067759515447311096025)
      ·
        refine ⟨77623550819636585483322019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103498067759515447311096025 77623550819636585483322019)
        ·
          refine ⟨116435326229454878224983029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77623550819636585483322019 116435326229454878224983029)
          ·
            refine ⟨10915811834011394833592159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116435326229454878224983029 10915811834011394833592159)
            ·
              refine ⟨16373717751017092250388239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10915811834011394833592159 16373717751017092250388239)
              ·
                refine ⟨24560576626525638375582359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16373717751017092250388239 24560576626525638375582359)
                ·
                  refine ⟨36840864939788457563373539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24560576626525638375582359 36840864939788457563373539)
                  ·
                    refine ⟨55261297409682686345060309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36840864939788457563373539 55261297409682686345060309)
                    ·
                      refine ⟨1295186658039437961212351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55261297409682686345060309 1295186658039437961212351)
                      ·
                        rfl

theorem cell23_2522367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_2522367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522367 prefixEnd_2522367 := by exact prefixLift 2522367
  have htrace : WordTrace (prefixWord ++ tailWord_2522367) baseStart_2522367 baseEnd_2522367 := by
    simpa [prefixWord, tailWord_2522367, baseEnd_2522367] using wordTrace_append hprefix tailTrace_2522367
  have hstable : (prefixWord ++ tailWord_2522367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522367).length < 2 ^ (prefixWord ++ tailWord_2522367).sum := by decide
  have hdescent : baseEnd_2522367 < baseStart_2522367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522372 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2522372 : Nat := 118140960795 + 2522372 * 2 ^ 59
def prefixEnd_2522372 : Nat := 4983230072969 + 3 ^ 40 * 2522372 * 2
def baseEnd_2522372 : Nat := 1295189225442710441649829

theorem tailTrace_2522372 : CollatzResearch.WordTrace tailWord_2522372 prefixEnd_2522372 1295189225442710441649829 := by
  unfold tailWord_2522372
  simp only [CollatzResearch.WordTrace]
  refine ⟨45999232408942252843008685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61332309878589670457344913 45999232408942252843008685)
  ·
    refine ⟨17249712153353344816128257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45999232408942252843008685 17249712153353344816128257)
    ·
      refine ⟨12937284115015008612096193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17249712153353344816128257 12937284115015008612096193)
      ·
        refine ⟨9702963086261256459072145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12937284115015008612096193 9702963086261256459072145)
        ·
          refine ⟨7277222314695942344304109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702963086261256459072145 7277222314695942344304109)
          ·
            refine ⟨2728958368010978379114041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7277222314695942344304109 2728958368010978379114041)
            ·
              refine ⟨2046718776008233784335531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728958368010978379114041 2046718776008233784335531)
              ·
                refine ⟨3070078164012350676503297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046718776008233784335531 3070078164012350676503297)
                ·
                  refine ⟨2302558623009263007377473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070078164012350676503297 2302558623009263007377473)
                  ·
                    refine ⟨1726918967256947255533105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302558623009263007377473 1726918967256947255533105)
                    ·
                      refine ⟨1295189225442710441649829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1726918967256947255533105 1295189225442710441649829)
                      ·
                        rfl

theorem cell23_2522372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2522372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522372 prefixEnd_2522372 := by exact prefixLift 2522372
  have htrace : WordTrace (prefixWord ++ tailWord_2522372) baseStart_2522372 baseEnd_2522372 := by
    simpa [prefixWord, tailWord_2522372, baseEnd_2522372] using wordTrace_append hprefix tailTrace_2522372
  have hstable : (prefixWord ++ tailWord_2522372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522372).length < 2 ^ (prefixWord ++ tailWord_2522372).sum := by decide
  have hdescent : baseEnd_2522372 < baseStart_2522372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522501 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_2522501 : Nat := 118140960795 + 2522501 * 2 ^ 59
def prefixEnd_2522501 : Nat := 4983230072969 + 3 ^ 40 * 2522501 * 2
def baseEnd_2522501 : Nat := 1295255464447140436936735

theorem tailTrace_2522501 : CollatzResearch.WordTrace tailWord_2522501 prefixEnd_2522501 1295255464447140436936735 := by
  unfold tailWord_2522501
  simp only [CollatzResearch.WordTrace]
  refine ⟨92003169834417160717463357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61335446556278107144975571 92003169834417160717463357)
  ·
    refine ⟨34501188687906435269048759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92003169834417160717463357 34501188687906435269048759)
    ·
      refine ⟨51751783031859652903573139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34501188687906435269048759 51751783031859652903573139)
      ·
        refine ⟨77627674547789479355359709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51751783031859652903573139 77627674547789479355359709)
        ·
          refine ⟨29110377955421054758259891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77627674547789479355359709 29110377955421054758259891)
          ·
            refine ⟨43665566933131582137389837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29110377955421054758259891 43665566933131582137389837)
            ·
              refine ⟨16374587599924343301521189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43665566933131582137389837 16374587599924343301521189)
              ·
                refine ⟨3070235174985814369035223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16374587599924343301521189 3070235174985814369035223)
                ·
                  refine ⟨4605352762478721553552835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070235174985814369035223 4605352762478721553552835)
                  ·
                    refine ⟨6908029143718082330329253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605352762478721553552835 6908029143718082330329253)
                    ·
                      refine ⟨1295255464447140436936735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6908029143718082330329253 1295255464447140436936735)
                      ·
                        rfl

theorem cell23_2522501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_2522501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522501 prefixEnd_2522501 := by exact prefixLift 2522501
  have htrace : WordTrace (prefixWord ++ tailWord_2522501) baseStart_2522501 baseEnd_2522501 := by
    simpa [prefixWord, tailWord_2522501, baseEnd_2522501] using wordTrace_append hprefix tailTrace_2522501
  have hstable : (prefixWord ++ tailWord_2522501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522501).length < 2 ^ (prefixWord ++ tailWord_2522501).sum := by decide
  have hdescent : baseEnd_2522501 < baseStart_2522501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522521 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2522521 : Nat := 118140960795 + 2522521 * 2 ^ 59
def prefixEnd_2522521 : Nat := 4983230072969 + 3 ^ 40 * 2522521 * 2
def baseEnd_2522521 : Nat := 1295265734060230358686643

theorem tailTrace_2522521 : CollatzResearch.WordTrace tailWord_2522521 prefixEnd_2522521 1295265734060230358686643 := by
  unfold tailWord_2522521
  simp only [CollatzResearch.WordTrace]
  refine ⟨92003899294344704133191417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61335932862896469422127611 92003899294344704133191417)
  ·
    refine ⟨69002924470758528099893563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92003899294344704133191417 69002924470758528099893563)
    ·
      refine ⟨103504386706137792149840345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69002924470758528099893563 103504386706137792149840345)
      ·
        refine ⟨77628290029603344112380259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103504386706137792149840345 77628290029603344112380259)
        ·
          refine ⟨116442435044405016168570389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77628290029603344112380259 116442435044405016168570389)
          ·
            refine ⟨5458239142706485132901737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116442435044405016168570389 5458239142706485132901737)
            ·
              refine ⟨4093679357029863849676303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458239142706485132901737 4093679357029863849676303)
              ·
                refine ⟨6140519035544795774514455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093679357029863849676303 6140519035544795774514455)
                ·
                  refine ⟨9210778553317193661771683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140519035544795774514455 9210778553317193661771683)
                  ·
                    refine ⟨13816167829975790492657525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9210778553317193661771683 13816167829975790492657525)
                    ·
                      refine ⟨1295265734060230358686643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13816167829975790492657525 1295265734060230358686643)
                      ·
                        rfl

theorem cell23_2522521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2522521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522521 prefixEnd_2522521 := by exact prefixLift 2522521
  have htrace : WordTrace (prefixWord ++ tailWord_2522521) baseStart_2522521 baseEnd_2522521 := by
    simpa [prefixWord, tailWord_2522521, baseEnd_2522521] using wordTrace_append hprefix tailTrace_2522521
  have hstable : (prefixWord ++ tailWord_2522521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522521).length < 2 ^ (prefixWord ++ tailWord_2522521).sum := by decide
  have hdescent : baseEnd_2522521 < baseStart_2522521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522541 : List Nat := [1, 5, 2, 2, 1, 1, 1, 10]
def baseStart_2522541 : Nat := 118140960795 + 2522541 * 2 ^ 59
def prefixEnd_2522541 : Nat := 4983230072969 + 3 ^ 40 * 2522541 * 2
def baseEnd_2522541 : Nat := 47973185321234084460613

theorem tailTrace_2522541 : CollatzResearch.WordTrace tailWord_2522541 prefixEnd_2522541 47973185321234084460613 := by
  unfold tailWord_2522541
  simp only [CollatzResearch.WordTrace]
  refine ⟨92004628754272247548919477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61336419169514831699279651 92004628754272247548919477)
  ·
    refine ⟨8625433945713023207711201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92004628754272247548919477 8625433945713023207711201)
    ·
      refine ⟨6469075459284767405783401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8625433945713023207711201 6469075459284767405783401)
      ·
        refine ⟨4851806594463575554337551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6469075459284767405783401 4851806594463575554337551)
        ·
          refine ⟨7277709891695363331506327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851806594463575554337551 7277709891695363331506327)
          ·
            refine ⟨10916564837543044997259491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277709891695363331506327 10916564837543044997259491)
            ·
              refine ⟨16374847256314567495889237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916564837543044997259491 16374847256314567495889237)
              ·
                refine ⟨47973185321234084460613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16374847256314567495889237 47973185321234084460613)
                ·
                  rfl

theorem cell23_2522541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 10].length) (baseStart_2522541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522541 prefixEnd_2522541 := by exact prefixLift 2522541
  have htrace : WordTrace (prefixWord ++ tailWord_2522541) baseStart_2522541 baseEnd_2522541 := by
    simpa [prefixWord, tailWord_2522541, baseEnd_2522541] using wordTrace_append hprefix tailTrace_2522541
  have hstable : (prefixWord ++ tailWord_2522541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522541).length < 2 ^ (prefixWord ++ tailWord_2522541).sum := by decide
  have hdescent : baseEnd_2522541 < baseStart_2522541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522551 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_2522551 : Nat := 118140960795 + 2522551 * 2 ^ 59
def prefixEnd_2522551 : Nat := 4983230072969 + 3 ^ 40 * 2522551 * 2
def baseEnd_2522551 : Nat := 1295281138479865241311505

theorem tailTrace_2522551 : CollatzResearch.WordTrace tailWord_2522551 prefixEnd_2522551 1295281138479865241311505 := by
  unfold tailWord_2522551
  simp only [CollatzResearch.WordTrace]
  refine ⟨92004993484236019256783507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61336662322824012837855671 92004993484236019256783507)
  ·
    refine ⟨138007490226354028885175261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92004993484236019256783507 138007490226354028885175261)
    ·
      refine ⟨51752808834882760831940723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138007490226354028885175261 51752808834882760831940723)
      ·
        refine ⟨77629213252324141247911085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51752808834882760831940723 77629213252324141247911085)
        ·
          refine ⟨29110954969621552967966657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77629213252324141247911085 29110954969621552967966657)
          ·
            refine ⟨21833216227216164725974993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29110954969621552967966657 21833216227216164725974993)
            ·
              refine ⟨16374912170412123544481245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21833216227216164725974993 16374912170412123544481245)
              ·
                refine ⟨6140592063904546329180467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16374912170412123544481245 6140592063904546329180467)
                ·
                  refine ⟨9210888095856819493770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140592063904546329180467 9210888095856819493770701)
                  ·
                    refine ⟨3454083035946307310164013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9210888095856819493770701 3454083035946307310164013)
                    ·
                      refine ⟨1295281138479865241311505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454083035946307310164013 1295281138479865241311505)
                      ·
                        rfl

theorem cell23_2522551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_2522551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522551 prefixEnd_2522551 := by exact prefixLift 2522551
  have htrace : WordTrace (prefixWord ++ tailWord_2522551) baseStart_2522551 baseEnd_2522551 := by
    simpa [prefixWord, tailWord_2522551, baseEnd_2522551] using wordTrace_append hprefix tailTrace_2522551
  have hstable : (prefixWord ++ tailWord_2522551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522551).length < 2 ^ (prefixWord ++ tailWord_2522551).sum := by decide
  have hdescent : baseEnd_2522551 < baseStart_2522551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522585 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2522585 : Nat := 118140960795 + 2522585 * 2 ^ 59
def prefixEnd_2522585 : Nat := 4983230072969 + 3 ^ 40 * 2522585 * 2
def baseEnd_2522585 : Nat := 1295298596822118108286349

theorem tailTrace_2522585 : CollatzResearch.WordTrace tailWord_2522585 prefixEnd_2522585 1295298596822118108286349 := by
  unfold tailWord_2522585
  simp only [CollatzResearch.WordTrace]
  refine ⟨92006233566112843063521209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61337489044075228709014139 92006233566112843063521209)
  ·
    refine ⟨69004675174584632297640907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92006233566112843063521209 69004675174584632297640907)
    ·
      refine ⟨103507012761876948446461361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69004675174584632297640907 103507012761876948446461361)
      ·
        refine ⟨77630259571407711334846021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103507012761876948446461361 77630259571407711334846021)
        ·
          refine ⟨14555673669638945875283629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77630259571407711334846021 14555673669638945875283629)
          ·
            refine ⟨5458377626114604703231361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14555673669638945875283629 5458377626114604703231361)
            ·
              refine ⟨4093783219585953527423521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458377626114604703231361 4093783219585953527423521)
              ·
                refine ⟨3070337414689465145567641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093783219585953527423521 3070337414689465145567641)
                ·
                  refine ⟨2302753061017098859175731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070337414689465145567641 2302753061017098859175731)
                  ·
                    refine ⟨3454129591525648288763597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302753061017098859175731 3454129591525648288763597)
                    ·
                      refine ⟨1295298596822118108286349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454129591525648288763597 1295298596822118108286349)
                      ·
                        rfl

theorem cell23_2522585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2522585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522585 prefixEnd_2522585 := by exact prefixLift 2522585
  have htrace : WordTrace (prefixWord ++ tailWord_2522585) baseStart_2522585 baseEnd_2522585 := by
    simpa [prefixWord, tailWord_2522585, baseEnd_2522585] using wordTrace_append hprefix tailTrace_2522585
  have hstable : (prefixWord ++ tailWord_2522585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522585).length < 2 ^ (prefixWord ++ tailWord_2522585).sum := by decide
  have hdescent : baseEnd_2522585 < baseStart_2522585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522608 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2]
def baseStart_2522608 : Nat := 118140960795 + 2522608 * 2 ^ 59
def prefixEnd_2522608 : Nat := 4983230072969 + 3 ^ 40 * 2522608 * 2
def baseEnd_2522608 : Nat := 1295310406877171518298743

theorem tailTrace_2522608 : CollatzResearch.WordTrace tailWord_2522608 prefixEnd_2522608 1295310406877171518298743 := by
  unfold tailWord_2522608
  simp only [CollatzResearch.WordTrace]
  refine ⟨46003536222514758995804239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61338048296686345327738985 46003536222514758995804239)
  ·
    refine ⟨69005304333772138493706359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46003536222514758995804239 69005304333772138493706359)
    ·
      refine ⟨103507956500658207740559539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69005304333772138493706359 103507956500658207740559539)
      ·
        refine ⟨155261934750987311610839309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103507956500658207740559539 155261934750987311610839309)
        ·
          refine ⟨58223225531620241854064741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155261934750987311610839309 58223225531620241854064741)
          ·
            refine ⟨10916854787178795347637139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58223225531620241854064741 10916854787178795347637139)
            ·
              refine ⟨16375282180768193021455709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916854787178795347637139 16375282180768193021455709)
              ·
                refine ⟨6140730817788072383045891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16375282180768193021455709 6140730817788072383045891)
                ·
                  refine ⟨9211096226682108574568837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140730817788072383045891 9211096226682108574568837)
                  ·
                    refine ⟨1727080542502895357731657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9211096226682108574568837 1727080542502895357731657)
                    ·
                      refine ⟨1295310406877171518298743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727080542502895357731657 1295310406877171518298743)
                      ·
                        rfl

theorem cell23_2522608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2].length) (baseStart_2522608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522608 prefixEnd_2522608 := by exact prefixLift 2522608
  have htrace : WordTrace (prefixWord ++ tailWord_2522608) baseStart_2522608 baseEnd_2522608 := by
    simpa [prefixWord, tailWord_2522608, baseEnd_2522608] using wordTrace_append hprefix tailTrace_2522608
  have hstable : (prefixWord ++ tailWord_2522608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522608).length < 2 ^ (prefixWord ++ tailWord_2522608).sum := by decide
  have hdescent : baseEnd_2522608 < baseStart_2522608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522641 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_2522641 : Nat := 118140960795 + 2522641 * 2 ^ 59
def prefixEnd_2522641 : Nat := 4983230072969 + 3 ^ 40 * 2522641 * 2
def baseEnd_2522641 : Nat := 1295327351738769889186091

theorem tailTrace_2522641 : CollatzResearch.WordTrace tailWord_2522641 prefixEnd_2522641 1295327351738769889186091 := by
  unfold tailWord_2522641
  simp only [CollatzResearch.WordTrace]
  refine ⟨92008276053909964627559777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61338850702606643085039851 92008276053909964627559777)
  ·
    refine ⟨69006207040432473470669833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92008276053909964627559777 69006207040432473470669833)
    ·
      refine ⟨51754655280324355103002375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69006207040432473470669833 51754655280324355103002375)
      ·
        refine ⟨77631982920486532654503563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51754655280324355103002375 77631982920486532654503563)
        ·
          refine ⟨116447974380729798981755345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77631982920486532654503563 116447974380729798981755345)
          ·
            refine ⟨87335980785547349236316509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116447974380729798981755345 87335980785547349236316509)
            ·
              refine ⟨32750992794580255963618691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87335980785547349236316509 32750992794580255963618691)
              ·
                refine ⟨49126489191870383945428037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32750992794580255963618691 49126489191870383945428037)
                ·
                  refine ⟨9211216723475696989767757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49126489191870383945428037 9211216723475696989767757)
                  ·
                    refine ⟨3454206271303386371162909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9211216723475696989767757 3454206271303386371162909)
                    ·
                      refine ⟨1295327351738769889186091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454206271303386371162909 1295327351738769889186091)
                      ·
                        rfl

theorem cell23_2522641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_2522641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522641 prefixEnd_2522641 := by exact prefixLift 2522641
  have htrace : WordTrace (prefixWord ++ tailWord_2522641) baseStart_2522641 baseEnd_2522641 := by
    simpa [prefixWord, tailWord_2522641, baseEnd_2522641] using wordTrace_append hprefix tailTrace_2522641
  have hstable : (prefixWord ++ tailWord_2522641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522641).length < 2 ^ (prefixWord ++ tailWord_2522641).sum := by decide
  have hdescent : baseEnd_2522641 < baseStart_2522641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522648 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 7]
def baseStart_2522648 : Nat := 118140960795 + 2522648 * 2 ^ 59
def prefixEnd_2522648 : Nat := 4983230072969 + 3 ^ 40 * 2522648 * 2
def baseEnd_2522648 : Nat := 143925660678150151310951

theorem tailTrace_2522648 : CollatzResearch.WordTrace tailWord_2522648 prefixEnd_2522648 143925660678150151310951 := by
  unfold tailWord_2522648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46004265682442302411532299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61339020909923069882043065 46004265682442302411532299)
  ·
    refine ⟨69006398523663453617298449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46004265682442302411532299 69006398523663453617298449)
    ·
      refine ⟨51754798892747590212973837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69006398523663453617298449 51754798892747590212973837)
      ·
        refine ⟨19408049584780346329865189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51754798892747590212973837 19408049584780346329865189)
        ·
          refine ⟨3639009297146314936849723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19408049584780346329865189 3639009297146314936849723)
          ·
            refine ⟨5458513945719472405274585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639009297146314936849723 5458513945719472405274585)
            ·
              refine ⟨4093885459289604303955939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458513945719472405274585 4093885459289604303955939)
              ·
                refine ⟨6140828188934406455933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093885459289604303955939 6140828188934406455933909)
                ·
                  refine ⟨143925660678150151310951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6140828188934406455933909 143925660678150151310951)
                  ·
                    rfl

theorem cell23_2522648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_2522648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522648 prefixEnd_2522648 := by exact prefixLift 2522648
  have htrace : WordTrace (prefixWord ++ tailWord_2522648) baseStart_2522648 baseEnd_2522648 := by
    simpa [prefixWord, tailWord_2522648, baseEnd_2522648] using wordTrace_append hprefix tailTrace_2522648
  have hstable : (prefixWord ++ tailWord_2522648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522648).length < 2 ^ (prefixWord ++ tailWord_2522648).sum := by decide
  have hdescent : baseEnd_2522648 < baseStart_2522648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522658 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2522658 : Nat := 118140960795 + 2522658 * 2 ^ 59
def prefixEnd_2522658 : Nat := 4983230072969 + 3 ^ 40 * 2522658 * 2
def baseEnd_2522658 : Nat := 1295336080909896322673513

theorem tailTrace_2522658 : CollatzResearch.WordTrace tailWord_2522658 prefixEnd_2522658 1295336080909896322673513 := by
  unfold tailWord_2522658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002224023712094132732157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61339264063232251020619085 23002224023712094132732157)
  ·
    refine ⟨8625834008892035299774559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23002224023712094132732157 8625834008892035299774559)
    ·
      refine ⟨12938751013338052949661839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8625834008892035299774559 12938751013338052949661839)
      ·
        refine ⟨19408126520007079424492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12938751013338052949661839 19408126520007079424492759)
        ·
          refine ⟨29112189780010619136739139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19408126520007079424492759 29112189780010619136739139)
          ·
            refine ⟨43668284670015928705108709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29112189780010619136739139 43668284670015928705108709)
            ·
              refine ⟨8187803375627986632207883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43668284670015928705108709 8187803375627986632207883)
              ·
                refine ⟨12281705063441979948311825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8187803375627986632207883 12281705063441979948311825)
                ·
                  refine ⟨9211278797581484961233869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12281705063441979948311825 9211278797581484961233869)
                  ·
                    refine ⟨3454229549093056860462701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9211278797581484961233869 3454229549093056860462701)
                    ·
                      refine ⟨1295336080909896322673513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454229549093056860462701 1295336080909896322673513)
                      ·
                        rfl

theorem cell23_2522658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2522658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522658 prefixEnd_2522658 := by exact prefixLift 2522658
  have htrace : WordTrace (prefixWord ++ tailWord_2522658) baseStart_2522658 baseEnd_2522658 := by
    simpa [prefixWord, tailWord_2522658, baseEnd_2522658] using wordTrace_append hprefix tailTrace_2522658
  have hstable : (prefixWord ++ tailWord_2522658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522658).length < 2 ^ (prefixWord ++ tailWord_2522658).sum := by decide
  have hdescent : baseEnd_2522658 < baseStart_2522658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522659 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 2, 2, 2]
def baseStart_2522659 : Nat := 118140960795 + 2522659 * 2 ^ 59
def prefixEnd_2522659 : Nat := 4983230072969 + 3 ^ 40 * 2522659 * 2
def baseEnd_2522659 : Nat := 1295336594390550818761009

theorem tailTrace_2522659 : CollatzResearch.WordTrace tailWord_2522659 prefixEnd_2522659 1295336594390550818761009 := by
  unfold tailWord_2522659
  simp only [CollatzResearch.WordTrace]
  refine ⟨92008932567844753701715031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61339288378563169134476687 92008932567844753701715031)
  ·
    refine ⟨138013398851767130552572547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92008932567844753701715031 138013398851767130552572547)
    ·
      refine ⟨207020098277650695828858821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138013398851767130552572547 207020098277650695828858821)
      ·
        refine ⟨38816268427059505467911029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207020098277650695828858821 38816268427059505467911029)
        ·
          refine ⟨3639025165036828637616659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38816268427059505467911029 3639025165036828637616659)
          ·
            refine ⟨5458537747555242956424989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639025165036828637616659 5458537747555242956424989)
            ·
              refine ⟨2046951655333216108659371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5458537747555242956424989 2046951655333216108659371)
              ·
                refine ⟨3070427482999824162989057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046951655333216108659371 3070427482999824162989057)
                ·
                  refine ⟨2302820612249868122241793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070427482999824162989057 2302820612249868122241793)
                  ·
                    refine ⟨1727115459187401091681345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302820612249868122241793 1727115459187401091681345)
                    ·
                      refine ⟨1295336594390550818761009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727115459187401091681345 1295336594390550818761009)
                      ·
                        rfl

theorem cell23_2522659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_2522659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522659 prefixEnd_2522659 := by exact prefixLift 2522659
  have htrace : WordTrace (prefixWord ++ tailWord_2522659) baseStart_2522659 baseEnd_2522659 := by
    simpa [prefixWord, tailWord_2522659, baseEnd_2522659] using wordTrace_append hprefix tailTrace_2522659
  have hstable : (prefixWord ++ tailWord_2522659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522659).length < 2 ^ (prefixWord ++ tailWord_2522659).sum := by decide
  have hdescent : baseEnd_2522659 < baseStart_2522659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522698 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2522698 : Nat := 118140960795 + 2522698 * 2 ^ 59
def prefixEnd_2522698 : Nat := 4983230072969 + 3 ^ 40 * 2522698 * 2
def baseEnd_2522698 : Nat := 1295356620136076166173329

theorem tailTrace_2522698 : CollatzResearch.WordTrace tailWord_2522698 prefixEnd_2522698 1295356620136076166173329 := by
  unfold tailWord_2522698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002588753675865840596187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61340236676468975574923165 23002588753675865840596187)
  ·
    refine ⟨34503883130513798760894281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23002588753675865840596187 34503883130513798760894281)
    ·
      refine ⟨25877912347885349070670711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34503883130513798760894281 25877912347885349070670711)
      ·
        refine ⟨38816868521828023606006067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25877912347885349070670711 38816868521828023606006067)
        ·
          refine ⟨58225302782742035409009101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38816868521828023606006067 58225302782742035409009101)
          ·
            refine ⟨21834488543528263278378413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58225302782742035409009101 21834488543528263278378413)
            ·
              refine ⟨8187933203823098729391905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21834488543528263278378413 8187933203823098729391905)
              ·
                refine ⟨6140949902867324047043929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8187933203823098729391905 6140949902867324047043929)
                ·
                  refine ⟨4605712427150493035282947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6140949902867324047043929 4605712427150493035282947)
                  ·
                    refine ⟨6908568640725739552924421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605712427150493035282947 6908568640725739552924421)
                    ·
                      refine ⟨1295356620136076166173329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6908568640725739552924421 1295356620136076166173329)
                      ·
                        rfl

theorem cell23_2522698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2522698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522698 prefixEnd_2522698 := by exact prefixLift 2522698
  have htrace : WordTrace (prefixWord ++ tailWord_2522698) baseStart_2522698 baseEnd_2522698 := by
    simpa [prefixWord, tailWord_2522698, baseEnd_2522698] using wordTrace_append hprefix tailTrace_2522698
  have hstable : (prefixWord ++ tailWord_2522698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522698).length < 2 ^ (prefixWord ++ tailWord_2522698).sum := by decide
  have hdescent : baseEnd_2522698 < baseStart_2522698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522710 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2522710 : Nat := 118140960795 + 2522710 * 2 ^ 59
def prefixEnd_2522710 : Nat := 4983230072969 + 3 ^ 40 * 2522710 * 2
def baseEnd_2522710 : Nat := 1295362781903930119223275

theorem tailTrace_2522710 : CollatzResearch.WordTrace tailWord_2522710 prefixEnd_2522710 1295362781903930119223275 := by
  unfold tailWord_2522710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750674543166249338238849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61340528460439992941214389 5750674543166249338238849)
  ·
    refine ⟨4313005907374687003679137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5750674543166249338238849 4313005907374687003679137)
    ·
      refine ⟨3234754430531015252759353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4313005907374687003679137 3234754430531015252759353)
      ·
        refine ⟨2426065822898261439569515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3234754430531015252759353 2426065822898261439569515)
        ·
          refine ⟨3639098734347392159354273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426065822898261439569515 3639098734347392159354273)
          ·
            refine ⟨2729324050760544119515705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3639098734347392159354273 2729324050760544119515705)
            ·
              refine ⟨2046993038070408089636779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729324050760544119515705 2046993038070408089636779)
              ·
                refine ⟨3070489557105612134455169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046993038070408089636779 3070489557105612134455169)
                ·
                  refine ⟨2302867167829209100841377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070489557105612134455169 2302867167829209100841377)
                  ·
                    refine ⟨1727150375871906825631033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302867167829209100841377 1727150375871906825631033)
                    ·
                      refine ⟨1295362781903930119223275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727150375871906825631033 1295362781903930119223275)
                      ·
                        rfl

theorem cell23_2522710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2522710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522710 prefixEnd_2522710 := by exact prefixLift 2522710
  have htrace : WordTrace (prefixWord ++ tailWord_2522710) baseStart_2522710 baseEnd_2522710 := by
    simpa [prefixWord, tailWord_2522710, baseEnd_2522710] using wordTrace_append hprefix tailTrace_2522710
  have hstable : (prefixWord ++ tailWord_2522710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522710).length < 2 ^ (prefixWord ++ tailWord_2522710).sum := by decide
  have hdescent : baseEnd_2522710 < baseStart_2522710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522759 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 1, 4]
def baseStart_2522759 : Nat := 118140960795 + 2522759 * 2 ^ 59
def prefixEnd_2522759 : Nat := 4983230072969 + 3 ^ 40 * 2522759 * 2
def baseEnd_2522759 : Nat := 431795980818666809170183

theorem tailTrace_2522759 : CollatzResearch.WordTrace tailWord_2522759 prefixEnd_2522759 431795980818666809170183 := by
  unfold tailWord_2522759
  simp only [CollatzResearch.WordTrace]
  refine ⟨92012579867482470780355331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61341719911654980520236887 92012579867482470780355331)
  ·
    refine ⟨138018869801223706170532997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92012579867482470780355331 138018869801223706170532997)
    ·
      refine ⟨25878538087729444906974937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138018869801223706170532997 25878538087729444906974937)
      ·
        refine ⟨19408903565797083680231203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25878538087729444906974937 19408903565797083680231203)
        ·
          refine ⟨29113355348695625520346805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19408903565797083680231203 29113355348695625520346805)
          ·
            refine ⟨2729377063940214892532513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29113355348695625520346805 2729377063940214892532513)
            ·
              refine ⟨2047032797955161169399385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729377063940214892532513 2047032797955161169399385)
              ·
                refine ⟨1535274598466370877049539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047032797955161169399385 1535274598466370877049539)
                ·
                  refine ⟨2302911897699556315574309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535274598466370877049539 2302911897699556315574309)
                  ·
                    refine ⟨431795980818666809170183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2302911897699556315574309 431795980818666809170183)
                    ·
                      rfl

theorem cell23_2522759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_2522759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522759 prefixEnd_2522759 := by exact prefixLift 2522759
  have htrace : WordTrace (prefixWord ++ tailWord_2522759) baseStart_2522759 baseEnd_2522759 := by
    simpa [prefixWord, tailWord_2522759, baseEnd_2522759] using wordTrace_append hprefix tailTrace_2522759
  have hstable : (prefixWord ++ tailWord_2522759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522759).length < 2 ^ (prefixWord ++ tailWord_2522759).sum := by decide
  have hdescent : baseEnd_2522759 < baseStart_2522759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522771 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_2522771 : Nat := 118140960795 + 2522771 * 2 ^ 59
def prefixEnd_2522771 : Nat := 4983230072969 + 3 ^ 40 * 2522771 * 2
def baseEnd_2522771 : Nat := 1295394104223854380560493

theorem tailTrace_2522771 : CollatzResearch.WordTrace tailWord_2522771 prefixEnd_2522771 1295394104223854380560493 := by
  unfold tailWord_2522771
  simp only [CollatzResearch.WordTrace]
  refine ⟨92013017543438996829792167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61342011695625997886528111 92013017543438996829792167)
  ·
    refine ⟨138019526315158495244688251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92013017543438996829792167 138019526315158495244688251)
    ·
      refine ⟨207029289472737742867032377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138019526315158495244688251 207029289472737742867032377)
      ·
        refine ⟨155271967104553307150274283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207029289472737742867032377 155271967104553307150274283)
        ·
          refine ⟨232907950656829960725411425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155271967104553307150274283 232907950656829960725411425)
          ·
            refine ⟨174680962992622470544058569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232907950656829960725411425 174680962992622470544058569)
            ·
              refine ⟨131010722244466852908043927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174680962992622470544058569 131010722244466852908043927)
              ·
                refine ⟨196516083366700279362065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131010722244466852908043927 196516083366700279362065891)
                ·
                  refine ⟨294774125050050419043098837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196516083366700279362065891 294774125050050419043098837)
                  ·
                    refine ⟨6908768555860556696322629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 294774125050050419043098837 6908768555860556696322629)
                    ·
                      refine ⟨1295394104223854380560493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6908768555860556696322629 1295394104223854380560493)
                      ·
                        rfl

theorem cell23_2522771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_2522771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522771 prefixEnd_2522771 := by exact prefixLift 2522771
  have htrace : WordTrace (prefixWord ++ tailWord_2522771) baseStart_2522771 baseEnd_2522771 := by
    simpa [prefixWord, tailWord_2522771, baseEnd_2522771] using wordTrace_append hprefix tailTrace_2522771
  have hstable : (prefixWord ++ tailWord_2522771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522771).length < 2 ^ (prefixWord ++ tailWord_2522771).sum := by decide
  have hdescent : baseEnd_2522771 < baseStart_2522771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522782 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2522782 : Nat := 118140960795 + 2522782 * 2 ^ 59
def prefixEnd_2522782 : Nat := 4983230072969 + 3 ^ 40 * 2522782 * 2
def baseEnd_2522782 : Nat := 1295399752511053837522943

theorem tailTrace_2522782 : CollatzResearch.WordTrace tailWord_2522782 prefixEnd_2522782 1295399752511053837522943 := by
  unfold tailWord_2522782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501677343299893213555325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61342279164266097138961733 11501677343299893213555325)
  ·
    refine ⟨4313129003737459955083247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11501677343299893213555325 4313129003737459955083247)
    ·
      refine ⟨6469693505606189932624871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313129003737459955083247 6469693505606189932624871)
      ·
        refine ⟨9704540258409284898937307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469693505606189932624871 9704540258409284898937307)
        ·
          refine ⟨14556810387613927348405961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704540258409284898937307 14556810387613927348405961)
          ·
            refine ⟨10917607790710445511304471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14556810387613927348405961 10917607790710445511304471)
            ·
              refine ⟨16376411686065668266956707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10917607790710445511304471 16376411686065668266956707)
              ·
                refine ⟨24564617529098502400435061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16376411686065668266956707 24564617529098502400435061)
                ·
                  refine ⟨2302932893352984600040787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24564617529098502400435061 2302932893352984600040787)
                  ·
                    refine ⟨3454399340029476900061181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302932893352984600040787 3454399340029476900061181)
                    ·
                      refine ⟨1295399752511053837522943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454399340029476900061181 1295399752511053837522943)
                      ·
                        rfl

theorem cell23_2522782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2522782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522782 prefixEnd_2522782 := by exact prefixLift 2522782
  have htrace : WordTrace (prefixWord ++ tailWord_2522782) baseStart_2522782 baseEnd_2522782 := by
    simpa [prefixWord, tailWord_2522782, baseEnd_2522782] using wordTrace_append hprefix tailTrace_2522782
  have hstable : (prefixWord ++ tailWord_2522782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522782).length < 2 ^ (prefixWord ++ tailWord_2522782).sum := by decide
  have hdescent : baseEnd_2522782 < baseStart_2522782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522786 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2522786 : Nat := 118140960795 + 2522786 * 2 ^ 59
def prefixEnd_2522786 : Nat := 4983230072969 + 3 ^ 40 * 2522786 * 2
def baseEnd_2522786 : Nat := 1295401806433671821872925

theorem tailTrace_2522786 : CollatzResearch.WordTrace tailWord_2522786 prefixEnd_2522786 1295401806433671821872925 := by
  unfold tailWord_2522786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003391159596163597897053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61342376425589769594392141 23003391159596163597897053)
  ·
    refine ⟨8626271684848561349211395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23003391159596163597897053 8626271684848561349211395)
    ·
      refine ⟨12939407527272842023817093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626271684848561349211395 12939407527272842023817093)
      ·
        refine ⟨2426138911363657879465705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12939407527272842023817093 2426138911363657879465705)
        ·
          refine ⟨1819604183522743409599279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426138911363657879465705 1819604183522743409599279)
          ·
            refine ⟨2729406275284115114398919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819604183522743409599279 2729406275284115114398919)
            ·
              refine ⟨4094109412926172671598379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729406275284115114398919 4094109412926172671598379)
              ·
                refine ⟨6141164119389259007397569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094109412926172671598379 6141164119389259007397569)
                ·
                  refine ⟨4605873089541944255548177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141164119389259007397569 4605873089541944255548177)
                  ·
                    refine ⟨3454404817156458191661133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4605873089541944255548177 3454404817156458191661133)
                    ·
                      refine ⟨1295401806433671821872925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454404817156458191661133 1295401806433671821872925)
                      ·
                        rfl

theorem cell23_2522786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2522786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522786 prefixEnd_2522786 := by exact prefixLift 2522786
  have htrace : WordTrace (prefixWord ++ tailWord_2522786) baseStart_2522786 baseEnd_2522786 := by
    simpa [prefixWord, tailWord_2522786, baseEnd_2522786] using wordTrace_append hprefix tailTrace_2522786
  have hstable : (prefixWord ++ tailWord_2522786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522786).length < 2 ^ (prefixWord ++ tailWord_2522786).sum := by decide
  have hdescent : baseEnd_2522786 < baseStart_2522786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522842 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2522842 : Nat := 118140960795 + 2522842 * 2 ^ 59
def prefixEnd_2522842 : Nat := 4983230072969 + 3 ^ 40 * 2522842 * 2
def baseEnd_2522842 : Nat := 1295430561350323602772667

theorem tailTrace_2522842 : CollatzResearch.WordTrace tailWord_2522842 prefixEnd_2522842 1295430561350323602772667 := by
  unfold tailWord_2522842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003901781545443988906695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61343738084121183970417853 23003901781545443988906695)
  ·
    refine ⟨34505852672318165983360043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23003901781545443988906695 34505852672318165983360043)
    ·
      refine ⟨51758779008477248975040065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34505852672318165983360043 51758779008477248975040065)
      ·
        refine ⟨38819084256357936731280049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51758779008477248975040065 38819084256357936731280049)
        ·
          refine ⟨29114313192268452548460037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38819084256357936731280049 29114313192268452548460037)
          ·
            refine ⟨5458933723550334852836257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29114313192268452548460037 5458933723550334852836257)
            ·
              refine ⟨4094200292662751139627193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458933723550334852836257 4094200292662751139627193)
              ·
                refine ⟨3070650219497063354720395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4094200292662751139627193 3070650219497063354720395)
                ·
                  refine ⟨4605975329245595032080593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070650219497063354720395 4605975329245595032080593)
                  ·
                    refine ⟨3454481496934196274060445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4605975329245595032080593 3454481496934196274060445)
                    ·
                      refine ⟨1295430561350323602772667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454481496934196274060445 1295430561350323602772667)
                      ·
                        rfl

theorem cell23_2522842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2522842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522842 prefixEnd_2522842 := by exact prefixLift 2522842
  have htrace : WordTrace (prefixWord ++ tailWord_2522842) baseStart_2522842 baseEnd_2522842 := by
    simpa [prefixWord, tailWord_2522842, baseEnd_2522842] using wordTrace_append hprefix tailTrace_2522842
  have hstable : (prefixWord ++ tailWord_2522842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522842).length < 2 ^ (prefixWord ++ tailWord_2522842).sum := by decide
  have hdescent : baseEnd_2522842 < baseStart_2522842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522856 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2522856 : Nat := 118140960795 + 2522856 * 2 ^ 59
def prefixEnd_2522856 : Nat := 4983230072969 + 3 ^ 40 * 2522856 * 2
def baseEnd_2522856 : Nat := 1295437750079486547997603

theorem tailTrace_2522856 : CollatzResearch.WordTrace tailWord_2522856 prefixEnd_2522856 1295437750079486547997603 := by
  unfold tailWord_2522856
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008058874065528173318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61344078498754037564424281 46008058874065528173318211)
  ·
    refine ⟨69012088311098292259977317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46008058874065528173318211 69012088311098292259977317)
    ·
      refine ⟨12939766558330929798745747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69012088311098292259977317 12939766558330929798745747)
      ·
        refine ⟨19409649837496394698118621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12939766558330929798745747 19409649837496394698118621)
        ·
          refine ⟨7278618689061148011794483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19409649837496394698118621 7278618689061148011794483)
          ·
            refine ⟨10917928033591722017691725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7278618689061148011794483 10917928033591722017691725)
            ·
              refine ⟨4094223012596895756634397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10917928033591722017691725 4094223012596895756634397)
              ·
                refine ⟨1535333629723835908737899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4094223012596895756634397 1535333629723835908737899)
                ·
                  refine ⟨2303000444585753863106849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535333629723835908737899 2303000444585753863106849)
                  ·
                    refine ⟨1727250333439315397330137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2303000444585753863106849 1727250333439315397330137)
                    ·
                      refine ⟨1295437750079486547997603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727250333439315397330137 1295437750079486547997603)
                      ·
                        rfl

theorem cell23_2522856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2522856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522856 prefixEnd_2522856 := by exact prefixLift 2522856
  have htrace : WordTrace (prefixWord ++ tailWord_2522856) baseStart_2522856 baseEnd_2522856 := by
    simpa [prefixWord, tailWord_2522856, baseEnd_2522856] using wordTrace_append hprefix tailTrace_2522856
  have hstable : (prefixWord ++ tailWord_2522856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522856).length < 2 ^ (prefixWord ++ tailWord_2522856).sum := by decide
  have hdescent : baseEnd_2522856 < baseStart_2522856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522888 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2522888 : Nat := 118140960795 + 2522888 * 2 ^ 59
def prefixEnd_2522888 : Nat := 4983230072969 + 3 ^ 40 * 2522888 * 2
def baseEnd_2522888 : Nat := 431818060486810140932485

theorem tailTrace_2522888 : CollatzResearch.WordTrace tailWord_2522888 prefixEnd_2522888 431818060486810140932485 := by
  unfold tailWord_2522888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008642442007562905900659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61344856589343417207867545 46008642442007562905900659)
  ·
    refine ⟨69012963663011344358850989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46008642442007562905900659 69012963663011344358850989)
    ·
      refine ⟨25879861373629254134569121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69012963663011344358850989 25879861373629254134569121)
      ·
        refine ⟨19409896030221940600926841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25879861373629254134569121 19409896030221940600926841)
        ·
          refine ⟨14557422022666455450695131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19409896030221940600926841 14557422022666455450695131)
          ·
            refine ⟨21836133033999683176042697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14557422022666455450695131 21836133033999683176042697)
            ·
              refine ⟨16377099775499762382032023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21836133033999683176042697 16377099775499762382032023)
              ·
                refine ⟨24565649663249643573048035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16377099775499762382032023 24565649663249643573048035)
                ·
                  refine ⟨36848474494874465359572053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24565649663249643573048035 36848474494874465359572053)
                  ·
                    refine ⟨431818060486810140932485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36848474494874465359572053 431818060486810140932485)
                    ·
                      rfl

theorem cell23_2522888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2522888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522888 prefixEnd_2522888 := by exact prefixLift 2522888
  have htrace : WordTrace (prefixWord ++ tailWord_2522888) baseStart_2522888 baseEnd_2522888 := by
    simpa [prefixWord, tailWord_2522888, baseEnd_2522888] using wordTrace_append hprefix tailTrace_2522888
  have hstable : (prefixWord ++ tailWord_2522888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522888).length < 2 ^ (prefixWord ++ tailWord_2522888).sum := by decide
  have hdescent : baseEnd_2522888 < baseStart_2522888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522893 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2522893 : Nat := 118140960795 + 2522893 * 2 ^ 59
def prefixEnd_2522893 : Nat := 4983230072969 + 3 ^ 40 * 2522893 * 2
def baseEnd_2522893 : Nat := 1295456748863702903234933

theorem tailTrace_2522893 : CollatzResearch.WordTrace tailWord_2522893 prefixEnd_2522893 1295456748863702903234933 := by
  unfold tailWord_2522893
  simp only [CollatzResearch.WordTrace]
  refine ⟨92017467248997011665733333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61344978165998007777155555 92017467248997011665733333)
  ·
    refine ⟨2156659388648367460915625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92017467248997011665733333 2156659388648367460915625)
    ·
      refine ⟨1617494541486275595686719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2156659388648367460915625 1617494541486275595686719)
      ·
        refine ⟨2426241812229413393530079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617494541486275595686719 2426241812229413393530079)
        ·
          refine ⟨3639362718344120090295119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426241812229413393530079 3639362718344120090295119)
          ·
            refine ⟨5459044077516180135442679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639362718344120090295119 5459044077516180135442679)
            ·
              refine ⟨8188566116274270203164019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459044077516180135442679 8188566116274270203164019)
              ·
                refine ⟨12282849174411405304746029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188566116274270203164019 12282849174411405304746029)
                ·
                  refine ⟨4606068440404276989279761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12282849174411405304746029 4606068440404276989279761)
                  ·
                    refine ⟨3454551330303207741959821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606068440404276989279761 3454551330303207741959821)
                    ·
                      refine ⟨1295456748863702903234933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454551330303207741959821 1295456748863702903234933)
                      ·
                        rfl

theorem cell23_2522893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2522893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522893 prefixEnd_2522893 := by exact prefixLift 2522893
  have htrace : WordTrace (prefixWord ++ tailWord_2522893) baseStart_2522893 baseEnd_2522893 := by
    simpa [prefixWord, tailWord_2522893, baseEnd_2522893] using wordTrace_append hprefix tailTrace_2522893
  have hstable : (prefixWord ++ tailWord_2522893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522893).length < 2 ^ (prefixWord ++ tailWord_2522893).sum := by decide
  have hdescent : baseEnd_2522893 < baseStart_2522893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522912 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2522912 : Nat := 118140960795 + 2522912 * 2 ^ 59
def prefixEnd_2522912 : Nat := 4983230072969 + 3 ^ 40 * 2522912 * 2
def baseEnd_2522912 : Nat := 1295466504996138328897345

theorem tailTrace_2522912 : CollatzResearch.WordTrace tailWord_2522912 prefixEnd_2522912 1295466504996138328897345 := by
  unfold tailWord_2522912
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009080117964088955337495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61345440157285451940449993 46009080117964088955337495)
  ·
    refine ⟨69013620176946133433006243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46009080117964088955337495 69013620176946133433006243)
    ·
      refine ⟨103520430265419200149509365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69013620176946133433006243 103520430265419200149509365)
      ·
        refine ⟨9705040337383050014016503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103520430265419200149509365 9705040337383050014016503)
        ·
          refine ⟨14557560506074575021024755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9705040337383050014016503 14557560506074575021024755)
          ·
            refine ⟨21836340759111862531537133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14557560506074575021024755 21836340759111862531537133)
            ·
              refine ⟨8188627784666948449326425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21836340759111862531537133 8188627784666948449326425)
              ·
                refine ⟨6141470838500211336994819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188627784666948449326425 6141470838500211336994819)
                ·
                  refine ⟨9212206257750317005492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141470838500211336994819 9212206257750317005492229)
                  ·
                    refine ⟨1727288673328184438529793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9212206257750317005492229 1727288673328184438529793)
                    ·
                      refine ⟨1295466504996138328897345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727288673328184438529793 1295466504996138328897345)
                      ·
                        rfl

theorem cell23_2522912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2522912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522912 prefixEnd_2522912 := by exact prefixLift 2522912
  have htrace : WordTrace (prefixWord ++ tailWord_2522912) baseStart_2522912 baseEnd_2522912 := by
    simpa [prefixWord, tailWord_2522912, baseEnd_2522912] using wordTrace_append hprefix tailTrace_2522912
  have hstable : (prefixWord ++ tailWord_2522912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522912).length < 2 ^ (prefixWord ++ tailWord_2522912).sum := by decide
  have hdescent : baseEnd_2522912 < baseStart_2522912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522916 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_2522916 : Nat := 118140960795 + 2522916 * 2 ^ 59
def prefixEnd_2522916 : Nat := 4983230072969 + 3 ^ 40 * 2522916 * 2
def baseEnd_2522916 : Nat := 1295468558918756313247327

theorem tailTrace_2522916 : CollatzResearch.WordTrace tailWord_2522916 prefixEnd_2522916 1295468558918756313247327 := by
  unfold tailWord_2522916
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009153063956843296910301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61345537418609124395880401 46009153063956843296910301)
  ·
    refine ⟨17253432398983816236341363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46009153063956843296910301 17253432398983816236341363)
    ·
      refine ⟨25880148598475724354512045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17253432398983816236341363 25880148598475724354512045)
      ·
        refine ⟨9705055724428396632942017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25880148598475724354512045 9705055724428396632942017)
        ·
          refine ⟨7278791793321297474706513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9705055724428396632942017 7278791793321297474706513)
          ·
            refine ⟨5459093844990973106029885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278791793321297474706513 5459093844990973106029885)
            ·
              refine ⟨2047160191871614914761207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5459093844990973106029885 2047160191871614914761207)
              ·
                refine ⟨3070740287807422372141811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047160191871614914761207 3070740287807422372141811)
                ·
                  refine ⟨4606110431711133558212717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070740287807422372141811 4606110431711133558212717)
                  ·
                    refine ⟨1727291411891675084329769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4606110431711133558212717 1727291411891675084329769)
                    ·
                      refine ⟨1295468558918756313247327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727291411891675084329769 1295468558918756313247327)
                      ·
                        rfl

theorem cell23_2522916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_2522916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522916 prefixEnd_2522916 := by exact prefixLift 2522916
  have htrace : WordTrace (prefixWord ++ tailWord_2522916) baseStart_2522916 baseEnd_2522916 := by
    simpa [prefixWord, tailWord_2522916, baseEnd_2522916] using wordTrace_append hprefix tailTrace_2522916
  have hstable : (prefixWord ++ tailWord_2522916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522916).length < 2 ^ (prefixWord ++ tailWord_2522916).sum := by decide
  have hdescent : baseEnd_2522916 < baseStart_2522916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522929 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_2522929 : Nat := 118140960795 + 2522929 * 2 ^ 59
def prefixEnd_2522929 : Nat := 4983230072969 + 3 ^ 40 * 2522929 * 2
def baseEnd_2522929 : Nat := 1295475234167264762384767

theorem tailTrace_2522929 : CollatzResearch.WordTrace tailWord_2522929 prefixEnd_2522929 1295475234167264762384767 := by
  unfold tailWord_2522929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92018780276866589814043841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61345853517911059876029227 92018780276866589814043841)
  ·
    refine ⟨69014085207649942360532881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92018780276866589814043841 69014085207649942360532881)
    ·
      refine ⟨51760563905737456770399661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69014085207649942360532881 51760563905737456770399661)
      ·
        refine ⟨19410211464651546288899873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51760563905737456770399661 19410211464651546288899873)
        ·
          refine ⟨14557658598488659716674905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19410211464651546288899873 14557658598488659716674905)
          ·
            refine ⟨10918243948866494787506179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14557658598488659716674905 10918243948866494787506179)
            ·
              refine ⟨16377365923299742181259269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10918243948866494787506179 16377365923299742181259269)
              ·
                refine ⟨3070756110618701658986113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16377365923299742181259269 3070756110618701658986113)
                ·
                  refine ⟨2303067082964026244239585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070756110618701658986113 2303067082964026244239585)
                  ·
                    refine ⟨1727300312223019683179689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2303067082964026244239585 1727300312223019683179689)
                    ·
                      refine ⟨1295475234167264762384767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727300312223019683179689 1295475234167264762384767)
                      ·
                        rfl

theorem cell23_2522929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_2522929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522929 prefixEnd_2522929 := by exact prefixLift 2522929
  have htrace : WordTrace (prefixWord ++ tailWord_2522929) baseStart_2522929 baseEnd_2522929 := by
    simpa [prefixWord, tailWord_2522929, baseEnd_2522929] using wordTrace_append hprefix tailTrace_2522929
  have hstable : (prefixWord ++ tailWord_2522929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522929).length < 2 ^ (prefixWord ++ tailWord_2522929).sum := by decide
  have hdescent : baseEnd_2522929 < baseStart_2522929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522932 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2522932 : Nat := 118140960795 + 2522932 * 2 ^ 59
def prefixEnd_2522932 : Nat := 4983230072969 + 3 ^ 40 * 2522932 * 2
def baseEnd_2522932 : Nat := 1295476774609228250647253

theorem tailTrace_2522932 : CollatzResearch.WordTrace tailWord_2522932 prefixEnd_2522932 1295476774609228250647253 := by
  unfold tailWord_2522932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009444847927860663201525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61345926463903814217602033 46009444847927860663201525)
  ·
    refine ⟨4313385454493236937175143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46009444847927860663201525 4313385454493236937175143)
    ·
      refine ⟨6470078181739855405762715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313385454493236937175143 6470078181739855405762715)
      ·
        refine ⟨9705117272609783108644073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6470078181739855405762715 9705117272609783108644073)
        ·
          refine ⟨7278837954457337331483055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9705117272609783108644073 7278837954457337331483055)
          ·
            refine ⟨10918256931686005997224583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7278837954457337331483055 10918256931686005997224583)
            ·
              refine ⟨16377385397529008995836875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10918256931686005997224583 16377385397529008995836875)
              ·
                refine ⟨24566078096293513493755313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16377385397529008995836875 24566078096293513493755313)
                ·
                  refine ⟨18424558572220135120316485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24566078096293513493755313 18424558572220135120316485)
                  ·
                    refine ⟨3454604732291275335059341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18424558572220135120316485 3454604732291275335059341)
                    ·
                      refine ⟨1295476774609228250647253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454604732291275335059341 1295476774609228250647253)
                      ·
                        rfl

theorem cell23_2522932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2522932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522932 prefixEnd_2522932 := by exact prefixLift 2522932
  have htrace : WordTrace (prefixWord ++ tailWord_2522932) baseStart_2522932 baseEnd_2522932 := by
    simpa [prefixWord, tailWord_2522932, baseEnd_2522932] using wordTrace_append hprefix tailTrace_2522932
  have hstable : (prefixWord ++ tailWord_2522932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522932).length < 2 ^ (prefixWord ++ tailWord_2522932).sum := by decide
  have hdescent : baseEnd_2522932 < baseStart_2522932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522942 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2522942 : Nat := 118140960795 + 2522942 * 2 ^ 59
def prefixEnd_2522942 : Nat := 4983230072969 + 3 ^ 40 * 2522942 * 2
def baseEnd_2522942 : Nat := 1295481909415773211522207

theorem tailTrace_2522942 : CollatzResearch.WordTrace tailWord_2522942 prefixEnd_2522942 1295481909415773211522207 := by
  unfold tailWord_2522942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502406803227436629283385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61346169617212995356178053 11502406803227436629283385)
  ·
    refine ⟨8626805102420577471962539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11502406803227436629283385 8626805102420577471962539)
    ·
      refine ⟨12940207653630866207943809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626805102420577471962539 12940207653630866207943809)
      ·
        refine ⟨9705155740223149655957857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12940207653630866207943809 9705155740223149655957857)
        ·
          refine ⟨7278866805167362241968393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9705155740223149655957857 7278866805167362241968393)
          ·
            refine ⟨5459150103875521681476295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278866805167362241968393 5459150103875521681476295)
            ·
              refine ⟨8188725155813282522214443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459150103875521681476295 8188725155813282522214443)
              ·
                refine ⟨12283087733719923783321665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188725155813282522214443 12283087733719923783321665)
                ·
                  refine ⟨9212315800289942837491249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12283087733719923783321665 9212315800289942837491249)
                  ·
                    refine ⟨6909236850217457128118437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9212315800289942837491249 6909236850217457128118437)
                    ·
                      refine ⟨1295481909415773211522207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6909236850217457128118437 1295481909415773211522207)
                      ·
                        rfl

theorem cell23_2522942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2522942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522942 prefixEnd_2522942 := by exact prefixLift 2522942
  have htrace : WordTrace (prefixWord ++ tailWord_2522942) baseStart_2522942 baseEnd_2522942 := by
    simpa [prefixWord, tailWord_2522942, baseEnd_2522942] using wordTrace_append hprefix tailTrace_2522942
  have hstable : (prefixWord ++ tailWord_2522942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522942).length < 2 ^ (prefixWord ++ tailWord_2522942).sum := by decide
  have hdescent : baseEnd_2522942 < baseStart_2522942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522965 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2522965 : Nat := 118140960795 + 2522965 * 2 ^ 59
def prefixEnd_2522965 : Nat := 4983230072969 + 3 ^ 40 * 2522965 * 2
def baseEnd_2522965 : Nat := 431831239823608873844867

theorem tailTrace_2522965 : CollatzResearch.WordTrace tailWord_2522965 prefixEnd_2522965 431831239823608873844867 := by
  unfold tailWord_2522965
  simp only [CollatzResearch.WordTrace]
  refine ⟨92020093304736167962354349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61346728869824111974902899 92020093304736167962354349)
  ·
    refine ⟨34507534989276062985882881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92020093304736167962354349 34507534989276062985882881)
    ·
      refine ⟨25880651241957047239412161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34507534989276062985882881 25880651241957047239412161)
      ·
        refine ⟨19410488431467785429559121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25880651241957047239412161 19410488431467785429559121)
        ·
          refine ⟨14557866323600839072169341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19410488431467785429559121 14557866323600839072169341)
          ·
            refine ⟨5459199871350314652063503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14557866323600839072169341 5459199871350314652063503)
            ·
              refine ⟨8188799807025471978095255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459199871350314652063503 8188799807025471978095255)
              ·
                refine ⟨12283199710538207967142883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188799807025471978095255 12283199710538207967142883)
                ·
                  refine ⟨18424799565807311950714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12283199710538207967142883 18424799565807311950714325)
                  ·
                    refine ⟨431831239823608873844867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18424799565807311950714325 431831239823608873844867)
                    ·
                      rfl

theorem cell23_2522965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2522965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522965 prefixEnd_2522965 := by exact prefixLift 2522965
  have htrace : WordTrace (prefixWord ++ tailWord_2522965) baseStart_2522965 baseEnd_2522965 := by
    simpa [prefixWord, tailWord_2522965, baseEnd_2522965] using wordTrace_append hprefix tailTrace_2522965
  have hstable : (prefixWord ++ tailWord_2522965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522965).length < 2 ^ (prefixWord ++ tailWord_2522965).sum := by decide
  have hdescent : baseEnd_2522965 < baseStart_2522965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522985 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_2522985 : Nat := 118140960795 + 2522985 * 2 ^ 59
def prefixEnd_2522985 : Nat := 4983230072969 + 3 ^ 40 * 2522985 * 2
def baseEnd_2522985 : Nat := 1295503989083916543284509

theorem tailTrace_2522985 : CollatzResearch.WordTrace tailWord_2522985 prefixEnd_2522985 1295503989083916543284509 := by
  unfold tailWord_2522985
  simp only [CollatzResearch.WordTrace]
  refine ⟨92020822764663711378082409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61347215176442474252054939 92020822764663711378082409)
  ·
    refine ⟨69015617073497783533561807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92020822764663711378082409 69015617073497783533561807)
    ·
      refine ⟨103523425610246675300342711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69015617073497783533561807 103523425610246675300342711)
      ·
        refine ⟨155285138415370012950514067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103523425610246675300342711 155285138415370012950514067)
        ·
          refine ⟨232927707623055019425771101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155285138415370012950514067 232927707623055019425771101)
          ·
            refine ⟨87347890358645632284664163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232927707623055019425771101 87347890358645632284664163)
            ·
              refine ⟨131021835537968448426996245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87347890358645632284664163 131021835537968448426996245)
              ·
                refine ⟨6141648540842271020015449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131021835537968448426996245 6141648540842271020015449)
                ·
                  refine ⟨4606236405631703265011587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141648540842271020015449 4606236405631703265011587)
                  ·
                    refine ⟨6909354608447554897517381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4606236405631703265011587 6909354608447554897517381)
                    ·
                      refine ⟨1295503989083916543284509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6909354608447554897517381 1295503989083916543284509)
                      ·
                        rfl

theorem cell23_2522985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_2522985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2522985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2522985 prefixEnd_2522985 := by exact prefixLift 2522985
  have htrace : WordTrace (prefixWord ++ tailWord_2522985) baseStart_2522985 baseEnd_2522985 := by
    simpa [prefixWord, tailWord_2522985, baseEnd_2522985] using wordTrace_append hprefix tailTrace_2522985
  have hstable : (prefixWord ++ tailWord_2522985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522985).length < 2 ^ (prefixWord ++ tailWord_2522985).sum := by decide
  have hdescent : baseEnd_2522985 < baseStart_2522985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523002 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_2523002 : Nat := 118140960795 + 2523002 * 2 ^ 59
def prefixEnd_2523002 : Nat := 4983230072969 + 3 ^ 40 * 2523002 * 2
def baseEnd_2523002 : Nat := 1295512718255042976771931

theorem tailTrace_2523002 : CollatzResearch.WordTrace tailWord_2523002 prefixEnd_2523002 1295512718255042976771931 := by
  unfold tailWord_2523002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23005360701400530820362815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61347628537068082187634173 23005360701400530820362815)
  ·
    refine ⟨34508041052100796230544223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23005360701400530820362815 34508041052100796230544223)
    ·
      refine ⟨51762061578151194345816335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34508041052100796230544223 51762061578151194345816335)
      ·
        refine ⟨77643092367226791518724503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51762061578151194345816335 77643092367226791518724503)
        ·
          refine ⟨116464638550840187278086755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77643092367226791518724503 116464638550840187278086755)
          ·
            refine ⟨174696957826260280917130133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116464638550840187278086755 174696957826260280917130133)
            ·
              refine ⟨8188919898105950667990475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174696957826260280917130133 8188919898105950667990475)
              ·
                refine ⟨12283379847158926001985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188919898105950667990475 12283379847158926001985713)
                ·
                  refine ⟨9212534885369194501489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12283379847158926001985713 9212534885369194501489285)
                  ·
                    refine ⟨1727350291006723969029241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9212534885369194501489285 1727350291006723969029241)
                    ·
                      refine ⟨1295512718255042976771931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727350291006723969029241 1295512718255042976771931)
                      ·
                        rfl

theorem cell23_2523002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_2523002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523002 prefixEnd_2523002 := by exact prefixLift 2523002
  have htrace : WordTrace (prefixWord ++ tailWord_2523002) baseStart_2523002 baseEnd_2523002 := by
    simpa [prefixWord, tailWord_2523002, baseEnd_2523002] using wordTrace_append hprefix tailTrace_2523002
  have hstable : (prefixWord ++ tailWord_2523002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523002).length < 2 ^ (prefixWord ++ tailWord_2523002).sum := by decide
  have hdescent : baseEnd_2523002 < baseStart_2523002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523012 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_2523012 : Nat := 118140960795 + 2523012 * 2 ^ 59
def prefixEnd_2523012 : Nat := 4983230072969 + 3 ^ 40 * 2523012 * 2
def baseEnd_2523012 : Nat := 431839284353862645882295

theorem tailTrace_2523012 : CollatzResearch.WordTrace tailWord_2523012 prefixEnd_2523012 431839284353862645882295 := by
  unfold tailWord_2523012
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010903767782947494657645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61347871690377263326210193 46010903767782947494657645)
  ·
    refine ⟨17254088912918605310496617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46010903767782947494657645 17254088912918605310496617)
    ·
      refine ⟨12940566684688953982872463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17254088912918605310496617 12940566684688953982872463)
      ·
        refine ⟨19410850027033430974308695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940566684688953982872463 19410850027033430974308695)
        ·
          refine ⟨29116275040550146461463043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19410850027033430974308695 29116275040550146461463043)
          ·
            refine ⟨43674412560825219692194565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116275040550146461463043 43674412560825219692194565)
            ·
              refine ⟨8188952355154728692286481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43674412560825219692194565 8188952355154728692286481)
              ·
                refine ⟨6141714266366046519214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188952355154728692286481 6141714266366046519214861)
                ·
                  refine ⟨2303142849887267444705573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6141714266366046519214861 2303142849887267444705573)
                  ·
                    refine ⟨431839284353862645882295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303142849887267444705573 431839284353862645882295)
                    ·
                      rfl

theorem cell23_2523012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_2523012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523012 prefixEnd_2523012 := by exact prefixLift 2523012
  have htrace : WordTrace (prefixWord ++ tailWord_2523012) baseStart_2523012 baseEnd_2523012 := by
    simpa [prefixWord, tailWord_2523012, baseEnd_2523012] using wordTrace_append hprefix tailTrace_2523012
  have hstable : (prefixWord ++ tailWord_2523012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523012).length < 2 ^ (prefixWord ++ tailWord_2523012).sum := by decide
  have hdescent : baseEnd_2523012 < baseStart_2523012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523039 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2523039 : Nat := 118140960795 + 2523039 * 2 ^ 59
def prefixEnd_2523039 : Nat := 4983230072969 + 3 ^ 40 * 2523039 * 2
def baseEnd_2523039 : Nat := 1295531717039259332009261

theorem tailTrace_2523039 : CollatzResearch.WordTrace tailWord_2523039 prefixEnd_2523039 1295531717039259332009261 := by
  unfold tailWord_2523039
  simp only [CollatzResearch.WordTrace]
  refine ⟨92022792306468078600548171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61348528204312052400365447 92022792306468078600548171)
  ·
    refine ⟨138034188459702117900822257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92022792306468078600548171 138034188459702117900822257)
    ·
      refine ⟨103525641344776588425616693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138034188459702117900822257 103525641344776588425616693)
      ·
        refine ⟨9705528876072805164901565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103525641344776588425616693 9705528876072805164901565)
        ·
          refine ⟨3639573328527301936838087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9705528876072805164901565 3639573328527301936838087)
          ·
            refine ⟨5459359992790952905257131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639573328527301936838087 5459359992790952905257131)
            ·
              refine ⟨8189039989186429357885697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459359992790952905257131 8189039989186429357885697)
              ·
                refine ⟨6141779991889822018414273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189039989186429357885697 6141779991889822018414273)
                ·
                  refine ⟨4606334993917366513810705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141779991889822018414273 4606334993917366513810705)
                  ·
                    refine ⟨3454751245438024885358029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606334993917366513810705 3454751245438024885358029)
                    ·
                      refine ⟨1295531717039259332009261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454751245438024885358029 1295531717039259332009261)
                      ·
                        rfl

theorem cell23_2523039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2523039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523039 prefixEnd_2523039 := by exact prefixLift 2523039
  have htrace : WordTrace (prefixWord ++ tailWord_2523039) baseStart_2523039 baseEnd_2523039 := by
    simpa [prefixWord, tailWord_2523039, baseEnd_2523039] using wordTrace_append hprefix tailTrace_2523039
  have hstable : (prefixWord ++ tailWord_2523039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523039).length < 2 ^ (prefixWord ++ tailWord_2523039).sum := by decide
  have hdescent : baseEnd_2523039 < baseStart_2523039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523055 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 3, 5]
def baseStart_2523055 : Nat := 118140960795 + 2523055 * 2 ^ 59
def prefixEnd_2523055 : Nat := 4983230072969 + 3 ^ 40 * 2523055 * 2
def baseEnd_2523055 : Nat := 431846644243243756469729

theorem tailTrace_2523055 : CollatzResearch.WordTrace tailWord_2523055 prefixEnd_2523055 431846644243243756469729 := by
  unfold tailWord_2523055
  simp only [CollatzResearch.WordTrace]
  refine ⟨92023375874410113333130619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61348917249606742222087079 92023375874410113333130619)
  ·
    refine ⟨138035063811615169999695929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92023375874410113333130619 138035063811615169999695929)
    ·
      refine ⟨103526297858711377499771947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138035063811615169999695929 103526297858711377499771947)
      ·
        refine ⟨155289446788067066249657921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103526297858711377499771947 155289446788067066249657921)
        ·
          refine ⟨116467085091050299687243441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155289446788067066249657921 116467085091050299687243441)
          ·
            refine ⟨87350313818287724765432581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116467085091050299687243441 87350313818287724765432581)
            ·
              refine ⟨16378183840928948393518609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87350313818287724765432581 16378183840928948393518609)
              ·
                refine ⟨12283637880696711295138957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16378183840928948393518609 12283637880696711295138957)
                ·
                  refine ⟨4606364205261266735677109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12283637880696711295138957 4606364205261266735677109)
                  ·
                    refine ⟨431846644243243756469729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606364205261266735677109 431846644243243756469729)
                    ·
                      rfl

theorem cell23_2523055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_2523055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523055 prefixEnd_2523055 := by exact prefixLift 2523055
  have htrace : WordTrace (prefixWord ++ tailWord_2523055) baseStart_2523055 baseEnd_2523055 := by
    simpa [prefixWord, tailWord_2523055, baseEnd_2523055] using wordTrace_append hprefix tailTrace_2523055
  have hstable : (prefixWord ++ tailWord_2523055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523055).length < 2 ^ (prefixWord ++ tailWord_2523055).sum := by decide
  have hdescent : baseEnd_2523055 < baseStart_2523055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523086 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_2523086 : Nat := 118140960795 + 2523086 * 2 ^ 59
def prefixEnd_2523086 : Nat := 4983230072969 + 3 ^ 40 * 2523086 * 2
def baseEnd_2523086 : Nat := 1295555850630020648121545

theorem tailTrace_2523086 : CollatzResearch.WordTrace tailWord_2523086 prefixEnd_2523086 1295555850630020648121545 := by
  unfold tailWord_2523086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11503063317162225703438639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61349671024865203751672741 11503063317162225703438639)
  ·
    refine ⟨17254594975743338555157959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11503063317162225703438639 17254594975743338555157959)
    ·
      refine ⟨25881892463615007832736939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17254594975743338555157959 25881892463615007832736939)
      ·
        refine ⟨38822838695422511749105409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25881892463615007832736939 38822838695422511749105409)
        ·
          refine ⟨29117129021566883811829057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38822838695422511749105409 29117129021566883811829057)
          ·
            refine ⟨21837846766175162858871793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29117129021566883811829057 21837846766175162858871793)
            ·
              refine ⟨16378385074631372144153845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21837846766175162858871793 16378385074631372144153845)
              ·
                refine ⟨1535473600746691138514423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16378385074631372144153845 1535473600746691138514423)
                ·
                  refine ⟨2303210401120036707771635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535473600746691138514423 2303210401120036707771635)
                  ·
                    refine ⟨3454815601680055061657453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2303210401120036707771635 3454815601680055061657453)
                    ·
                      refine ⟨1295555850630020648121545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454815601680055061657453 1295555850630020648121545)
                      ·
                        rfl

theorem cell23_2523086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_2523086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523086 prefixEnd_2523086 := by exact prefixLift 2523086
  have htrace : WordTrace (prefixWord ++ tailWord_2523086) baseStart_2523086 baseEnd_2523086 := by
    simpa [prefixWord, tailWord_2523086, baseEnd_2523086] using wordTrace_append hprefix tailTrace_2523086
  have hstable : (prefixWord ++ tailWord_2523086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523086).length < 2 ^ (prefixWord ++ tailWord_2523086).sum := by decide
  have hdescent : baseEnd_2523086 < baseStart_2523086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523103 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 1, 1, 3]
def baseStart_2523103 : Nat := 118140960795 + 2523103 * 2 ^ 59
def prefixEnd_2523103 : Nat := 4983230072969 + 3 ^ 40 * 2523103 * 2
def baseEnd_2523103 : Nat := 1295564579801147081608967

theorem tailTrace_2523103 : CollatzResearch.WordTrace tailWord_2523103 prefixEnd_2523103 1295564579801147081608967 := by
  unfold tailWord_2523103
  simp only [CollatzResearch.WordTrace]
  refine ⟨92025126578236217530877963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61350084385490811687251975 92025126578236217530877963)
  ·
    refine ⟨138037689867354326296316945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92025126578236217530877963 138037689867354326296316945)
    ·
      refine ⟨103528267400515744722237709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138037689867354326296316945 103528267400515744722237709)
      ·
        refine ⟨38823100275193404270839141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103528267400515744722237709 38823100275193404270839141)
        ·
          refine ⟨7279331301598763300782339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38823100275193404270839141 7279331301598763300782339)
          ·
            refine ⟨10918996952398144951173509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279331301598763300782339 10918996952398144951173509)
            ·
              refine ⟨2047311928574652178345033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10918996952398144951173509 2047311928574652178345033)
              ·
                refine ⟨1535483946430989133758775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047311928574652178345033 1535483946430989133758775)
                ·
                  refine ⟨2303225919646483700638163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535483946430989133758775 2303225919646483700638163)
                  ·
                    refine ⟨3454838879469725550957245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2303225919646483700638163 3454838879469725550957245)
                    ·
                      refine ⟨1295564579801147081608967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454838879469725550957245 1295564579801147081608967)
                      ·
                        rfl

theorem cell23_2523103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_2523103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523103 prefixEnd_2523103 := by exact prefixLift 2523103
  have htrace : WordTrace (prefixWord ++ tailWord_2523103) baseStart_2523103 baseEnd_2523103 := by
    simpa [prefixWord, tailWord_2523103, baseEnd_2523103] using wordTrace_append hprefix tailTrace_2523103
  have hstable : (prefixWord ++ tailWord_2523103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523103).length < 2 ^ (prefixWord ++ tailWord_2523103).sum := by decide
  have hdescent : baseEnd_2523103 < baseStart_2523103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523105 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2523105 : Nat := 118140960795 + 2523105 * 2 ^ 59
def prefixEnd_2523105 : Nat := 4983230072969 + 3 ^ 40 * 2523105 * 2
def baseEnd_2523105 : Nat := 1295565606762456073783957

theorem tailTrace_2523105 : CollatzResearch.WordTrace tailWord_2523105 prefixEnd_2523105 1295565606762456073783957 := by
  unfold tailWord_2523105
  simp only [CollatzResearch.WordTrace]
  refine ⟨92025199524228971872450769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61350133016152647914967179 92025199524228971872450769)
  ·
    refine ⟨69018899643171728904338077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92025199524228971872450769 69018899643171728904338077)
    ·
      refine ⟨25882087366189398339126779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69018899643171728904338077 25882087366189398339126779)
      ·
        refine ⟨38823131049284097508690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882087366189398339126779 38823131049284097508690169)
        ·
          refine ⟨29117348286963073131517627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38823131049284097508690169 29117348286963073131517627)
          ·
            refine ⟨43676022430444609697276441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29117348286963073131517627 43676022430444609697276441)
            ·
              refine ⟨32757016822833457272957331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43676022430444609697276441 32757016822833457272957331)
              ·
                refine ⟨49135525234250185909435997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32757016822833457272957331 49135525234250185909435997)
                ·
                  refine ⟨18425821962843819716038499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49135525234250185909435997 18425821962843819716038499)
                  ·
                    refine ⟨27638732944265729574057749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18425821962843819716038499 27638732944265729574057749)
                    ·
                      refine ⟨1295565606762456073783957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27638732944265729574057749 1295565606762456073783957)
                      ·
                        rfl

theorem cell23_2523105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2523105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523105 prefixEnd_2523105 := by exact prefixLift 2523105
  have htrace : WordTrace (prefixWord ++ tailWord_2523105) baseStart_2523105 baseEnd_2523105 := by
    simpa [prefixWord, tailWord_2523105, baseEnd_2523105] using wordTrace_append hprefix tailTrace_2523105
  have hstable : (prefixWord ++ tailWord_2523105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523105).length < 2 ^ (prefixWord ++ tailWord_2523105).sum := by decide
  have hdescent : baseEnd_2523105 < baseStart_2523105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523132 : List Nat := [2, 2, 2, 1, 2, 2, 5, 7]
def baseStart_2523132 : Nat := 118140960795 + 2523132 * 2 ^ 59
def prefixEnd_2523132 : Nat := 4983230072969 + 3 ^ 40 * 2523132 * 2
def baseEnd_2523132 : Nat := 47984424842226943264679

theorem tailTrace_2523132 : CollatzResearch.WordTrace tailWord_2523132 prefixEnd_2523132 47984424842226943264679 := by
  unfold tailWord_2523132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013092147565577741841825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61350789530087436989122433 46013092147565577741841825)
  ·
    refine ⟨34509819110674183306381369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46013092147565577741841825 34509819110674183306381369)
    ·
      refine ⟨25882364333005637479786027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34509819110674183306381369 25882364333005637479786027)
      ·
        refine ⟨38823546499508456219679041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882364333005637479786027 38823546499508456219679041)
        ·
          refine ⟨29117659874631342164759281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38823546499508456219679041 29117659874631342164759281)
          ·
            refine ⟨21838244905973506623569461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29117659874631342164759281 21838244905973506623569461)
            ·
              refine ⟨2047335459935016245959637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21838244905973506623569461 2047335459935016245959637)
              ·
                refine ⟨47984424842226943264679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2047335459935016245959637 47984424842226943264679)
                ·
                  rfl

theorem cell23_2523132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 7].length) (baseStart_2523132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523132 prefixEnd_2523132 := by exact prefixLift 2523132
  have htrace : WordTrace (prefixWord ++ tailWord_2523132) baseStart_2523132 baseEnd_2523132 := by
    simpa [prefixWord, tailWord_2523132, baseEnd_2523132] using wordTrace_append hprefix tailTrace_2523132
  have hstable : (prefixWord ++ tailWord_2523132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523132).length < 2 ^ (prefixWord ++ tailWord_2523132).sum := by decide
  have hdescent : baseEnd_2523132 < baseStart_2523132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523140 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_2523140 : Nat := 118140960795 + 2523140 * 2 ^ 59
def prefixEnd_2523140 : Nat := 4983230072969 + 3 ^ 40 * 2523140 * 2
def baseEnd_2523140 : Nat := 431861192861787812282099

theorem tailTrace_2523140 : CollatzResearch.WordTrace tailWord_2523140 prefixEnd_2523140 431861192861787812282099 := by
  unfold tailWord_2523140
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013238039551086424987437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61350984052734781899983249 46013238039551086424987437)
  ·
    refine ⟨17254964264831657409370289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46013238039551086424987437 17254964264831657409370289)
    ·
      refine ⟨12941223198623743057027717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17254964264831657409370289 12941223198623743057027717)
      ·
        refine ⟨2426479349741951823192697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12941223198623743057027717 2426479349741951823192697)
        ·
          refine ⟨1819859512306463867394523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426479349741951823192697 1819859512306463867394523)
          ·
            refine ⟨2729789268459695801091785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819859512306463867394523 2729789268459695801091785)
            ·
              refine ⟨2047341951344771850818839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729789268459695801091785 2047341951344771850818839)
              ·
                refine ⟨3071012927017157776228259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047341951344771850818839 3071012927017157776228259)
                ·
                  refine ⟨4606519390525736664342389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071012927017157776228259 4606519390525736664342389)
                  ·
                    refine ⟨431861192861787812282099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606519390525736664342389 431861192861787812282099)
                    ·
                      rfl

theorem cell23_2523140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_2523140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523140 prefixEnd_2523140 := by exact prefixLift 2523140
  have htrace : WordTrace (prefixWord ++ tailWord_2523140) baseStart_2523140 baseEnd_2523140 := by
    simpa [prefixWord, tailWord_2523140, baseEnd_2523140] using wordTrace_append hprefix tailTrace_2523140
  have hstable : (prefixWord ++ tailWord_2523140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523140).length < 2 ^ (prefixWord ++ tailWord_2523140).sum := by decide
  have hdescent : baseEnd_2523140 < baseStart_2523140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523143 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2523143 : Nat := 118140960795 + 2523143 * 2 ^ 59
def prefixEnd_2523143 : Nat := 4983230072969 + 3 ^ 40 * 2523143 * 2
def baseEnd_2523143 : Nat := 1295585119027326925108783

theorem tailTrace_2523143 : CollatzResearch.WordTrace tailWord_2523143 prefixEnd_2523143 1295585119027326925108783 := by
  unfold tailWord_2523143
  simp only [CollatzResearch.WordTrace]
  refine ⟨92026585498091304362334083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61351056998727536241556055 92026585498091304362334083)
  ·
    refine ⟨138039878247136956543501125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92026585498091304362334083 138039878247136956543501125)
    ·
      refine ⟨25882477171338179351906461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138039878247136956543501125 25882477171338179351906461)
      ·
        refine ⟨9705928939251817256964923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25882477171338179351906461 9705928939251817256964923)
        ·
          refine ⟨14558893408877725885447385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9705928939251817256964923 14558893408877725885447385)
          ·
            refine ⟨10919170056658294414085539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14558893408877725885447385 10919170056658294414085539)
            ·
              refine ⟨16378755084987441621128309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10919170056658294414085539 16378755084987441621128309)
              ·
                refine ⟨1535508289217572651980779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16378755084987441621128309 1535508289217572651980779)
                ·
                  refine ⟨2303262433826358977971169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535508289217572651980779 2303262433826358977971169)
                  ·
                    refine ⟨1727446825369769233478377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2303262433826358977971169 1727446825369769233478377)
                    ·
                      refine ⟨1295585119027326925108783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727446825369769233478377 1295585119027326925108783)
                      ·
                        rfl

theorem cell23_2523143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2523143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523143 prefixEnd_2523143 := by exact prefixLift 2523143
  have htrace : WordTrace (prefixWord ++ tailWord_2523143) baseStart_2523143 baseEnd_2523143 := by
    simpa [prefixWord, tailWord_2523143, baseEnd_2523143] using wordTrace_append hprefix tailTrace_2523143
  have hstable : (prefixWord ++ tailWord_2523143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523143).length < 2 ^ (prefixWord ++ tailWord_2523143).sum := by decide
  have hdescent : baseEnd_2523143 < baseStart_2523143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523146 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2523146 : Nat := 118140960795 + 2523146 * 2 ^ 59
def prefixEnd_2523146 : Nat := 4983230072969 + 3 ^ 40 * 2523146 * 2
def baseEnd_2523146 : Nat := 1295586659469290413371269

theorem tailTrace_2523146 : CollatzResearch.WordTrace tailWord_2523146 prefixEnd_2523146 1295586659469290413371269 := by
  unfold tailWord_2523146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23006673729270108968673323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61351129944720290583128861 23006673729270108968673323)
  ·
    refine ⟨34510010593905163453009985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23006673729270108968673323 34510010593905163453009985)
    ·
      refine ⟨25882507945428872589757489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34510010593905163453009985 25882507945428872589757489)
      ·
        refine ⟨19411880959071654442318117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25882507945428872589757489 19411880959071654442318117)
        ·
          refine ⟨3639727679825935207934647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19411880959071654442318117 3639727679825935207934647)
          ·
            refine ⟨5459591519738902811901971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639727679825935207934647 5459591519738902811901971)
            ·
              refine ⟨8189387279608354217852957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459591519738902811901971 8189387279608354217852957)
              ·
                refine ⟨3071020229853132831694859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189387279608354217852957 3071020229853132831694859)
                ·
                  refine ⟨4606530344779699247542289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071020229853132831694859 4606530344779699247542289)
                  ·
                    refine ⟨3454897758584774435656717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606530344779699247542289 3454897758584774435656717)
                    ·
                      refine ⟨1295586659469290413371269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3454897758584774435656717 1295586659469290413371269)
                      ·
                        rfl

theorem cell23_2523146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2523146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523146 prefixEnd_2523146 := by exact prefixLift 2523146
  have htrace : WordTrace (prefixWord ++ tailWord_2523146) baseStart_2523146 baseEnd_2523146 := by
    simpa [prefixWord, tailWord_2523146, baseEnd_2523146] using wordTrace_append hprefix tailTrace_2523146
  have hstable : (prefixWord ++ tailWord_2523146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523146).length < 2 ^ (prefixWord ++ tailWord_2523146).sum := by decide
  have hdescent : baseEnd_2523146 < baseStart_2523146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523186 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_2523186 : Nat := 118140960795 + 2523186 * 2 ^ 59
def prefixEnd_2523186 : Nat := 4983230072969 + 3 ^ 40 * 2523186 * 2
def baseEnd_2523186 : Nat := 1295607198695470256871085

theorem tailTrace_2523186 : CollatzResearch.WordTrace tailWord_2523186 prefixEnd_2523186 1295607198695470256871085 := by
  unfold tailWord_2523186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007038459233880676537353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61352102557957015137432941 23007038459233880676537353)
  ·
    refine ⟨17255278844425410507403015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23007038459233880676537353 17255278844425410507403015)
    ·
      refine ⟨25882918266638115761104523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17255278844425410507403015 25882918266638115761104523)
      ·
        refine ⟨38824377399957173641656785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882918266638115761104523 38824377399957173641656785)
        ·
          refine ⟨29118283049967880231242589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38824377399957173641656785 29118283049967880231242589)
          ·
            refine ⟨10919356143737955086715971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29118283049967880231242589 10919356143737955086715971)
            ·
              refine ⟨16379034215606932630073957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10919356143737955086715971 16379034215606932630073957)
              ·
                refine ⟨3071068915426299868138867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16379034215606932630073957 3071068915426299868138867)
                ·
                  refine ⟨4606603373139449802208301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071068915426299868138867 4606603373139449802208301)
                  ·
                    refine ⟨1727476264927293675828113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4606603373139449802208301 1727476264927293675828113)
                    ·
                      refine ⟨1295607198695470256871085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727476264927293675828113 1295607198695470256871085)
                      ·
                        rfl

theorem cell23_2523186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_2523186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523186 prefixEnd_2523186 := by exact prefixLift 2523186
  have htrace : WordTrace (prefixWord ++ tailWord_2523186) baseStart_2523186 baseEnd_2523186 := by
    simpa [prefixWord, tailWord_2523186, baseEnd_2523186] using wordTrace_append hprefix tailTrace_2523186
  have hstable : (prefixWord ++ tailWord_2523186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523186).length < 2 ^ (prefixWord ++ tailWord_2523186).sum := by decide
  have hdescent : baseEnd_2523186 < baseStart_2523186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523199 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 4, 2]
def baseStart_2523199 : Nat := 118140960795 + 2523199 * 2 ^ 59
def prefixEnd_2523199 : Nat := 4983230072969 + 3 ^ 40 * 2523199 * 2
def baseEnd_2523199 : Nat := 1295613873943978706008525

theorem tailTrace_2523199 : CollatzResearch.WordTrace tailWord_2523199 prefixEnd_2523199 1295613873943978706008525 := by
  unfold tailWord_2523199
  simp only [CollatzResearch.WordTrace]
  refine ⟨92028627985888425926372651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61352418657258950617581767 92028627985888425926372651)
  ·
    refine ⟨138042941978832638889558977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92028627985888425926372651 138042941978832638889558977)
    ·
      refine ⟨103532206484124479167169233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138042941978832638889558977 103532206484124479167169233)
      ·
        refine ⟨77649154863093359375376925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103532206484124479167169233 77649154863093359375376925)
        ·
          refine ⟨29118433073660009765766347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77649154863093359375376925 29118433073660009765766347)
          ·
            refine ⟨43677649610490014648649521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29118433073660009765766347 43677649610490014648649521)
            ·
              refine ⟨32758237207867510986487141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43677649610490014648649521 32758237207867510986487141)
              ·
                refine ⟨6142169476475158309966339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32758237207867510986487141 6142169476475158309966339)
                ·
                  refine ⟨9213254214712737464949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142169476475158309966339 9213254214712737464949509)
                  ·
                    refine ⟨1727485165258638274678033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9213254214712737464949509 1727485165258638274678033)
                    ·
                      refine ⟨1295613873943978706008525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727485165258638274678033 1295613873943978706008525)
                      ·
                        rfl

theorem cell23_2523199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_2523199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523199 prefixEnd_2523199 := by exact prefixLift 2523199
  have htrace : WordTrace (prefixWord ++ tailWord_2523199) baseStart_2523199 baseEnd_2523199 := by
    simpa [prefixWord, tailWord_2523199, baseEnd_2523199] using wordTrace_append hprefix tailTrace_2523199
  have hstable : (prefixWord ++ tailWord_2523199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523199).length < 2 ^ (prefixWord ++ tailWord_2523199).sum := by decide
  have hdescent : baseEnd_2523199 < baseStart_2523199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523212 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2523212 : Nat := 118140960795 + 2523212 * 2 ^ 59
def prefixEnd_2523212 : Nat := 4983230072969 + 3 ^ 40 * 2523212 * 2
def baseEnd_2523212 : Nat := 1295620549192487155145965

theorem tailTrace_2523212 : CollatzResearch.WordTrace tailWord_2523212 prefixEnd_2523212 1295620549192487155145965 := by
  unfold tailWord_2523212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46014551067420664573297945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61352734756560886097730593 46014551067420664573297945)
  ·
    refine ⟨34510913300565498429973459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46014551067420664573297945 34510913300565498429973459)
    ·
      refine ⟨51766369950848247644960189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34510913300565498429973459 51766369950848247644960189)
      ·
        refine ⟨19412388731568092866860071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51766369950848247644960189 19412388731568092866860071)
        ·
          refine ⟨29118583097352139300290107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19412388731568092866860071 29118583097352139300290107)
          ·
            refine ⟨43677874646028208950435161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29118583097352139300290107 43677874646028208950435161)
            ·
              refine ⟨32758405984521156712826371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43677874646028208950435161 32758405984521156712826371)
              ·
                refine ⟨49137608976781735069239557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32758405984521156712826371 49137608976781735069239557)
                ·
                  refine ⟨9213301683146575325482417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49137608976781735069239557 9213301683146575325482417)
                  ·
                    refine ⟨6909976262359931494111813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9213301683146575325482417 6909976262359931494111813)
                    ·
                      refine ⟨1295620549192487155145965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6909976262359931494111813 1295620549192487155145965)
                      ·
                        rfl

theorem cell23_2523212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2523212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523212 prefixEnd_2523212 := by exact prefixLift 2523212
  have htrace : WordTrace (prefixWord ++ tailWord_2523212) baseStart_2523212 baseEnd_2523212 := by
    simpa [prefixWord, tailWord_2523212, baseEnd_2523212] using wordTrace_append hprefix tailTrace_2523212
  have hstable : (prefixWord ++ tailWord_2523212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523212).length < 2 ^ (prefixWord ++ tailWord_2523212).sum := by decide
  have hdescent : baseEnd_2523212 < baseStart_2523212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523269 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_2523269 : Nat := 118140960795 + 2523269 * 2 ^ 59
def prefixEnd_2523269 : Nat := 4983230072969 + 3 ^ 40 * 2523269 * 2
def baseEnd_2523269 : Nat := 431883272529931144044401

theorem tailTrace_2523269 : CollatzResearch.WordTrace tailWord_2523269 prefixEnd_2523269 431883272529931144044401 := by
  unfold tailWord_2523269
  simp only [CollatzResearch.WordTrace]
  refine ⟨92031181095634827881420861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61354120730423218587613907 92031181095634827881420861)
  ·
    refine ⟨34511692910863060455532823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92031181095634827881420861 34511692910863060455532823)
    ·
      refine ⟨51767539366294590683299235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34511692910863060455532823 51767539366294590683299235)
      ·
        refine ⟨77651309049441886024948853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51767539366294590683299235 77651309049441886024948853)
        ·
          refine ⟨7279810223385176814838955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77651309049441886024948853 7279810223385176814838955)
          ·
            refine ⟨10919715335077765222258433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279810223385176814838955 10919715335077765222258433)
            ·
              refine ⟨8189786501308323916693825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10919715335077765222258433 8189786501308323916693825)
              ·
                refine ⟨6142339875981242937520369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189786501308323916693825 6142339875981242937520369)
                ·
                  refine ⟨4606754906985932203140277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142339875981242937520369 4606754906985932203140277)
                  ·
                    refine ⟨431883272529931144044401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606754906985932203140277 431883272529931144044401)
                    ·
                      rfl

theorem cell23_2523269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_2523269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523269 prefixEnd_2523269 := by exact prefixLift 2523269
  have htrace : WordTrace (prefixWord ++ tailWord_2523269) baseStart_2523269 baseEnd_2523269 := by
    simpa [prefixWord, tailWord_2523269, baseEnd_2523269] using wordTrace_append hprefix tailTrace_2523269
  have hstable : (prefixWord ++ tailWord_2523269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523269).length < 2 ^ (prefixWord ++ tailWord_2523269).sum := by decide
  have hdescent : baseEnd_2523269 < baseStart_2523269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523303 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2523303 : Nat := 118140960795 + 2523303 * 2 ^ 59
def prefixEnd_2523303 : Nat := 4983230072969 + 3 ^ 40 * 2523303 * 2
def baseEnd_2523303 : Nat := 431889091977348766369349

theorem tailTrace_2523303 : CollatzResearch.WordTrace tailWord_2523303 prefixEnd_2523303 431889091977348766369349 := by
  unfold tailWord_2523303
  simp only [CollatzResearch.WordTrace]
  refine ⟨92032421177511651688158563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61354947451674434458772375 92032421177511651688158563)
  ·
    refine ⟨138048631766267477532237845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92032421177511651688158563 138048631766267477532237845)
    ·
      refine ⟨6471029614043788009323649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138048631766267477532237845 6471029614043788009323649)
      ·
        refine ⟨4853272210532841006992737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6471029614043788009323649 4853272210532841006992737)
        ·
          refine ⟨3639954157899630755244553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853272210532841006992737 3639954157899630755244553)
          ·
            refine ⟨2729965618424723066433415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3639954157899630755244553 2729965618424723066433415)
            ·
              refine ⟨4094948427637084599650123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729965618424723066433415 4094948427637084599650123)
              ·
                refine ⟨6142422641455626899475185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094948427637084599650123 6142422641455626899475185)
                ·
                  refine ⟨4606816981091720174606389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142422641455626899475185 4606816981091720174606389)
                  ·
                    refine ⟨431889091977348766369349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606816981091720174606389 431889091977348766369349)
                    ·
                      rfl

theorem cell23_2523303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2523303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523303 prefixEnd_2523303 := by exact prefixLift 2523303
  have htrace : WordTrace (prefixWord ++ tailWord_2523303) baseStart_2523303 baseEnd_2523303 := by
    simpa [prefixWord, tailWord_2523303, baseEnd_2523303] using wordTrace_append hprefix tailTrace_2523303
  have hstable : (prefixWord ++ tailWord_2523303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523303).length < 2 ^ (prefixWord ++ tailWord_2523303).sum := by decide
  have hdescent : baseEnd_2523303 < baseStart_2523303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523409 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_2523409 : Nat := 118140960795 + 2523409 * 2 ^ 59
def prefixEnd_2523409 : Nat := 4983230072969 + 3 ^ 40 * 2523409 * 2
def baseEnd_2523409 : Nat := 1295721704881422884382559

theorem tailTrace_2523409 : CollatzResearch.WordTrace tailWord_2523409 prefixEnd_2523409 1295721704881422884382559 := by
  unfold tailWord_2523409
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036287315127631791517281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61357524876751754527678187 92036287315127631791517281)
  ·
    refine ⟨69027215486345723843637961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92036287315127631791517281 69027215486345723843637961)
    ·
      refine ⟨51770411614759292882728471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69027215486345723843637961 51770411614759292882728471)
      ·
        refine ⟨77655617422138939324092707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51770411614759292882728471 77655617422138939324092707)
        ·
          refine ⟨116483426133208408986139061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77655617422138939324092707 116483426133208408986139061)
          ·
            refine ⟨10920321199988288342450537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116483426133208408986139061 10920321199988288342450537)
            ·
              refine ⟨8190240899991216256837903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10920321199988288342450537 8190240899991216256837903)
              ·
                refine ⟨12285361349986824385256855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190240899991216256837903 12285361349986824385256855)
                ·
                  refine ⟨18428042024980236577885283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12285361349986824385256855 18428042024980236577885283)
                  ·
                    refine ⟨27642063037470354866827925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18428042024980236577885283 27642063037470354866827925)
                    ·
                      refine ⟨1295721704881422884382559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27642063037470354866827925 1295721704881422884382559)
                      ·
                        rfl

theorem cell23_2523409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_2523409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523409 prefixEnd_2523409 := by exact prefixLift 2523409
  have htrace : WordTrace (prefixWord ++ tailWord_2523409) baseStart_2523409 baseEnd_2523409 := by
    simpa [prefixWord, tailWord_2523409, baseEnd_2523409] using wordTrace_append hprefix tailTrace_2523409
  have hstable : (prefixWord ++ tailWord_2523409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523409).length < 2 ^ (prefixWord ++ tailWord_2523409).sum := by decide
  have hdescent : baseEnd_2523409 < baseStart_2523409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523413 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_2523413 : Nat := 118140960795 + 2523413 * 2 ^ 59
def prefixEnd_2523413 : Nat := 4983230072969 + 3 ^ 40 * 2523413 * 2
def baseEnd_2523413 : Nat := 1295723758804040868732541

theorem tailTrace_2523413 : CollatzResearch.WordTrace tailWord_2523413 prefixEnd_2523413 1295723758804040868732541 := by
  unfold tailWord_2523413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036433207113140474662893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61357622138075426983108595 92036433207113140474662893)
  ·
    refine ⟨34513662452667427677998585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92036433207113140474662893 34513662452667427677998585)
    ·
      refine ⟨25885246839500570758498939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34513662452667427677998585 25885246839500570758498939)
      ·
        refine ⟨38827870259250856137748409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25885246839500570758498939 38827870259250856137748409)
        ·
          refine ⟨29120902694438142103311307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38827870259250856137748409 29120902694438142103311307)
          ·
            refine ⟨43681354041657213154966961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29120902694438142103311307 43681354041657213154966961)
            ·
              refine ⟨32761015531242909866225221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43681354041657213154966961 32761015531242909866225221)
              ·
                refine ⟨6142690412108045599917229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32761015531242909866225221 6142690412108045599917229)
                ·
                  refine ⟨2303508904540517099968961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6142690412108045599917229 2303508904540517099968961)
                  ·
                    refine ⟨1727631678405387824976721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2303508904540517099968961 1727631678405387824976721)
                    ·
                      refine ⟨1295723758804040868732541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727631678405387824976721 1295723758804040868732541)
                      ·
                        rfl

theorem cell23_2523413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_2523413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523413 prefixEnd_2523413 := by exact prefixLift 2523413
  have htrace : WordTrace (prefixWord ++ tailWord_2523413) baseStart_2523413 baseEnd_2523413 := by
    simpa [prefixWord, tailWord_2523413, baseEnd_2523413] using wordTrace_append hprefix tailTrace_2523413
  have hstable : (prefixWord ++ tailWord_2523413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523413).length < 2 ^ (prefixWord ++ tailWord_2523413).sum := by decide
  have hdescent : baseEnd_2523413 < baseStart_2523413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523416 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2523416 : Nat := 118140960795 + 2523416 * 2 ^ 59
def prefixEnd_2523416 : Nat := 4983230072969 + 3 ^ 40 * 2523416 * 2
def baseEnd_2523416 : Nat := 1295725299246004356995027

theorem tailTrace_2523416 : CollatzResearch.WordTrace tailWord_2523416 prefixEnd_2523416 1295725299246004356995027 := by
  unfold tailWord_2523416
  simp only [CollatzResearch.WordTrace]
  refine ⟨46018271313051135993511051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61357695084068181324681401 46018271313051135993511051)
  ·
    refine ⟨69027406969576703990266577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46018271313051135993511051 69027406969576703990266577)
    ·
      refine ⟨51770555227182527992699933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69027406969576703990266577 51770555227182527992699933)
      ·
        refine ⟨19413958210193447997262475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51770555227182527992699933 19413958210193447997262475)
        ·
          refine ⟨29120937315290171995893713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19413958210193447997262475 29120937315290171995893713)
          ·
            refine ⟨21840702986467628996920285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29120937315290171995893713 21840702986467628996920285)
            ·
              refine ⟨8190263619925360873845107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21840702986467628996920285 8190263619925360873845107)
              ·
                refine ⟨12285395429888041310767661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190263619925360873845107 12285395429888041310767661)
                ·
                  refine ⟨4607023286208015491537873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12285395429888041310767661 4607023286208015491537873)
                  ·
                    refine ⟨3455267464656011618653405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607023286208015491537873 3455267464656011618653405)
                    ·
                      refine ⟨1295725299246004356995027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3455267464656011618653405 1295725299246004356995027)
                      ·
                        rfl

theorem cell23_2523416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2523416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523416 prefixEnd_2523416 := by exact prefixLift 2523416
  have htrace : WordTrace (prefixWord ++ tailWord_2523416) baseStart_2523416 baseEnd_2523416 := by
    simpa [prefixWord, tailWord_2523416, baseEnd_2523416] using wordTrace_append hprefix tailTrace_2523416
  have hstable : (prefixWord ++ tailWord_2523416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523416).length < 2 ^ (prefixWord ++ tailWord_2523416).sum := by decide
  have hdescent : baseEnd_2523416 < baseStart_2523416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523426 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2523426 : Nat := 118140960795 + 2523426 * 2 ^ 59
def prefixEnd_2523426 : Nat := 4983230072969 + 3 ^ 40 * 2523426 * 2
def baseEnd_2523426 : Nat := 1295730434052549317869981

theorem tailTrace_2523426 : CollatzResearch.WordTrace tailWord_2523426 prefixEnd_2523426 1295730434052549317869981 := by
  unfold tailWord_2523426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23009226839016510923721533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61357938237377362463257421 23009226839016510923721533)
  ·
    refine ⟨8628460064631191596395575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23009226839016510923721533 8628460064631191596395575)
    ·
      refine ⟨12942690096946787394593363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628460064631191596395575 12942690096946787394593363)
      ·
        refine ⟨19414035145420181091890045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12942690096946787394593363 19414035145420181091890045)
        ·
          refine ⟨7280263179532567909458767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19414035145420181091890045 7280263179532567909458767)
          ·
            refine ⟨10920394769298851864188151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280263179532567909458767 10920394769298851864188151)
            ·
              refine ⟨16380592153948277796282227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920394769298851864188151 16380592153948277796282227)
              ·
                refine ⟨24570888230922416694423341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16380592153948277796282227 24570888230922416694423341)
                ·
                  refine ⟨9214083086595906260408753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24570888230922416694423341 9214083086595906260408753)
                  ·
                    refine ⟨6910562314946929695306565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9214083086595906260408753 6910562314946929695306565)
                    ·
                      refine ⟨1295730434052549317869981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6910562314946929695306565 1295730434052549317869981)
                      ·
                        rfl

theorem cell23_2523426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2523426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523426 prefixEnd_2523426 := by exact prefixLift 2523426
  have htrace : WordTrace (prefixWord ++ tailWord_2523426) baseStart_2523426 baseEnd_2523426 := by
    simpa [prefixWord, tailWord_2523426, baseEnd_2523426] using wordTrace_append hprefix tailTrace_2523426
  have hstable : (prefixWord ++ tailWord_2523426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523426).length < 2 ^ (prefixWord ++ tailWord_2523426).sum := by decide
  have hdescent : baseEnd_2523426 < baseStart_2523426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523460 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2523460 : Nat := 118140960795 + 2523460 * 2 ^ 59
def prefixEnd_2523460 : Nat := 4983230072969 + 3 ^ 40 * 2523460 * 2
def baseEnd_2523460 : Nat := 1295747892394802184844825

theorem tailTrace_2523460 : CollatzResearch.WordTrace tailWord_2523460 prefixEnd_2523460 1295747892394802184844825 := by
  unfold tailWord_2523460
  simp only [CollatzResearch.WordTrace]
  refine ⟨46019073718971433750811917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61358764958628578334415889 46019073718971433750811917)
  ·
    refine ⟨17257152644614287656554469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46019073718971433750811917 17257152644614287656554469)
    ·
      refine ⟨3235716120865178935603963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17257152644614287656554469 3235716120865178935603963)
      ·
        refine ⟨4853574181297768403405945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235716120865178935603963 4853574181297768403405945)
        ·
          refine ⟨3640180635973326302554459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853574181297768403405945 3640180635973326302554459)
          ·
            refine ⟨5460270953959989453831689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640180635973326302554459 5460270953959989453831689)
            ·
              refine ⟨4095203215469992090373767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460270953959989453831689 4095203215469992090373767)
              ·
                refine ⟨6142804823204988135560651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095203215469992090373767 6142804823204988135560651)
                ·
                  refine ⟨9214207234807482203340977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142804823204988135560651 9214207234807482203340977)
                  ·
                    refine ⟨6910655426105611652505733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9214207234807482203340977 6910655426105611652505733)
                    ·
                      refine ⟨1295747892394802184844825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6910655426105611652505733 1295747892394802184844825)
                      ·
                        rfl

theorem cell23_2523460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2523460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523460 prefixEnd_2523460 := by exact prefixLift 2523460
  have htrace : WordTrace (prefixWord ++ tailWord_2523460) baseStart_2523460 baseEnd_2523460 := by
    simpa [prefixWord, tailWord_2523460, baseEnd_2523460] using wordTrace_append hprefix tailTrace_2523460
  have hstable : (prefixWord ++ tailWord_2523460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523460).length < 2 ^ (prefixWord ++ tailWord_2523460).sum := by decide
  have hdescent : baseEnd_2523460 < baseStart_2523460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523463 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2523463 : Nat := 118140960795 + 2523463 * 2 ^ 59
def prefixEnd_2523463 : Nat := 4983230072969 + 3 ^ 40 * 2523463 * 2
def baseEnd_2523463 : Nat := 1295749432836765673107311

theorem tailTrace_2523463 : CollatzResearch.WordTrace tailWord_2523463 prefixEnd_2523463 1295749432836765673107311 := by
  unfold tailWord_2523463
  simp only [CollatzResearch.WordTrace]
  refine ⟨92038256856931999013983043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61358837904621332675988695 92038256856931999013983043)
  ·
    refine ⟨138057385285397998520974565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92038256856931999013983043 138057385285397998520974565)
    ·
      refine ⟨25885759741012124722682731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138057385285397998520974565 25885759741012124722682731)
      ·
        refine ⟨38828639611518187084024097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25885759741012124722682731 38828639611518187084024097)
        ·
          refine ⟨29121479708638640313018073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38828639611518187084024097 29121479708638640313018073)
          ·
            refine ⟨21841109781478980234763555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29121479708638640313018073 21841109781478980234763555)
            ·
              refine ⟨32761664672218470352145333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21841109781478980234763555 32761664672218470352145333)
              ·
                refine ⟨3071406063020481595513625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32761664672218470352145333 3071406063020481595513625)
                ·
                  refine ⟨2303554547265361196635219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071406063020481595513625 2303554547265361196635219)
                  ·
                    refine ⟨3455331820898041794952829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2303554547265361196635219 3455331820898041794952829)
                    ·
                      refine ⟨1295749432836765673107311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3455331820898041794952829 1295749432836765673107311)
                      ·
                        rfl

theorem cell23_2523463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2523463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523463 prefixEnd_2523463 := by exact prefixLift 2523463
  have htrace : WordTrace (prefixWord ++ tailWord_2523463) baseStart_2523463 baseEnd_2523463 := by
    simpa [prefixWord, tailWord_2523463, baseEnd_2523463] using wordTrace_append hprefix tailTrace_2523463
  have hstable : (prefixWord ++ tailWord_2523463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523463).length < 2 ^ (prefixWord ++ tailWord_2523463).sum := by decide
  have hdescent : baseEnd_2523463 < baseStart_2523463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523473 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_2523473 : Nat := 118140960795 + 2523473 * 2 ^ 59
def prefixEnd_2523473 : Nat := 4983230072969 + 3 ^ 40 * 2523473 * 2
def baseEnd_2523473 : Nat := 1295754567643310633982265

theorem tailTrace_2523473 : CollatzResearch.WordTrace tailWord_2523473 prefixEnd_2523473 1295754567643310633982265 := by
  unfold tailWord_2523473
  simp only [CollatzResearch.WordTrace]
  refine ⟨92038621586895770721847073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61359081057930513814564715 92038621586895770721847073)
  ·
    refine ⟨69028966190171828041385305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92038621586895770721847073 69028966190171828041385305)
    ·
      refine ⟨51771724642628871031038979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69028966190171828041385305 51771724642628871031038979)
      ·
        refine ⟨77657586963943306546558469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51771724642628871031038979 77657586963943306546558469)
        ·
          refine ⟨14560797555739369977479713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77657586963943306546558469 14560797555739369977479713)
          ·
            refine ⟨10920598166804527483109785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14560797555739369977479713 10920598166804527483109785)
            ·
              refine ⟨8190448625103395612332339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10920598166804527483109785 8190448625103395612332339)
              ·
                refine ⟨12285672937655093418498509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190448625103395612332339 12285672937655093418498509)
                ·
                  refine ⟨4607127351620660031936941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12285672937655093418498509 4607127351620660031936941)
                  ·
                    refine ⟨1727672756857747511976353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4607127351620660031936941 1727672756857747511976353)
                    ·
                      refine ⟨1295754567643310633982265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727672756857747511976353 1295754567643310633982265)
                      ·
                        rfl

theorem cell23_2523473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_2523473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523473 prefixEnd_2523473 := by exact prefixLift 2523473
  have htrace : WordTrace (prefixWord ++ tailWord_2523473) baseStart_2523473 baseEnd_2523473 := by
    simpa [prefixWord, tailWord_2523473, baseEnd_2523473] using wordTrace_append hprefix tailTrace_2523473
  have hstable : (prefixWord ++ tailWord_2523473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523473).length < 2 ^ (prefixWord ++ tailWord_2523473).sum := by decide
  have hdescent : baseEnd_2523473 < baseStart_2523473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523479 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 8]
def baseStart_2523479 : Nat := 118140960795 + 2523479 * 2 ^ 59
def prefixEnd_2523479 : Nat := 4983230072969 + 3 ^ 40 * 2523479 * 2
def baseEnd_2523479 : Nat := 431919216175745870169079

theorem tailTrace_2523479 : CollatzResearch.WordTrace tailWord_2523479 prefixEnd_2523479 431919216175745870169079 := by
  unfold tailWord_2523479
  simp only [CollatzResearch.WordTrace]
  refine ⟨92038840424874033746565491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61359226949916022497710327 92038840424874033746565491)
  ·
    refine ⟨138058260637311050619848237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92038840424874033746565491 138058260637311050619848237)
    ·
      refine ⟨51771847738991643982443089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138058260637311050619848237 51771847738991643982443089)
      ·
        refine ⟨38828885804243732986832317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51771847738991643982443089 38828885804243732986832317)
        ·
          refine ⟨14560832176591399870062119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38828885804243732986832317 14560832176591399870062119)
          ·
            refine ⟨21841248264887099805093179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14560832176591399870062119 21841248264887099805093179)
            ·
              refine ⟨32761872397330649707639769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21841248264887099805093179 32761872397330649707639769)
              ·
                refine ⟨24571404297997987280729827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32761872397330649707639769 24571404297997987280729827)
                ·
                  refine ⟨36857106446996980921094741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24571404297997987280729827 36857106446996980921094741)
                  ·
                    refine ⟨431919216175745870169079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36857106446996980921094741 431919216175745870169079)
                    ·
                      rfl

theorem cell23_2523479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_2523479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523479 prefixEnd_2523479 := by exact prefixLift 2523479
  have htrace : WordTrace (prefixWord ++ tailWord_2523479) baseStart_2523479 baseEnd_2523479 := by
    simpa [prefixWord, tailWord_2523479, baseEnd_2523479] using wordTrace_append hprefix tailTrace_2523479
  have hstable : (prefixWord ++ tailWord_2523479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523479).length < 2 ^ (prefixWord ++ tailWord_2523479).sum := by decide
  have hdescent : baseEnd_2523479 < baseStart_2523479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523484 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2523484 : Nat := 118140960795 + 2523484 * 2 ^ 59
def prefixEnd_2523484 : Nat := 4983230072969 + 3 ^ 40 * 2523484 * 2
def baseEnd_2523484 : Nat := 1295760215930510090944715

theorem tailTrace_2523484 : CollatzResearch.WordTrace tailWord_2523484 prefixEnd_2523484 1295760215930510090944715 := by
  unfold tailWord_2523484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46019511394927959800248753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61359348526570613066998337 46019511394927959800248753)
  ·
    refine ⟨34514633546195969850186565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46019511394927959800248753 34514633546195969850186565)
    ·
      refine ⟨6471493789911744346909981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34514633546195969850186565 6471493789911744346909981)
      ·
        refine ⟨2426810171216904130091243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6471493789911744346909981 2426810171216904130091243)
        ·
          refine ⟨3640215256825356195136865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426810171216904130091243 3640215256825356195136865)
          ·
            refine ⟨2730161442619017146352649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640215256825356195136865 2730161442619017146352649)
            ·
              refine ⟨2047621081964262859764487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2730161442619017146352649 2047621081964262859764487)
              ·
                refine ⟨3071431622946394289646731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047621081964262859764487 3071431622946394289646731)
                ·
                  refine ⟨4607147434419591434470097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071431622946394289646731 4607147434419591434470097)
                  ·
                    refine ⟨3455360575814693575852573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607147434419591434470097 3455360575814693575852573)
                    ·
                      refine ⟨1295760215930510090944715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3455360575814693575852573 1295760215930510090944715)
                      ·
                        rfl

theorem cell23_2523484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2523484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523484 prefixEnd_2523484 := by exact prefixLift 2523484
  have htrace : WordTrace (prefixWord ++ tailWord_2523484) baseStart_2523484 baseEnd_2523484 := by
    simpa [prefixWord, tailWord_2523484, baseEnd_2523484] using wordTrace_append hprefix tailTrace_2523484
  have hstable : (prefixWord ++ tailWord_2523484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523484).length < 2 ^ (prefixWord ++ tailWord_2523484).sum := by decide
  have hdescent : baseEnd_2523484 < baseStart_2523484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523496 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2523496 : Nat := 118140960795 + 2523496 * 2 ^ 59
def prefixEnd_2523496 : Nat := 4983230072969 + 3 ^ 40 * 2523496 * 2
def baseEnd_2523496 : Nat := 431922125899454681331553

theorem tailTrace_2523496 : CollatzResearch.WordTrace tailWord_2523496 prefixEnd_2523496 431922125899454681331553 := by
  unfold tailWord_2523496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46019730232906222824967171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61359640310541630433289561 46019730232906222824967171)
  ·
    refine ⟨69029595349359334237450757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46019730232906222824967171 69029595349359334237450757)
    ·
      refine ⟨12943049128004875169522017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69029595349359334237450757 12943049128004875169522017)
      ·
        refine ⟨9707286846003656377141513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12943049128004875169522017 9707286846003656377141513)
        ·
          refine ⟨7280465134502742282856135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9707286846003656377141513 7280465134502742282856135)
          ·
            refine ⟨10920697701754113424284203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280465134502742282856135 10920697701754113424284203)
            ·
              refine ⟨16381046552631170136426305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920697701754113424284203 16381046552631170136426305)
              ·
                refine ⟨12285784914473377602319729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16381046552631170136426305 12285784914473377602319729)
                ·
                  refine ⟨9214338685855033201739797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12285784914473377602319729 9214338685855033201739797)
                  ·
                    refine ⟨431922125899454681331553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9214338685855033201739797 431922125899454681331553)
                    ·
                      rfl

theorem cell23_2523496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2523496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523496 prefixEnd_2523496 := by exact prefixLift 2523496
  have htrace : WordTrace (prefixWord ++ tailWord_2523496) baseStart_2523496 baseEnd_2523496 := by
    simpa [prefixWord, tailWord_2523496, baseEnd_2523496] using wordTrace_append hprefix tailTrace_2523496
  have hstable : (prefixWord ++ tailWord_2523496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523496).length < 2 ^ (prefixWord ++ tailWord_2523496).sum := by decide
  have hdescent : baseEnd_2523496 < baseStart_2523496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523499 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_2523499 : Nat := 118140960795 + 2523499 * 2 ^ 59
def prefixEnd_2523499 : Nat := 4983230072969 + 3 ^ 40 * 2523499 * 2
def baseEnd_2523499 : Nat := 1295767918140327532257145

theorem tailTrace_2523499 : CollatzResearch.WordTrace tailWord_2523499 prefixEnd_2523499 1295767918140327532257145 := by
  unfold tailWord_2523499
  simp only [CollatzResearch.WordTrace]
  refine ⟨92039569884801577162293551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61359713256534384774862367 92039569884801577162293551)
  ·
    refine ⟨138059354827202365743440327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92039569884801577162293551 138059354827202365743440327)
    ·
      refine ⟨207089032240803548615160491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138059354827202365743440327 207089032240803548615160491)
      ·
        refine ⟨310633548361205322922740737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207089032240803548615160491 310633548361205322922740737)
        ·
          refine ⟨232975161270903992192055553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310633548361205322922740737 232975161270903992192055553)
          ·
            refine ⟨174731370953177994144041665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232975161270903992192055553 174731370953177994144041665)
            ·
              refine ⟨131048528214883495608031249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174731370953177994144041665 131048528214883495608031249)
              ·
                refine ⟨98286396161162621706023437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131048528214883495608031249 98286396161162621706023437)
                ·
                  refine ⟨36857398560435983139758789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98286396161162621706023437 36857398560435983139758789)
                  ·
                    refine ⟨6910762230081746838704773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36857398560435983139758789 6910762230081746838704773)
                    ·
                      refine ⟨1295767918140327532257145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6910762230081746838704773 1295767918140327532257145)
                      ·
                        rfl

theorem cell23_2523499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_2523499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523499 prefixEnd_2523499 := by exact prefixLift 2523499
  have htrace : WordTrace (prefixWord ++ tailWord_2523499) baseStart_2523499 baseEnd_2523499 := by
    simpa [prefixWord, tailWord_2523499, baseEnd_2523499] using wordTrace_append hprefix tailTrace_2523499
  have hstable : (prefixWord ++ tailWord_2523499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523499).length < 2 ^ (prefixWord ++ tailWord_2523499).sum := by decide
  have hdescent : baseEnd_2523499 < baseStart_2523499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523543 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 5]
def baseStart_2523543 : Nat := 118140960795 + 2523543 * 2 ^ 59
def prefixEnd_2523543 : Nat := 4983230072969 + 3 ^ 40 * 2523543 * 2
def baseEnd_2523543 : Nat := 143976723476569484456327

theorem tailTrace_2523543 : CollatzResearch.WordTrace tailWord_2523543 prefixEnd_2523543 143976723476569484456327 := by
  unfold tailWord_2523543
  simp only [CollatzResearch.WordTrace]
  refine ⟨92041174696642172676895283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61360783131094781784596855 92041174696642172676895283)
  ·
    refine ⟨138061762044963259015342925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92041174696642172676895283 138061762044963259015342925)
    ·
      refine ⟨51773160766861222130753597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138061762044963259015342925 51773160766861222130753597)
      ·
        refine ⟨19414935287572958299032599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51773160766861222130753597 19414935287572958299032599)
        ·
          refine ⟨29122402931359437448548899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19414935287572958299032599 29122402931359437448548899)
          ·
            refine ⟨43683604397039156172823349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29122402931359437448548899 43683604397039156172823349)
            ·
              refine ⟨4095337912222420891202189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43683604397039156172823349 4095337912222420891202189)
              ·
                refine ⟨1535751717083407834200821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4095337912222420891202189 1535751717083407834200821)
                ·
                  refine ⟨143976723476569484456327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535751717083407834200821 143976723476569484456327)
                  ·
                    rfl

theorem cell23_2523543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 5].length) (baseStart_2523543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523543 prefixEnd_2523543 := by exact prefixLift 2523543
  have htrace : WordTrace (prefixWord ++ tailWord_2523543) baseStart_2523543 baseEnd_2523543 := by
    simpa [prefixWord, tailWord_2523543, baseEnd_2523543] using wordTrace_append hprefix tailTrace_2523543
  have hstable : (prefixWord ++ tailWord_2523543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523543).length < 2 ^ (prefixWord ++ tailWord_2523543).sum := by decide
  have hdescent : baseEnd_2523543 < baseStart_2523543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523556 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_2523556 : Nat := 118140960795 + 2523556 * 2 ^ 59
def prefixEnd_2523556 : Nat := 4983230072969 + 3 ^ 40 * 2523556 * 2
def baseEnd_2523556 : Nat := 431932395512544603081461

theorem tailTrace_2523556 : CollatzResearch.WordTrace tailWord_2523556 prefixEnd_2523556 431932395512544603081461 := by
  unfold tailWord_2523556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46020824422797537948559261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61361099230396717264745681 46020824422797537948559261)
  ·
    refine ⟨17257809158549076730709723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46020824422797537948559261 17257809158549076730709723)
    ·
      refine ⟨25886713737823615096064585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17257809158549076730709723 25886713737823615096064585)
      ·
        refine ⟨19415035303367711322048439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25886713737823615096064585 19415035303367711322048439)
        ·
          refine ⟨29122552955051566983072659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19415035303367711322048439 29122552955051566983072659)
          ·
            refine ⟨43683829432577350474608989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29122552955051566983072659 43683829432577350474608989)
            ·
              refine ⟨16381436037216506427978371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43683829432577350474608989 16381436037216506427978371)
              ·
                refine ⟨24572154055824759641967557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16381436037216506427978371 24572154055824759641967557)
                ·
                  refine ⟨4607278885467142432868917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24572154055824759641967557 4607278885467142432868917)
                  ·
                    refine ⟨431932395512544603081461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4607278885467142432868917 431932395512544603081461)
                    ·
                      rfl

theorem cell23_2523556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_2523556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523556 prefixEnd_2523556 := by exact prefixLift 2523556
  have htrace : WordTrace (prefixWord ++ tailWord_2523556) baseStart_2523556 baseEnd_2523556 := by
    simpa [prefixWord, tailWord_2523556, baseEnd_2523556] using wordTrace_append hprefix tailTrace_2523556
  have hstable : (prefixWord ++ tailWord_2523556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523556).length < 2 ^ (prefixWord ++ tailWord_2523556).sum := by decide
  have hdescent : baseEnd_2523556 < baseStart_2523556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523560 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 7]
def baseStart_2523560 : Nat := 118140960795 + 2523560 * 2 ^ 59
def prefixEnd_2523560 : Nat := 4983230072969 + 3 ^ 40 * 2523560 * 2
def baseEnd_2523560 : Nat := 143977693384472421510485

theorem tailTrace_2523560 : CollatzResearch.WordTrace tailWord_2523560 prefixEnd_2523560 143977693384472421510485 := by
  unfold tailWord_2523560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46020897368790292290132067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61361196491720389720176089 46020897368790292290132067)
  ·
    refine ⟨69031346053185438435198101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46020897368790292290132067 69031346053185438435198101)
    ·
      refine ⟨3235844346243067426649911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69031346053185438435198101 3235844346243067426649911)
      ·
        refine ⟨4853766519364601139974867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235844346243067426649911 4853766519364601139974867)
        ·
          refine ⟨7280649779046901709962301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853766519364601139974867 7280649779046901709962301)
          ·
            refine ⟨2730243667142588141235863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7280649779046901709962301 2730243667142588141235863)
            ·
              refine ⟨4095365500713882211853795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730243667142588141235863 4095365500713882211853795)
              ·
                refine ⟨6143048251070823317780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095365500713882211853795 6143048251070823317780693)
                ·
                  refine ⟨143977693384472421510485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6143048251070823317780693 143977693384472421510485)
                  ·
                    rfl

theorem cell23_2523560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_2523560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523560 prefixEnd_2523560 := by exact prefixLift 2523560
  have htrace : WordTrace (prefixWord ++ tailWord_2523560) baseStart_2523560 baseEnd_2523560 := by
    simpa [prefixWord, tailWord_2523560, baseEnd_2523560] using wordTrace_append hprefix tailTrace_2523560
  have hstable : (prefixWord ++ tailWord_2523560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523560).length < 2 ^ (prefixWord ++ tailWord_2523560).sum := by decide
  have hdescent : baseEnd_2523560 < baseStart_2523560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523576 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2523576 : Nat := 118140960795 + 2523576 * 2 ^ 59
def prefixEnd_2523576 : Nat := 4983230072969 + 3 ^ 40 * 2523576 * 2
def baseEnd_2523576 : Nat := 1295807456150723730994291

theorem tailTrace_2523576 : CollatzResearch.WordTrace tailWord_2523576 prefixEnd_2523576 1295807456150723730994291 := by
  unfold tailWord_2523576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46021189152761309656423291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61361585537015079541897721 46021189152761309656423291)
  ·
    refine ⟨69031783729141964484634937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46021189152761309656423291 69031783729141964484634937)
    ·
      refine ⟨51773837796856473363476203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69031783729141964484634937 51773837796856473363476203)
      ·
        refine ⟨77660756695284710045214305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51773837796856473363476203 77660756695284710045214305)
        ·
          refine ⟨58245567521463532533910729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77660756695284710045214305 58245567521463532533910729)
          ·
            refine ⟨43684175641097649400433047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58245567521463532533910729 43684175641097649400433047)
            ·
              refine ⟨65526263461646474100649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43684175641097649400433047 65526263461646474100649571)
              ·
                refine ⟨98289395192469711150974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65526263461646474100649571 98289395192469711150974357)
                ·
                  refine ⟨4607315399647017710201923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98289395192469711150974357 4607315399647017710201923)
                  ·
                    refine ⟨6910973099470526565302885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607315399647017710201923 6910973099470526565302885)
                    ·
                      refine ⟨1295807456150723730994291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6910973099470526565302885 1295807456150723730994291)
                      ·
                        rfl

theorem cell23_2523576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2523576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523576 prefixEnd_2523576 := by exact prefixLift 2523576
  have htrace : WordTrace (prefixWord ++ tailWord_2523576) baseStart_2523576 baseEnd_2523576 := by
    simpa [prefixWord, tailWord_2523576, baseEnd_2523576] using wordTrace_append hprefix tailTrace_2523576
  have hstable : (prefixWord ++ tailWord_2523576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523576).length < 2 ^ (prefixWord ++ tailWord_2523576).sum := by decide
  have hdescent : baseEnd_2523576 < baseStart_2523576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523637 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2523637 : Nat := 118140960795 + 2523637 * 2 ^ 59
def prefixEnd_2523637 : Nat := 4983230072969 + 3 ^ 40 * 2523637 * 2
def baseEnd_2523637 : Nat := 431946259490215997443837

theorem tailTrace_2523637 : CollatzResearch.WordTrace tailWord_2523637 prefixEnd_2523637 431946259490215997443837 := by
  unfold tailWord_2523637
  simp only [CollatzResearch.WordTrace]
  refine ⟨92044603158301626730817165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61363068772201084487211443 92044603158301626730817165)
  ·
    refine ⟨34516726184363110024056437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92044603158301626730817165 34516726184363110024056437)
    ·
      refine ⟨3235943079784041564755291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34516726184363110024056437 3235943079784041564755291)
      ·
        refine ⟨4853914619676062347132937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235943079784041564755291 4853914619676062347132937)
        ·
          refine ⟨3640435964757046760349703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853914619676062347132937 3640435964757046760349703)
          ·
            refine ⟨5460653947135570140524555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640435964757046760349703 5460653947135570140524555)
            ·
              refine ⟨8190980920703355210786833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460653947135570140524555 8190980920703355210786833)
              ·
                refine ⟨6143235690527516408090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8190980920703355210786833 6143235690527516408090125)
                ·
                  refine ⟨2303713383947818653033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6143235690527516408090125 2303713383947818653033797)
                  ·
                    refine ⟨431946259490215997443837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303713383947818653033797 431946259490215997443837)
                    ·
                      rfl

theorem cell23_2523637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2523637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523637 prefixEnd_2523637 := by exact prefixLift 2523637
  have htrace : WordTrace (prefixWord ++ tailWord_2523637) baseStart_2523637 baseEnd_2523637 := by
    simpa [prefixWord, tailWord_2523637, baseEnd_2523637] using wordTrace_append hprefix tailTrace_2523637
  have hstable : (prefixWord ++ tailWord_2523637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523637).length < 2 ^ (prefixWord ++ tailWord_2523637).sum := by decide
  have hdescent : baseEnd_2523637 < baseStart_2523637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523656 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2523656 : Nat := 118140960795 + 2523656 * 2 ^ 59
def prefixEnd_2523656 : Nat := 4983230072969 + 3 ^ 40 * 2523656 * 2
def baseEnd_2523656 : Nat := 1295848534603083417993923

theorem tailTrace_2523656 : CollatzResearch.WordTrace tailWord_2523656 prefixEnd_2523656 1295848534603083417993923 := by
  unfold tailWord_2523656
  simp only [CollatzResearch.WordTrace]
  refine ⟨46022648072616396487879411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61363530763488528650505881 46022648072616396487879411)
  ·
    refine ⟨69033972108924594731819117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46022648072616396487879411 69033972108924594731819117)
    ·
      refine ⟨25887739540846723024432169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69033972108924594731819117 25887739540846723024432169)
      ·
        refine ⟨19415804655635042268324127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25887739540846723024432169 19415804655635042268324127)
        ·
          refine ⟨29123706983452563402486191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19415804655635042268324127 29123706983452563402486191)
          ·
            refine ⟨43685560475178845103729287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29123706983452563402486191 43685560475178845103729287)
            ·
              refine ⟨65528340712768267655593931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43685560475178845103729287 65528340712768267655593931)
              ·
                refine ⟨98292511069152401483390897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65528340712768267655593931 98292511069152401483390897)
                ·
                  refine ⟨73719383301864301112543173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98292511069152401483390897 73719383301864301112543173)
                  ·
                    refine ⟨13822384369099556458601845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73719383301864301112543173 13822384369099556458601845)
                    ·
                      refine ⟨1295848534603083417993923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13822384369099556458601845 1295848534603083417993923)
                      ·
                        rfl

theorem cell23_2523656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2523656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523656 prefixEnd_2523656 := by exact prefixLift 2523656
  have htrace : WordTrace (prefixWord ++ tailWord_2523656) baseStart_2523656 baseEnd_2523656 := by
    simpa [prefixWord, tailWord_2523656, baseEnd_2523656] using wordTrace_append hprefix tailTrace_2523656
  have hstable : (prefixWord ++ tailWord_2523656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523656).length < 2 ^ (prefixWord ++ tailWord_2523656).sum := by decide
  have hdescent : baseEnd_2523656 < baseStart_2523656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523677 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2523677 : Nat := 118140960795 + 2523677 * 2 ^ 59
def prefixEnd_2523677 : Nat := 4983230072969 + 3 ^ 40 * 2523677 * 2
def baseEnd_2523677 : Nat := 1295859317696827835831327

theorem tailTrace_2523677 : CollatzResearch.WordTrace tailWord_2523677 prefixEnd_2523677 1295859317696827835831327 := by
  unfold tailWord_2523677
  simp only [CollatzResearch.WordTrace]
  refine ⟨92046062078156713562273285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61364041385437809041515523 92046062078156713562273285)
  ·
    refine ⟨17258636639654383792926241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92046062078156713562273285 17258636639654383792926241)
    ·
      refine ⟨12943977479740787844694681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17258636639654383792926241 12943977479740787844694681)
      ·
        refine ⟨9707983109805590883521011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12943977479740787844694681 9707983109805590883521011)
        ·
          refine ⟨14561974664708386325281517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707983109805590883521011 14561974664708386325281517)
          ·
            refine ⟨5460740499265644871980569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14561974664708386325281517 5460740499265644871980569)
            ·
              refine ⟨4095555374449233653985427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460740499265644871980569 4095555374449233653985427)
              ·
                refine ⟨6143333061673850480978141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095555374449233653985427 6143333061673850480978141)
                ·
                  refine ⟨2303749898127693930366803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6143333061673850480978141 2303749898127693930366803)
                  ·
                    refine ⟨3455624847191540895550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2303749898127693930366803 3455624847191540895550205)
                    ·
                      refine ⟨1295859317696827835831327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3455624847191540895550205 1295859317696827835831327)
                      ·
                        rfl

theorem cell23_2523677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2523677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523677 prefixEnd_2523677 := by exact prefixLift 2523677
  have htrace : WordTrace (prefixWord ++ tailWord_2523677) baseStart_2523677 baseEnd_2523677 := by
    simpa [prefixWord, tailWord_2523677, baseEnd_2523677] using wordTrace_append hprefix tailTrace_2523677
  have hstable : (prefixWord ++ tailWord_2523677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523677).length < 2 ^ (prefixWord ++ tailWord_2523677).sum := by decide
  have hdescent : baseEnd_2523677 < baseStart_2523677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523740 : List Nat := [2, 2, 4, 1, 3, 1, 2, 8]
def baseStart_2523740 : Nat := 118140960795 + 2523740 * 2 ^ 59
def prefixEnd_2523740 : Nat := 4983230072969 + 3 ^ 40 * 2523740 * 2
def baseEnd_2523740 : Nat := 47995987665854114420131

theorem tailTrace_2523740 : CollatzResearch.WordTrace tailWord_2523740 prefixEnd_2523740 47995987665854114420131 := by
  unfold tailWord_2523740
  simp only [CollatzResearch.WordTrace]
  refine ⟨46024179938464237660908337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61365573251285650214544449 46024179938464237660908337)
  ·
    refine ⟨34518134953848178245681253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46024179938464237660908337 34518134953848178245681253)
    ·
      refine ⟨6472150303846533421065235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34518134953848178245681253 6472150303846533421065235)
      ·
        refine ⟨9708225455769800131597853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472150303846533421065235 9708225455769800131597853)
        ·
          refine ⟨3640584545913675049349195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9708225455769800131597853 3640584545913675049349195)
          ·
            refine ⟨5460876818870512574023793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640584545913675049349195 5460876818870512574023793)
            ·
              refine ⟨4095657614152884430517845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460876818870512574023793 4095657614152884430517845)
              ·
                refine ⟨47995987665854114420131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4095657614152884430517845 47995987665854114420131)
                ·
                  rfl

theorem cell23_2523740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 8].length) (baseStart_2523740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523740 prefixEnd_2523740 := by exact prefixLift 2523740
  have htrace : WordTrace (prefixWord ++ tailWord_2523740) baseStart_2523740 baseEnd_2523740 := by
    simpa [prefixWord, tailWord_2523740, baseEnd_2523740] using wordTrace_append hprefix tailTrace_2523740
  have hstable : (prefixWord ++ tailWord_2523740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523740).length < 2 ^ (prefixWord ++ tailWord_2523740).sum := by decide
  have hdescent : baseEnd_2523740 < baseStart_2523740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523778 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2523778 : Nat := 118140960795 + 2523778 * 2 ^ 59
def prefixEnd_2523778 : Nat := 4983230072969 + 3 ^ 40 * 2523778 * 2
def baseEnd_2523778 : Nat := 431970393080977313556121

theorem tailTrace_2523778 : CollatzResearch.WordTrace tailWord_2523778 prefixEnd_2523778 431970393080977313556121 := by
  unfold tailWord_2523778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012436462697701952924997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61366497233860538541133325 23012436462697701952924997)
  ·
    refine ⟨4314831836755819116173437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23012436462697701952924997 4314831836755819116173437)
    ·
      refine ⟨1618061938783432168565039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4314831836755819116173437 1618061938783432168565039)
      ·
        refine ⟨2427092908175148252847559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618061938783432168565039 2427092908175148252847559)
        ·
          refine ⟨3640639362262722379271339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427092908175148252847559 3640639362262722379271339)
          ·
            refine ⟨5460959043394083568907009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640639362262722379271339 5460959043394083568907009)
            ·
              refine ⟨4095719282545562676680257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460959043394083568907009 4095719282545562676680257)
              ·
                refine ⟨3071789461909172007510193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095719282545562676680257 3071789461909172007510193)
                ·
                  refine ⟨2303842096431879005632645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071789461909172007510193 2303842096431879005632645)
                  ·
                    refine ⟨431970393080977313556121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303842096431879005632645 431970393080977313556121)
                    ·
                      rfl

theorem cell23_2523778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2523778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523778 prefixEnd_2523778 := by exact prefixLift 2523778
  have htrace : WordTrace (prefixWord ++ tailWord_2523778) baseStart_2523778 baseEnd_2523778 := by
    simpa [prefixWord, tailWord_2523778, baseEnd_2523778] using wordTrace_append hprefix tailTrace_2523778
  have hstable : (prefixWord ++ tailWord_2523778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523778).length < 2 ^ (prefixWord ++ tailWord_2523778).sum := by decide
  have hdescent : baseEnd_2523778 < baseStart_2523778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523783 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 6]
def baseStart_2523783 : Nat := 118140960795 + 2523783 * 2 ^ 59
def prefixEnd_2523783 : Nat := 4983230072969 + 3 ^ 40 * 2523783 * 2
def baseEnd_2523783 : Nat := 431971248882068140368613

theorem tailTrace_2523783 : CollatzResearch.WordTrace tailWord_2523783 prefixEnd_2523783 431971248882068140368613 := by
  unfold tailWord_2523783
  simp only [CollatzResearch.WordTrace]
  refine ⟨92049928215772693665632003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61366618810515129110421335 92049928215772693665632003)
  ·
    refine ⟨138074892323659040498448005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92049928215772693665632003 138074892323659040498448005)
    ·
      refine ⟨25889042310686070093459001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138074892323659040498448005 25889042310686070093459001)
      ·
        refine ⟨19416781733014552570094251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25889042310686070093459001 19416781733014552570094251)
        ·
          refine ⟨29125172599521828855141377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19416781733014552570094251 29125172599521828855141377)
          ·
            refine ⟨21843879449641371641356033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29125172599521828855141377 21843879449641371641356033)
            ·
              refine ⟨16382909587231028731017025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21843879449641371641356033 16382909587231028731017025)
              ·
                refine ⟨12287182190423271548262769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16382909587231028731017025 12287182190423271548262769)
                ·
                  refine ⟨9215386642817453661197077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12287182190423271548262769 9215386642817453661197077)
                  ·
                    refine ⟨431971248882068140368613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9215386642817453661197077 431971248882068140368613)
                    ·
                      rfl

theorem cell23_2523783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_2523783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523783 prefixEnd_2523783 := by exact prefixLift 2523783
  have htrace : WordTrace (prefixWord ++ tailWord_2523783) baseStart_2523783 baseEnd_2523783 := by
    simpa [prefixWord, tailWord_2523783, baseEnd_2523783] using wordTrace_append hprefix tailTrace_2523783
  have hstable : (prefixWord ++ tailWord_2523783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523783).length < 2 ^ (prefixWord ++ tailWord_2523783).sum := by decide
  have hdescent : baseEnd_2523783 < baseStart_2523783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523840 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_2523840 : Nat := 118140960795 + 2523840 * 2 ^ 59
def prefixEnd_2523840 : Nat := 4983230072969 + 3 ^ 40 * 2523840 * 2
def baseEnd_2523840 : Nat := 1295943015043510698093077

theorem tailTrace_2523840 : CollatzResearch.WordTrace tailWord_2523840 prefixEnd_2523840 1295943015043510698093077 := by
  unfold tailWord_2523840
  simp only [CollatzResearch.WordTrace]
  refine ⟨46026003588283096200228487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61368004784377461600304649 46026003588283096200228487)
  ·
    refine ⟨69039005382424644300342731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46026003588283096200228487 69039005382424644300342731)
    ·
      refine ⟨103558508073636966450514097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69039005382424644300342731 103558508073636966450514097)
      ·
        refine ⟨77668881055227724837885573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103558508073636966450514097 77668881055227724837885573)
        ·
          refine ⟨14562915197855198407103545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77668881055227724837885573 14562915197855198407103545)
          ·
            refine ⟨10922186398391398805327659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14562915197855198407103545 10922186398391398805327659)
            ·
              refine ⟨16383279597587098207991489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922186398391398805327659 16383279597587098207991489)
              ·
                refine ⟨12287459698190323655993617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16383279597587098207991489 12287459698190323655993617)
                ·
                  refine ⟨9215594773642742741995213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12287459698190323655993617 9215594773642742741995213)
                  ·
                    refine ⟨3455848040116028528248205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9215594773642742741995213 3455848040116028528248205)
                    ·
                      refine ⟨1295943015043510698093077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3455848040116028528248205 1295943015043510698093077)
                      ·
                        rfl

theorem cell23_2523840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_2523840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523840 prefixEnd_2523840 := by exact prefixLift 2523840
  have htrace : WordTrace (prefixWord ++ tailWord_2523840) baseStart_2523840 baseEnd_2523840 := by
    simpa [prefixWord, tailWord_2523840, baseEnd_2523840] using wordTrace_append hprefix tailTrace_2523840
  have hstable : (prefixWord ++ tailWord_2523840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523840).length < 2 ^ (prefixWord ++ tailWord_2523840).sum := by decide
  have hdescent : baseEnd_2523840 < baseStart_2523840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523858 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2523858 : Nat := 118140960795 + 2523858 * 2 ^ 59
def prefixEnd_2523858 : Nat := 4983230072969 + 3 ^ 40 * 2523858 * 2
def baseEnd_2523858 : Nat := 1295952257695291627667995

theorem tailTrace_2523858 : CollatzResearch.WordTrace tailWord_2523858 prefixEnd_2523858 1295952257695291627667995 := by
  unfold tailWord_2523858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013165922625245368653057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61368442460333987649741485 23013165922625245368653057)
  ·
    refine ⟨17259874441968934026489793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23013165922625245368653057 17259874441968934026489793)
    ·
      refine ⟨12944905831476700519867345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17259874441968934026489793 12944905831476700519867345)
      ·
        refine ⟨9708679373607525389900509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12944905831476700519867345 9708679373607525389900509)
        ·
          refine ⟨3640754765102822021212691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9708679373607525389900509 3640754765102822021212691)
          ·
            refine ⟨5461132147654233031819037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640754765102822021212691 5461132147654233031819037)
            ·
              refine ⟨2047924555370337386932139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5461132147654233031819037 2047924555370337386932139)
              ·
                refine ⟨3071886833055506080398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047924555370337386932139 3071886833055506080398209)
                ·
                  refine ⟨2303915124791629560298657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071886833055506080398209 2303915124791629560298657)
                  ·
                    refine ⟨1727936343593722170223993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2303915124791629560298657 1727936343593722170223993)
                    ·
                      refine ⟨1295952257695291627667995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1727936343593722170223993 1295952257695291627667995)
                      ·
                        rfl

theorem cell23_2523858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2523858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523858 prefixEnd_2523858 := by exact prefixLift 2523858
  have htrace : WordTrace (prefixWord ++ tailWord_2523858) baseStart_2523858 baseEnd_2523858 := by
    simpa [prefixWord, tailWord_2523858, baseEnd_2523858] using wordTrace_append hprefix tailTrace_2523858
  have hstable : (prefixWord ++ tailWord_2523858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523858).length < 2 ^ (prefixWord ++ tailWord_2523858).sum := by decide
  have hdescent : baseEnd_2523858 < baseStart_2523858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
