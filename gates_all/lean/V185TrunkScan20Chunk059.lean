import V185TrunkScan20Chunk058

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_359029 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_359029 : Nat := 118140960795 + 359029 * 2 ^ 59
def prefixEnd_359029 : Nat := 4983230072969 + 3 ^ 40 * 359029 * 2
def baseEnd_359029 : Nat := 163870618580605360965655

theorem tailTrace_359029 : CollatzResearch.WordTrace tailWord_359029 prefixEnd_359029 163870618580605360965655 := by
  unfold tailWord_359029
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094863416306725116592141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729908944204483411061427 13094863416306725116592141)
  ·
    refine ⟨4910573781115021918722053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13094863416306725116592141 4910573781115021918722053)
    ·
      refine ⟨920732583959066609760385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4910573781115021918722053 920732583959066609760385)
      ·
        refine ⟨690549437969299957320289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920732583959066609760385 690549437969299957320289)
        ·
          refine ⟨517912078476974967990217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690549437969299957320289 517912078476974967990217)
          ·
            refine ⟨388434058857731225992663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517912078476974967990217 388434058857731225992663)
            ·
              refine ⟨582651088286596838988995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388434058857731225992663 582651088286596838988995)
              ·
                refine ⟨873976632429895258483493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582651088286596838988995 873976632429895258483493)
                ·
                  refine ⟨163870618580605360965655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873976632429895258483493 163870618580605360965655)
                  ·
                    rfl

theorem cell20_359029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_359029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359029 prefixEnd_359029 := by exact prefixLift 359029
  have htrace : WordTrace (prefixWord ++ tailWord_359029) baseStart_359029 baseEnd_359029 := by
    simpa [prefixWord, tailWord_359029, baseEnd_359029] using wordTrace_append hprefix tailTrace_359029
  have hstable : (prefixWord ++ tailWord_359029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359029).length < 2 ^ (prefixWord ++ tailWord_359029).sum := by decide
  have hdescent : baseEnd_359029 < baseStart_359029 := by decide
  rcases family_descends (prefixWord ++ tailWord_359029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359033 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_359033 : Nat := 118140960795 + 359033 * 2 ^ 59
def prefixEnd_359033 : Nat := 4983230072969 + 3 ^ 40 * 359033 * 2
def baseEnd_359033 : Nat := 163872444289599124832305

theorem tailTrace_359033 : CollatzResearch.WordTrace tailWord_359033 prefixEnd_359033 163872444289599124832305 := by
  unfold tailWord_359033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095009308292233799737753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8730006205528155866491835 13095009308292233799737753)
  ·
    refine ⟨9821256981219175349803315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13095009308292233799737753 9821256981219175349803315)
    ·
      refine ⟨14731885471828763024704973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821256981219175349803315 14731885471828763024704973)
      ·
        refine ⟨5524457051935786134264365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14731885471828763024704973 5524457051935786134264365)
        ·
          refine ⟨2071671394475919800349137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5524457051935786134264365 2071671394475919800349137)
          ·
            refine ⟨1553753545856939850261853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071671394475919800349137 1553753545856939850261853)
            ·
              refine ⟨582657579696352443848195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1553753545856939850261853 582657579696352443848195)
              ·
                refine ⟨873986369544528665772293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582657579696352443848195 873986369544528665772293)
                ·
                  refine ⟨163872444289599124832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873986369544528665772293 163872444289599124832305)
                  ·
                    rfl

theorem cell20_359033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_359033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359033 prefixEnd_359033 := by exact prefixLift 359033
  have htrace : WordTrace (prefixWord ++ tailWord_359033) baseStart_359033 baseEnd_359033 := by
    simpa [prefixWord, tailWord_359033, baseEnd_359033] using wordTrace_append hprefix tailTrace_359033
  have hstable : (prefixWord ++ tailWord_359033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359033).length < 2 ^ (prefixWord ++ tailWord_359033).sum := by decide
  have hdescent : baseEnd_359033 < baseStart_359033 := by decide
  rcases family_descends (prefixWord ++ tailWord_359033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359040 : List Nat := [2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_359040 : Nat := 118140960795 + 359040 * 2 ^ 59
def prefixEnd_359040 : Nat := 4983230072969 + 3 ^ 40 * 359040 * 2
def baseEnd_359040 : Nat := 54625213093446070532981

theorem tailTrace_359040 : CollatzResearch.WordTrace tailWord_359040 prefixEnd_359040 54625213093446070532981 := by
  unfold tailWord_359040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547632309633436997621287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8730176412844582663495049 6547632309633436997621287)
  ·
    refine ⟨9821448464450155496431931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6547632309633436997621287 9821448464450155496431931)
    ·
      refine ⟨14732172696675233244647897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821448464450155496431931 14732172696675233244647897)
      ·
        refine ⟨11049129522506424933485923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14732172696675233244647897 11049129522506424933485923)
        ·
          refine ⟨16573694283759637400228885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11049129522506424933485923 16573694283759637400228885)
          ·
            refine ⟨776891919551233003135729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16573694283759637400228885 776891919551233003135729)
            ·
              refine ⟨582668939663424752351797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776891919551233003135729 582668939663424752351797)
              ·
                refine ⟨54625213093446070532981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582668939663424752351797 54625213093446070532981)
                ·
                  rfl

theorem cell20_359040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_359040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359040 prefixEnd_359040 := by exact prefixLift 359040
  have htrace : WordTrace (prefixWord ++ tailWord_359040) baseStart_359040 baseEnd_359040 := by
    simpa [prefixWord, tailWord_359040, baseEnd_359040] using wordTrace_append hprefix tailTrace_359040
  have hstable : (prefixWord ++ tailWord_359040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359040).length < 2 ^ (prefixWord ++ tailWord_359040).sum := by decide
  have hdescent : baseEnd_359040 < baseStart_359040 := by decide
  rcases family_descends (prefixWord ++ tailWord_359040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359095 : List Nat := [1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_359095 : Nat := 118140960795 + 359095 * 2 ^ 59
def prefixEnd_359095 : Nat := 4983230072969 + 3 ^ 40 * 359095 * 2
def baseEnd_359095 : Nat := 54633580926334154921795

theorem tailTrace_359095 : CollatzResearch.WordTrace tailWord_359095 prefixEnd_359095 54633580926334154921795 := by
  unfold tailWord_359095
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097270634067618388494739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8731513756045078925663159 13097270634067618388494739)
  ·
    refine ⟨19645905951101427582742109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097270634067618388494739 19645905951101427582742109)
    ·
      refine ⟨7367214731663035343528291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19645905951101427582742109 7367214731663035343528291)
      ·
        refine ⟨11050822097494553015292437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367214731663035343528291 11050822097494553015292437)
        ·
          refine ⟨518007285820057172591833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11050822097494553015292437 518007285820057172591833)
          ·
            refine ⟨388505464365042879443875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518007285820057172591833 388505464365042879443875)
            ·
              refine ⟨582758196547564319165813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388505464365042879443875 582758196547564319165813)
              ·
                refine ⟨54633580926334154921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582758196547564319165813 54633580926334154921795)
                ·
                  rfl

theorem cell20_359095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_359095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359095 prefixEnd_359095 := by exact prefixLift 359095
  have htrace : WordTrace (prefixWord ++ tailWord_359095) baseStart_359095 baseEnd_359095 := by
    simpa [prefixWord, tailWord_359095, baseEnd_359095] using wordTrace_append hprefix tailTrace_359095
  have hstable : (prefixWord ++ tailWord_359095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359095).length < 2 ^ (prefixWord ++ tailWord_359095).sum := by decide
  have hdescent : baseEnd_359095 < baseStart_359095 := by decide
  rcases family_descends (prefixWord ++ tailWord_359095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359102 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_359102 : Nat := 118140960795 + 359102 * 2 ^ 59
def prefixEnd_359102 : Nat := 4983230072969 + 3 ^ 40 * 359102 * 2
def baseEnd_359102 : Nat := 163903937769741551532023

theorem tailTrace_359102 : CollatzResearch.WordTrace tailWord_359102 prefixEnd_359102 163903937769741551532023 := by
  unfold tailWord_359102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637190743130282322999945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8731683963361505722666373 1637190743130282322999945)
  ·
    refine ⟨1227893057347711742249959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1637190743130282322999945 1227893057347711742249959)
    ·
      refine ⟨1841839586021567613374939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227893057347711742249959 1841839586021567613374939)
      ·
        refine ⟨2762759379032351420062409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841839586021567613374939 2762759379032351420062409)
        ·
          refine ⟨2072069534274263565046807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2762759379032351420062409 2072069534274263565046807)
          ·
            refine ⟨3108104301411395347570211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072069534274263565046807 3108104301411395347570211)
            ·
              refine ⟨4662156452117093021355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108104301411395347570211 4662156452117093021355317)
              ·
                refine ⟨437077167385977470752061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4662156452117093021355317 437077167385977470752061)
                ·
                  refine ⟨163903937769741551532023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437077167385977470752061 163903937769741551532023)
                  ·
                    rfl

theorem cell20_359102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_359102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359102 prefixEnd_359102 := by exact prefixLift 359102
  have htrace : WordTrace (prefixWord ++ tailWord_359102) baseStart_359102 baseEnd_359102 := by
    simpa [prefixWord, tailWord_359102, baseEnd_359102] using wordTrace_append hprefix tailTrace_359102
  have hstable : (prefixWord ++ tailWord_359102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359102).length < 2 ^ (prefixWord ++ tailWord_359102).sum := by decide
  have hdescent : baseEnd_359102 < baseStart_359102 := by decide
  rcases family_descends (prefixWord ++ tailWord_359102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359105 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_359105 : Nat := 118140960795 + 359105 * 2 ^ 59
def prefixEnd_359105 : Nat := 4983230072969 + 3 ^ 40 * 359105 * 2
def baseEnd_359105 : Nat := 163905307051486874432011

theorem tailTrace_359105 : CollatzResearch.WordTrace tailWord_359105 prefixEnd_359105 163905307051486874432011 := by
  unfold tailWord_359105
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097635364031390096358769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8731756909354260064239179 13097635364031390096358769)
  ·
    refine ⟨9823226523023542572269077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13097635364031390096358769 9823226523023542572269077)
    ·
      refine ⟨460463743266728558075113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9823226523023542572269077 460463743266728558075113)
      ·
        refine ⟨345347807450046418556335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460463743266728558075113 345347807450046418556335)
        ·
          refine ⟨518021711175069627834503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345347807450046418556335 518021711175069627834503)
          ·
            refine ⟨777032566762604441751755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518021711175069627834503 777032566762604441751755)
            ·
              refine ⟨1165548850143906662627633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777032566762604441751755 1165548850143906662627633)
              ·
                refine ⟨874161637607929996970725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165548850143906662627633 874161637607929996970725)
                ·
                  refine ⟨163905307051486874432011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874161637607929996970725 163905307051486874432011)
                  ·
                    rfl

theorem cell20_359105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_359105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359105 prefixEnd_359105 := by exact prefixLift 359105
  have htrace : WordTrace (prefixWord ++ tailWord_359105) baseStart_359105 baseEnd_359105 := by
    simpa [prefixWord, tailWord_359105, baseEnd_359105] using wordTrace_append hprefix tailTrace_359105
  have hstable : (prefixWord ++ tailWord_359105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359105).length < 2 ^ (prefixWord ++ tailWord_359105).sum := by decide
  have hdescent : baseEnd_359105 < baseStart_359105 := by decide
  rcases family_descends (prefixWord ++ tailWord_359105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359130 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_359130 : Nat := 118140960795 + 359130 * 2 ^ 59
def prefixEnd_359130 : Nat := 4983230072969 + 3 ^ 40 * 359130 * 2
def baseEnd_359130 : Nat := 163916717732697898598575

theorem tailTrace_359130 : CollatzResearch.WordTrace tailWord_359130 prefixEnd_359130 163916717732697898598575 := by
  unfold tailWord_359130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274636797235204841504711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8732364792627212910679229 3274636797235204841504711)
  ·
    refine ⟨4911955195852807262257067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274636797235204841504711 4911955195852807262257067)
    ·
      refine ⟨7367932793779210893385601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4911955195852807262257067 7367932793779210893385601)
      ·
        refine ⟨5525949595334408170039201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7367932793779210893385601 5525949595334408170039201)
        ·
          refine ⟨4144462196500806127529401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5525949595334408170039201 4144462196500806127529401)
          ·
            refine ⟨3108346647375604595647051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144462196500806127529401 3108346647375604595647051)
            ·
              refine ⟨4662519971063406893470577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108346647375604595647051 4662519971063406893470577)
              ·
                refine ⟨3496889978297555170102933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662519971063406893470577 3496889978297555170102933)
                ·
                  refine ⟨163916717732697898598575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3496889978297555170102933 163916717732697898598575)
                  ·
                    rfl

theorem cell20_359130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_359130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359130 prefixEnd_359130 := by exact prefixLift 359130
  have htrace : WordTrace (prefixWord ++ tailWord_359130) baseStart_359130 baseEnd_359130 := by
    simpa [prefixWord, tailWord_359130, baseEnd_359130] using wordTrace_append hprefix tailTrace_359130
  have hstable : (prefixWord ++ tailWord_359130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359130).length < 2 ^ (prefixWord ++ tailWord_359130).sum := by decide
  have hdescent : baseEnd_359130 < baseStart_359130 := by decide
  rcases family_descends (prefixWord ++ tailWord_359130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359140 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_359140 : Nat := 118140960795 + 359140 * 2 ^ 59
def prefixEnd_359140 : Nat := 4983230072969 + 3 ^ 40 * 359140 * 2
def baseEnd_359140 : Nat := 163921282005182308265201

theorem tailTrace_359140 : CollatzResearch.WordTrace tailWord_359140 prefixEnd_359140 163921282005182308265201 := by
  unfold tailWord_359140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549455959452295536941437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8732607945936394049255249 6549455959452295536941437)
  ·
    refine ⟨2456045984794610826353039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6549455959452295536941437 2456045984794610826353039)
    ·
      refine ⟨3684068977191916239529559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456045984794610826353039 3684068977191916239529559)
      ·
        refine ⟨5526103465787874359294339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684068977191916239529559 5526103465787874359294339)
        ·
          refine ⟨8289155198681811538941509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526103465787874359294339 8289155198681811538941509)
          ·
            refine ⟨1554216599752839663551533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8289155198681811538941509 1554216599752839663551533)
            ·
              refine ⟨582831224907314873831825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554216599752839663551533 582831224907314873831825)
              ·
                refine ⟨437123418680486155373869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582831224907314873831825 437123418680486155373869)
                ·
                  refine ⟨163921282005182308265201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437123418680486155373869 163921282005182308265201)
                  ·
                    rfl

theorem cell20_359140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_359140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359140 prefixEnd_359140 := by exact prefixLift 359140
  have htrace : WordTrace (prefixWord ++ tailWord_359140) baseStart_359140 baseEnd_359140 := by
    simpa [prefixWord, tailWord_359140, baseEnd_359140] using wordTrace_append hprefix tailTrace_359140
  have hstable : (prefixWord ++ tailWord_359140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359140).length < 2 ^ (prefixWord ++ tailWord_359140).sum := by decide
  have hdescent : baseEnd_359140 < baseStart_359140 := by decide
  rcases family_descends (prefixWord ++ tailWord_359140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359161 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_359161 : Nat := 118140960795 + 359161 * 2 ^ 59
def prefixEnd_359161 : Nat := 4983230072969 + 3 ^ 40 * 359161 * 2
def baseEnd_359161 : Nat := 163930866977399568565115

theorem tailTrace_359161 : CollatzResearch.WordTrace tailWord_359161 prefixEnd_359161 163930866977399568565115 := by
  unfold tailWord_359161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099677851828511660397337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8733118567885674440264891 13099677851828511660397337)
  ·
    refine ⟨9824758388871383745298003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13099677851828511660397337 9824758388871383745298003)
    ·
      refine ⟨14737137583307075617947005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9824758388871383745298003 14737137583307075617947005)
      ·
        refine ⟨5526426593740153356730127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14737137583307075617947005 5526426593740153356730127)
        ·
          refine ⟨8289639890610230035095191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526426593740153356730127 8289639890610230035095191)
          ·
            refine ⟨12434459835915345052642787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289639890610230035095191 12434459835915345052642787)
            ·
              refine ⟨18651689753873017578964181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12434459835915345052642787 18651689753873017578964181)
              ·
                refine ⟨437148978606398849506973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18651689753873017578964181 437148978606398849506973)
                ·
                  refine ⟨163930866977399568565115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437148978606398849506973 163930866977399568565115)
                  ·
                    rfl

theorem cell20_359161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_359161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359161 prefixEnd_359161 := by exact prefixLift 359161
  have htrace : WordTrace (prefixWord ++ tailWord_359161) baseStart_359161 baseEnd_359161 := by
    simpa [prefixWord, tailWord_359161, baseEnd_359161] using wordTrace_append hprefix tailTrace_359161
  have hstable : (prefixWord ++ tailWord_359161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359161).length < 2 ^ (prefixWord ++ tailWord_359161).sum := by decide
  have hdescent : baseEnd_359161 < baseStart_359161 := by decide
  rcases family_descends (prefixWord ++ tailWord_359161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359199 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_359199 : Nat := 118140960795 + 359199 * 2 ^ 59
def prefixEnd_359199 : Nat := 4983230072969 + 3 ^ 40 * 359199 * 2
def baseEnd_359199 : Nat := 163948211212840325298293

theorem tailTrace_359199 : CollatzResearch.WordTrace tailWord_359199 prefixEnd_359199 163948211212840325298293 := by
  unfold tailWord_359199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13101063825690844150280651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8734042550460562766853767 13101063825690844150280651)
  ·
    refine ⟨19651595738536266225420977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13101063825690844150280651 19651595738536266225420977)
    ·
      refine ⟨14738696803902199669065733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19651595738536266225420977 14738696803902199669065733)
      ·
        refine ⟨2763505650731662437949825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14738696803902199669065733 2763505650731662437949825)
        ·
          refine ⟨2072629238048746828462369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2763505650731662437949825 2072629238048746828462369)
          ·
            refine ⟨1554471928536560121346777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072629238048746828462369 1554471928536560121346777)
            ·
              refine ⟨1165853946402420091010083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554471928536560121346777 1165853946402420091010083)
              ·
                refine ⟨1748780919603630136515125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165853946402420091010083 1748780919603630136515125)
                ·
                  refine ⟨163948211212840325298293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1748780919603630136515125 163948211212840325298293)
                  ·
                    rfl

theorem cell20_359199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_359199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359199 prefixEnd_359199 := by exact prefixLift 359199
  have htrace : WordTrace (prefixWord ++ tailWord_359199) baseStart_359199 baseEnd_359199 := by
    simpa [prefixWord, tailWord_359199, baseEnd_359199] using wordTrace_append hprefix tailTrace_359199
  have hstable : (prefixWord ++ tailWord_359199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359199).length < 2 ^ (prefixWord ++ tailWord_359199).sum := by decide
  have hdescent : baseEnd_359199 < baseStart_359199 := by decide
  rcases family_descends (prefixWord ++ tailWord_359199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359202 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_359202 : Nat := 118140960795 + 359202 * 2 ^ 59
def prefixEnd_359202 : Nat := 4983230072969 + 3 ^ 40 * 359202 * 2
def baseEnd_359202 : Nat := 163949580494585648198281

theorem tailTrace_359202 : CollatzResearch.WordTrace tailWord_359202 prefixEnd_359202 163949580494585648198281 := by
  unfold tailWord_359202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275293311169993915659965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8734115496453317108426573 3275293311169993915659965)
  ·
    refine ⟨1228234991688747718372487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3275293311169993915659965 1228234991688747718372487)
    ·
      refine ⟨1842352487533121577558731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228234991688747718372487 1842352487533121577558731)
      ·
        refine ⟨2763528731299682366338097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842352487533121577558731 2763528731299682366338097)
        ·
          refine ⟨2072646548474761774753573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2763528731299682366338097 2072646548474761774753573)
          ·
            refine ⟨388621227839017832766295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2072646548474761774753573 388621227839017832766295)
            ·
              refine ⟨582931841758526749149443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388621227839017832766295 582931841758526749149443)
              ·
                refine ⟨874397762637790123724165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582931841758526749149443 874397762637790123724165)
                ·
                  refine ⟨163949580494585648198281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874397762637790123724165 163949580494585648198281)
                  ·
                    rfl

theorem cell20_359202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_359202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359202 prefixEnd_359202 := by exact prefixLift 359202
  have htrace : WordTrace (prefixWord ++ tailWord_359202) baseStart_359202 baseEnd_359202 := by
    simpa [prefixWord, tailWord_359202, baseEnd_359202] using wordTrace_append hprefix tailTrace_359202
  have hstable : (prefixWord ++ tailWord_359202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359202).length < 2 ^ (prefixWord ++ tailWord_359202).sum := by decide
  have hdescent : baseEnd_359202 < baseStart_359202 := by decide
  rcases family_descends (prefixWord ++ tailWord_359202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359257 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 2]
def baseStart_359257 : Nat := 118140960795 + 359257 * 2 ^ 59
def prefixEnd_359257 : Nat := 4983230072969 + 3 ^ 40 * 359257 * 2
def baseEnd_359257 : Nat := 163974683993249901364723

theorem tailTrace_359257 : CollatzResearch.WordTrace tailWord_359257 prefixEnd_359257 163974683993249901364723 := by
  unfold tailWord_359257
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103179259480720055892025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735452839653813370594683 13103179259480720055892025)
  ·
    refine ⟨9827384444610540041919019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13103179259480720055892025 9827384444610540041919019)
    ·
      refine ⟨14741076666915810062878529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9827384444610540041919019 14741076666915810062878529)
      ·
        refine ⟨11055807500186857547158897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14741076666915810062878529 11055807500186857547158897)
        ·
          refine ⟨8291855625140143160369173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11055807500186857547158897 8291855625140143160369173)
          ·
            refine ⟨388680732428444210642305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8291855625140143160369173 388680732428444210642305)
            ·
              refine ⟨291510549321333157981729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388680732428444210642305 291510549321333157981729)
              ·
                refine ⟨218632911990999868486297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291510549321333157981729 218632911990999868486297)
                ·
                  refine ⟨163974683993249901364723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218632911990999868486297 163974683993249901364723)
                  ·
                    rfl

theorem cell20_359257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_359257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359257 prefixEnd_359257 := by exact prefixLift 359257
  have htrace : WordTrace (prefixWord ++ tailWord_359257) baseStart_359257 baseEnd_359257 := by
    simpa [prefixWord, tailWord_359257, baseEnd_359257] using wordTrace_append hprefix tailTrace_359257
  have hstable : (prefixWord ++ tailWord_359257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359257).length < 2 ^ (prefixWord ++ tailWord_359257).sum := by decide
  have hdescent : baseEnd_359257 < baseStart_359257 := by decide
  rcases family_descends (prefixWord ++ tailWord_359257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359268 : List Nat := [2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_359268 : Nat := 118140960795 + 359268 * 2 ^ 59
def prefixEnd_359268 : Nat := 4983230072969 + 3 ^ 40 * 359268 * 2
def baseEnd_359268 : Nat := 54659901564327583999337

theorem tailTrace_359268 : CollatzResearch.WordTrace tailWord_359268 prefixEnd_359268 54659901564327583999337 := by
  unfold tailWord_359268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551790231220434467271229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8735720308293912623028305 6551790231220434467271229)
  ·
    refine ⟨2456921336707662925226711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6551790231220434467271229 2456921336707662925226711)
    ·
      refine ⟨3685382005061494387840067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456921336707662925226711 3685382005061494387840067)
      ·
        refine ⟨5528073007592241581760101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685382005061494387840067 5528073007592241581760101)
        ·
          refine ⟨1036513688923545296580019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5528073007592241581760101 1036513688923545296580019)
          ·
            refine ⟨1554770533385317944870029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036513688923545296580019 1554770533385317944870029)
            ·
              refine ⟨583038950019494229326261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554770533385317944870029 583038950019494229326261)
              ·
                refine ⟨54659901564327583999337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583038950019494229326261 54659901564327583999337)
                ·
                  rfl

theorem cell20_359268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_359268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359268 prefixEnd_359268 := by exact prefixLift 359268
  have htrace : WordTrace (prefixWord ++ tailWord_359268) baseStart_359268 baseEnd_359268 := by
    simpa [prefixWord, tailWord_359268, baseEnd_359268] using wordTrace_append hprefix tailTrace_359268
  have hstable : (prefixWord ++ tailWord_359268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359268).length < 2 ^ (prefixWord ++ tailWord_359268).sum := by decide
  have hdescent : baseEnd_359268 < baseStart_359268 := by decide
  rcases family_descends (prefixWord ++ tailWord_359268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359275 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_359275 : Nat := 118140960795 + 359275 * 2 ^ 59
def prefixEnd_359275 : Nat := 4983230072969 + 3 ^ 40 * 359275 * 2
def baseEnd_359275 : Nat := 163982899683721838764649

theorem tailTrace_359275 : CollatzResearch.WordTrace tailWord_359275 prefixEnd_359275 163982899683721838764649 := by
  unfold tailWord_359275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103835773415509130047279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735890515610339420031519 13103835773415509130047279)
  ·
    refine ⟨19655753660123263695070919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103835773415509130047279 19655753660123263695070919)
    ·
      refine ⟨29483630490184895542606379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655753660123263695070919 29483630490184895542606379)
      ·
        refine ⟨44225445735277343313909569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29483630490184895542606379 44225445735277343313909569)
        ·
          refine ⟨33169084301458007485432177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44225445735277343313909569 33169084301458007485432177)
          ·
            refine ⟨24876813226093505614074133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33169084301458007485432177 24876813226093505614074133)
            ·
              refine ⟨1166100619973133075659725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24876813226093505614074133 1166100619973133075659725)
              ·
                refine ⟨437287732489924903372397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1166100619973133075659725 437287732489924903372397)
                ·
                  refine ⟨163982899683721838764649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437287732489924903372397 163982899683721838764649)
                  ·
                    rfl

theorem cell20_359275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_359275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359275 prefixEnd_359275 := by exact prefixLift 359275
  have htrace : WordTrace (prefixWord ++ tailWord_359275) baseStart_359275 baseEnd_359275 := by
    simpa [prefixWord, tailWord_359275, baseEnd_359275] using wordTrace_append hprefix tailTrace_359275
  have hstable : (prefixWord ++ tailWord_359275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359275).length < 2 ^ (prefixWord ++ tailWord_359275).sum := by decide
  have hdescent : baseEnd_359275 < baseStart_359275 := by decide
  rcases family_descends (prefixWord ++ tailWord_359275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359278 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_359278 : Nat := 118140960795 + 359278 * 2 ^ 59
def prefixEnd_359278 : Nat := 4983230072969 + 3 ^ 40 * 359278 * 2
def baseEnd_359278 : Nat := 163984268965467161664637

theorem tailTrace_359278 : CollatzResearch.WordTrace tailWord_359278 prefixEnd_359278 163984268965467161664637 := by
  unfold tailWord_359278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637993149050580080300811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8735963461603093761604325 1637993149050580080300811)
  ·
    refine ⟨2456989723575870120451217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1637993149050580080300811 2456989723575870120451217)
    ·
      refine ⟨1842742292681902590338413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2456989723575870120451217 1842742292681902590338413)
      ·
        refine ⟨691028359755713471376905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1842742292681902590338413 691028359755713471376905)
        ·
          refine ⟨518271269816785103532679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691028359755713471376905 518271269816785103532679)
          ·
            refine ⟨777406904725177655299019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518271269816785103532679 777406904725177655299019)
            ·
              refine ⟨1166110357087766482948529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777406904725177655299019 1166110357087766482948529)
              ·
                refine ⟨874582767815824862211397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166110357087766482948529 874582767815824862211397)
                ·
                  refine ⟨163984268965467161664637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874582767815824862211397 163984268965467161664637)
                  ·
                    rfl

theorem cell20_359278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_359278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359278 prefixEnd_359278 := by exact prefixLift 359278
  have htrace : WordTrace (prefixWord ++ tailWord_359278) baseStart_359278 baseEnd_359278 := by
    simpa [prefixWord, tailWord_359278, baseEnd_359278] using wordTrace_append hprefix tailTrace_359278
  have hstable : (prefixWord ++ tailWord_359278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359278).length < 2 ^ (prefixWord ++ tailWord_359278).sum := by decide
  have hdescent : baseEnd_359278 < baseStart_359278 := by decide
  rcases family_descends (prefixWord ++ tailWord_359278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359282 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_359282 : Nat := 118140960795 + 359282 * 2 ^ 59
def prefixEnd_359282 : Nat := 4983230072969 + 3 ^ 40 * 359282 * 2
def baseEnd_359282 : Nat := 163986094674460925531287

theorem tailTrace_359282 : CollatzResearch.WordTrace tailWord_359282 prefixEnd_359282 163986094674460925531287 := by
  unfold tailWord_359282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276022771097537331388025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8736060722926766217034733 3276022771097537331388025)
  ·
    refine ⟨2457017078323152998541019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3276022771097537331388025 2457017078323152998541019)
    ·
      refine ⟨3685525617484729497811529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457017078323152998541019 3685525617484729497811529)
      ·
        refine ⟨2764144213113547123358647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685525617484729497811529 2764144213113547123358647)
        ·
          refine ⟨4146216319670320685037971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764144213113547123358647 4146216319670320685037971)
          ·
            refine ⟨6219324479505481027556957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146216319670320685037971 6219324479505481027556957)
            ·
              refine ⟨2332246679814555385333859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6219324479505481027556957 2332246679814555385333859)
              ·
                refine ⟨3498370019721833078000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332246679814555385333859 3498370019721833078000789)
                ·
                  refine ⟨163986094674460925531287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3498370019721833078000789 163986094674460925531287)
                  ·
                    rfl

theorem cell20_359282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_359282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359282 prefixEnd_359282 := by exact prefixLift 359282
  have htrace : WordTrace (prefixWord ++ tailWord_359282) baseStart_359282 baseEnd_359282 := by
    simpa [prefixWord, tailWord_359282, baseEnd_359282] using wordTrace_append hprefix tailTrace_359282
  have hstable : (prefixWord ++ tailWord_359282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359282).length < 2 ^ (prefixWord ++ tailWord_359282).sum := by decide
  have hdescent : baseEnd_359282 < baseStart_359282 := by decide
  rcases family_descends (prefixWord ++ tailWord_359282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359285 : List Nat := [1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_359285 : Nat := 118140960795 + 359285 * 2 ^ 59
def prefixEnd_359285 : Nat := 4983230072969 + 3 ^ 40 * 359285 * 2
def baseEnd_359285 : Nat := 54662487985402082810425

theorem tailTrace_359285 : CollatzResearch.WordTrace tailWord_359285 prefixEnd_359285 54662487985402082810425 := by
  unfold tailWord_359285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104200503379280837911309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8736133668919520558607539 13104200503379280837911309)
  ·
    refine ⟨4914075188767230314216741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13104200503379280837911309 4914075188767230314216741)
    ·
      refine ⟨921389097893855683915639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4914075188767230314216741 921389097893855683915639)
      ·
        refine ⟨1382083646840783525873459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921389097893855683915639 1382083646840783525873459)
        ·
          refine ⟨2073125470261175288810189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382083646840783525873459 2073125470261175288810189)
          ·
            refine ⟨777422051347940733303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2073125470261175288810189 777422051347940733303821)
            ·
              refine ⟨291533269255477774988933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777422051347940733303821 291533269255477774988933)
              ·
                refine ⟨54662487985402082810425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291533269255477774988933 54662487985402082810425)
                ·
                  rfl

theorem cell20_359285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_359285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359285 prefixEnd_359285 := by exact prefixLift 359285
  have htrace : WordTrace (prefixWord ++ tailWord_359285) baseStart_359285 baseEnd_359285 := by
    simpa [prefixWord, tailWord_359285, baseEnd_359285] using wordTrace_append hprefix tailTrace_359285
  have hstable : (prefixWord ++ tailWord_359285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359285).length < 2 ^ (prefixWord ++ tailWord_359285).sum := by decide
  have hdescent : baseEnd_359285 < baseStart_359285 := by decide
  rcases family_descends (prefixWord ++ tailWord_359285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359306 : List Nat := [3, 1, 2, 4, 1, 2, 7]
def baseStart_359306 : Nat := 118140960795 + 359306 * 2 ^ 59
def prefixEnd_359306 : Nat := 4983230072969 + 3 ^ 40 * 359306 * 2
def baseEnd_359306 : Nat := 18221894325380389859021

theorem tailTrace_359306 : CollatzResearch.WordTrace tailWord_359306 prefixEnd_359306 18221894325380389859021 := by
  unfold tailWord_359306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276241609075800356106443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8736644290868800949617181 3276241609075800356106443)
  ·
    refine ⟨4914362413613700534159665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276241609075800356106443 4914362413613700534159665)
    ·
      refine ⟨3685771810210275400619749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4914362413613700534159665 3685771810210275400619749)
      ·
        refine ⟨691082214414426637616203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3685771810210275400619749 691082214414426637616203)
        ·
          refine ⟨1036623321621639956424305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691082214414426637616203 1036623321621639956424305)
          ·
            refine ⟨777467491216229967318229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036623321621639956424305 777467491216229967318229)
            ·
              refine ⟨18221894325380389859021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 777467491216229967318229 18221894325380389859021)
              ·
                rfl

theorem cell20_359306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_359306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359306 prefixEnd_359306 := by exact prefixLift 359306
  have htrace : WordTrace (prefixWord ++ tailWord_359306) baseStart_359306 baseEnd_359306 := by
    simpa [prefixWord, tailWord_359306, baseEnd_359306] using wordTrace_append hprefix tailTrace_359306
  have hstable : (prefixWord ++ tailWord_359306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359306).length < 2 ^ (prefixWord ++ tailWord_359306).sum := by decide
  have hdescent : baseEnd_359306 < baseStart_359306 := by decide
  rcases family_descends (prefixWord ++ tailWord_359306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359316 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_359316 : Nat := 118140960795 + 359316 * 2 ^ 59
def prefixEnd_359316 : Nat := 4983230072969 + 3 ^ 40 * 359316 * 2
def baseEnd_359316 : Nat := 164001613200907918397815

theorem tailTrace_359316 : CollatzResearch.WordTrace tailWord_359316 prefixEnd_359316 164001613200907918397815 := by
  unfold tailWord_359316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6552665583133486566144901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8736887444177982088193201 6552665583133486566144901)
  ·
    refine ⟨1228624796837528731152169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6552665583133486566144901 1228624796837528731152169)
    ·
      refine ⟨921468597628146548364127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228624796837528731152169 921468597628146548364127)
      ·
        refine ⟨1382202896442219822546191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921468597628146548364127 1382202896442219822546191)
        ·
          refine ⟨2073304344663329733819287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382202896442219822546191 2073304344663329733819287)
          ·
            refine ⟨3109956516994994600728931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073304344663329733819287 3109956516994994600728931)
            ·
              refine ⟨4664934775492491901093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109956516994994600728931 4664934775492491901093397)
              ·
                refine ⟨218668817601210557863753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4664934775492491901093397 218668817601210557863753)
                ·
                  refine ⟨164001613200907918397815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218668817601210557863753 164001613200907918397815)
                  ·
                    rfl

theorem cell20_359316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_359316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359316 prefixEnd_359316 := by exact prefixLift 359316
  have htrace : WordTrace (prefixWord ++ tailWord_359316) baseStart_359316 baseEnd_359316 := by
    simpa [prefixWord, tailWord_359316, baseEnd_359316] using wordTrace_append hprefix tailTrace_359316
  have hstable : (prefixWord ++ tailWord_359316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359316).length < 2 ^ (prefixWord ++ tailWord_359316).sum := by decide
  have hdescent : baseEnd_359316 < baseStart_359316 := by decide
  rcases family_descends (prefixWord ++ tailWord_359316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359375 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_359375 : Nat := 118140960795 + 359375 * 2 ^ 59
def prefixEnd_359375 : Nat := 4983230072969 + 3 ^ 40 * 359375 * 2
def baseEnd_359375 : Nat := 164028542408565935430907

theorem tailTrace_359375 : CollatzResearch.WordTrace tailWord_359375 prefixEnd_359375 164028542408565935430907 := by
  unfold tailWord_359375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107483073053226208687579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8738322048702150805791719 13107483073053226208687579)
  ·
    refine ⟨19661224609579839313031369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107483073053226208687579 19661224609579839313031369)
    ·
      refine ⟨14745918457184879484773527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19661224609579839313031369 14745918457184879484773527)
      ·
        refine ⟨22118877685777319227160291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745918457184879484773527 22118877685777319227160291)
        ·
          refine ⟨33178316528665978840740437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22118877685777319227160291 33178316528665978840740437)
          ·
            refine ⟨388808396820304439539927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 33178316528665978840740437 388808396820304439539927)
            ·
              refine ⟨583212595230456659309891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388808396820304439539927 583212595230456659309891)
              ·
                refine ⟨874818892845684988964837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583212595230456659309891 874818892845684988964837)
                ·
                  refine ⟨164028542408565935430907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874818892845684988964837 164028542408565935430907)
                  ·
                    rfl

theorem cell20_359375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_359375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359375 prefixEnd_359375 := by exact prefixLift 359375
  have htrace : WordTrace (prefixWord ++ tailWord_359375) baseStart_359375 baseEnd_359375 := by
    simpa [prefixWord, tailWord_359375, baseEnd_359375] using wordTrace_append hprefix tailTrace_359375
  have hstable : (prefixWord ++ tailWord_359375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359375).length < 2 ^ (prefixWord ++ tailWord_359375).sum := by decide
  have hdescent : baseEnd_359375 < baseStart_359375 := by decide
  rcases family_descends (prefixWord ++ tailWord_359375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359385 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_359385 : Nat := 118140960795 + 359385 * 2 ^ 59
def prefixEnd_359385 : Nat := 4983230072969 + 3 ^ 40 * 359385 * 2
def baseEnd_359385 : Nat := 164033106681050345097533

theorem tailTrace_359385 : CollatzResearch.WordTrace tailWord_359385 prefixEnd_359385 164033106681050345097533 := by
  unfold tailWord_359385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107847803016997916551609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8738565202011331944367739 13107847803016997916551609)
  ·
    refine ⟨9830885852262748437413707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13107847803016997916551609 9830885852262748437413707)
    ·
      refine ⟨14746328778394122656120561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9830885852262748437413707 14746328778394122656120561)
      ·
        refine ⟨11059746583795591992090421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14746328778394122656120561 11059746583795591992090421)
        ·
          refine ⟨1036851242230836749258477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11059746583795591992090421 1036851242230836749258477)
          ·
            refine ⟨388819215836563780971929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1036851242230836749258477 388819215836563780971929)
            ·
              refine ⟨291614411877422835728947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388819215836563780971929 291614411877422835728947)
              ·
                refine ⟨437421617816134253593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291614411877422835728947 437421617816134253593421)
                ·
                  refine ⟨164033106681050345097533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437421617816134253593421 164033106681050345097533)
                  ·
                    rfl

theorem cell20_359385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_359385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359385 prefixEnd_359385 := by exact prefixLift 359385
  have htrace : WordTrace (prefixWord ++ tailWord_359385) baseStart_359385 baseEnd_359385 := by
    simpa [prefixWord, tailWord_359385, baseEnd_359385] using wordTrace_append hprefix tailTrace_359385
  have hstable : (prefixWord ++ tailWord_359385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359385).length < 2 ^ (prefixWord ++ tailWord_359385).sum := by decide
  have hdescent : baseEnd_359385 < baseStart_359385 := by decide
  rcases family_descends (prefixWord ++ tailWord_359385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359426 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_359426 : Nat := 118140960795 + 359426 * 2 ^ 59
def prefixEnd_359426 : Nat := 4983230072969 + 3 ^ 40 * 359426 * 2
def baseEnd_359426 : Nat := 164051820198236424730699

theorem tailTrace_359426 : CollatzResearch.WordTrace tailWord_359426 prefixEnd_359426 164051820198236424730699 := by
  unfold tailWord_359426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277335798967115479698533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8739562130578974612529421 3277335798967115479698533)
  ·
    refine ⟨614500462306334152443475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3277335798967115479698533 614500462306334152443475)
    ·
      refine ⟨921750693459501228665213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614500462306334152443475 921750693459501228665213)
      ·
        refine ⟨345656510047312960749455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 921750693459501228665213 345656510047312960749455)
        ·
          refine ⟨518484765070969441124183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345656510047312960749455 518484765070969441124183)
          ·
            refine ⟨777727147606454161686275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518484765070969441124183 777727147606454161686275)
            ·
              refine ⟨1166590721409681242529413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777727147606454161686275 1166590721409681242529413)
              ·
                refine ⟨218735760264315232974265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1166590721409681242529413 218735760264315232974265)
                ·
                  refine ⟨164051820198236424730699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218735760264315232974265 164051820198236424730699)
                  ·
                    rfl

theorem cell20_359426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_359426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359426 prefixEnd_359426 := by exact prefixLift 359426
  have htrace : WordTrace (prefixWord ++ tailWord_359426) baseStart_359426 baseEnd_359426 := by
    simpa [prefixWord, tailWord_359426, baseEnd_359426] using wordTrace_append hprefix tailTrace_359426
  have hstable : (prefixWord ++ tailWord_359426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359426).length < 2 ^ (prefixWord ++ tailWord_359426).sum := by decide
  have hdescent : baseEnd_359426 < baseStart_359426 := by decide
  rcases family_descends (prefixWord ++ tailWord_359426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359534 : List Nat := [4, 1, 2, 2, 1, 4, 6]
def baseStart_359534 : Nat := 118140960795 + 359534 * 2 ^ 59
def prefixEnd_359534 : Nat := 4983230072969 + 3 ^ 40 * 359534 * 2
def baseEnd_359534 : Nat := 18233457149007561014473

theorem tailTrace_359534 : CollatzResearch.WordTrace tailWord_359534 prefixEnd_359534 18233457149007561014473 := by
  unfold tailWord_359534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639160284934649545465707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8742188186318130909150437 1639160284934649545465707)
  ·
    refine ⟨2458740427401974318198561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639160284934649545465707 2458740427401974318198561)
    ·
      refine ⟨1844055320551480738648921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2458740427401974318198561 1844055320551480738648921)
      ·
        refine ⟨1383041490413610553986691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844055320551480738648921 1383041490413610553986691)
        ·
          refine ⟨2074562235620415830980037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383041490413610553986691 2074562235620415830980037)
          ·
            refine ⟨388980419178827968308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2074562235620415830980037 388980419178827968308757)
            ·
              refine ⟨18233457149007561014473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 388980419178827968308757 18233457149007561014473)
              ·
                rfl

theorem cell20_359534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_359534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359534 prefixEnd_359534 := by exact prefixLift 359534
  have htrace : WordTrace (prefixWord ++ tailWord_359534) baseStart_359534 baseEnd_359534 := by
    simpa [prefixWord, tailWord_359534, baseEnd_359534] using wordTrace_append hprefix tailTrace_359534
  have hstable : (prefixWord ++ tailWord_359534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359534).length < 2 ^ (prefixWord ++ tailWord_359534).sum := by decide
  have hdescent : baseEnd_359534 < baseStart_359534 := by decide
  rcases family_descends (prefixWord ++ tailWord_359534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359550 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_359550 : Nat := 118140960795 + 359550 * 2 ^ 59
def prefixEnd_359550 : Nat := 4983230072969 + 3 ^ 40 * 359550 * 2
def baseEnd_359550 : Nat := 164108417177043104596859

theorem tailTrace_359550 : CollatzResearch.WordTrace tailWord_359550 prefixEnd_359550 164108417177043104596859 := by
  unfold tailWord_359550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639233230927403887038513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8742577231612820730872069 1639233230927403887038513)
  ·
    refine ⟨1229424923195552915278885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1639233230927403887038513 1229424923195552915278885)
    ·
      refine ⟨230517173099166171614791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1229424923195552915278885 230517173099166171614791)
      ·
        refine ⟨345775759648749257422187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230517173099166171614791 345775759648749257422187)
        ·
          refine ⟨518663639473123886133281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345775759648749257422187 518663639473123886133281)
          ·
            refine ⟨388997729604842914599961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518663639473123886133281 388997729604842914599961)
            ·
              refine ⟨291748297203632185949971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388997729604842914599961 291748297203632185949971)
              ·
                refine ⟨437622445805448278924957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291748297203632185949971 437622445805448278924957)
                ·
                  refine ⟨164108417177043104596859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437622445805448278924957 164108417177043104596859)
                  ·
                    rfl

theorem cell20_359550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_359550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359550 prefixEnd_359550 := by exact prefixLift 359550
  have htrace : WordTrace (prefixWord ++ tailWord_359550) baseStart_359550 baseEnd_359550 := by
    simpa [prefixWord, tailWord_359550, baseEnd_359550] using wordTrace_append hprefix tailTrace_359550
  have hstable : (prefixWord ++ tailWord_359550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359550).length < 2 ^ (prefixWord ++ tailWord_359550).sum := by decide
  have hdescent : baseEnd_359550 < baseStart_359550 := by decide
  rcases family_descends (prefixWord ++ tailWord_359550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359555 : List Nat := [1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_359555 : Nat := 118140960795 + 359555 * 2 ^ 59
def prefixEnd_359555 : Nat := 4983230072969 + 3 ^ 40 * 359555 * 2
def baseEnd_359555 : Nat := 54703566437761769810057

theorem tailTrace_359555 : CollatzResearch.WordTrace tailWord_359555 prefixEnd_359555 54703566437761769810057 := by
  unfold tailWord_359555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114048212401116950240119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8742698808267411300160079 13114048212401116950240119)
  ·
    refine ⟨19671072318601675425360179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13114048212401116950240119 19671072318601675425360179)
    ·
      refine ⟨29506608477902513138040269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19671072318601675425360179 29506608477902513138040269)
      ·
        refine ⟨11064978179213442426765101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29506608477902513138040269 11064978179213442426765101)
        ·
          refine ⟨4149366817205040910036913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11064978179213442426765101 4149366817205040910036913)
          ·
            refine ⟨3112025112903780682527685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149366817205040910036913 3112025112903780682527685)
            ·
              refine ⟨583504708669458877973941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3112025112903780682527685 583504708669458877973941)
              ·
                refine ⟨54703566437761769810057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583504708669458877973941 54703566437761769810057)
                ·
                  rfl

theorem cell20_359555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_359555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359555 prefixEnd_359555 := by exact prefixLift 359555
  have htrace : WordTrace (prefixWord ++ tailWord_359555) baseStart_359555 baseEnd_359555 := by
    simpa [prefixWord, tailWord_359555, baseEnd_359555] using wordTrace_append hprefix tailTrace_359555
  have hstable : (prefixWord ++ tailWord_359555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359555).length < 2 ^ (prefixWord ++ tailWord_359555).sum := by decide
  have hdescent : baseEnd_359555 < baseStart_359555 := by decide
  rcases family_descends (prefixWord ++ tailWord_359555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359662 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_359662 : Nat := 118140960795 + 359662 * 2 ^ 59
def prefixEnd_359662 : Nat := 4983230072969 + 3 ^ 40 * 359662 * 2
def baseEnd_359662 : Nat := 164159537028868492863067

theorem tailTrace_359662 : CollatzResearch.WordTrace tailWord_359662 prefixEnd_359662 164159537028868492863067 := by
  unfold tailWord_359662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639743852876684278048155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8745300548675649482923493 1639743852876684278048155)
  ·
    refine ⟨2459615779315026417072233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639743852876684278048155 2459615779315026417072233)
    ·
      refine ⟨1844711834486269812804175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459615779315026417072233 1844711834486269812804175)
      ·
        refine ⟨2767067751729404719206263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844711834486269812804175 2767067751729404719206263)
        ·
          refine ⟨4150601627594107078809395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767067751729404719206263 4150601627594107078809395)
          ·
            refine ⟨6225902441391160618214093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150601627594107078809395 6225902441391160618214093)
            ·
              refine ⟨2334713415521685231830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6225902441391160618214093 2334713415521685231830285)
              ·
                refine ⟨875517530820631961936357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334713415521685231830285 875517530820631961936357)
                ·
                  refine ⟨164159537028868492863067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875517530820631961936357 164159537028868492863067)
                  ·
                    rfl

theorem cell20_359662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_359662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359662 prefixEnd_359662 := by exact prefixLift 359662
  have htrace : WordTrace (prefixWord ++ tailWord_359662) baseStart_359662 baseEnd_359662 := by
    simpa [prefixWord, tailWord_359662, baseEnd_359662] using wordTrace_append hprefix tailTrace_359662
  have hstable : (prefixWord ++ tailWord_359662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359662).length < 2 ^ (prefixWord ++ tailWord_359662).sum := by decide
  have hdescent : baseEnd_359662 < baseStart_359662 := by decide
  rcases family_descends (prefixWord ++ tailWord_359662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359682 : List Nat := [3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_359682 : Nat := 118140960795 + 359682 * 2 ^ 59
def prefixEnd_359682 : Nat := 4983230072969 + 3 ^ 40 * 359682 * 2
def baseEnd_359682 : Nat := 54722888524612437398773

theorem tailTrace_359682 : CollatzResearch.WordTrace tailWord_359682 prefixEnd_359682 54722888524612437398773 := by
  unfold tailWord_359682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279670070735254410028325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8745786855294011760075533 3279670070735254410028325)
  ·
    refine ⟨614938138262860201880311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3279670070735254410028325 614938138262860201880311)
    ·
      refine ⟨922407207394290302820467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614938138262860201880311 922407207394290302820467)
      ·
        refine ⟨1383610811091435454230701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922407207394290302820467 1383610811091435454230701)
        ·
          refine ⟨518854054159288295336513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1383610811091435454230701 518854054159288295336513)
          ·
            refine ⟨389140540619466221502385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518854054159288295336513 389140540619466221502385)
            ·
              refine ⟨291855405464599666126789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389140540619466221502385 291855405464599666126789)
              ·
                refine ⟨54722888524612437398773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291855405464599666126789 54722888524612437398773)
                ·
                  rfl

theorem cell20_359682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_359682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359682 prefixEnd_359682 := by exact prefixLift 359682
  have htrace : WordTrace (prefixWord ++ tailWord_359682) baseStart_359682 baseEnd_359682 := by
    simpa [prefixWord, tailWord_359682, baseEnd_359682] using wordTrace_append hprefix tailTrace_359682
  have hstable : (prefixWord ++ tailWord_359682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359682).length < 2 ^ (prefixWord ++ tailWord_359682).sum := by decide
  have hdescent : baseEnd_359682 < baseStart_359682 := by decide
  rcases family_descends (prefixWord ++ tailWord_359682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359717 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_359717 : Nat := 118140960795 + 359717 * 2 ^ 59
def prefixEnd_359717 : Nat := 4983230072969 + 3 ^ 40 * 359717 * 2
def baseEnd_359717 : Nat := 164184640527532746029509

theorem tailTrace_359717 : CollatzResearch.WordTrace tailWord_359717 prefixEnd_359717 164184640527532746029509 := by
  unfold tailWord_359717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119956837814218617637405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8746637891876145745091603 13119956837814218617637405)
  ·
    refine ⟨4919983814180331981614027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13119956837814218617637405 4919983814180331981614027)
    ·
      refine ⟨7379975721270497972421041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919983814180331981614027 7379975721270497972421041)
      ·
        refine ⟨5534981790952873479315781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379975721270497972421041 5534981790952873479315781)
        ·
          refine ⟨1037809085803663777371709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5534981790952873479315781 1037809085803663777371709)
          ·
            refine ⟨389178407176373916514391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037809085803663777371709 389178407176373916514391)
            ·
              refine ⟨583767610764560874771587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389178407176373916514391 583767610764560874771587)
              ·
                refine ⟨875651416146841312157381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583767610764560874771587 875651416146841312157381)
                ·
                  refine ⟨164184640527532746029509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875651416146841312157381 164184640527532746029509)
                  ·
                    rfl

theorem cell20_359717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_359717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359717 prefixEnd_359717 := by exact prefixLift 359717
  have htrace : WordTrace (prefixWord ++ tailWord_359717) baseStart_359717 baseEnd_359717 := by
    simpa [prefixWord, tailWord_359717, baseEnd_359717] using wordTrace_append hprefix tailTrace_359717
  have hstable : (prefixWord ++ tailWord_359717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359717).length < 2 ^ (prefixWord ++ tailWord_359717).sum := by decide
  have hdescent : baseEnd_359717 < baseStart_359717 := by decide
  rcases family_descends (prefixWord ++ tailWord_359717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359731 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_359731 : Nat := 118140960795 + 359731 * 2 ^ 59
def prefixEnd_359731 : Nat := 4983230072969 + 3 ^ 40 * 359731 * 2
def baseEnd_359731 : Nat := 164191030509010919562785

theorem tailTrace_359731 : CollatzResearch.WordTrace tailWord_359731 prefixEnd_359731 164191030509010919562785 := by
  unfold tailWord_359731
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120467459763499008647047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8746978306508999339098031 13120467459763499008647047)
  ·
    refine ⟨19680701189645248512970571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13120467459763499008647047 19680701189645248512970571)
    ·
      refine ⟨29521051784467872769455857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19680701189645248512970571 29521051784467872769455857)
      ·
        refine ⟨22140788838350904577091893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29521051784467872769455857 22140788838350904577091893)
        ·
          refine ⟨2075698953595397304102365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22140788838350904577091893 2075698953595397304102365)
          ·
            refine ⟨778387107598273989038387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2075698953595397304102365 778387107598273989038387)
            ·
              refine ⟨1167580661397410983557581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778387107598273989038387 1167580661397410983557581)
              ·
                refine ⟨437842748024029118834093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167580661397410983557581 437842748024029118834093)
                ·
                  refine ⟨164191030509010919562785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437842748024029118834093 164191030509010919562785)
                  ·
                    rfl

theorem cell20_359731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_359731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359731 prefixEnd_359731 := by exact prefixLift 359731
  have htrace : WordTrace (prefixWord ++ tailWord_359731) baseStart_359731 baseEnd_359731 := by
    simpa [prefixWord, tailWord_359731, baseEnd_359731] using wordTrace_append hprefix tailTrace_359731
  have hstable : (prefixWord ++ tailWord_359731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359731).length < 2 ^ (prefixWord ++ tailWord_359731).sum := by decide
  have hdescent : baseEnd_359731 < baseStart_359731 := by decide
  rcases family_descends (prefixWord ++ tailWord_359731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359806 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_359806 : Nat := 118140960795 + 359806 * 2 ^ 59
def prefixEnd_359806 : Nat := 4983230072969 + 3 ^ 40 * 359806 * 2
def baseEnd_359806 : Nat := 164225262552643992062479

theorem tailTrace_359806 : CollatzResearch.WordTrace tailWord_359806 prefixEnd_359806 164225262552643992062479 := by
  unfold tailWord_359806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640400366811473352203409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8748801956327857878418181 1640400366811473352203409)
  ·
    refine ⟨1230300275108605014152557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1640400366811473352203409 1230300275108605014152557)
    ·
      refine ⟨461362603165726880307209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1230300275108605014152557 461362603165726880307209)
      ·
        refine ⟨346021952374295160230407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461362603165726880307209 346021952374295160230407)
        ·
          refine ⟨519032928561442740345611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346021952374295160230407 519032928561442740345611)
          ·
            refine ⟨778549392842164110518417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519032928561442740345611 778549392842164110518417)
            ·
              refine ⟨583912044631623082888813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778549392842164110518417 583912044631623082888813)
              ·
                refine ⟨218967016736858656083305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583912044631623082888813 218967016736858656083305)
                ·
                  refine ⟨164225262552643992062479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218967016736858656083305 164225262552643992062479)
                  ·
                    rfl

theorem cell20_359806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_359806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359806 prefixEnd_359806 := by exact prefixLift 359806
  have htrace : WordTrace (prefixWord ++ tailWord_359806) baseStart_359806 baseEnd_359806 := by
    simpa [prefixWord, tailWord_359806, baseEnd_359806] using wordTrace_append hprefix tailTrace_359806
  have hstable : (prefixWord ++ tailWord_359806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359806).length < 2 ^ (prefixWord ++ tailWord_359806).sum := by decide
  have hdescent : baseEnd_359806 < baseStart_359806 := by decide
  rcases family_descends (prefixWord ++ tailWord_359806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359865 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 2]
def baseStart_359865 : Nat := 118140960795 + 359865 * 2 ^ 59
def prefixEnd_359865 : Nat := 4983230072969 + 3 ^ 40 * 359865 * 2
def baseEnd_359865 : Nat := 164252191760302009095571

theorem tailTrace_359865 : CollatzResearch.WordTrace tailWord_359865 prefixEnd_359865 164252191760302009095571 := by
  unfold tailWord_359865
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125354841278039894025049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8750236560852026596016699 13125354841278039894025049)
  ·
    refine ⟨9844016130958529920518787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13125354841278039894025049 9844016130958529920518787)
    ·
      refine ⟨14766024196437794880778181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844016130958529920518787 14766024196437794880778181)
      ·
        refine ⟨2768629536832086540145909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14766024196437794880778181 2768629536832086540145909)
        ·
          refine ⟨259559019078008113138679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2768629536832086540145909 259559019078008113138679)
          ·
            refine ⟨389338528617012169708019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259559019078008113138679 389338528617012169708019)
            ·
              refine ⟨584007792925518254562029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389338528617012169708019 584007792925518254562029)
              ·
                refine ⟨219002922347069345460761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584007792925518254562029 219002922347069345460761)
                ·
                  refine ⟨164252191760302009095571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219002922347069345460761 164252191760302009095571)
                  ·
                    rfl

theorem cell20_359865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_359865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359865 prefixEnd_359865 := by exact prefixLift 359865
  have htrace : WordTrace (prefixWord ++ tailWord_359865) baseStart_359865 baseEnd_359865 := by
    simpa [prefixWord, tailWord_359865, baseEnd_359865] using wordTrace_append hprefix tailTrace_359865
  have hstable : (prefixWord ++ tailWord_359865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359865).length < 2 ^ (prefixWord ++ tailWord_359865).sum := by decide
  have hdescent : baseEnd_359865 < baseStart_359865 := by decide
  rcases family_descends (prefixWord ++ tailWord_359865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359876 : List Nat := [2, 3, 3, 2, 1, 3, 6]
def baseStart_359876 : Nat := 118140960795 + 359876 * 2 ^ 59
def prefixEnd_359876 : Nat := 4983230072969 + 3 ^ 40 * 359876 * 2
def baseEnd_359876 : Nat := 18250801384448317747651

theorem tailTrace_359876 : CollatzResearch.WordTrace tailWord_359876 prefixEnd_359876 18250801384448317747651 := by
  unfold tailWord_359876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6562878022119094386337741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8750504029492125848450321 6562878022119094386337741)
  ·
    refine ⟨2461079258294660394876653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6562878022119094386337741 2461079258294660394876653)
    ·
      refine ⟨922904721860497648078745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2461079258294660394876653 922904721860497648078745)
      ·
        refine ⟨692178541395373236059059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922904721860497648078745 692178541395373236059059)
        ·
          refine ⟨1038267812093059854088589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692178541395373236059059 1038267812093059854088589)
          ·
            refine ⟨389350429534897445283221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038267812093059854088589 389350429534897445283221)
            ·
              refine ⟨18250801384448317747651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 389350429534897445283221 18250801384448317747651)
              ·
                rfl

theorem cell20_359876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_359876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359876 prefixEnd_359876 := by exact prefixLift 359876
  have htrace : WordTrace (prefixWord ++ tailWord_359876) baseStart_359876 baseEnd_359876 := by
    simpa [prefixWord, tailWord_359876, baseEnd_359876] using wordTrace_append hprefix tailTrace_359876
  have hstable : (prefixWord ++ tailWord_359876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359876).length < 2 ^ (prefixWord ++ tailWord_359876).sum := by decide
  have hdescent : baseEnd_359876 < baseStart_359876 := by decide
  rcases family_descends (prefixWord ++ tailWord_359876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359897 : List Nat := [1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_359897 : Nat := 118140960795 + 359897 * 2 ^ 59
def prefixEnd_359897 : Nat := 4983230072969 + 3 ^ 40 * 359897 * 2
def baseEnd_359897 : Nat := 54755599144084040009591

theorem tailTrace_359897 : CollatzResearch.WordTrace tailWord_359897 prefixEnd_359897 54755599144084040009591 := by
  unfold tailWord_359897
  simp only [CollatzResearch.WordTrace]
  refine ⟨13126521977162109359189945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8751014651441406239459963 13126521977162109359189945)
  ·
    refine ⟨9844891482871582019392459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13126521977162109359189945 9844891482871582019392459)
    ·
      refine ⟨14767337224307373029088689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844891482871582019392459 14767337224307373029088689)
      ·
        refine ⟨11075502918230529771816517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14767337224307373029088689 11075502918230529771816517)
        ·
          refine ⟨2076656797168224332215597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11075502918230529771816517 2076656797168224332215597)
          ·
            refine ⟨778746298938084124580849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2076656797168224332215597 778746298938084124580849)
            ·
              refine ⟨584059724203563093435637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778746298938084124580849 584059724203563093435637)
              ·
                refine ⟨54755599144084040009591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 584059724203563093435637 54755599144084040009591)
                ·
                  rfl

theorem cell20_359897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_359897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359897 prefixEnd_359897 := by exact prefixLift 359897
  have htrace : WordTrace (prefixWord ++ tailWord_359897) baseStart_359897 baseEnd_359897 := by
    simpa [prefixWord, tailWord_359897, baseEnd_359897] using wordTrace_append hprefix tailTrace_359897
  have hstable : (prefixWord ++ tailWord_359897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359897).length < 2 ^ (prefixWord ++ tailWord_359897).sum := by decide
  have hdescent : baseEnd_359897 < baseStart_359897 := by decide
  rcases family_descends (prefixWord ++ tailWord_359897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359938 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_359938 : Nat := 118140960795 + 359938 * 2 ^ 59
def prefixEnd_359938 : Nat := 4983230072969 + 3 ^ 40 * 359938 * 2
def baseEnd_359938 : Nat := 164285510949438199661939

theorem tailTrace_359938 : CollatzResearch.WordTrace tailWord_359938 prefixEnd_359938 164285510949438199661939 := by
  unfold tailWord_359938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282004342503393340358117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8752011580009048907621645 3282004342503393340358117)
  ·
    refine ⟨615375814219386251317147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3282004342503393340358117 615375814219386251317147)
    ·
      refine ⟨923063721329079376975721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615375814219386251317147 923063721329079376975721)
      ·
        refine ⟨692297790996809532731791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923063721329079376975721 692297790996809532731791)
        ·
          refine ⟨1038446686495214299097687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692297790996809532731791 1038446686495214299097687)
          ·
            refine ⟨1557670029742821448646531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038446686495214299097687 1557670029742821448646531)
            ·
              refine ⟨2336505044614232172969797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557670029742821448646531 2336505044614232172969797)
              ·
                refine ⟨438094695865168532431837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2336505044614232172969797 438094695865168532431837)
                ·
                  refine ⟨164285510949438199661939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438094695865168532431837 164285510949438199661939)
                  ·
                    rfl

theorem cell20_359938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_359938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359938 prefixEnd_359938 := by exact prefixLift 359938
  have htrace : WordTrace (prefixWord ++ tailWord_359938) baseStart_359938 baseEnd_359938 := by
    simpa [prefixWord, tailWord_359938, baseEnd_359938] using wordTrace_append hprefix tailTrace_359938
  have hstable : (prefixWord ++ tailWord_359938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359938).length < 2 ^ (prefixWord ++ tailWord_359938).sum := by decide
  have hdescent : baseEnd_359938 < baseStart_359938 := by decide
  rcases family_descends (prefixWord ++ tailWord_359938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359990 : List Nat := [5, 1, 2, 1, 3, 1, 7]
def baseStart_359990 : Nat := 118140960795 + 359990 * 2 ^ 59
def prefixEnd_359990 : Nat := 4983230072969 + 3 ^ 40 * 359990 * 2
def baseEnd_359990 : Nat := 18256582796261903325377

theorem tailTrace_359990 : CollatzResearch.WordTrace tailWord_359990 prefixEnd_359990 18256582796261903325377 := by
  unfold tailWord_359990
  simp only [CollatzResearch.WordTrace]
  refine ⟨820619622864074140145339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8753275977216790828216949 820619622864074140145339)
  ·
    refine ⟨1230929434296111210218009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820619622864074140145339 1230929434296111210218009)
    ·
      refine ⟨923197075722083407663507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230929434296111210218009 923197075722083407663507)
      ·
        refine ⟨1384795613583125111495261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923197075722083407663507 1384795613583125111495261)
        ·
          refine ⟨519298355093671916810723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1384795613583125111495261 519298355093671916810723)
          ·
            refine ⟨778947532640507875216085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519298355093671916810723 778947532640507875216085)
            ·
              refine ⟨18256582796261903325377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 778947532640507875216085 18256582796261903325377)
              ·
                rfl

theorem cell20_359990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_359990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359990 prefixEnd_359990 := by exact prefixLift 359990
  have htrace : WordTrace (prefixWord ++ tailWord_359990) baseStart_359990 baseEnd_359990 := by
    simpa [prefixWord, tailWord_359990, baseEnd_359990] using wordTrace_append hprefix tailTrace_359990
  have hstable : (prefixWord ++ tailWord_359990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359990).length < 2 ^ (prefixWord ++ tailWord_359990).sum := by decide
  have hdescent : baseEnd_359990 < baseStart_359990 := by decide
  rcases family_descends (prefixWord ++ tailWord_359990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359994 : List Nat := [3, 1, 1, 1, 3, 2, 9]
def baseStart_359994 : Nat := 118140960795 + 359994 * 2 ^ 59
def prefixEnd_359994 : Nat := 4983230072969 + 3 ^ 40 * 359994 * 2
def baseEnd_359994 : Nat := 18256785652816765977227

theorem tailTrace_359994 : CollatzResearch.WordTrace tailWord_359994 prefixEnd_359994 18256785652816765977227 := by
  unfold tailWord_359994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282514964452673731367759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8753373238540463283647357 3282514964452673731367759)
  ·
    refine ⟨4923772446679010597051639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282514964452673731367759 4923772446679010597051639)
    ·
      refine ⟨7385658670018515895577459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923772446679010597051639 7385658670018515895577459)
      ·
        refine ⟨11078488005027773843366189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385658670018515895577459 11078488005027773843366189)
        ·
          refine ⟨4154433001885415191262321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11078488005027773843366189 4154433001885415191262321)
          ·
            refine ⟨3115824751414061393446741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4154433001885415191262321 3115824751414061393446741)
            ·
              refine ⟨18256785652816765977227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3115824751414061393446741 18256785652816765977227)
              ·
                rfl

theorem cell20_359994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_359994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359994 prefixEnd_359994 := by exact prefixLift 359994
  have htrace : WordTrace (prefixWord ++ tailWord_359994) baseStart_359994 baseEnd_359994 := by
    simpa [prefixWord, tailWord_359994, baseEnd_359994] using wordTrace_append hprefix tailTrace_359994
  have hstable : (prefixWord ++ tailWord_359994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359994).length < 2 ^ (prefixWord ++ tailWord_359994).sum := by decide
  have hdescent : baseEnd_359994 < baseStart_359994 := by decide
  rcases family_descends (prefixWord ++ tailWord_359994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359997 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_359997 : Nat := 118140960795 + 359997 * 2 ^ 59
def prefixEnd_359997 : Nat := 4983230072969 + 3 ^ 40 * 359997 * 2
def baseEnd_359997 : Nat := 164312440157096216695031

theorem tailTrace_359997 : CollatzResearch.WordTrace tailWord_359997 prefixEnd_359997 164312440157096216695031 := by
  unfold tailWord_359997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130169276799826437830245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8753446184533217625220163 13130169276799826437830245)
  ·
    refine ⟨2461906739399967457093171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13130169276799826437830245 2461906739399967457093171)
    ·
      refine ⟨3692860109099951185639757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461906739399967457093171 3692860109099951185639757)
      ·
        refine ⟨1384822540912481694614909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3692860109099951185639757 1384822540912481694614909)
        ·
          refine ⟨519308452842180635480591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1384822540912481694614909 519308452842180635480591)
          ·
            refine ⟨778962679263270953220887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519308452842180635480591 778962679263270953220887)
            ·
              refine ⟨1168444018894906429831331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778962679263270953220887 1168444018894906429831331)
              ·
                refine ⟨1752666028342359644746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168444018894906429831331 1752666028342359644746997)
                ·
                  refine ⟨164312440157096216695031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1752666028342359644746997 164312440157096216695031)
                  ·
                    rfl

theorem cell20_359997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_359997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359997 prefixEnd_359997 := by exact prefixLift 359997
  have htrace : WordTrace (prefixWord ++ tailWord_359997) baseStart_359997 baseEnd_359997 := by
    simpa [prefixWord, tailWord_359997, baseEnd_359997] using wordTrace_append hprefix tailTrace_359997
  have hstable : (prefixWord ++ tailWord_359997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359997).length < 2 ^ (prefixWord ++ tailWord_359997).sum := by decide
  have hdescent : baseEnd_359997 < baseStart_359997 := by decide
  rcases family_descends (prefixWord ++ tailWord_359997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360028 : List Nat := [2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_360028 : Nat := 118140960795 + 360028 * 2 ^ 59
def prefixEnd_360028 : Nat := 4983230072969 + 3 ^ 40 * 360028 * 2
def baseEnd_360028 : Nat := 54775529800599295553857

theorem tailTrace_360028 : CollatzResearch.WordTrace tailWord_360028 prefixEnd_360028 54775529800599295553857 := by
  unfold tailWord_360028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565649969843759366104369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8754199959791679154805825 6565649969843759366104369)
  ·
    refine ⟨4924237477382819524578277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6565649969843759366104369 4924237477382819524578277)
    ·
      refine ⟨923294527009278660858427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4924237477382819524578277 923294527009278660858427)
      ·
        refine ⟨1384941790513917991287641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923294527009278660858427 1384941790513917991287641)
        ·
          refine ⟨1038706342885438493465731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384941790513917991287641 1038706342885438493465731)
          ·
            refine ⟨1558059514328157740198597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038706342885438493465731 1558059514328157740198597)
            ·
              refine ⟨292136158936529576287237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1558059514328157740198597 292136158936529576287237)
              ·
                refine ⟨54775529800599295553857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292136158936529576287237 54775529800599295553857)
                ·
                  rfl

theorem cell20_360028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_360028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360028 prefixEnd_360028 := by exact prefixLift 360028
  have htrace : WordTrace (prefixWord ++ tailWord_360028) baseStart_360028 baseEnd_360028 := by
    simpa [prefixWord, tailWord_360028, baseEnd_360028] using wordTrace_append hprefix tailTrace_360028
  have hstable : (prefixWord ++ tailWord_360028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360028).length < 2 ^ (prefixWord ++ tailWord_360028).sum := by decide
  have hdescent : baseEnd_360028 < baseStart_360028 := by decide
  rcases family_descends (prefixWord ++ tailWord_360028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360059 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 2]
def baseStart_360059 : Nat := 118140960795 + 360059 * 2 ^ 59
def prefixEnd_360059 : Nat := 4983230072969 + 3 ^ 40 * 360059 * 2
def baseEnd_360059 : Nat := 164340738646499556628111

theorem tailTrace_360059 : CollatzResearch.WordTrace tailWord_360059 prefixEnd_360059 164340738646499556628111 := by
  unfold tailWord_360059
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132430602575211026587231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8754953735050140684391487 13132430602575211026587231)
  ·
    refine ⟨19698645903862816539880847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13132430602575211026587231 19698645903862816539880847)
    ·
      refine ⟨29547968855794224809821271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19698645903862816539880847 29547968855794224809821271)
      ·
        refine ⟨44321953283691337214731907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29547968855794224809821271 44321953283691337214731907)
        ·
          refine ⟨66482929925537005822097861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44321953283691337214731907 66482929925537005822097861)
          ·
            refine ⟨12465549361038188591643349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66482929925537005822097861 12465549361038188591643349)
            ·
              refine ⟨292161313149332545116641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12465549361038188591643349 292161313149332545116641)
              ·
                refine ⟨219120984861999408837481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292161313149332545116641 219120984861999408837481)
                ·
                  refine ⟨164340738646499556628111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219120984861999408837481 164340738646499556628111)
                  ·
                    rfl

theorem cell20_360059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2].length) (baseStart_360059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360059 prefixEnd_360059 := by exact prefixLift 360059
  have htrace : WordTrace (prefixWord ++ tailWord_360059) baseStart_360059 baseEnd_360059 := by
    simpa [prefixWord, tailWord_360059, baseEnd_360059] using wordTrace_append hprefix tailTrace_360059
  have hstable : (prefixWord ++ tailWord_360059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360059).length < 2 ^ (prefixWord ++ tailWord_360059).sum := by decide
  have hdescent : baseEnd_360059 < baseStart_360059 := by decide
  rcases family_descends (prefixWord ++ tailWord_360059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360073 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_360073 : Nat := 118140960795 + 360073 * 2 ^ 59
def prefixEnd_360073 : Nat := 4983230072969 + 3 ^ 40 * 360073 * 2
def baseEnd_360073 : Nat := 164347128627977730161387

theorem tailTrace_360073 : CollatzResearch.WordTrace tailWord_360073 prefixEnd_360073 164347128627977730161387 := by
  unfold tailWord_360073
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132941224524491417596873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755294149682994278397915 13132941224524491417596873)
  ·
    refine ⟨9849705918393368563197655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13132941224524491417596873 9849705918393368563197655)
    ·
      refine ⟨14774558877590052844796483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849705918393368563197655 14774558877590052844796483)
      ·
        refine ⟨22161838316385079267194725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14774558877590052844796483 22161838316385079267194725)
        ·
          refine ⟨4155344684322202362599011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22161838316385079267194725 4155344684322202362599011)
          ·
            refine ⟨6233017026483303543898517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155344684322202362599011 6233017026483303543898517)
            ·
              refine ⟨292172673116404853620243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6233017026483303543898517 292172673116404853620243)
              ·
                refine ⟨438259009674607280430365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292172673116404853620243 438259009674607280430365)
                ·
                  refine ⟨164347128627977730161387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438259009674607280430365 164347128627977730161387)
                  ·
                    rfl

theorem cell20_360073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_360073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360073 prefixEnd_360073 := by exact prefixLift 360073
  have htrace : WordTrace (prefixWord ++ tailWord_360073) baseStart_360073 baseEnd_360073 := by
    simpa [prefixWord, tailWord_360073, baseEnd_360073] using wordTrace_append hprefix tailTrace_360073
  have hstable : (prefixWord ++ tailWord_360073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360073).length < 2 ^ (prefixWord ++ tailWord_360073).sum := by decide
  have hdescent : baseEnd_360073 < baseStart_360073 := by decide
  rcases family_descends (prefixWord ++ tailWord_360073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360104 : List Nat := [2, 1, 7, 1, 9]
def baseStart_360104 : Nat := 118140960795 + 360104 * 2 ^ 59
def prefixEnd_360104 : Nat := 4983230072969 + 3 ^ 40 * 360104 * 2
def baseEnd_360104 : Nat := 2029151578675054322567

theorem tailTrace_360104 : CollatzResearch.WordTrace tailWord_360104 prefixEnd_360104 2029151578675054322567 := by
  unfold tailWord_360104
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567035943706091855987683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8756047924941455807983577 6567035943706091855987683)
  ·
    refine ⟨9850553915559137783981525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6567035943706091855987683 9850553915559137783981525)
    ·
      refine ⟨230872357395917291812067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9850553915559137783981525 230872357395917291812067)
      ·
        refine ⟨346308536093875937718101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230872357395917291812067 346308536093875937718101)
        ·
          refine ⟨2029151578675054322567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 346308536093875937718101 2029151578675054322567)
          ·
            rfl

theorem cell20_360104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 9].length) (baseStart_360104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360104 prefixEnd_360104 := by exact prefixLift 360104
  have htrace : WordTrace (prefixWord ++ tailWord_360104) baseStart_360104 baseEnd_360104 := by
    simpa [prefixWord, tailWord_360104, baseEnd_360104] using wordTrace_append hprefix tailTrace_360104
  have hstable : (prefixWord ++ tailWord_360104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360104).length < 2 ^ (prefixWord ++ tailWord_360104).sum := by decide
  have hdescent : baseEnd_360104 < baseStart_360104 := by decide
  rcases family_descends (prefixWord ++ tailWord_360104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360110 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_360110 : Nat := 118140960795 + 360110 * 2 ^ 59
def prefixEnd_360110 : Nat := 4983230072969 + 3 ^ 40 * 360110 * 2
def baseEnd_360110 : Nat := 164364016436170045927903

theorem tailTrace_360110 : CollatzResearch.WordTrace tailWord_360110 prefixEnd_360110 164364016436170045927903 := by
  unfold tailWord_360110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641786340673805842086723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8756193816926964491129189 1641786340673805842086723)
  ·
    refine ⟨2462679511010708763130085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641786340673805842086723 2462679511010708763130085)
    ·
      refine ⟨461752408314507893086891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2462679511010708763130085 461752408314507893086891)
      ·
        refine ⟨692628612471761839630337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461752408314507893086891 692628612471761839630337)
        ·
          refine ⟨519471459353821379722753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692628612471761839630337 519471459353821379722753)
          ·
            refine ⟨389603594515366034792065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519471459353821379722753 389603594515366034792065)
            ·
              refine ⟨292202695886524526094049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389603594515366034792065 292202695886524526094049)
              ·
                refine ⟨219152021914893394570537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292202695886524526094049 219152021914893394570537)
                ·
                  refine ⟨164364016436170045927903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219152021914893394570537 164364016436170045927903)
                  ·
                    rfl

theorem cell20_360110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_360110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360110 prefixEnd_360110 := by exact prefixLift 360110
  have htrace : WordTrace (prefixWord ++ tailWord_360110) baseStart_360110 baseEnd_360110 := by
    simpa [prefixWord, tailWord_360110, baseEnd_360110] using wordTrace_append hprefix tailTrace_360110
  have hstable : (prefixWord ++ tailWord_360110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360110).length < 2 ^ (prefixWord ++ tailWord_360110).sum := by decide
  have hdescent : baseEnd_360110 < baseStart_360110 := by decide
  rcases family_descends (prefixWord ++ tailWord_360110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360163 : List Nat := [1, 1, 1, 7, 2, 1, 7]
def baseStart_360163 : Nat := 118140960795 + 360163 * 2 ^ 59
def prefixEnd_360163 : Nat := 4983230072969 + 3 ^ 40 * 360163 * 2
def baseEnd_360163 : Nat := 18265356342259713017891

theorem tailTrace_360163 : CollatzResearch.WordTrace tailWord_360163 prefixEnd_360163 18265356342259713017891 := by
  unfold tailWord_360163
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136223794198436788373143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757482529465624525582095 13136223794198436788373143)
  ·
    refine ⟨19704335691297655182559715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13136223794198436788373143 19704335691297655182559715)
    ·
      refine ⟨29556503536946482773839573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19704335691297655182559715 29556503536946482773839573)
      ·
        refine ⟨692730551647183190011865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29556503536946482773839573 692730551647183190011865)
        ·
          refine ⟨519547913735387392508899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692730551647183190011865 519547913735387392508899)
          ·
            refine ⟨779321870603081088763349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519547913735387392508899 779321870603081088763349)
            ·
              refine ⟨18265356342259713017891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 779321870603081088763349 18265356342259713017891)
              ·
                rfl

theorem cell20_360163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_360163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360163 prefixEnd_360163 := by exact prefixLift 360163
  have htrace : WordTrace (prefixWord ++ tailWord_360163) baseStart_360163 baseEnd_360163 := by
    simpa [prefixWord, tailWord_360163, baseEnd_360163] using wordTrace_append hprefix tailTrace_360163
  have hstable : (prefixWord ++ tailWord_360163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360163).length < 2 ^ (prefixWord ++ tailWord_360163).sum := by decide
  have hdescent : baseEnd_360163 < baseStart_360163 := by decide
  rcases family_descends (prefixWord ++ tailWord_360163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360173 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 2]
def baseStart_360173 : Nat := 118140960795 + 360173 * 2 ^ 59
def prefixEnd_360173 : Nat := 4983230072969 + 3 ^ 40 * 360173 * 2
def baseEnd_360173 : Nat := 164392771352821826827645

theorem tailTrace_360173 : CollatzResearch.WordTrace tailWord_360173 prefixEnd_360173 164392771352821826827645 := by
  unfold tailWord_360173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136588524162208496237173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757725682774805664158115 13136588524162208496237173)
  ·
    refine ⟨1231555174140207046522235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13136588524162208496237173 1231555174140207046522235)
    ·
      refine ⟨1847332761210310569783353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231555174140207046522235 1847332761210310569783353)
      ·
        refine ⟨1385499570907732927337515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847332761210310569783353 1385499570907732927337515)
        ·
          refine ⟨2078249356361599391006273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385499570907732927337515 2078249356361599391006273)
          ·
            refine ⟨1558687017271199543254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078249356361599391006273 1558687017271199543254705)
            ·
              refine ⟨1169015262953399657441029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558687017271199543254705 1169015262953399657441029)
              ·
                refine ⟨219190361803762435770193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1169015262953399657441029 219190361803762435770193)
                ·
                  refine ⟨164392771352821826827645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219190361803762435770193 164392771352821826827645)
                  ·
                    rfl

theorem cell20_360173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_360173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360173 prefixEnd_360173 := by exact prefixLift 360173
  have htrace : WordTrace (prefixWord ++ tailWord_360173) baseStart_360173 baseEnd_360173 := by
    simpa [prefixWord, tailWord_360173, baseEnd_360173] using wordTrace_append hprefix tailTrace_360173
  have hstable : (prefixWord ++ tailWord_360173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360173).length < 2 ^ (prefixWord ++ tailWord_360173).sum := by decide
  have hdescent : baseEnd_360173 < baseStart_360173 := by decide
  rcases family_descends (prefixWord ++ tailWord_360173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360177 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_360177 : Nat := 118140960795 + 360177 * 2 ^ 59
def prefixEnd_360177 : Nat := 4983230072969 + 3 ^ 40 * 360177 * 2
def baseEnd_360177 : Nat := 164394597061815590694295

theorem tailTrace_360177 : CollatzResearch.WordTrace tailWord_360177 prefixEnd_360177 164394597061815590694295 := by
  unfold tailWord_360177
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136734416147717179382785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757822944098478119588523 13136734416147717179382785)
  ·
    refine ⟨9852550812110787884537089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13136734416147717179382785 9852550812110787884537089)
    ·
      refine ⟨7389413109083090913402817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9852550812110787884537089 7389413109083090913402817)
      ·
        refine ⟨5542059831812318185052113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7389413109083090913402817 5542059831812318185052113)
        ·
          refine ⟨4156544873859238638789085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5542059831812318185052113 4156544873859238638789085)
          ·
            refine ⟨1558704327697214489545907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4156544873859238638789085 1558704327697214489545907)
            ·
              refine ⟨2338056491545821734318861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558704327697214489545907 2338056491545821734318861)
              ·
                refine ⟨876771184329683150369573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2338056491545821734318861 876771184329683150369573)
                ·
                  refine ⟨164394597061815590694295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876771184329683150369573 164394597061815590694295)
                  ·
                    rfl

theorem cell20_360177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_360177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360177 prefixEnd_360177 := by exact prefixLift 360177
  have htrace : WordTrace (prefixWord ++ tailWord_360177) baseStart_360177 baseEnd_360177 := by
    simpa [prefixWord, tailWord_360177, baseEnd_360177] using wordTrace_append hprefix tailTrace_360177
  have hstable : (prefixWord ++ tailWord_360177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360177).length < 2 ^ (prefixWord ++ tailWord_360177).sum := by decide
  have hdescent : baseEnd_360177 < baseStart_360177 := by decide
  rcases family_descends (prefixWord ++ tailWord_360177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360194 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_360194 : Nat := 118140960795 + 360194 * 2 ^ 59
def prefixEnd_360194 : Nat := 4983230072969 + 3 ^ 40 * 360194 * 2
def baseEnd_360194 : Nat := 164402356325039087127559

theorem tailTrace_360194 : CollatzResearch.WordTrace tailWord_360194 prefixEnd_360194 164402356325039087127559 := by
  unfold tailWord_360194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284338614271532270687909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8758236304724086055167757 3284338614271532270687909)
  ·
    refine ⟨615813490175912300753983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3284338614271532270687909 615813490175912300753983)
    ·
      refine ⟨923720235263868451130975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615813490175912300753983 923720235263868451130975)
      ·
        refine ⟨1385580352895802676696463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923720235263868451130975 1385580352895802676696463)
        ·
          refine ⟨2078370529343704015044695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385580352895802676696463 2078370529343704015044695)
          ·
            refine ⟨3117555794015556022567043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078370529343704015044695 3117555794015556022567043)
            ·
              refine ⟨4676333691023334033850565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117555794015556022567043 4676333691023334033850565)
              ·
                refine ⟨876812567066875131346981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4676333691023334033850565 876812567066875131346981)
                ·
                  refine ⟨164402356325039087127559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876812567066875131346981 164402356325039087127559)
                  ·
                    rfl

theorem cell20_360194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_360194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360194 prefixEnd_360194 := by exact prefixLift 360194
  have htrace : WordTrace (prefixWord ++ tailWord_360194) baseStart_360194 baseEnd_360194 := by
    simpa [prefixWord, tailWord_360194, baseEnd_360194] using wordTrace_append hprefix tailTrace_360194
  have hstable : (prefixWord ++ tailWord_360194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360194).length < 2 ^ (prefixWord ++ tailWord_360194).sum := by decide
  have hdescent : baseEnd_360194 < baseStart_360194 := by decide
  rcases family_descends (prefixWord ++ tailWord_360194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360228 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_360228 : Nat := 118140960795 + 360228 * 2 ^ 59
def prefixEnd_360228 : Nat := 4983230072969 + 3 ^ 40 * 360228 * 2
def baseEnd_360228 : Nat := 164417874851486079994087

theorem tailTrace_360228 : CollatzResearch.WordTrace tailWord_360228 prefixEnd_360228 164417874851486079994087 := by
  unfold tailWord_360228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569297269481476444744669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8759063025975301926326225 6569297269481476444744669)
  ·
    refine ⟨2463486476055553666779251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6569297269481476444744669 2463486476055553666779251)
    ·
      refine ⟨3695229714083330500168877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463486476055553666779251 3695229714083330500168877)
      ·
        refine ⟨1385711142781248937563329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3695229714083330500168877 1385711142781248937563329)
        ·
          refine ⟨1039283357085936703172497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385711142781248937563329 1039283357085936703172497)
          ·
            refine ⟨779462517814452527379373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039283357085936703172497 779462517814452527379373)
            ·
              refine ⟨292298444180419697767265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 779462517814452527379373 292298444180419697767265)
              ·
                refine ⟨219223833135314773325449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292298444180419697767265 219223833135314773325449)
                ·
                  refine ⟨164417874851486079994087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219223833135314773325449 164417874851486079994087)
                  ·
                    rfl

theorem cell20_360228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_360228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360228 prefixEnd_360228 := by exact prefixLift 360228
  have htrace : WordTrace (prefixWord ++ tailWord_360228) baseStart_360228 baseEnd_360228 := by
    simpa [prefixWord, tailWord_360228, baseEnd_360228] using wordTrace_append hprefix tailTrace_360228
  have hstable : (prefixWord ++ tailWord_360228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360228).length < 2 ^ (prefixWord ++ tailWord_360228).sum := by decide
  have hdescent : baseEnd_360228 < baseStart_360228 := by decide
  rcases family_descends (prefixWord ++ tailWord_360228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360232 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_360232 : Nat := 118140960795 + 360232 * 2 ^ 59
def prefixEnd_360232 : Nat := 4983230072969 + 3 ^ 40 * 360232 * 2
def baseEnd_360232 : Nat := 164419700560479843860737

theorem tailTrace_360232 : CollatzResearch.WordTrace tailWord_360232 prefixEnd_360232 164419700560479843860737 := by
  unfold tailWord_360232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569370215474230786317475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8759160287298974381756633 6569370215474230786317475)
  ·
    refine ⟨9854055323211346179476213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6569370215474230786317475 9854055323211346179476213)
    ·
      refine ⟨923817686551063704325895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9854055323211346179476213 923817686551063704325895)
      ·
        refine ⟨1385726529826595556488843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923817686551063704325895 1385726529826595556488843)
        ·
          refine ⟨2078589794739893334733265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385726529826595556488843 2078589794739893334733265)
          ·
            refine ⟨1558942346054920001049949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078589794739893334733265 1558942346054920001049949)
            ·
              refine ⟨584603379770595000393731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558942346054920001049949 584603379770595000393731)
              ·
                refine ⟨876905069655892500590597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584603379770595000393731 876905069655892500590597)
                ·
                  refine ⟨164419700560479843860737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876905069655892500590597 164419700560479843860737)
                  ·
                    rfl

theorem cell20_360232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_360232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360232 prefixEnd_360232 := by exact prefixLift 360232
  have htrace : WordTrace (prefixWord ++ tailWord_360232) baseStart_360232 baseEnd_360232 := by
    simpa [prefixWord, tailWord_360232, baseEnd_360232] using wordTrace_append hprefix tailTrace_360232
  have hstable : (prefixWord ++ tailWord_360232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360232).length < 2 ^ (prefixWord ++ tailWord_360232).sum := by decide
  have hdescent : baseEnd_360232 < baseStart_360232 := by decide
  rcases family_descends (prefixWord ++ tailWord_360232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360238 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_360238 : Nat := 118140960795 + 360238 * 2 ^ 59
def prefixEnd_360238 : Nat := 4983230072969 + 3 ^ 40 * 360238 * 2
def baseEnd_360238 : Nat := 164422439123970489660713

theorem tailTrace_360238 : CollatzResearch.WordTrace tailWord_360238 prefixEnd_360238 164422439123970489660713 := by
  unfold tailWord_360238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642369908615840574669171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8759306179284483064902245 1642369908615840574669171)
  ·
    refine ⟨2463554862923760862003757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1642369908615840574669171 2463554862923760862003757)
    ·
      refine ⟨923833073596410323251409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2463554862923760862003757 923833073596410323251409)
      ·
        refine ⟨692874805197307742438557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923833073596410323251409 692874805197307742438557)
        ·
          refine ⟨259828051948990403414459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 692874805197307742438557 259828051948990403414459)
          ·
            refine ⟨389742077923485605121689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259828051948990403414459 389742077923485605121689)
            ·
              refine ⟨292306558442614203841267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389742077923485605121689 292306558442614203841267)
              ·
                refine ⟨438459837663921305761901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292306558442614203841267 438459837663921305761901)
                ·
                  refine ⟨164422439123970489660713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438459837663921305761901 164422439123970489660713)
                  ·
                    rfl

theorem cell20_360238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_360238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360238 prefixEnd_360238 := by exact prefixLift 360238
  have htrace : WordTrace (prefixWord ++ tailWord_360238) baseStart_360238 baseEnd_360238 := by
    simpa [prefixWord, tailWord_360238, baseEnd_360238] using wordTrace_append hprefix tailTrace_360238
  have hstable : (prefixWord ++ tailWord_360238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360238).length < 2 ^ (prefixWord ++ tailWord_360238).sum := by decide
  have hdescent : baseEnd_360238 < baseStart_360238 := by decide
  rcases family_descends (prefixWord ++ tailWord_360238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360242 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_360242 : Nat := 118140960795 + 360242 * 2 ^ 59
def prefixEnd_360242 : Nat := 4983230072969 + 3 ^ 40 * 360242 * 2
def baseEnd_360242 : Nat := 164424264832964253527363

theorem tailTrace_360242 : CollatzResearch.WordTrace tailWord_360242 prefixEnd_360242 164424264832964253527363 := by
  unfold tailWord_360242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284776290228058320124745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8759403440608155520332653 3284776290228058320124745)
  ·
    refine ⟨2463582217671043740093559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3284776290228058320124745 2463582217671043740093559)
    ·
      refine ⟨3695373326506565610140339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463582217671043740093559 3695373326506565610140339)
      ·
        refine ⟨5543059989759848415210509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695373326506565610140339 5543059989759848415210509)
        ·
          refine ⟨2078647496159943155703941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5543059989759848415210509 2078647496159943155703941)
          ·
            refine ⟨389746405529989341694489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2078647496159943155703941 389746405529989341694489)
            ·
              refine ⟨292309804147492006270867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389746405529989341694489 292309804147492006270867)
              ·
                refine ⟨438464706221238009406301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292309804147492006270867 438464706221238009406301)
                ·
                  refine ⟨164424264832964253527363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438464706221238009406301 164424264832964253527363)
                  ·
                    rfl

theorem cell20_360242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_360242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360242 prefixEnd_360242 := by exact prefixLift 360242
  have htrace : WordTrace (prefixWord ++ tailWord_360242) baseStart_360242 baseEnd_360242 := by
    simpa [prefixWord, tailWord_360242, baseEnd_360242] using wordTrace_append hprefix tailTrace_360242
  have hstable : (prefixWord ++ tailWord_360242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360242).length < 2 ^ (prefixWord ++ tailWord_360242).sum := by decide
  have hdescent : baseEnd_360242 < baseStart_360242 := by decide
  rcases family_descends (prefixWord ++ tailWord_360242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360287 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 2]
def baseStart_360287 : Nat := 118140960795 + 360287 * 2 ^ 59
def prefixEnd_360287 : Nat := 4983230072969 + 3 ^ 40 * 360287 * 2
def baseEnd_360287 : Nat := 164444804059144097027179

theorem tailTrace_360287 : CollatzResearch.WordTrace tailWord_360287 prefixEnd_360287 164444804059144097027179 := by
  unfold tailWord_360287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140746445749205965887115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8760497630499470643924743 13140746445749205965887115)
  ·
    refine ⟨19711119668623808948830673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13140746445749205965887115 19711119668623808948830673)
    ·
      refine ⟨14783339751467856711623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19711119668623808948830673 14783339751467856711623005)
      ·
        refine ⟨5543752406800446266858627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14783339751467856711623005 5543752406800446266858627)
        ·
          refine ⟨8315628610200669400287941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543752406800446266858627 8315628610200669400287941)
          ·
            refine ⟨1559180364412625512553989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8315628610200669400287941 1559180364412625512553989)
            ·
              refine ⟨292346318327367283603873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1559180364412625512553989 292346318327367283603873)
              ·
                refine ⟨219259738745525462702905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292346318327367283603873 219259738745525462702905)
                ·
                  refine ⟨164444804059144097027179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219259738745525462702905 164444804059144097027179)
                  ·
                    rfl

theorem cell20_360287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2].length) (baseStart_360287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360287 prefixEnd_360287 := by exact prefixLift 360287
  have htrace : WordTrace (prefixWord ++ tailWord_360287) baseStart_360287 baseEnd_360287 := by
    simpa [prefixWord, tailWord_360287, baseEnd_360287] using wordTrace_append hprefix tailTrace_360287
  have hstable : (prefixWord ++ tailWord_360287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360287).length < 2 ^ (prefixWord ++ tailWord_360287).sum := by decide
  have hdescent : baseEnd_360287 < baseStart_360287 := by decide
  rcases family_descends (prefixWord ++ tailWord_360287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360346 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_360346 : Nat := 118140960795 + 360346 * 2 ^ 59
def prefixEnd_360346 : Nat := 4983230072969 + 3 ^ 40 * 360346 * 2
def baseEnd_360346 : Nat := 164471733266802114060271

theorem tailTrace_360346 : CollatzResearch.WordTrace tailWord_360346 prefixEnd_360346 164471733266802114060271 := by
  unfold tailWord_360346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285724588133864760571223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8761932235023639361523261 3285724588133864760571223)
  ·
    refine ⟨4928586882200797140856835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3285724588133864760571223 4928586882200797140856835)
    ·
      refine ⟨7392880323301195711285253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928586882200797140856835 7392880323301195711285253)
      ·
        refine ⟨1386165060618974195865985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7392880323301195711285253 1386165060618974195865985)
        ·
          refine ⟨1039623795464230646899489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386165060618974195865985 1039623795464230646899489)
          ·
            refine ⟨779717846598172985174617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039623795464230646899489 779717846598172985174617)
            ·
              refine ⟨584788384948629738880963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779717846598172985174617 584788384948629738880963)
              ·
                refine ⟨877182577422944608321445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584788384948629738880963 877182577422944608321445)
                ·
                  refine ⟨164471733266802114060271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877182577422944608321445 164471733266802114060271)
                  ·
                    rfl

theorem cell20_360346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_360346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360346 prefixEnd_360346 := by exact prefixLift 360346
  have htrace : WordTrace (prefixWord ++ tailWord_360346) baseStart_360346 baseEnd_360346 := by
    simpa [prefixWord, tailWord_360346, baseEnd_360346] using wordTrace_append hprefix tailTrace_360346
  have hstable : (prefixWord ++ tailWord_360346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360346).length < 2 ^ (prefixWord ++ tailWord_360346).sum := by decide
  have hdescent : baseEnd_360346 < baseStart_360346 := by decide
  rcases family_descends (prefixWord ++ tailWord_360346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360398 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_360398 : Nat := 118140960795 + 360398 * 2 ^ 59
def prefixEnd_360398 : Nat := 4983230072969 + 3 ^ 40 * 360398 * 2
def baseEnd_360398 : Nat := 164495467483721044326725

theorem tailTrace_360398 : CollatzResearch.WordTrace tailWord_360398 prefixEnd_360398 164495467483721044326725 := by
  unfold tailWord_360398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643099368543383990397231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8763196632231381282118565 1643099368543383990397231)
  ·
    refine ⟨2464649052815075985595847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643099368543383990397231 2464649052815075985595847)
    ·
      refine ⟨3696973579222613978393771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464649052815075985595847 3696973579222613978393771)
      ·
        refine ⟨5545460368833920967590657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696973579222613978393771 5545460368833920967590657)
        ·
          refine ⟨4159095276625440725692993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545460368833920967590657 4159095276625440725692993)
          ·
            refine ⟨3119321457469080544269745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159095276625440725692993 3119321457469080544269745)
            ·
              refine ⟨2339491093101810408202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119321457469080544269745 2339491093101810408202309)
              ·
                refine ⟨438654579956589451537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2339491093101810408202309 438654579956589451537933)
                ·
                  refine ⟨164495467483721044326725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438654579956589451537933 164495467483721044326725)
                  ·
                    rfl

theorem cell20_360398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_360398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360398 prefixEnd_360398 := by exact prefixLift 360398
  have htrace : WordTrace (prefixWord ++ tailWord_360398) baseStart_360398 baseEnd_360398 := by
    simpa [prefixWord, tailWord_360398, baseEnd_360398] using wordTrace_append hprefix tailTrace_360398
  have hstable : (prefixWord ++ tailWord_360398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360398).length < 2 ^ (prefixWord ++ tailWord_360398).sum := by decide
  have hdescent : baseEnd_360398 < baseStart_360398 := by decide
  rcases family_descends (prefixWord ++ tailWord_360398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360415 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_360415 : Nat := 118140960795 + 360415 * 2 ^ 59
def prefixEnd_360415 : Nat := 4983230072969 + 3 ^ 40 * 360415 * 2
def baseEnd_360415 : Nat := 164503226746944540759989

theorem tailTrace_360415 : CollatzResearch.WordTrace tailWord_360415 prefixEnd_360415 164503226746944540759989 := by
  unfold tailWord_360415
  simp only [CollatzResearch.WordTrace]
  refine ⟨13145414989285483826546699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8763609992856989217697799 13145414989285483826546699)
  ·
    refine ⟨19718122483928225739820049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13145414989285483826546699 19718122483928225739820049)
    ·
      refine ⟨14788591862946169304865037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19718122483928225739820049 14788591862946169304865037)
      ·
        refine ⟨5545721948604813489324389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14788591862946169304865037 5545721948604813489324389)
        ·
          refine ⟨1039822865363402529248323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5545721948604813489324389 1039822865363402529248323)
          ·
            refine ⟨1559734298045103793872485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039822865363402529248323 1559734298045103793872485)
            ·
              refine ⟨292450180883456961351091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1559734298045103793872485 292450180883456961351091)
              ·
                refine ⟨438675271325185442026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292450180883456961351091 438675271325185442026637)
                ·
                  refine ⟨164503226746944540759989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438675271325185442026637 164503226746944540759989)
                  ·
                    rfl

theorem cell20_360415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_360415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360415 prefixEnd_360415 := by exact prefixLift 360415
  have htrace : WordTrace (prefixWord ++ tailWord_360415) baseStart_360415 baseEnd_360415 := by
    simpa [prefixWord, tailWord_360415, baseEnd_360415] using wordTrace_append hprefix tailTrace_360415
  have hstable : (prefixWord ++ tailWord_360415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360415).length < 2 ^ (prefixWord ++ tailWord_360415).sum := by decide
  have hdescent : baseEnd_360415 < baseStart_360415 := by decide
  rcases family_descends (prefixWord ++ tailWord_360415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360450 : List Nat := [3, 4, 1, 12]
def baseStart_360450 : Nat := 118140960795 + 360450 * 2 ^ 59
def prefixEnd_360450 : Nat := 4983230072969 + 3 ^ 40 * 360450 * 2
def baseEnd_360450 : Nat := 677033751854485492153

theorem tailTrace_360450 : CollatzResearch.WordTrace tailWord_360450 prefixEnd_360450 677033751854485492153 := by
  unfold tailWord_360450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286672886039671201017701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8764461029439123202713869 3286672886039671201017701)
  ·
    refine ⟨616251166132438350190819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3286672886039671201017701 616251166132438350190819)
    ·
      refine ⟨924376749198657525286229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616251166132438350190819 924376749198657525286229)
      ·
        refine ⟨677033751854485492153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 924376749198657525286229 677033751854485492153)
        ·
          rfl

theorem cell20_360450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 12].length) (baseStart_360450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360450 prefixEnd_360450 := by exact prefixLift 360450
  have htrace : WordTrace (prefixWord ++ tailWord_360450) baseStart_360450 baseEnd_360450 := by
    simpa [prefixWord, tailWord_360450, baseEnd_360450] using wordTrace_append hprefix tailTrace_360450
  have hstable : (prefixWord ++ tailWord_360450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360450).length < 2 ^ (prefixWord ++ tailWord_360450).sum := by decide
  have hdescent : baseEnd_360450 < baseStart_360450 := by decide
  rcases family_descends (prefixWord ++ tailWord_360450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360452 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_360452 : Nat := 118140960795 + 360452 * 2 ^ 59
def prefixEnd_360452 : Nat := 4983230072969 + 3 ^ 40 * 360452 * 2
def baseEnd_360452 : Nat := 164520114555136856526505

theorem tailTrace_360452 : CollatzResearch.WordTrace tailWord_360452 prefixEnd_360452 164520114555136856526505 := by
  unfold tailWord_360452
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573382245075719572821805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8764509660100959430429073 6573382245075719572821805)
  ·
    refine ⟨2465018341903394839808177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6573382245075719572821805 2465018341903394839808177)
    ·
      refine ⟨1848763756427546129856133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465018341903394839808177 1848763756427546129856133)
      ·
        refine ⟨346643204330164899348025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1848763756427546129856133 346643204330164899348025)
        ·
          refine ⟨259982403247623674511019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346643204330164899348025 259982403247623674511019)
          ·
            refine ⟨389973604871435511766529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259982403247623674511019 389973604871435511766529)
            ·
              refine ⟨292480203653576633824897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389973604871435511766529 292480203653576633824897)
              ·
                refine ⟨219360152740182475368673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292480203653576633824897 219360152740182475368673)
                ·
                  refine ⟨164520114555136856526505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219360152740182475368673 164520114555136856526505)
                  ·
                    rfl

theorem cell20_360452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_360452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360452 prefixEnd_360452 := by exact prefixLift 360452
  have htrace : WordTrace (prefixWord ++ tailWord_360452) baseStart_360452 baseEnd_360452 := by
    simpa [prefixWord, tailWord_360452, baseEnd_360452] using wordTrace_append hprefix tailTrace_360452
  have hstable : (prefixWord ++ tailWord_360452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360452).length < 2 ^ (prefixWord ++ tailWord_360452).sum := by decide
  have hdescent : baseEnd_360452 < baseStart_360452 := by decide
  rcases family_descends (prefixWord ++ tailWord_360452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360460 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_360460 : Nat := 118140960795 + 360460 * 2 ^ 59
def prefixEnd_360460 : Nat := 4983230072969 + 3 ^ 40 * 360460 * 2
def baseEnd_360460 : Nat := 164523765973124384259805

theorem tailTrace_360460 : CollatzResearch.WordTrace tailWord_360460 prefixEnd_360460 164523765973124384259805 := by
  unfold tailWord_360460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573528137061228255967417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8764704182748304341289889 6573528137061228255967417)
  ·
    refine ⟨4930146102795921191975563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6573528137061228255967417 4930146102795921191975563)
    ·
      refine ⟨7395219154193881787963345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930146102795921191975563 7395219154193881787963345)
      ·
        refine ⟨5546414365645411340972509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395219154193881787963345 5546414365645411340972509)
        ·
          refine ⟨2079905387117029252864691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5546414365645411340972509 2079905387117029252864691)
          ·
            refine ⟨3119858080675543879297037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079905387117029252864691 3119858080675543879297037)
            ·
              refine ⟨1169946780253328954736389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3119858080675543879297037 1169946780253328954736389)
              ·
                refine ⟨219365021297499179013073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1169946780253328954736389 219365021297499179013073)
                ·
                  refine ⟨164523765973124384259805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219365021297499179013073 164523765973124384259805)
                  ·
                    rfl

theorem cell20_360460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_360460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360460 prefixEnd_360460 := by exact prefixLift 360460
  have htrace : WordTrace (prefixWord ++ tailWord_360460) baseStart_360460 baseEnd_360460 := by
    simpa [prefixWord, tailWord_360460, baseEnd_360460] using wordTrace_append hprefix tailTrace_360460
  have hstable : (prefixWord ++ tailWord_360460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360460).length < 2 ^ (prefixWord ++ tailWord_360460).sum := by decide
  have hdescent : baseEnd_360460 < baseStart_360460 := by decide
  rcases family_descends (prefixWord ++ tailWord_360460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360474 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_360474 : Nat := 118140960795 + 360474 * 2 ^ 59
def prefixEnd_360474 : Nat := 4983230072969 + 3 ^ 40 * 360474 * 2
def baseEnd_360474 : Nat := 164530155954602557793081

theorem tailTrace_360474 : CollatzResearch.WordTrace tailWord_360474 prefixEnd_360474 164530155954602557793081 := by
  unfold tailWord_360474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286891724017934225736119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8765044597381157935296317 3286891724017934225736119)
  ·
    refine ⟨4930337586026901338604179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286891724017934225736119 4930337586026901338604179)
    ·
      refine ⟨7395506379040352007906269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930337586026901338604179 7395506379040352007906269)
      ·
        refine ⟨2773314892140132002964851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7395506379040352007906269 2773314892140132002964851)
        ·
          refine ⟨4159972338210198004447277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773314892140132002964851 4159972338210198004447277)
          ·
            refine ⟨1559989626828824251667729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4159972338210198004447277 1559989626828824251667729)
            ·
              refine ⟨1169992220121618188750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559989626828824251667729 1169992220121618188750797)
              ·
                refine ⟨438747082545606820781549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1169992220121618188750797 438747082545606820781549)
                ·
                  refine ⟨164530155954602557793081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438747082545606820781549 164530155954602557793081)
                  ·
                    rfl

theorem cell20_360474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_360474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360474 prefixEnd_360474 := by exact prefixLift 360474
  have htrace : WordTrace (prefixWord ++ tailWord_360474) baseStart_360474 baseEnd_360474 := by
    simpa [prefixWord, tailWord_360474, baseEnd_360474] using wordTrace_append hprefix tailTrace_360474
  have hstable : (prefixWord ++ tailWord_360474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360474).length < 2 ^ (prefixWord ++ tailWord_360474).sum := by decide
  have hdescent : baseEnd_360474 < baseStart_360474 := by decide
  rcases family_descends (prefixWord ++ tailWord_360474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360484 : List Nat := [2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_360484 : Nat := 118140960795 + 360484 * 2 ^ 59
def prefixEnd_360484 : Nat := 4983230072969 + 3 ^ 40 * 360484 * 2
def baseEnd_360484 : Nat := 54844906742362322486569

theorem tailTrace_360484 : CollatzResearch.WordTrace tailWord_360484 prefixEnd_360484 54844906742362322486569 := by
  unfold tailWord_360484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573965813017754305404253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8765287750690339073872337 6573965813017754305404253)
  ·
    refine ⟨2465237179881657864526595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6573965813017754305404253 2465237179881657864526595)
    ·
      refine ⟨3697855769822486796789893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465237179881657864526595 3697855769822486796789893)
      ·
        refine ⟨693347956841716274398105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3697855769822486796789893 693347956841716274398105)
        ·
          refine ⟨520010967631287205798579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693347956841716274398105 520010967631287205798579)
          ·
            refine ⟨780016451446930808697869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520010967631287205798579 780016451446930808697869)
            ·
              refine ⟨292506169292599053261701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780016451446930808697869 292506169292599053261701)
              ·
                refine ⟨54844906742362322486569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292506169292599053261701 54844906742362322486569)
                ·
                  rfl

theorem cell20_360484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_360484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360484 prefixEnd_360484 := by exact prefixLift 360484
  have htrace : WordTrace (prefixWord ++ tailWord_360484) baseStart_360484 baseEnd_360484 := by
    simpa [prefixWord, tailWord_360484, baseEnd_360484] using wordTrace_append hprefix tailTrace_360484
  have hstable : (prefixWord ++ tailWord_360484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360484).length < 2 ^ (prefixWord ++ tailWord_360484).sum := by decide
  have hdescent : baseEnd_360484 < baseStart_360484 := by decide
  rcases family_descends (prefixWord ++ tailWord_360484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360498 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_360498 : Nat := 118140960795 + 360498 * 2 ^ 59
def prefixEnd_360498 : Nat := 4983230072969 + 3 ^ 40 * 360498 * 2
def baseEnd_360498 : Nat := 164541110208565140992983

theorem tailTrace_360498 : CollatzResearch.WordTrace tailWord_360498 prefixEnd_360498 164541110208565140992983 := by
  unfold tailWord_360498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287110561996197250454537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8765628165323192667878765 3287110561996197250454537)
  ·
    refine ⟨2465332921497147937840903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3287110561996197250454537 2465332921497147937840903)
    ·
      refine ⟨3697999382245721906761355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465332921497147937840903 3697999382245721906761355)
      ·
        refine ⟨5546999073368582860142033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697999382245721906761355 5546999073368582860142033)
        ·
          refine ⟨4160249305026437145106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546999073368582860142033 4160249305026437145106525)
          ·
            refine ⟨1560093489384913929414947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4160249305026437145106525 1560093489384913929414947)
            ·
              refine ⟨2340140234077370894122421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560093489384913929414947 2340140234077370894122421)
              ·
                refine ⟨219388146944753521323977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2340140234077370894122421 219388146944753521323977)
                ·
                  refine ⟨164541110208565140992983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219388146944753521323977 164541110208565140992983)
                  ·
                    rfl

theorem cell20_360498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_360498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360498 prefixEnd_360498 := by exact prefixLift 360498
  have htrace : WordTrace (prefixWord ++ tailWord_360498) baseStart_360498 baseEnd_360498 := by
    simpa [prefixWord, tailWord_360498, baseEnd_360498] using wordTrace_append hprefix tailTrace_360498
  have hstable : (prefixWord ++ tailWord_360498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360498).length < 2 ^ (prefixWord ++ tailWord_360498).sum := by decide
  have hdescent : baseEnd_360498 < baseStart_360498 := by decide
  rcases family_descends (prefixWord ++ tailWord_360498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360512 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_360512 : Nat := 118140960795 + 360512 * 2 ^ 59
def prefixEnd_360512 : Nat := 4983230072969 + 3 ^ 40 * 360512 * 2
def baseEnd_360512 : Nat := 164547500190043314526259

theorem tailTrace_360512 : CollatzResearch.WordTrace tailWord_360512 prefixEnd_360512 164547500190043314526259 := by
  unfold tailWord_360512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574476434967034696413895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8765968579956046261885193 6574476434967034696413895)
  ·
    refine ⟨9861714652450552044620843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6574476434967034696413895 9861714652450552044620843)
    ·
      refine ⟨14792571978675828066931265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9861714652450552044620843 14792571978675828066931265)
      ·
        refine ⟨11094428984006871050198449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14792571978675828066931265 11094428984006871050198449)
        ·
          refine ⟨8320821738005153287648837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11094428984006871050198449 8320821738005153287648837)
          ·
            refine ⟨1560154075875966241434157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8320821738005153287648837 1560154075875966241434157)
            ·
              refine ⟨585057778453487340537809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1560154075875966241434157 585057778453487340537809)
              ·
                refine ⟨438793333840115505403357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585057778453487340537809 438793333840115505403357)
                ·
                  refine ⟨164547500190043314526259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438793333840115505403357 164547500190043314526259)
                  ·
                    rfl

theorem cell20_360512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_360512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360512 prefixEnd_360512 := by exact prefixLift 360512
  have htrace : WordTrace (prefixWord ++ tailWord_360512) baseStart_360512 baseEnd_360512 := by
    simpa [prefixWord, tailWord_360512, baseEnd_360512] using wordTrace_append hprefix tailTrace_360512
  have hstable : (prefixWord ++ tailWord_360512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360512).length < 2 ^ (prefixWord ++ tailWord_360512).sum := by decide
  have hdescent : baseEnd_360512 < baseStart_360512 := by decide
  rcases family_descends (prefixWord ++ tailWord_360512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360519 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_360519 : Nat := 118140960795 + 360519 * 2 ^ 59
def prefixEnd_360519 : Nat := 4983230072969 + 3 ^ 40 * 360519 * 2
def baseEnd_360519 : Nat := 164550695180782401292897

theorem tailTrace_360519 : CollatzResearch.WordTrace tailWord_360519 prefixEnd_360519 164550695180782401292897 := by
  unfold tailWord_360519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13149208180908709588332611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8766138787272473058888407 13149208180908709588332611)
  ·
    refine ⟨19723812271363064382498917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13149208180908709588332611 19723812271363064382498917)
    ·
      refine ⟨3698214800880574571718547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19723812271363064382498917 3698214800880574571718547)
      ·
        refine ⟨5547322201320861857577821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698214800880574571718547 5547322201320861857577821)
        ·
          refine ⟨2080245825495323196591683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5547322201320861857577821 2080245825495323196591683)
          ·
            refine ⟨3120368738242984794887525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080245825495323196591683 3120368738242984794887525)
            ·
              refine ⟨585069138420559649041411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3120368738242984794887525 585069138420559649041411)
              ·
                refine ⟨877603707630839473562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585069138420559649041411 877603707630839473562117)
                ·
                  refine ⟨164550695180782401292897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877603707630839473562117 164550695180782401292897)
                  ·
                    rfl

theorem cell20_360519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_360519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360519 prefixEnd_360519 := by exact prefixLift 360519
  have htrace : WordTrace (prefixWord ++ tailWord_360519) baseStart_360519 baseEnd_360519 := by
    simpa [prefixWord, tailWord_360519, baseEnd_360519] using wordTrace_append hprefix tailTrace_360519
  have hstable : (prefixWord ++ tailWord_360519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360519).length < 2 ^ (prefixWord ++ tailWord_360519).sum := by decide
  have hdescent : baseEnd_360519 < baseStart_360519 := by decide
  rcases family_descends (prefixWord ++ tailWord_360519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360584 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_360584 : Nat := 118140960795 + 360584 * 2 ^ 59
def prefixEnd_360584 : Nat := 4983230072969 + 3 ^ 40 * 360584 * 2
def baseEnd_360584 : Nat := 164580362951931064125965

theorem tailTrace_360584 : CollatzResearch.WordTrace tailWord_360584 prefixEnd_360584 164580362951931064125965 := by
  unfold tailWord_360584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575789462836612844724403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8767719283782150459632537 6575789462836612844724403)
  ·
    refine ⟨9863684194254919267086605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6575789462836612844724403 9863684194254919267086605)
    ·
      refine ⟨3698881572845594725157477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9863684194254919267086605 3698881572845594725157477)
      ·
        refine ⟨693540294908549010967027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3698881572845594725157477 693540294908549010967027)
        ·
          refine ⟨1040310442362823516450541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693540294908549010967027 1040310442362823516450541)
          ·
            refine ⟨390116415886058818668953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1040310442362823516450541 390116415886058818668953)
            ·
              refine ⟨292587311914544114001715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390116415886058818668953 292587311914544114001715)
              ·
                refine ⟨438880967871816171002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292587311914544114001715 438880967871816171002573)
                ·
                  refine ⟨164580362951931064125965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438880967871816171002573 164580362951931064125965)
                  ·
                    rfl

theorem cell20_360584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_360584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360584 prefixEnd_360584 := by exact prefixLift 360584
  have htrace : WordTrace (prefixWord ++ tailWord_360584) baseStart_360584 baseEnd_360584 := by
    simpa [prefixWord, tailWord_360584, baseEnd_360584] using wordTrace_append hprefix tailTrace_360584
  have hstable : (prefixWord ++ tailWord_360584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360584).length < 2 ^ (prefixWord ++ tailWord_360584).sum := by decide
  have hdescent : baseEnd_360584 < baseStart_360584 := by decide
  rcases family_descends (prefixWord ++ tailWord_360584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360625 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 2]
def baseStart_360625 : Nat := 118140960795 + 360625 * 2 ^ 59
def prefixEnd_360625 : Nat := 4983230072969 + 3 ^ 40 * 360625 * 2
def baseEnd_360625 : Nat := 164599076469117143759131

theorem tailTrace_360625 : CollatzResearch.WordTrace tailWord_360625 prefixEnd_360625 164599076469117143759131 := by
  unfold tailWord_360625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153074318524689691691329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8768716212349793127794219 13153074318524689691691329)
  ·
    refine ⟨9864805738893517268768497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13153074318524689691691329 9864805738893517268768497)
    ·
      refine ⟨7398604304170137951576373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9864805738893517268768497 7398604304170137951576373)
      ·
        refine ⟨693619153515950432960285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7398604304170137951576373 693619153515950432960285)
        ·
          refine ⟨260107182568481412360107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693619153515950432960285 260107182568481412360107)
          ·
            refine ⟨390160773852722118540161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260107182568481412360107 390160773852722118540161)
            ·
              refine ⟨292620580389541588905121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390160773852722118540161 292620580389541588905121)
              ·
                refine ⟨219465435292156191678841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292620580389541588905121 219465435292156191678841)
                ·
                  refine ⟨164599076469117143759131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219465435292156191678841 164599076469117143759131)
                  ·
                    rfl

theorem cell20_360625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_360625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360625 prefixEnd_360625 := by exact prefixLift 360625
  have htrace : WordTrace (prefixWord ++ tailWord_360625) baseStart_360625 baseEnd_360625 := by
    simpa [prefixWord, tailWord_360625, baseEnd_360625] using wordTrace_append hprefix tailTrace_360625
  have hstable : (prefixWord ++ tailWord_360625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360625).length < 2 ^ (prefixWord ++ tailWord_360625).sum := by decide
  have hdescent : baseEnd_360625 < baseStart_360625 := by decide
  rcases family_descends (prefixWord ++ tailWord_360625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360626 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_360626 : Nat := 118140960795 + 360626 * 2 ^ 59
def prefixEnd_360626 : Nat := 4983230072969 + 3 ^ 40 * 360626 * 2
def baseEnd_360626 : Nat := 164599532896365584725793

theorem tailTrace_360626 : CollatzResearch.WordTrace tailWord_360626 prefixEnd_360626 164599532896365584725793 := by
  unfold tailWord_360626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288277697880266715619433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8768740527680711241651821 3288277697880266715619433)
  ·
    refine ⟨2466208273410200036714575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3288277697880266715619433 2466208273410200036714575)
    ·
      refine ⟨3699312410115300055071863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466208273410200036714575 3699312410115300055071863)
      ·
        refine ⟨5548968615172950082607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699312410115300055071863 5548968615172950082607795)
        ·
          refine ⟨8323452922759425123911693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548968615172950082607795 8323452922759425123911693)
          ·
            refine ⟨3121294846034784421466885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8323452922759425123911693 3121294846034784421466885)
            ·
              refine ⟨585242783631522079025041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3121294846034784421466885 585242783631522079025041)
              ·
                refine ⟨438932087723641559268781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585242783631522079025041 438932087723641559268781)
                ·
                  refine ⟨164599532896365584725793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438932087723641559268781 164599532896365584725793)
                  ·
                    rfl

theorem cell20_360626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_360626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360626 prefixEnd_360626 := by exact prefixLift 360626
  have htrace : WordTrace (prefixWord ++ tailWord_360626) baseStart_360626 baseEnd_360626 := by
    simpa [prefixWord, tailWord_360626, baseEnd_360626] using wordTrace_append hprefix tailTrace_360626
  have hstable : (prefixWord ++ tailWord_360626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360626).length < 2 ^ (prefixWord ++ tailWord_360626).sum := by decide
  have hdescent : baseEnd_360626 < baseStart_360626 := by decide
  rcases family_descends (prefixWord ++ tailWord_360626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360636 : List Nat := [2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_360636 : Nat := 118140960795 + 360636 * 2 ^ 59
def prefixEnd_360636 : Nat := 4983230072969 + 3 ^ 40 * 360636 * 2
def baseEnd_360636 : Nat := 54868032389616664797473

theorem tailTrace_360636 : CollatzResearch.WordTrace tailWord_360636 prefixEnd_360636 54868032389616664797473 := by
  unfold tailWord_360636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576737760742419285170881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8768983680989892380227841 6576737760742419285170881)
  ·
    refine ⟨4932553320556814463878161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6576737760742419285170881 4932553320556814463878161)
    ·
      refine ⟨3699414990417610847908621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932553320556814463878161 3699414990417610847908621)
      ·
        refine ⟨1387280621406604067965733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3699414990417610847908621 1387280621406604067965733)
        ·
          refine ⟨260115116513738262743575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1387280621406604067965733 260115116513738262743575)
          ·
            refine ⟨390172674770607394115363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260115116513738262743575 390172674770607394115363)
            ·
              refine ⟨585259012155911091173045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390172674770607394115363 585259012155911091173045)
              ·
                refine ⟨54868032389616664797473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585259012155911091173045 54868032389616664797473)
                ·
                  rfl

theorem cell20_360636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_360636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360636 prefixEnd_360636 := by exact prefixLift 360636
  have htrace : WordTrace (prefixWord ++ tailWord_360636) baseStart_360636 baseEnd_360636 := by
    simpa [prefixWord, tailWord_360636, baseEnd_360636] using wordTrace_append hprefix tailTrace_360636
  have hstable : (prefixWord ++ tailWord_360636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360636).length < 2 ^ (prefixWord ++ tailWord_360636).sum := by decide
  have hdescent : baseEnd_360636 < baseStart_360636 := by decide
  rcases family_descends (prefixWord ++ tailWord_360636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360640 : List Nat := [2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_360640 : Nat := 118140960795 + 360640 * 2 ^ 59
def prefixEnd_360640 : Nat := 4983230072969 + 3 ^ 40 * 360640 * 2
def baseEnd_360640 : Nat := 54868640959281252753023

theorem tailTrace_360640 : CollatzResearch.WordTrace tailWord_360640 prefixEnd_360640 54868640959281252753023 := by
  unfold tailWord_360640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576810706735173626743687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8769080942313564835658249 6576810706735173626743687)
  ·
    refine ⟨9865216060102760440115531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6576810706735173626743687 9865216060102760440115531)
    ·
      refine ⟨14797824090154140660173297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9865216060102760440115531 14797824090154140660173297)
      ·
        refine ⟨11098368067615605495129973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14797824090154140660173297 11098368067615605495129973)
        ·
          refine ⟨1040472006338963015168435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11098368067615605495129973 1040472006338963015168435)
          ·
            refine ⟨1560708009508444522752653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040472006338963015168435 1560708009508444522752653)
            ·
              refine ⟨585265503565666696032245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1560708009508444522752653 585265503565666696032245)
              ·
                refine ⟨54868640959281252753023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585265503565666696032245 54868640959281252753023)
                ·
                  rfl

theorem cell20_360640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_360640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360640 prefixEnd_360640 := by exact prefixLift 360640
  have htrace : WordTrace (prefixWord ++ tailWord_360640) baseStart_360640 baseEnd_360640 := by
    simpa [prefixWord, tailWord_360640, baseEnd_360640] using wordTrace_append hprefix tailTrace_360640
  have hstable : (prefixWord ++ tailWord_360640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360640).length < 2 ^ (prefixWord ++ tailWord_360640).sum := by decide
  have hdescent : baseEnd_360640 < baseStart_360640 := by decide
  rcases family_descends (prefixWord ++ tailWord_360640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360733 : List Nat := [1, 4, 2, 3, 2, 2, 6]
def baseStart_360733 : Nat := 118140960795 + 360733 * 2 ^ 59
def prefixEnd_360733 : Nat := 4983230072969 + 3 ^ 40 * 360733 * 2
def baseEnd_360733 : Nat := 18294263401327640906521

theorem tailTrace_360733 : CollatzResearch.WordTrace tailWord_360733 prefixEnd_360733 18294263401327640906521 := by
  unfold tailWord_360733
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157013402133424136622853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771342268088949424415235 13157013402133424136622853)
  ·
    refine ⟨2466940012900017025616785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13157013402133424136622853 2466940012900017025616785)
    ·
      refine ⟨1850205009675012769212589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2466940012900017025616785 1850205009675012769212589)
      ·
        refine ⟨693826878628129788454721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1850205009675012769212589 693826878628129788454721)
        ·
          refine ⟨520370158971097341341041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693826878628129788454721 520370158971097341341041)
          ·
            refine ⟨390277619228323006005781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520370158971097341341041 390277619228323006005781)
            ·
              refine ⟨18294263401327640906521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 390277619228323006005781 18294263401327640906521)
              ·
                rfl

theorem cell20_360733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_360733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360733 prefixEnd_360733 := by exact prefixLift 360733
  have htrace : WordTrace (prefixWord ++ tailWord_360733) baseStart_360733 baseEnd_360733 := by
    simpa [prefixWord, tailWord_360733, baseEnd_360733] using wordTrace_append hprefix tailTrace_360733
  have hstable : (prefixWord ++ tailWord_360733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360733).length < 2 ^ (prefixWord ++ tailWord_360733).sum := by decide
  have hdescent : baseEnd_360733 < baseStart_360733 := by decide
  rcases family_descends (prefixWord ++ tailWord_360733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360737 : List Nat := [1, 2, 3, 2, 1, 1, 10]
def baseStart_360737 : Nat := 118140960795 + 360737 * 2 ^ 59
def prefixEnd_360737 : Nat := 4983230072969 + 3 ^ 40 * 360737 * 2
def baseEnd_360737 : Nat := 18294466257882503558371

theorem tailTrace_360737 : CollatzResearch.WordTrace tailWord_360737 prefixEnd_360737 18294466257882503558371 := by
  unfold tailWord_360737
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157159294118932819768465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771439529412621879845643 13157159294118932819768465)
  ·
    refine ⟨9867869470589199614826349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13157159294118932819768465 9867869470589199614826349)
    ·
      refine ⟨3700451051470949855559881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9867869470589199614826349 3700451051470949855559881)
      ·
        refine ⟨2775338288603212391669911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3700451051470949855559881 2775338288603212391669911)
        ·
          refine ⟨4163007432904818587504867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775338288603212391669911 4163007432904818587504867)
          ·
            refine ⟨6244511149357227881257301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163007432904818587504867 6244511149357227881257301)
            ·
              refine ⟨18294466257882503558371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6244511149357227881257301 18294466257882503558371)
              ·
                rfl

theorem cell20_360737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_360737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360737 prefixEnd_360737 := by exact prefixLift 360737
  have htrace : WordTrace (prefixWord ++ tailWord_360737) baseStart_360737 baseEnd_360737 := by
    simpa [prefixWord, tailWord_360737, baseEnd_360737] using wordTrace_append hprefix tailTrace_360737
  have hstable : (prefixWord ++ tailWord_360737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360737).length < 2 ^ (prefixWord ++ tailWord_360737).sum := by decide
  have hdescent : baseEnd_360737 < baseStart_360737 := by decide
  rcases family_descends (prefixWord ++ tailWord_360737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360750 : List Nat := [4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_360750 : Nat := 118140960795 + 360750 * 2 ^ 59
def prefixEnd_360750 : Nat := 4983230072969 + 3 ^ 40 * 360750 * 2
def baseEnd_360750 : Nat := 54885376625057421530651

theorem tailTrace_360750 : CollatzResearch.WordTrace tailWord_360750 prefixEnd_360750 54885376625057421530651 := by
  unfold tailWord_360750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644704180383979504998963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8771755628714557359994469 1644704180383979504998963)
  ·
    refine ⟨2467056270575969257498445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644704180383979504998963 2467056270575969257498445)
    ·
      refine ⟨925146101465988471561917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2467056270575969257498445 925146101465988471561917)
      ·
        refine ⟨346929788049745676835719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 925146101465988471561917 346929788049745676835719)
        ·
          refine ⟨520394682074618515253579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346929788049745676835719 520394682074618515253579)
          ·
            refine ⟨780592023111927772880369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520394682074618515253579 780592023111927772880369)
            ·
              refine ⟨585444017333945829660277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780592023111927772880369 585444017333945829660277)
              ·
                refine ⟨54885376625057421530651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585444017333945829660277 54885376625057421530651)
                ·
                  rfl

theorem cell20_360750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_360750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360750 prefixEnd_360750 := by exact prefixLift 360750
  have htrace : WordTrace (prefixWord ++ tailWord_360750) baseStart_360750 baseEnd_360750 := by
    simpa [prefixWord, tailWord_360750, baseEnd_360750] using wordTrace_append hprefix tailTrace_360750
  have hstable : (prefixWord ++ tailWord_360750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360750).length < 2 ^ (prefixWord ++ tailWord_360750).sum := by decide
  have hdescent : baseEnd_360750 < baseStart_360750 := by decide
  rcases family_descends (prefixWord ++ tailWord_360750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360775 : List Nat := [1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_360775 : Nat := 118140960795 + 360775 * 2 ^ 59
def prefixEnd_360775 : Nat := 4983230072969 + 3 ^ 40 * 360775 * 2
def baseEnd_360775 : Nat := 54889180185461096252839

theorem tailTrace_360775 : CollatzResearch.WordTrace tailWord_360775 prefixEnd_360775 54889180185461096252839 := by
  unfold tailWord_360775
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158545267981265309651779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8772363511987510206434519 13158545267981265309651779)
  ·
    refine ⟨19737817901971897964477669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13158545267981265309651779 19737817901971897964477669)
    ·
      refine ⟨3700840856619730868339563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19737817901971897964477669 3700840856619730868339563)
      ·
        refine ⟨5551261284929596302509345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700840856619730868339563 5551261284929596302509345)
        ·
          refine ⟨4163445963697197226882009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5551261284929596302509345 4163445963697197226882009)
          ·
            refine ⟨3122584472772897920161507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4163445963697197226882009 3122584472772897920161507)
            ·
              refine ⟨4683876709159346880242261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122584472772897920161507 4683876709159346880242261)
              ·
                refine ⟨54889180185461096252839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4683876709159346880242261 54889180185461096252839)
                ·
                  rfl

theorem cell20_360775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_360775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360775 prefixEnd_360775 := by exact prefixLift 360775
  have htrace : WordTrace (prefixWord ++ tailWord_360775) baseStart_360775 baseEnd_360775 := by
    simpa [prefixWord, tailWord_360775, baseEnd_360775] using wordTrace_append hprefix tailTrace_360775
  have hstable : (prefixWord ++ tailWord_360775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360775).length < 2 ^ (prefixWord ++ tailWord_360775).sum := by decide
  have hdescent : baseEnd_360775 < baseStart_360775 := by decide
  rcases family_descends (prefixWord ++ tailWord_360775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360799 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_360799 : Nat := 118140960795 + 360799 * 2 ^ 59
def prefixEnd_360799 : Nat := 4983230072969 + 3 ^ 40 * 360799 * 2
def baseEnd_360799 : Nat := 164678494810345871958419

theorem tailTrace_360799 : CollatzResearch.WordTrace tailWord_360799 prefixEnd_360799 164678494810345871958419 := by
  unfold tailWord_360799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13159420619894317408525451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8772947079929544939016967 13159420619894317408525451)
  ·
    refine ⟨19739130929841476112788177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13159420619894317408525451 19739130929841476112788177)
    ·
      refine ⟨14804348197381107084591133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19739130929841476112788177 14804348197381107084591133)
      ·
        refine ⟨5551630574017915156721675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14804348197381107084591133 5551630574017915156721675)
        ·
          refine ⟨8327445861026872735082513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551630574017915156721675 8327445861026872735082513)
          ·
            refine ⟨6245584395770154551311885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8327445861026872735082513 6245584395770154551311885)
            ·
              refine ⟨2342094148413807956741957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245584395770154551311885 2342094148413807956741957)
              ·
                refine ⟨439142652827588991889117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2342094148413807956741957 439142652827588991889117)
                ·
                  refine ⟨164678494810345871958419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439142652827588991889117 164678494810345871958419)
                  ·
                    rfl

theorem cell20_360799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_360799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360799 prefixEnd_360799 := by exact prefixLift 360799
  have htrace : WordTrace (prefixWord ++ tailWord_360799) baseStart_360799 baseEnd_360799 := by
    simpa [prefixWord, tailWord_360799, baseEnd_360799] using wordTrace_append hprefix tailTrace_360799
  have hstable : (prefixWord ++ tailWord_360799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360799).length < 2 ^ (prefixWord ++ tailWord_360799).sum := by decide
  have hdescent : baseEnd_360799 < baseStart_360799 := by decide
  rcases family_descends (prefixWord ++ tailWord_360799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360840 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_360840 : Nat := 118140960795 + 360840 * 2 ^ 59
def prefixEnd_360840 : Nat := 4983230072969 + 3 ^ 40 * 360840 * 2
def baseEnd_360840 : Nat := 164697208327531951591585

theorem tailTrace_360840 : CollatzResearch.WordTrace tailWord_360840 prefixEnd_360840 164697208327531951591585 := by
  unfold tailWord_360840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580458006372890705383987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8773944008497187607178649 6580458006372890705383987)
  ·
    refine ⟨9870687009559336058075981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6580458006372890705383987 9870687009559336058075981)
    ·
      refine ⟨3701507628584751021778493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9870687009559336058075981 3701507628584751021778493)
      ·
        refine ⟨1388065360719281633166935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3701507628584751021778493 1388065360719281633166935)
        ·
          refine ⟨2082098041078922449750403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388065360719281633166935 2082098041078922449750403)
          ·
            refine ⟨3123147061618383674625605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082098041078922449750403 3123147061618383674625605)
            ·
              refine ⟨585590074053446938992301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3123147061618383674625605 585590074053446938992301)
              ·
                refine ⟨219596277770042602122113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585590074053446938992301 219596277770042602122113)
                ·
                  refine ⟨164697208327531951591585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219596277770042602122113 164697208327531951591585)
                  ·
                    rfl

theorem cell20_360840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_360840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360840 prefixEnd_360840 := by exact prefixLift 360840
  have htrace : WordTrace (prefixWord ++ tailWord_360840) baseStart_360840 baseEnd_360840 := by
    simpa [prefixWord, tailWord_360840, baseEnd_360840] using wordTrace_append hprefix tailTrace_360840
  have hstable : (prefixWord ++ tailWord_360840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360840).length < 2 ^ (prefixWord ++ tailWord_360840).sum := by decide
  have hdescent : baseEnd_360840 < baseStart_360840 := by decide
  rcases family_descends (prefixWord ++ tailWord_360840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360871 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_360871 : Nat := 118140960795 + 360871 * 2 ^ 59
def prefixEnd_360871 : Nat := 4983230072969 + 3 ^ 40 * 360871 * 2
def baseEnd_360871 : Nat := 164711357572233621558125

theorem tailTrace_360871 : CollatzResearch.WordTrace tailWord_360871 prefixEnd_360871 164711357572233621558125 := by
  unfold tailWord_360871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162046675633473705146467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8774697783755649136764311 13162046675633473705146467)
  ·
    refine ⟨19743070013450210557719701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13162046675633473705146467 19743070013450210557719701)
    ·
      refine ⟨925456406880478619893111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19743070013450210557719701 925456406880478619893111)
      ·
        refine ⟨1388184610320717929839667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925456406880478619893111 1388184610320717929839667)
        ·
          refine ⟨2082276915481076894759501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388184610320717929839667 2082276915481076894759501)
          ·
            refine ⟨780853843305403835534813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2082276915481076894759501 780853843305403835534813)
            ·
              refine ⟨292820191239526438325555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780853843305403835534813 292820191239526438325555)
              ·
                refine ⟨439230286859289657488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292820191239526438325555 439230286859289657488333)
                ·
                  refine ⟨164711357572233621558125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439230286859289657488333 164711357572233621558125)
                  ·
                    rfl

theorem cell20_360871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_360871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360871 prefixEnd_360871 := by exact prefixLift 360871
  have htrace : WordTrace (prefixWord ++ tailWord_360871) baseStart_360871 baseEnd_360871 := by
    simpa [prefixWord, tailWord_360871, baseEnd_360871] using wordTrace_append hprefix tailTrace_360871
  have hstable : (prefixWord ++ tailWord_360871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360871).length < 2 ^ (prefixWord ++ tailWord_360871).sum := by decide
  have hdescent : baseEnd_360871 < baseStart_360871 := by decide
  rcases family_descends (prefixWord ++ tailWord_360871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360882 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_360882 : Nat := 118140960795 + 360882 * 2 ^ 59
def prefixEnd_360882 : Nat := 4983230072969 + 3 ^ 40 * 360882 * 2
def baseEnd_360882 : Nat := 164716378271966472191413

theorem tailTrace_360882 : CollatzResearch.WordTrace tailWord_360882 prefixEnd_360882 164716378271966472191413 := by
  unfold tailWord_360882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290611969648405645949225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8774965252395748389197933 3290611969648405645949225)
  ·
    refine ⟨2467958977236304234461919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3290611969648405645949225 2467958977236304234461919)
    ·
      refine ⟨3701938465854456351692879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467958977236304234461919 3701938465854456351692879)
      ·
        refine ⟨5552907698781684527539319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701938465854456351692879 5552907698781684527539319)
        ·
          refine ⟨8329361548172526791308979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552907698781684527539319 8329361548172526791308979)
          ·
            refine ⟨12494042322258790186963469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329361548172526791308979 12494042322258790186963469)
            ·
              refine ⟨4685265870847046320111301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12494042322258790186963469 4685265870847046320111301)
              ·
                refine ⟨878487350783821185020869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4685265870847046320111301 878487350783821185020869)
                ·
                  refine ⟨164716378271966472191413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878487350783821185020869 164716378271966472191413)
                  ·
                    rfl

theorem cell20_360882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_360882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360882 prefixEnd_360882 := by exact prefixLift 360882
  have htrace : WordTrace (prefixWord ++ tailWord_360882) baseStart_360882 baseEnd_360882 := by
    simpa [prefixWord, tailWord_360882, baseEnd_360882] using wordTrace_append hprefix tailTrace_360882
  have hstable : (prefixWord ++ tailWord_360882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360882).length < 2 ^ (prefixWord ++ tailWord_360882).sum := by decide
  have hdescent : baseEnd_360882 < baseStart_360882 := by decide
  rcases family_descends (prefixWord ++ tailWord_360882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360916 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_360916 : Nat := 118140960795 + 360916 * 2 ^ 59
def prefixEnd_360916 : Nat := 4983230072969 + 3 ^ 40 * 360916 * 2
def baseEnd_360916 : Nat := 164731896798413465057941

theorem tailTrace_360916 : CollatzResearch.WordTrace tailWord_360916 prefixEnd_360916 164731896798413465057941 := by
  unfold tailWord_360916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581843980235223195267301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8775791973646964260356401 6581843980235223195267301)
  ·
    refine ⟨1234095746294104349112619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6581843980235223195267301 1234095746294104349112619)
    ·
      refine ⟨1851143619441156523668929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234095746294104349112619 1851143619441156523668929)
      ·
        refine ⟨1388357714580867392751697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1851143619441156523668929 1388357714580867392751697)
        ·
          refine ⟨1041268285935650544563773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388357714580867392751697 1041268285935650544563773)
          ·
            refine ⟨390475607225868954211415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1041268285935650544563773 390475607225868954211415)
            ·
              refine ⟨585713410838803431317123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390475607225868954211415 585713410838803431317123)
              ·
                refine ⟨878570116258205146975685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585713410838803431317123 878570116258205146975685)
                ·
                  refine ⟨164731896798413465057941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878570116258205146975685 164731896798413465057941)
                  ·
                    rfl

theorem cell20_360916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_360916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360916 prefixEnd_360916 := by exact prefixLift 360916
  have htrace : WordTrace (prefixWord ++ tailWord_360916) baseStart_360916 baseEnd_360916 := by
    simpa [prefixWord, tailWord_360916, baseEnd_360916] using wordTrace_append hprefix tailTrace_360916
  have hstable : (prefixWord ++ tailWord_360916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360916).length < 2 ^ (prefixWord ++ tailWord_360916).sum := by decide
  have hdescent : baseEnd_360916 < baseStart_360916 := by decide
  rcases family_descends (prefixWord ++ tailWord_360916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360927 : List Nat := [1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_360927 : Nat := 118140960795 + 360927 * 2 ^ 59
def prefixEnd_360927 : Nat := 4983230072969 + 3 ^ 40 * 360927 * 2
def baseEnd_360927 : Nat := 54912305832715438563743

theorem tailTrace_360927 : CollatzResearch.WordTrace tailWord_360927 prefixEnd_360927 54912305832715438563743 := by
  unfold tailWord_360927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164089163430595269185035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8776059442287063512790023 13164089163430595269185035)
  ·
    refine ⟨19746133745145892903777553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13164089163430595269185035 19746133745145892903777553)
    ·
      refine ⟨14809600308859419677833165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19746133745145892903777553 14809600308859419677833165)
      ·
        refine ⟨5553600115822282379187437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14809600308859419677833165 5553600115822282379187437)
        ·
          refine ⟨2082600043433355892195289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5553600115822282379187437 2082600043433355892195289)
          ·
            refine ⟨1561950032575016919146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082600043433355892195289 1561950032575016919146467)
            ·
              refine ⟨2342925048862525378719701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561950032575016919146467 2342925048862525378719701)
              ·
                refine ⟨54912305832715438563743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2342925048862525378719701 54912305832715438563743)
                ·
                  rfl

theorem cell20_360927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_360927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360927 prefixEnd_360927 := by exact prefixLift 360927
  have htrace : WordTrace (prefixWord ++ tailWord_360927) baseStart_360927 baseEnd_360927 := by
    simpa [prefixWord, tailWord_360927, baseEnd_360927] using wordTrace_append hprefix tailTrace_360927
  have hstable : (prefixWord ++ tailWord_360927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360927).length < 2 ^ (prefixWord ++ tailWord_360927).sum := by decide
  have hdescent : baseEnd_360927 < baseStart_360927 := by decide
  rcases family_descends (prefixWord ++ tailWord_360927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360971 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 2]
def baseStart_360971 : Nat := 118140960795 + 360971 * 2 ^ 59
def prefixEnd_360971 : Nat := 4983230072969 + 3 ^ 40 * 360971 * 2
def baseEnd_360971 : Nat := 164757000297077718224383

theorem tailTrace_360971 : CollatzResearch.WordTrace tailWord_360971 prefixEnd_360971 164757000297077718224383 := by
  unfold tailWord_360971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165693975271190783786767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777129316847460522524511 13165693975271190783786767)
  ·
    refine ⟨19748540962906786175680151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13165693975271190783786767 19748540962906786175680151)
    ·
      refine ⟨29622811444360179263520227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748540962906786175680151 29622811444360179263520227)
      ·
        refine ⟨44434217166540268895280341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29622811444360179263520227 44434217166540268895280341)
        ·
          refine ⟨1041426964840787552233133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44434217166540268895280341 1041426964840787552233133)
          ·
            refine ⟨390535111815295332087425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1041426964840787552233133 390535111815295332087425)
            ·
              refine ⟨292901333861471499065569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390535111815295332087425 292901333861471499065569)
              ·
                refine ⟨219676000396103624299177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292901333861471499065569 219676000396103624299177)
                ·
                  refine ⟨164757000297077718224383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219676000396103624299177 164757000297077718224383)
                  ·
                    rfl

theorem cell20_360971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 2].length) (baseStart_360971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_360971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_360971 prefixEnd_360971 := by exact prefixLift 360971
  have htrace : WordTrace (prefixWord ++ tailWord_360971) baseStart_360971 baseEnd_360971 := by
    simpa [prefixWord, tailWord_360971, baseEnd_360971] using wordTrace_append hprefix tailTrace_360971
  have hstable : (prefixWord ++ tailWord_360971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360971).length < 2 ^ (prefixWord ++ tailWord_360971).sum := by decide
  have hdescent : baseEnd_360971 < baseStart_360971 := by decide
  rcases family_descends (prefixWord ++ tailWord_360971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361005 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 2]
def baseStart_361005 : Nat := 118140960795 + 361005 * 2 ^ 59
def prefixEnd_361005 : Nat := 4983230072969 + 3 ^ 40 * 361005 * 2
def baseEnd_361005 : Nat := 164772518823524711090911

theorem tailTrace_361005 : CollatzResearch.WordTrace tailWord_361005 prefixEnd_361005 164772518823524711090911 := by
  unfold tailWord_361005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166934057148014590524469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777956038098676393682979 13166934057148014590524469)
  ·
    refine ⟨1234400067857626367861669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13166934057148014590524469 1234400067857626367861669)
    ·
      refine ⟨231450012723304943974063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1234400067857626367861669 231450012723304943974063)
      ·
        refine ⟨347175019084957415961095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231450012723304943974063 347175019084957415961095)
        ·
          refine ⟨520762528627436123941643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347175019084957415961095 520762528627436123941643)
          ·
            refine ⟨781143792941154185912465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520762528627436123941643 781143792941154185912465)
            ·
              refine ⟨585857844705865639434349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781143792941154185912465 585857844705865639434349)
              ·
                refine ⟨219696691764699614787881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585857844705865639434349 219696691764699614787881)
                ·
                  refine ⟨164772518823524711090911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219696691764699614787881 164772518823524711090911)
                  ·
                    rfl

theorem cell20_361005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_361005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361005 prefixEnd_361005 := by exact prefixLift 361005
  have htrace : WordTrace (prefixWord ++ tailWord_361005) baseStart_361005 baseEnd_361005 := by
    simpa [prefixWord, tailWord_361005, baseEnd_361005] using wordTrace_append hprefix tailTrace_361005
  have hstable : (prefixWord ++ tailWord_361005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361005).length < 2 ^ (prefixWord ++ tailWord_361005).sum := by decide
  have hdescent : baseEnd_361005 < baseStart_361005 := by decide
  rcases family_descends (prefixWord ++ tailWord_361005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361030 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_361030 : Nat := 118140960795 + 361030 * 2 ^ 59
def prefixEnd_361030 : Nat := 4983230072969 + 3 ^ 40 * 361030 * 2
def baseEnd_361030 : Nat := 164783929504735735257475

theorem tailTrace_361030 : CollatzResearch.WordTrace tailWord_361030 prefixEnd_361030 164783929504735735257475 := by
  unfold tailWord_361030
  simp only [CollatzResearch.WordTrace]
  refine ⟨411495183814295120630767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8778563921371629240123029 411495183814295120630767)
  ·
    refine ⟨617242775721442680946151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411495183814295120630767 617242775721442680946151)
    ·
      refine ⟨925864163582164021419227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617242775721442680946151 925864163582164021419227)
      ·
        refine ⟨1388796245373246032128841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925864163582164021419227 1388796245373246032128841)
        ·
          refine ⟨1041597184029934524096631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388796245373246032128841 1041597184029934524096631)
          ·
            refine ⟨1562395776044901786144947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041597184029934524096631 1562395776044901786144947)
            ·
              refine ⟨2343593664067352679217421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562395776044901786144947 2343593664067352679217421)
              ·
                refine ⟨878847624025257254706533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2343593664067352679217421 878847624025257254706533)
                ·
                  refine ⟨164783929504735735257475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878847624025257254706533 164783929504735735257475)
                  ·
                    rfl

theorem cell20_361030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_361030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361030 prefixEnd_361030 := by exact prefixLift 361030
  have htrace : WordTrace (prefixWord ++ tailWord_361030) baseStart_361030 baseEnd_361030 := by
    simpa [prefixWord, tailWord_361030, baseEnd_361030] using wordTrace_append hprefix tailTrace_361030
  have hstable : (prefixWord ++ tailWord_361030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361030).length < 2 ^ (prefixWord ++ tailWord_361030).sum := by decide
  have hdescent : baseEnd_361030 < baseStart_361030 := by decide
  rcases family_descends (prefixWord ++ tailWord_361030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361034 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_361034 : Nat := 118140960795 + 361034 * 2 ^ 59
def prefixEnd_361034 : Nat := 4983230072969 + 3 ^ 40 * 361034 * 2
def baseEnd_361034 : Nat := 164785755213729499124125

theorem tailTrace_361034 : CollatzResearch.WordTrace tailWord_361034 prefixEnd_361034 164785755213729499124125 := by
  unfold tailWord_361034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291997943510738135832539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8778661182695301695553437 3291997943510738135832539)
  ·
    refine ⟨4937996915266107203748809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3291997943510738135832539 4937996915266107203748809)
    ·
      refine ⟨3703497686449580402811607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4937996915266107203748809 3703497686449580402811607)
      ·
        refine ⟨5555246529674370604217411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703497686449580402811607 5555246529674370604217411)
        ·
          refine ⟨8332869794511555906326117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555246529674370604217411 8332869794511555906326117)
          ·
            refine ⟨1562413086470916732436147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8332869794511555906326117 1562413086470916732436147)
            ·
              refine ⟨2343619629706375098654221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562413086470916732436147 2343619629706375098654221)
              ·
                refine ⟨878857361139890661995333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2343619629706375098654221 878857361139890661995333)
                ·
                  refine ⟨164785755213729499124125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878857361139890661995333 164785755213729499124125)
                  ·
                    rfl

theorem cell20_361034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_361034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361034 prefixEnd_361034 := by exact prefixLift 361034
  have htrace : WordTrace (prefixWord ++ tailWord_361034) baseStart_361034 baseEnd_361034 := by
    simpa [prefixWord, tailWord_361034, baseEnd_361034] using wordTrace_append hprefix tailTrace_361034
  have hstable : (prefixWord ++ tailWord_361034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361034).length < 2 ^ (prefixWord ++ tailWord_361034).sum := by decide
  have hdescent : baseEnd_361034 < baseStart_361034 := by decide
  rcases family_descends (prefixWord ++ tailWord_361034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361064 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_361064 : Nat := 118140960795 + 361064 * 2 ^ 59
def prefixEnd_361064 : Nat := 4983230072969 + 3 ^ 40 * 361064 * 2
def baseEnd_361064 : Nat := 164799448031182728124003

theorem tailTrace_361064 : CollatzResearch.WordTrace tailWord_361064 prefixEnd_361064 164799448031182728124003 := by
  unfold tailWord_361064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584542981967133833461123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8779390642622845111281497 6584542981967133833461123)
  ·
    refine ⟨9876814472950700750191685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6584542981967133833461123 9876814472950700750191685)
    ·
      refine ⟨1851902713678256390660941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9876814472950700750191685 1851902713678256390660941)
      ·
        refine ⟨694463517629346146497853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1851902713678256390660941 694463517629346146497853)
        ·
          refine ⟨260423819111004804936695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 694463517629346146497853 260423819111004804936695)
          ·
            refine ⟨390635728666507207405043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260423819111004804936695 390635728666507207405043)
            ·
              refine ⟨585953592999760811107565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390635728666507207405043 585953592999760811107565)
              ·
                refine ⟨219732597374910304165337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585953592999760811107565 219732597374910304165337)
                ·
                  refine ⟨164799448031182728124003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219732597374910304165337 164799448031182728124003)
                  ·
                    rfl

theorem cell20_361064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_361064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361064 prefixEnd_361064 := by exact prefixLift 361064
  have htrace : WordTrace (prefixWord ++ tailWord_361064) baseStart_361064 baseEnd_361064 := by
    simpa [prefixWord, tailWord_361064, baseEnd_361064] using wordTrace_append hprefix tailTrace_361064
  have hstable : (prefixWord ++ tailWord_361064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361064).length < 2 ^ (prefixWord ++ tailWord_361064).sum := by decide
  have hdescent : baseEnd_361064 < baseStart_361064 := by decide
  rcases family_descends (prefixWord ++ tailWord_361064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361085 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 2]
def baseStart_361085 : Nat := 118140960795 + 361085 * 2 ^ 59
def prefixEnd_361085 : Nat := 4983230072969 + 3 ^ 40 * 361085 * 2
def baseEnd_361085 : Nat := 164809033003399988423917

theorem tailTrace_361085 : CollatzResearch.WordTrace tailWord_361085 prefixEnd_361085 164809033003399988423917 := by
  unfold tailWord_361085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13169851896858188253436709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8779901264572125502291139 13169851896858188253436709)
  ·
    refine ⟨2469347230660910297519383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13169851896858188253436709 2469347230660910297519383)
    ·
      refine ⟨3704020845991365446279075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469347230660910297519383 3704020845991365446279075)
      ·
        refine ⟨5556031268987048169418613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704020845991365446279075 5556031268987048169418613)
        ·
          refine ⟨520877931467535765882995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5556031268987048169418613 520877931467535765882995)
          ·
            refine ⟨781316897201303648824493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520877931467535765882995 781316897201303648824493)
            ·
              refine ⟨292993836450488868309185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781316897201303648824493 292993836450488868309185)
              ·
                refine ⟨219745377337866651231889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292993836450488868309185 219745377337866651231889)
                ·
                  refine ⟨164809033003399988423917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219745377337866651231889 164809033003399988423917)
                  ·
                    rfl

theorem cell20_361085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_361085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361085 prefixEnd_361085 := by exact prefixLift 361085
  have htrace : WordTrace (prefixWord ++ tailWord_361085) baseStart_361085 baseEnd_361085 := by
    simpa [prefixWord, tailWord_361085, baseEnd_361085] using wordTrace_append hprefix tailTrace_361085
  have hstable : (prefixWord ++ tailWord_361085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361085).length < 2 ^ (prefixWord ++ tailWord_361085).sum := by decide
  have hdescent : baseEnd_361085 < baseStart_361085 := by decide
  rcases family_descends (prefixWord ++ tailWord_361085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361117 : List Nat := [1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_361117 : Nat := 118140960795 + 361117 * 2 ^ 59
def prefixEnd_361117 : Nat := 4983230072969 + 3 ^ 40 * 361117 * 2
def baseEnd_361117 : Nat := 54941212891783366452373

theorem tailTrace_361117 : CollatzResearch.WordTrace tailWord_361117 prefixEnd_361117 54941212891783366452373 := by
  unfold tailWord_361117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13171019032742257718601605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8780679355161505145734403 13171019032742257718601605)
  ·
    refine ⟨2469566068639173322237801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13171019032742257718601605 2469566068639173322237801)
    ·
      refine ⟨1852174551479379991678351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2469566068639173322237801 1852174551479379991678351)
      ·
        refine ⟨2778261827219069987517527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852174551479379991678351 2778261827219069987517527)
        ·
          refine ⟨4167392740828604981276291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778261827219069987517527 4167392740828604981276291)
          ·
            refine ⟨6251089111242907471914437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167392740828604981276291 6251089111242907471914437)
            ·
              refine ⟨1172079208358045150983957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6251089111242907471914437 1172079208358045150983957)
              ·
                refine ⟨54941212891783366452373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1172079208358045150983957 54941212891783366452373)
                ·
                  rfl

theorem cell20_361117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_361117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361117 prefixEnd_361117 := by exact prefixLift 361117
  have htrace : WordTrace (prefixWord ++ tailWord_361117) baseStart_361117 baseEnd_361117 := by
    simpa [prefixWord, tailWord_361117, baseEnd_361117] using wordTrace_append hprefix tailTrace_361117
  have hstable : (prefixWord ++ tailWord_361117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361117).length < 2 ^ (prefixWord ++ tailWord_361117).sum := by decide
  have hdescent : baseEnd_361117 < baseStart_361117 := by decide
  rcases family_descends (prefixWord ++ tailWord_361117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361134 : List Nat := [4, 1, 4, 1, 1, 9]
def baseStart_361134 : Nat := 118140960795 + 361134 * 2 ^ 59
def prefixEnd_361134 : Nat := 4983230072969 + 3 ^ 40 * 361134 * 2
def baseEnd_361134 : Nat := 6104866590317540584829

theorem tailTrace_361134 : CollatzResearch.WordTrace tailWord_361134 prefixEnd_361134 6104866590317540584829 := by
  unfold tailWord_361134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646454884210083702746307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8781092715787113081313637 1646454884210083702746307)
  ·
    refine ⟨2469682326315125554119461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646454884210083702746307 2469682326315125554119461)
    ·
      refine ⟨463065436184086041397399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2469682326315125554119461 463065436184086041397399)
      ·
        refine ⟨694598154276129062096099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463065436184086041397399 694598154276129062096099)
        ·
          refine ⟨1041897231414193593144149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694598154276129062096099 1041897231414193593144149)
          ·
            refine ⟨6104866590317540584829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1041897231414193593144149 6104866590317540584829)
            ·
              rfl

theorem cell20_361134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 9].length) (baseStart_361134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361134 prefixEnd_361134 := by exact prefixLift 361134
  have htrace : WordTrace (prefixWord ++ tailWord_361134) baseStart_361134 baseEnd_361134 := by
    simpa [prefixWord, tailWord_361134, baseEnd_361134] using wordTrace_append hprefix tailTrace_361134
  have hstable : (prefixWord ++ tailWord_361134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361134).length < 2 ^ (prefixWord ++ tailWord_361134).sum := by decide
  have hdescent : baseEnd_361134 < baseStart_361134 := by decide
  rcases family_descends (prefixWord ++ tailWord_361134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361137 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_361137 : Nat := 118140960795 + 361137 * 2 ^ 59
def prefixEnd_361137 : Nat := 4983230072969 + 3 ^ 40 * 361137 * 2
def baseEnd_361137 : Nat := 164832767220318918690371

theorem tailTrace_361137 : CollatzResearch.WordTrace tailWord_361137 prefixEnd_361137 164832767220318918690371 := by
  unfold tailWord_361137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13171748492669801134329665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8781165661779867422886443 13171748492669801134329665)
  ·
    refine ⟨9878811369502350850747249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13171748492669801134329665 9878811369502350850747249)
    ·
      refine ⟨7409108527126763138060437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9878811369502350850747249 7409108527126763138060437)
      ·
        refine ⟨347301962209067022096583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7409108527126763138060437 347301962209067022096583)
        ·
          refine ⟨520952943313600533144875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347301962209067022096583 520952943313600533144875)
          ·
            refine ⟨781429414970400799717313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520952943313600533144875 781429414970400799717313)
            ·
              refine ⟨586072061227800599787985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781429414970400799717313 586072061227800599787985)
              ·
                refine ⟨439554045920850449840989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586072061227800599787985 439554045920850449840989)
                ·
                  refine ⟨164832767220318918690371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439554045920850449840989 164832767220318918690371)
                  ·
                    rfl

theorem cell20_361137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_361137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361137 prefixEnd_361137 := by exact prefixLift 361137
  have htrace : WordTrace (prefixWord ++ tailWord_361137) baseStart_361137 baseEnd_361137 := by
    simpa [prefixWord, tailWord_361137, baseEnd_361137] using wordTrace_append hprefix tailTrace_361137
  have hstable : (prefixWord ++ tailWord_361137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361137).length < 2 ^ (prefixWord ++ tailWord_361137).sum := by decide
  have hdescent : baseEnd_361137 < baseStart_361137 := by decide
  rcases family_descends (prefixWord ++ tailWord_361137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361148 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_361148 : Nat := 118140960795 + 361148 * 2 ^ 59
def prefixEnd_361148 : Nat := 4983230072969 + 3 ^ 40 * 361148 * 2
def baseEnd_361148 : Nat := 164837787920051769323659

theorem tailTrace_361148 : CollatzResearch.WordTrace tailWord_361148 prefixEnd_361148 164837787920051769323659 := by
  unfold tailWord_361148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586074847814975006490049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8781433130419966675320065 6586074847814975006490049)
  ·
    refine ⟨4939556135861231254867537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6586074847814975006490049 4939556135861231254867537)
    ·
      refine ⟨3704667101895923441150653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4939556135861231254867537 3704667101895923441150653)
      ·
        refine ⟨1389250163210971290431495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3704667101895923441150653 1389250163210971290431495)
        ·
          refine ⟨2083875244816456935647243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389250163210971290431495 2083875244816456935647243)
          ·
            refine ⟨3125812867224685403470865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083875244816456935647243 3125812867224685403470865)
            ·
              refine ⟨2344359650418514052603149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125812867224685403470865 2344359650418514052603149)
              ·
                refine ⟨879134868906942769726181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344359650418514052603149 879134868906942769726181)
                ·
                  refine ⟨164837787920051769323659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 879134868906942769726181 164837787920051769323659)
                  ·
                    rfl

theorem cell20_361148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_361148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361148 prefixEnd_361148 := by exact prefixLift 361148
  have htrace : WordTrace (prefixWord ++ tailWord_361148) baseStart_361148 baseEnd_361148 := by
    simpa [prefixWord, tailWord_361148, baseEnd_361148] using wordTrace_append hprefix tailTrace_361148
  have hstable : (prefixWord ++ tailWord_361148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361148).length < 2 ^ (prefixWord ++ tailWord_361148).sum := by decide
  have hdescent : baseEnd_361148 < baseStart_361148 := by decide
  rcases family_descends (prefixWord ++ tailWord_361148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361200 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_361200 : Nat := 118140960795 + 361200 * 2 ^ 59
def prefixEnd_361200 : Nat := 4983230072969 + 3 ^ 40 * 361200 * 2
def baseEnd_361200 : Nat := 164861522136970699590113

theorem tailTrace_361200 : CollatzResearch.WordTrace tailWord_361200 prefixEnd_361200 164861522136970699590113 := by
  unfold tailWord_361200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587023145720781446936527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8782697527627708595915369 6587023145720781446936527)
  ·
    refine ⟨9880534718581172170404791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587023145720781446936527 9880534718581172170404791)
    ·
      refine ⟨14820802077871758255607187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9880534718581172170404791 14820802077871758255607187)
      ·
        refine ⟨22231203116807637383410781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14820802077871758255607187 22231203116807637383410781)
        ·
          refine ⟨8336701168802864018779043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22231203116807637383410781 8336701168802864018779043)
          ·
            refine ⟨12505051753204296028168565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336701168802864018779043 12505051753204296028168565)
            ·
              refine ⟨1172348601862902752640803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12505051753204296028168565 1172348601862902752640803)
              ·
                refine ⟨1758522902794354128961205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172348601862902752640803 1758522902794354128961205)
                ·
                  refine ⟨164861522136970699590113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758522902794354128961205 164861522136970699590113)
                  ·
                    rfl

theorem cell20_361200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_361200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361200 prefixEnd_361200 := by exact prefixLift 361200
  have htrace : WordTrace (prefixWord ++ tailWord_361200) baseStart_361200 baseEnd_361200 := by
    simpa [prefixWord, tailWord_361200, baseEnd_361200] using wordTrace_append hprefix tailTrace_361200
  have hstable : (prefixWord ++ tailWord_361200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361200).length < 2 ^ (prefixWord ++ tailWord_361200).sum := by decide
  have hdescent : baseEnd_361200 < baseStart_361200 := by decide
  rcases family_descends (prefixWord ++ tailWord_361200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361224 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_361224 : Nat := 118140960795 + 361224 * 2 ^ 59
def prefixEnd_361224 : Nat := 4983230072969 + 3 ^ 40 * 361224 * 2
def baseEnd_361224 : Nat := 164872476390933282790015

theorem tailTrace_361224 : CollatzResearch.WordTrace tailWord_361224 prefixEnd_361224 164872476390933282790015 := by
  unfold tailWord_361224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587460821677307496373363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8783281095569743328497817 6587460821677307496373363)
  ·
    refine ⟨9881191232515961244560045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587460821677307496373363 9881191232515961244560045)
    ·
      refine ⟨3705446712193485466710017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9881191232515961244560045 3705446712193485466710017)
      ·
        refine ⟨2779085034145114100032513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3705446712193485466710017 2779085034145114100032513)
        ·
          refine ⟨2084313775608835575024385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779085034145114100032513 2084313775608835575024385)
          ·
            refine ⟨1563235331706626681268289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084313775608835575024385 1563235331706626681268289)
            ·
              refine ⟨1172426498779970010951217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563235331706626681268289 1172426498779970010951217)
              ·
                refine ⟨879319874084977508213413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172426498779970010951217 879319874084977508213413)
                ·
                  refine ⟨164872476390933282790015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 879319874084977508213413 164872476390933282790015)
                  ·
                    rfl

theorem cell20_361224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_361224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361224 prefixEnd_361224 := by exact prefixLift 361224
  have htrace : WordTrace (prefixWord ++ tailWord_361224) baseStart_361224 baseEnd_361224 := by
    simpa [prefixWord, tailWord_361224, baseEnd_361224] using wordTrace_append hprefix tailTrace_361224
  have hstable : (prefixWord ++ tailWord_361224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361224).length < 2 ^ (prefixWord ++ tailWord_361224).sum := by decide
  have hdescent : baseEnd_361224 < baseStart_361224 := by decide
  rcases family_descends (prefixWord ++ tailWord_361224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361268 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_361268 : Nat := 118140960795 + 361268 * 2 ^ 59
def prefixEnd_361268 : Nat := 4983230072969 + 3 ^ 40 * 361268 * 2
def baseEnd_361268 : Nat := 164892559189864685323169

theorem tailTrace_361268 : CollatzResearch.WordTrace tailWord_361268 prefixEnd_361268 164892559189864685323169 := by
  unfold tailWord_361268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588263227597605253674229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8784350970130140338232305 6588263227597605253674229)
  ·
    refine ⟨617649677587275492531959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6588263227597605253674229 617649677587275492531959)
    ·
      refine ⟨926474516380913238797939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617649677587275492531959 926474516380913238797939)
      ·
        refine ⟨1389711774571369858196909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926474516380913238797939 1389711774571369858196909)
        ·
          refine ⟨521141915464263696823841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389711774571369858196909 521141915464263696823841)
          ·
            refine ⟨390856436598197772617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521141915464263696823841 390856436598197772617881)
            ·
              refine ⟨293142327448648329463411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390856436598197772617881 293142327448648329463411)
              ·
                refine ⟨439713491172972494195117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293142327448648329463411 439713491172972494195117)
                ·
                  refine ⟨164892559189864685323169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439713491172972494195117 164892559189864685323169)
                  ·
                    rfl

theorem cell20_361268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_361268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361268 prefixEnd_361268 := by exact prefixLift 361268
  have htrace : WordTrace (prefixWord ++ tailWord_361268) baseStart_361268 baseEnd_361268 := by
    simpa [prefixWord, tailWord_361268, baseEnd_361268] using wordTrace_append hprefix tailTrace_361268
  have hstable : (prefixWord ++ tailWord_361268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361268).length < 2 ^ (prefixWord ++ tailWord_361268).sum := by decide
  have hdescent : baseEnd_361268 < baseStart_361268 := by decide
  rcases family_descends (prefixWord ++ tailWord_361268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361269 : List Nat := [1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_361269 : Nat := 118140960795 + 361269 * 2 ^ 59
def prefixEnd_361269 : Nat := 4983230072969 + 3 ^ 40 * 361269 * 2
def baseEnd_361269 : Nat := 54964338539037708763277

theorem tailTrace_361269 : CollatzResearch.WordTrace tailWord_361269 prefixEnd_361269 54964338539037708763277 := by
  unfold tailWord_361269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13176562928191587678134861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8784375285461058452089907 13176562928191587678134861)
  ·
    refine ⟨4941211098071845379300573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13176562928191587678134861 4941211098071845379300573)
    ·
      refine ⟨1852954161776942017237715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4941211098071845379300573 1852954161776942017237715)
      ·
        refine ⟨2779431242665413025856573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852954161776942017237715 2779431242665413025856573)
        ·
          refine ⟨1042286715999529884696215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2779431242665413025856573 1042286715999529884696215)
          ·
            refine ⟨1563430073999294827044323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042286715999529884696215 1563430073999294827044323)
            ·
              refine ⟨2345145110998942240566485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563430073999294827044323 2345145110998942240566485)
              ·
                refine ⟨54964338539037708763277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2345145110998942240566485 54964338539037708763277)
                ·
                  rfl

theorem cell20_361269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_361269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361269 prefixEnd_361269 := by exact prefixLift 361269
  have htrace : WordTrace (prefixWord ++ tailWord_361269) baseStart_361269 baseEnd_361269 := by
    simpa [prefixWord, tailWord_361269, baseEnd_361269] using wordTrace_append hprefix tailTrace_361269
  have hstable : (prefixWord ++ tailWord_361269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361269).length < 2 ^ (prefixWord ++ tailWord_361269).sum := by decide
  have hdescent : baseEnd_361269 < baseStart_361269 := by decide
  rcases family_descends (prefixWord ++ tailWord_361269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361283 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_361283 : Nat := 118140960795 + 361283 * 2 ^ 59
def prefixEnd_361283 : Nat := 4983230072969 + 3 ^ 40 * 361283 * 2
def baseEnd_361283 : Nat := 164899405598591299823107

theorem tailTrace_361283 : CollatzResearch.WordTrace tailWord_361283 prefixEnd_361283 164899405598591299823107 := by
  unfold tailWord_361283
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177073550140868069144503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8784715700093912046096335 13177073550140868069144503)
  ·
    refine ⟨19765610325211302103716755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177073550140868069144503 19765610325211302103716755)
    ·
      refine ⟨29648415487816953155575133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19765610325211302103716755 29648415487816953155575133)
      ·
        refine ⟨11118155807931357433340675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29648415487816953155575133 11118155807931357433340675)
        ·
          refine ⟨16677233711897036150011013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118155807931357433340675 16677233711897036150011013)
          ·
            refine ⟨3126981320980694278127065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16677233711897036150011013 3126981320980694278127065)
            ·
              refine ⟨2345235990735520708595299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126981320980694278127065 2345235990735520708595299)
              ·
                refine ⟨3517853986103281062892949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345235990735520708595299 3517853986103281062892949)
                ·
                  refine ⟨164899405598591299823107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3517853986103281062892949 164899405598591299823107)
                  ·
                    rfl

theorem cell20_361283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_361283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361283 prefixEnd_361283 := by exact prefixLift 361283
  have htrace : WordTrace (prefixWord ++ tailWord_361283) baseStart_361283 baseEnd_361283 := by
    simpa [prefixWord, tailWord_361283, baseEnd_361283] using wordTrace_append hprefix tailTrace_361283
  have hstable : (prefixWord ++ tailWord_361283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361283).length < 2 ^ (prefixWord ++ tailWord_361283).sum := by decide
  have hdescent : baseEnd_361283 < baseStart_361283 := by decide
  rcases family_descends (prefixWord ++ tailWord_361283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361362 : List Nat := [3, 2, 3, 2, 2, 1, 7]
def baseStart_361362 : Nat := 118140960795 + 361362 * 2 ^ 59
def prefixEnd_361362 : Nat := 4983230072969 + 3 ^ 40 * 361362 * 2
def baseEnd_361362 : Nat := 18326162594579792909939

theorem tailTrace_361362 : CollatzResearch.WordTrace tailWord_361362 prefixEnd_361362 18326162594579792909939 := by
  unfold tailWord_361362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294988729213666140317585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8786636611236443040846893 3294988729213666140317585)
  ·
    refine ⟨2471241546910249605238189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3294988729213666140317585 2471241546910249605238189)
    ·
      refine ⟨926715580091343601964321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2471241546910249605238189 926715580091343601964321)
      ·
        refine ⟨695036685068507701473241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926715580091343601964321 695036685068507701473241)
        ·
          refine ⟨521277513801380776104931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695036685068507701473241 521277513801380776104931)
          ·
            refine ⟨781916270702071164157397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521277513801380776104931 781916270702071164157397)
            ·
              refine ⟨18326162594579792909939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 781916270702071164157397 18326162594579792909939)
              ·
                rfl

theorem cell20_361362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_361362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361362 prefixEnd_361362 := by exact prefixLift 361362
  have htrace : WordTrace (prefixWord ++ tailWord_361362) baseStart_361362 baseEnd_361362 := by
    simpa [prefixWord, tailWord_361362, baseEnd_361362] using wordTrace_append hprefix tailTrace_361362
  have hstable : (prefixWord ++ tailWord_361362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361362).length < 2 ^ (prefixWord ++ tailWord_361362).sum := by decide
  have hdescent : baseEnd_361362 < baseStart_361362 := by decide
  rcases family_descends (prefixWord ++ tailWord_361362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361396 : List Nat := [2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_361396 : Nat := 118140960795 + 361396 * 2 ^ 59
def prefixEnd_361396 : Nat := 4983230072969 + 3 ^ 40 * 361396 * 2
def baseEnd_361396 : Nat := 54983660625888376351993

theorem tailTrace_361396 : CollatzResearch.WordTrace tailWord_361396 prefixEnd_361396 54983660625888376351993 := by
  unfold tailWord_361396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590597499365744184004021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8787463332487658912005361 6590597499365744184004021)
  ·
    refine ⟨617868515565538517250377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6590597499365744184004021 617868515565538517250377)
    ·
      refine ⟨463401386674153887937783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 617868515565538517250377 463401386674153887937783)
      ·
        refine ⟨695102080011230831906675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463401386674153887937783 695102080011230831906675)
        ·
          refine ⟨1042653120016846247860013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695102080011230831906675 1042653120016846247860013)
          ·
            refine ⟨390994920006317342947505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042653120016846247860013 390994920006317342947505)
            ·
              refine ⟨293246190004738007210629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390994920006317342947505 293246190004738007210629)
              ·
                refine ⟨54983660625888376351993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293246190004738007210629 54983660625888376351993)
                ·
                  rfl

theorem cell20_361396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_361396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361396 prefixEnd_361396 := by exact prefixLift 361396
  have htrace : WordTrace (prefixWord ++ tailWord_361396) baseStart_361396 baseEnd_361396 := by
    simpa [prefixWord, tailWord_361396, baseEnd_361396] using wordTrace_append hprefix tailTrace_361396
  have hstable : (prefixWord ++ tailWord_361396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361396).length < 2 ^ (prefixWord ++ tailWord_361396).sum := by decide
  have hdescent : baseEnd_361396 < baseStart_361396 := by decide
  rcases family_descends (prefixWord ++ tailWord_361396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361400 : List Nat := [2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_361400 : Nat := 118140960795 + 361400 * 2 ^ 59
def prefixEnd_361400 : Nat := 4983230072969 + 3 ^ 40 * 361400 * 2
def baseEnd_361400 : Nat := 54984269195552964307543

theorem tailTrace_361400 : CollatzResearch.WordTrace tailWord_361400 prefixEnd_361400 54984269195552964307543 := by
  unfold tailWord_361400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590670445358498525576827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8787560593811331367435769 6590670445358498525576827)
  ·
    refine ⟨9886005668037747788365241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6590670445358498525576827 9886005668037747788365241)
    ·
      refine ⟨7414504251028310841273931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886005668037747788365241 7414504251028310841273931)
      ·
        refine ⟨11121756376542466261910897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414504251028310841273931 11121756376542466261910897)
        ·
          refine ⟨8341317282406849696433173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11121756376542466261910897 8341317282406849696433173)
          ·
            refine ⟨390999247612821079520305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8341317282406849696433173 390999247612821079520305)
            ·
              refine ⟨293249435709615809640229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390999247612821079520305 293249435709615809640229)
              ·
                refine ⟨54984269195552964307543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293249435709615809640229 54984269195552964307543)
                ·
                  rfl

theorem cell20_361400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_361400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361400 prefixEnd_361400 := by exact prefixLift 361400
  have htrace : WordTrace (prefixWord ++ tailWord_361400) baseStart_361400 baseEnd_361400 := by
    simpa [prefixWord, tailWord_361400, baseEnd_361400] using wordTrace_append hprefix tailTrace_361400
  have hstable : (prefixWord ++ tailWord_361400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361400).length < 2 ^ (prefixWord ++ tailWord_361400).sum := by decide
  have hdescent : baseEnd_361400 < baseStart_361400 := by decide
  rcases family_descends (prefixWord ++ tailWord_361400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361480 : List Nat := [2, 1, 3, 2, 1, 11]
def baseStart_361480 : Nat := 118140960795 + 361480 * 2 ^ 59
def prefixEnd_361480 : Nat := 4983230072969 + 3 ^ 40 * 361480 * 2
def baseEnd_361480 : Nat := 6110715620982747046505

theorem tailTrace_361480 : CollatzResearch.WordTrace tailWord_361480 prefixEnd_361480 6110715620982747046505 := by
  unfold tailWord_361480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592129365213585357032947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8789505820284780476043929 6592129365213585357032947)
  ·
    refine ⟨9888194047820378035549421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592129365213585357032947 9888194047820378035549421)
    ·
      refine ⟨3708072767932641763331033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9888194047820378035549421 3708072767932641763331033)
      ·
        refine ⟨2781054575949481322498275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3708072767932641763331033 2781054575949481322498275)
        ·
          refine ⟨4171581863924221983747413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781054575949481322498275 4171581863924221983747413)
          ·
            refine ⟨6110715620982747046505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4171581863924221983747413 6110715620982747046505)
            ·
              rfl

theorem cell20_361480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 11].length) (baseStart_361480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361480 prefixEnd_361480 := by exact prefixLift 361480
  have htrace : WordTrace (prefixWord ++ tailWord_361480) baseStart_361480 baseEnd_361480 := by
    simpa [prefixWord, tailWord_361480, baseEnd_361480] using wordTrace_append hprefix tailTrace_361480
  have hstable : (prefixWord ++ tailWord_361480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361480).length < 2 ^ (prefixWord ++ tailWord_361480).sum := by decide
  have hdescent : baseEnd_361480 < baseStart_361480 := by decide
  rcases family_descends (prefixWord ++ tailWord_361480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361483 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_361483 : Nat := 118140960795 + 361483 * 2 ^ 59
def prefixEnd_361483 : Nat := 4983230072969 + 3 ^ 40 * 361483 * 2
def baseEnd_361483 : Nat := 164990691048279493155623

theorem tailTrace_361483 : CollatzResearch.WordTrace tailWord_361483 prefixEnd_361483 164990691048279493155623 := by
  unfold tailWord_361483
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184368149416302226425103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8789578766277534817616735 13184368149416302226425103)
  ·
    refine ⟨19776552224124453339637655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13184368149416302226425103 19776552224124453339637655)
    ·
      refine ⟨29664828336186680009456483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19776552224124453339637655 29664828336186680009456483)
      ·
        refine ⟨44497242504280020014184725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29664828336186680009456483 44497242504280020014184725)
        ·
          refine ⟨2085808242388125938164909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44497242504280020014184725 2085808242388125938164909)
          ·
            refine ⟨782178090895547226811841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2085808242388125938164909 782178090895547226811841)
            ·
              refine ⟨586633568171660420108881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782178090895547226811841 586633568171660420108881)
              ·
                refine ⟨439975176128745315081661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586633568171660420108881 439975176128745315081661)
                ·
                  refine ⟨164990691048279493155623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439975176128745315081661 164990691048279493155623)
                  ·
                    rfl

theorem cell20_361483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_361483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361483 prefixEnd_361483 := by exact prefixLift 361483
  have htrace : WordTrace (prefixWord ++ tailWord_361483) baseStart_361483 baseEnd_361483 := by
    simpa [prefixWord, tailWord_361483, baseEnd_361483] using wordTrace_append hprefix tailTrace_361483
  have hstable : (prefixWord ++ tailWord_361483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361483).length < 2 ^ (prefixWord ++ tailWord_361483).sum := by decide
  have hdescent : baseEnd_361483 < baseStart_361483 := by decide
  rcases family_descends (prefixWord ++ tailWord_361483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361486 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_361486 : Nat := 118140960795 + 361486 * 2 ^ 59
def prefixEnd_361486 : Nat := 4983230072969 + 3 ^ 40 * 361486 * 2
def baseEnd_361486 : Nat := 164992060330024816055611

theorem tailTrace_361486 : CollatzResearch.WordTrace tailWord_361486 prefixEnd_361486 164992060330024816055611 := by
  unfold tailWord_361486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648059696050679217348039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8789651712270289159189541 1648059696050679217348039)
  ·
    refine ⟨2472089544076018826022059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648059696050679217348039 2472089544076018826022059)
    ·
      refine ⟨3708134316114028239033089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472089544076018826022059 3708134316114028239033089)
      ·
        refine ⟨2781100737085521179274817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3708134316114028239033089 2781100737085521179274817)
        ·
          refine ⟨2085825552814140884456113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781100737085521179274817 2085825552814140884456113)
          ·
            refine ⟨1564369164610605663342085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085825552814140884456113 1564369164610605663342085)
            ·
              refine ⟨293319218364488561876641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564369164610605663342085 293319218364488561876641)
              ·
                refine ⟨219989413773366421407481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293319218364488561876641 219989413773366421407481)
                ·
                  refine ⟨164992060330024816055611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219989413773366421407481 164992060330024816055611)
                  ·
                    rfl

theorem cell20_361486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_361486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361486 prefixEnd_361486 := by exact prefixLift 361486
  have htrace : WordTrace (prefixWord ++ tailWord_361486) baseStart_361486 baseEnd_361486 := by
    simpa [prefixWord, tailWord_361486, baseEnd_361486] using wordTrace_append hprefix tailTrace_361486
  have hstable : (prefixWord ++ tailWord_361486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361486).length < 2 ^ (prefixWord ++ tailWord_361486).sum := by decide
  have hdescent : baseEnd_361486 < baseStart_361486 := by decide
  rcases family_descends (prefixWord ++ tailWord_361486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361524 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_361524 : Nat := 118140960795 + 361524 * 2 ^ 59
def prefixEnd_361524 : Nat := 4983230072969 + 3 ^ 40 * 361524 * 2
def baseEnd_361524 : Nat := 165009404565465572788789

theorem tailTrace_361524 : CollatzResearch.WordTrace tailWord_361524 prefixEnd_361524 165009404565465572788789 := by
  unfold tailWord_361524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592931771133883114333813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8790575694845177485778417 6592931771133883114333813)
  ·
    refine ⟨618087353543801541968795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6592931771133883114333813 618087353543801541968795)
    ·
      refine ⟨927131030315702312953193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618087353543801541968795 927131030315702312953193)
      ·
        refine ⟨695348272736776734714895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927131030315702312953193 695348272736776734714895)
        ·
          refine ⟨1043022409105165102072343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695348272736776734714895 1043022409105165102072343)
          ·
            refine ⟨1564533613657747653108515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043022409105165102072343 1564533613657747653108515)
            ·
              refine ⟨2346800420486621479662773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564533613657747653108515 2346800420486621479662773)
              ·
                refine ⟨220012539420620763718385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2346800420486621479662773 220012539420620763718385)
                ·
                  refine ⟨165009404565465572788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220012539420620763718385 165009404565465572788789)
                  ·
                    rfl

theorem cell20_361524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_361524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361524 prefixEnd_361524 := by exact prefixLift 361524
  have htrace : WordTrace (prefixWord ++ tailWord_361524) baseStart_361524 baseEnd_361524 := by
    simpa [prefixWord, tailWord_361524, baseEnd_361524] using wordTrace_append hprefix tailTrace_361524
  have hstable : (prefixWord ++ tailWord_361524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361524).length < 2 ^ (prefixWord ++ tailWord_361524).sum := by decide
  have hdescent : baseEnd_361524 < baseStart_361524 := by decide
  rcases family_descends (prefixWord ++ tailWord_361524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361604 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_361604 : Nat := 118140960795 + 361604 * 2 ^ 59
def prefixEnd_361604 : Nat := 4983230072969 + 3 ^ 40 * 361604 * 2
def baseEnd_361604 : Nat := 165045918745340850121795

theorem tailTrace_361604 : CollatzResearch.WordTrace tailWord_361604 prefixEnd_361604 165045918745340850121795 := by
  unfold tailWord_361604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594390690988969945789933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8792520921318626594386577 6594390690988969945789933)
  ·
    refine ⟨2472896509120863729671225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6594390690988969945789933 2472896509120863729671225)
    ·
      refine ⟨1854672381840647797253419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472896509120863729671225 1854672381840647797253419)
      ·
        refine ⟨2782008572760971695880129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854672381840647797253419 2782008572760971695880129)
        ·
          refine ⟨2086506429570728771910097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782008572760971695880129 2086506429570728771910097)
          ·
            refine ⟨1564879822178046578932573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086506429570728771910097 1564879822178046578932573)
            ·
              refine ⟨586829933316767467099715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1564879822178046578932573 586829933316767467099715)
              ·
                refine ⟨880244899975151200649573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586829933316767467099715 880244899975151200649573)
                ·
                  refine ⟨165045918745340850121795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880244899975151200649573 165045918745340850121795)
                  ·
                    rfl

theorem cell20_361604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_361604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361604 prefixEnd_361604 := by exact prefixLift 361604
  have htrace : WordTrace (prefixWord ++ tailWord_361604) baseStart_361604 baseEnd_361604 := by
    simpa [prefixWord, tailWord_361604, baseEnd_361604] using wordTrace_append hprefix tailTrace_361604
  have hstable : (prefixWord ++ tailWord_361604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361604).length < 2 ^ (prefixWord ++ tailWord_361604).sum := by decide
  have hdescent : baseEnd_361604 < baseStart_361604 := by decide
  rcases family_descends (prefixWord ++ tailWord_361604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361614 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_361614 : Nat := 118140960795 + 361614 * 2 ^ 59
def prefixEnd_361614 : Nat := 4983230072969 + 3 ^ 40 * 361614 * 2
def baseEnd_361614 : Nat := 165050483017825259788421

theorem tailTrace_361614 : CollatzResearch.WordTrace tailWord_361614 prefixEnd_361614 165050483017825259788421 := by
  unfold tailWord_361614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648643263992713949930487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8792764074627807732962597 1648643263992713949930487)
  ·
    refine ⟨2472964895989070924895731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648643263992713949930487 2472964895989070924895731)
    ·
      refine ⟨3709447343983606387343597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472964895989070924895731 3709447343983606387343597)
      ·
        refine ⟨1391042753993852395253849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3709447343983606387343597 1391042753993852395253849)
        ·
          refine ⟨1043282065495389296440387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391042753993852395253849 1043282065495389296440387)
          ·
            refine ⟨1564923098243083944660581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043282065495389296440387 1564923098243083944660581)
            ·
              refine ⟨293423080920578239623859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564923098243083944660581 293423080920578239623859)
              ·
                refine ⟨440134621380867359435789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293423080920578239623859 440134621380867359435789)
                ·
                  refine ⟨165050483017825259788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440134621380867359435789 165050483017825259788421)
                  ·
                    rfl

theorem cell20_361614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_361614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361614 prefixEnd_361614 := by exact prefixLift 361614
  have htrace : WordTrace (prefixWord ++ tailWord_361614) baseStart_361614 baseEnd_361614 := by
    simpa [prefixWord, tailWord_361614, baseEnd_361614] using wordTrace_append hprefix tailTrace_361614
  have hstable : (prefixWord ++ tailWord_361614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361614).length < 2 ^ (prefixWord ++ tailWord_361614).sum := by decide
  have hdescent : baseEnd_361614 < baseStart_361614 := by decide
  rcases family_descends (prefixWord ++ tailWord_361614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361632 : List Nat := [2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_361632 : Nat := 118140960795 + 361632 * 2 ^ 59
def prefixEnd_361632 : Nat := 4983230072969 + 3 ^ 40 * 361632 * 2
def baseEnd_361632 : Nat := 55019566236099065729449

theorem tailTrace_361632 : CollatzResearch.WordTrace tailWord_361632 prefixEnd_361632 55019566236099065729449 := by
  unfold tailWord_361632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594901312938250336799575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8793201750584333782399433 6594901312938250336799575)
  ·
    refine ⟨9892351969407375505199363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594901312938250336799575 9892351969407375505199363)
    ·
      refine ⟨14838527954111063257799045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9892351969407375505199363 14838527954111063257799045)
      ·
        refine ⟨2782223991395824360837321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14838527954111063257799045 2782223991395824360837321)
        ·
          refine ⟨2086667993546868270627991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782223991395824360837321 2086667993546868270627991)
          ·
            refine ⟨3130001990320302405941987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086667993546868270627991 3130001990320302405941987)
            ·
              refine ⟨4695002985480453608912981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130001990320302405941987 4695002985480453608912981)
              ·
                refine ⟨55019566236099065729449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4695002985480453608912981 55019566236099065729449)
                ·
                  rfl

theorem cell20_361632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_361632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361632 prefixEnd_361632 := by exact prefixLift 361632
  have htrace : WordTrace (prefixWord ++ tailWord_361632) baseStart_361632 baseEnd_361632 := by
    simpa [prefixWord, tailWord_361632, baseEnd_361632] using wordTrace_append hprefix tailTrace_361632
  have hstable : (prefixWord ++ tailWord_361632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361632).length < 2 ^ (prefixWord ++ tailWord_361632).sum := by decide
  have hdescent : baseEnd_361632 < baseStart_361632 := by decide
  rcases family_descends (prefixWord ++ tailWord_361632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361697 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 2]
def baseStart_361697 : Nat := 118140960795 + 361697 * 2 ^ 59
def prefixEnd_361697 : Nat := 4983230072969 + 3 ^ 40 * 361697 * 2
def baseEnd_361697 : Nat := 165088366479445860021415

theorem tailTrace_361697 : CollatzResearch.WordTrace tailWord_361697 prefixEnd_361697 165088366479445860021415 := by
  unfold tailWord_361697
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192173370641016774715345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794782247094011183143563 13192173370641016774715345)
  ·
    refine ⟨9894130027980762581036509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13192173370641016774715345 9894130027980762581036509)
    ·
      refine ⟨3710298760492785967888691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9894130027980762581036509 3710298760492785967888691)
      ·
        refine ⟨5565448140739178951833037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710298760492785967888691 5565448140739178951833037)
        ·
          refine ⟨2087043052777192106937389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5565448140739178951833037 2087043052777192106937389)
          ·
            refine ⟨782641144791447040101521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087043052777192106937389 782641144791447040101521)
            ·
              refine ⟨586980858593585280076141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782641144791447040101521 586980858593585280076141)
              ·
                refine ⟨220117821972594480028553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586980858593585280076141 220117821972594480028553)
                ·
                  refine ⟨165088366479445860021415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220117821972594480028553 165088366479445860021415)
                  ·
                    rfl

theorem cell20_361697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_361697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361697 prefixEnd_361697 := by exact prefixLift 361697
  have htrace : WordTrace (prefixWord ++ tailWord_361697) baseStart_361697 baseEnd_361697 := by
    simpa [prefixWord, tailWord_361697, baseEnd_361697] using wordTrace_append hprefix tailTrace_361697
  have hstable : (prefixWord ++ tailWord_361697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361697).length < 2 ^ (prefixWord ++ tailWord_361697).sum := by decide
  have hdescent : baseEnd_361697 < baseStart_361697 := by decide
  rcases family_descends (prefixWord ++ tailWord_361697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361708 : List Nat := [2, 2, 1, 1, 2, 5, 7]
def baseStart_361708 : Nat := 118140960795 + 361708 * 2 ^ 59
def prefixEnd_361708 : Nat := 4983230072969 + 3 ^ 40 * 361708 * 2
def baseEnd_361708 : Nat := 18343709686575412294967

theorem tailTrace_361708 : CollatzResearch.WordTrace tailWord_361708 prefixEnd_361708 18343709686575412294967 := by
  unfold tailWord_361708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596287286800582826682889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8795049715734110435577185 6596287286800582826682889)
  ·
    refine ⟨4947215465100437120012167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6596287286800582826682889 4947215465100437120012167)
    ·
      refine ⟨7420823197650655680018251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947215465100437120012167 7420823197650655680018251)
      ·
        refine ⟨11131234796475983520027377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420823197650655680018251 11131234796475983520027377)
        ·
          refine ⟨8348426097356987640020533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11131234796475983520027377 8348426097356987640020533)
          ·
            refine ⟨782664946627217591251925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8348426097356987640020533 782664946627217591251925)
            ·
              refine ⟨18343709686575412294967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 782664946627217591251925 18343709686575412294967)
              ·
                rfl

theorem cell20_361708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_361708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361708 prefixEnd_361708 := by exact prefixLift 361708
  have htrace : WordTrace (prefixWord ++ tailWord_361708) baseStart_361708 baseEnd_361708 := by
    simpa [prefixWord, tailWord_361708, baseEnd_361708] using wordTrace_append hprefix tailTrace_361708
  have hstable : (prefixWord ++ tailWord_361708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361708).length < 2 ^ (prefixWord ++ tailWord_361708).sum := by decide
  have hdescent : baseEnd_361708 < baseStart_361708 := by decide
  rcases family_descends (prefixWord ++ tailWord_361708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361739 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_361739 : Nat := 118140960795 + 361739 * 2 ^ 59
def prefixEnd_361739 : Nat := 4983230072969 + 3 ^ 40 * 361739 * 2
def baseEnd_361739 : Nat := 165107536423880380621243

theorem tailTrace_361739 : CollatzResearch.WordTrace tailWord_361739 prefixEnd_361739 165107536423880380621243 := by
  unfold tailWord_361739
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193705236488857947744271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8795803490992571965162847 13193705236488857947744271)
  ·
    refine ⟨19790557854733286921616407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13193705236488857947744271 19790557854733286921616407)
    ·
      refine ⟨29685836782099930382424611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19790557854733286921616407 29685836782099930382424611)
      ·
        refine ⟨44528755173149895573636917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29685836782099930382424611 44528755173149895573636917)
        ·
          refine ⟨4174570797482802710028461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44528755173149895573636917 4174570797482802710028461)
          ·
            refine ⟨1565464049056051016260673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4174570797482802710028461 1565464049056051016260673)
            ·
              refine ⟨1174098036792038262195505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565464049056051016260673 1174098036792038262195505)
              ·
                refine ⟨880573527594028696646629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174098036792038262195505 880573527594028696646629)
                ·
                  refine ⟨165107536423880380621243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880573527594028696646629 165107536423880380621243)
                  ·
                    rfl

theorem cell20_361739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_361739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361739 prefixEnd_361739 := by exact prefixLift 361739
  have htrace : WordTrace (prefixWord ++ tailWord_361739) baseStart_361739 baseEnd_361739 := by
    simpa [prefixWord, tailWord_361739, baseEnd_361739] using wordTrace_append hprefix tailTrace_361739
  have hstable : (prefixWord ++ tailWord_361739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361739).length < 2 ^ (prefixWord ++ tailWord_361739).sum := by decide
  have hdescent : baseEnd_361739 < baseStart_361739 := by decide
  rcases family_descends (prefixWord ++ tailWord_361739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361742 : List Nat := [4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_361742 : Nat := 118140960795 + 361742 * 2 ^ 59
def prefixEnd_361742 : Nat := 4983230072969 + 3 ^ 40 * 361742 * 2
def baseEnd_361742 : Nat := 55036301901875234507077

theorem tailTrace_361742 : CollatzResearch.WordTrace tailWord_361742 prefixEnd_361742 55036301901875234507077 := by
  unfold tailWord_361742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649226831934748682512935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8795876436985326306735653 1649226831934748682512935)
  ·
    refine ⟨2473840247902123023769403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649226831934748682512935 2473840247902123023769403)
    ·
      refine ⟨3710760371853184535654105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473840247902123023769403 3710760371853184535654105)
      ·
        refine ⟨2783070278889888401740579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710760371853184535654105 2783070278889888401740579)
        ·
          refine ⟨4174605418334832602610869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783070278889888401740579 4174605418334832602610869)
          ·
            refine ⟨391369257968890556494769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4174605418334832602610869 391369257968890556494769)
            ·
              refine ⟨293526943476667917371077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391369257968890556494769 293526943476667917371077)
              ·
                refine ⟨55036301901875234507077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293526943476667917371077 55036301901875234507077)
                ·
                  rfl

theorem cell20_361742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_361742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361742 prefixEnd_361742 := by exact prefixLift 361742
  have htrace : WordTrace (prefixWord ++ tailWord_361742) baseStart_361742 baseEnd_361742 := by
    simpa [prefixWord, tailWord_361742, baseEnd_361742] using wordTrace_append hprefix tailTrace_361742
  have hstable : (prefixWord ++ tailWord_361742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361742).length < 2 ^ (prefixWord ++ tailWord_361742).sum := by decide
  have hdescent : baseEnd_361742 < baseStart_361742 := by decide
  rcases family_descends (prefixWord ++ tailWord_361742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361773 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_361773 : Nat := 118140960795 + 361773 * 2 ^ 59
def prefixEnd_361773 : Nat := 4983230072969 + 3 ^ 40 * 361773 * 2
def baseEnd_361773 : Nat := 165123054950327373487771

theorem tailTrace_361773 : CollatzResearch.WordTrace tailWord_361773 prefixEnd_361773 165123054950327373487771 := by
  unfold tailWord_361773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194945318365681754481973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8796630212243787836321315 13194945318365681754481973)
  ·
    refine ⟨1237026123596782664482685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13194945318365681754481973 1237026123596782664482685)
    ·
      refine ⟨463884796348793499181007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1237026123596782664482685 463884796348793499181007)
      ·
        refine ⟨695827194523190248771511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463884796348793499181007 695827194523190248771511)
        ·
          refine ⟨1043740791784785373157267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695827194523190248771511 1043740791784785373157267)
          ·
            refine ⟨1565611187677178059735901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043740791784785373157267 1565611187677178059735901)
            ·
              refine ⟨587104195378941772400963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565611187677178059735901 587104195378941772400963)
              ·
                refine ⟨880656293068412658601445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587104195378941772400963 880656293068412658601445)
                ·
                  refine ⟨165123054950327373487771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880656293068412658601445 165123054950327373487771)
                  ·
                    rfl

theorem cell20_361773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_361773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361773 prefixEnd_361773 := by exact prefixLift 361773
  have htrace : WordTrace (prefixWord ++ tailWord_361773) baseStart_361773 baseEnd_361773 := by
    simpa [prefixWord, tailWord_361773, baseEnd_361773] using wordTrace_append hprefix tailTrace_361773
  have hstable : (prefixWord ++ tailWord_361773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361773).length < 2 ^ (prefixWord ++ tailWord_361773).sum := by decide
  have hdescent : baseEnd_361773 < baseStart_361773 := by decide
  rcases family_descends (prefixWord ++ tailWord_361773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361814 : List Nat := [5, 2, 3, 1, 2, 7]
def baseStart_361814 : Nat := 118140960795 + 361814 * 2 ^ 59
def prefixEnd_361814 : Nat := 4983230072969 + 3 ^ 40 * 361814 * 2
def baseEnd_361814 : Nat := 6116361795093090856331

theorem tailTrace_361814 : CollatzResearch.WordTrace tailWord_361814 prefixEnd_361814 6116361795093090856331 := by
  unfold tailWord_361814
  simp only [CollatzResearch.WordTrace]
  refine ⟨824777544451071609795281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8797627140811430504482997 824777544451071609795281)
  ·
    refine ⟨618583158338303707346461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 824777544451071609795281 618583158338303707346461)
    ·
      refine ⟨231968684376863890254923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 618583158338303707346461 231968684376863890254923)
      ·
        refine ⟨347953026565295835382385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231968684376863890254923 347953026565295835382385)
        ·
          refine ⟨260964769923971876536789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347953026565295835382385 260964769923971876536789)
          ·
            refine ⟨6116361795093090856331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 260964769923971876536789 6116361795093090856331)
            ·
              rfl

theorem cell20_361814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 7].length) (baseStart_361814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361814 prefixEnd_361814 := by exact prefixLift 361814
  have htrace : WordTrace (prefixWord ++ tailWord_361814) baseStart_361814 baseEnd_361814 := by
    simpa [prefixWord, tailWord_361814, baseEnd_361814] using wordTrace_append hprefix tailTrace_361814
  have hstable : (prefixWord ++ tailWord_361814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361814).length < 2 ^ (prefixWord ++ tailWord_361814).sum := by decide
  have hdescent : baseEnd_361814 < baseStart_361814 := by decide
  rcases family_descends (prefixWord ++ tailWord_361814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361828 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_361828 : Nat := 118140960795 + 361828 * 2 ^ 59
def prefixEnd_361828 : Nat := 4983230072969 + 3 ^ 40 * 361828 * 2
def baseEnd_361828 : Nat := 165148158448991626654213

theorem tailTrace_361828 : CollatzResearch.WordTrace tailWord_361828 prefixEnd_361828 165148158448991626654213 := by
  unfold tailWord_361828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598475666583213073867069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8797967555444284098489425 6598475666583213073867069)
  ·
    refine ⟨2474428374968704902700151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6598475666583213073867069 2474428374968704902700151)
    ·
      refine ⟨3711642562453057354050227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474428374968704902700151 3711642562453057354050227)
      ·
        refine ⟨5567463843679586031075341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711642562453057354050227 5567463843679586031075341)
        ·
          refine ⟨2087798941379844761653253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5567463843679586031075341 2087798941379844761653253)
          ·
            refine ⟨391462301508720892809985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2087798941379844761653253 391462301508720892809985)
            ·
              refine ⟨293596726131540669607489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391462301508720892809985 293596726131540669607489)
              ·
                refine ⟨220197544598655502205617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293596726131540669607489 220197544598655502205617)
                ·
                  refine ⟨165148158448991626654213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220197544598655502205617 165148158448991626654213)
                  ·
                    rfl

theorem cell20_361828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_361828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361828 prefixEnd_361828 := by exact prefixLift 361828
  have htrace : WordTrace (prefixWord ++ tailWord_361828) baseStart_361828 baseEnd_361828 := by
    simpa [prefixWord, tailWord_361828, baseEnd_361828] using wordTrace_append hprefix tailTrace_361828
  have hstable : (prefixWord ++ tailWord_361828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361828).length < 2 ^ (prefixWord ++ tailWord_361828).sum := by decide
  have hdescent : baseEnd_361828 < baseStart_361828 := by decide
  rcases family_descends (prefixWord ++ tailWord_361828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361853 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_361853 : Nat := 118140960795 + 361853 * 2 ^ 59
def prefixEnd_361853 : Nat := 4983230072969 + 3 ^ 40 * 361853 * 2
def baseEnd_361853 : Nat := 165159569130202650820777

theorem tailTrace_361853 : CollatzResearch.WordTrace tailWord_361853 prefixEnd_361853 165159569130202650820777 := by
  unfold tailWord_361853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197863158075855417394213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8798575438717236944929475 13197863158075855417394213)
  ·
    refine ⟨2474599342139222890761415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13197863158075855417394213 2474599342139222890761415)
    ·
      refine ⟨3711899013208834336142123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474599342139222890761415 3711899013208834336142123)
      ·
        refine ⟨5567848519813251504213185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711899013208834336142123 5567848519813251504213185)
        ·
          refine ⟨4175886389859938628159889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5567848519813251504213185 4175886389859938628159889)
          ·
            refine ⟨3131914792394953971119917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175886389859938628159889 3131914792394953971119917)
            ·
              refine ⟨1174468047148107739169969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3131914792394953971119917 1174468047148107739169969)
              ·
                refine ⟨880851035361080804377477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174468047148107739169969 880851035361080804377477)
                ·
                  refine ⟨165159569130202650820777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880851035361080804377477 165159569130202650820777)
                  ·
                    rfl

theorem cell20_361853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_361853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361853 prefixEnd_361853 := by exact prefixLift 361853
  have htrace : WordTrace (prefixWord ++ tailWord_361853) baseStart_361853 baseEnd_361853 := by
    simpa [prefixWord, tailWord_361853, baseEnd_361853] using wordTrace_append hprefix tailTrace_361853
  have hstable : (prefixWord ++ tailWord_361853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361853).length < 2 ^ (prefixWord ++ tailWord_361853).sum := by decide
  have hdescent : baseEnd_361853 < baseStart_361853 := by decide
  rcases family_descends (prefixWord ++ tailWord_361853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361867 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_361867 : Nat := 118140960795 + 361867 * 2 ^ 59
def prefixEnd_361867 : Nat := 4983230072969 + 3 ^ 40 * 361867 * 2
def baseEnd_361867 : Nat := 165165959111680824354053

theorem tailTrace_361867 : CollatzResearch.WordTrace tailWord_361867 prefixEnd_361867 165165959111680824354053 := by
  unfold tailWord_361867
  simp only [CollatzResearch.WordTrace]
  refine ⟨13198373780025135808403855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8798915853350090538935903 13198373780025135808403855)
  ·
    refine ⟨19797560670037703712605783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13198373780025135808403855 19797560670037703712605783)
    ·
      refine ⟨29696341005056555568908675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19797560670037703712605783 29696341005056555568908675)
      ·
        refine ⟨44544511507584833353363013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29696341005056555568908675 44544511507584833353363013)
        ·
          refine ⟨8352095907672156253755565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44544511507584833353363013 8352095907672156253755565)
          ·
            refine ⟨3132035965377058595158337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8352095907672156253755565 3132035965377058595158337)
            ·
              refine ⟨2349026974032793946368753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132035965377058595158337 2349026974032793946368753)
              ·
                refine ⟨1761770230524595459776565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349026974032793946368753 1761770230524595459776565)
                ·
                  refine ⟨165165959111680824354053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761770230524595459776565 165165959111680824354053)
                  ·
                    rfl

theorem cell20_361867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_361867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361867 prefixEnd_361867 := by exact prefixLift 361867
  have htrace : WordTrace (prefixWord ++ tailWord_361867) baseStart_361867 baseEnd_361867 := by
    simpa [prefixWord, tailWord_361867, baseEnd_361867] using wordTrace_append hprefix tailTrace_361867
  have hstable : (prefixWord ++ tailWord_361867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361867).length < 2 ^ (prefixWord ++ tailWord_361867).sum := by decide
  have hdescent : baseEnd_361867 < baseStart_361867 := by decide
  rcases family_descends (prefixWord ++ tailWord_361867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361880 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_361880 : Nat := 118140960795 + 361880 * 2 ^ 59
def prefixEnd_361880 : Nat := 4983230072969 + 3 ^ 40 * 361880 * 2
def baseEnd_361880 : Nat := 165171892665910556920667

theorem tailTrace_361880 : CollatzResearch.WordTrace tailWord_361880 prefixEnd_361880 165171892665910556920667 := by
  unfold tailWord_361880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599423964489019514313547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8799231952652026019084729 6599423964489019514313547)
  ·
    refine ⟨9899135946733529271470321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6599423964489019514313547 9899135946733529271470321)
    ·
      refine ⟨7424351960050146953602741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9899135946733529271470321 7424351960050146953602741)
      ·
        refine ⟨696032996254701276900257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7424351960050146953602741 696032996254701276900257)
        ·
          refine ⟨522024747191025957675193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696032996254701276900257 522024747191025957675193)
          ·
            refine ⟨391518560393269468256395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522024747191025957675193 391518560393269468256395)
            ·
              refine ⟨587277840589904202384593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391518560393269468256395 587277840589904202384593)
              ·
                refine ⟨440458380442428151788445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587277840589904202384593 440458380442428151788445)
                ·
                  refine ⟨165171892665910556920667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440458380442428151788445 165171892665910556920667)
                  ·
                    rfl

theorem cell20_361880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_361880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361880 prefixEnd_361880 := by exact prefixLift 361880
  have htrace : WordTrace (prefixWord ++ tailWord_361880) baseStart_361880 baseEnd_361880 := by
    simpa [prefixWord, tailWord_361880, baseEnd_361880] using wordTrace_append hprefix tailTrace_361880
  have hstable : (prefixWord ++ tailWord_361880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361880).length < 2 ^ (prefixWord ++ tailWord_361880).sum := by decide
  have hdescent : baseEnd_361880 < baseStart_361880 := by decide
  rcases family_descends (prefixWord ++ tailWord_361880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361891 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_361891 : Nat := 118140960795 + 361891 * 2 ^ 59
def prefixEnd_361891 : Nat := 4983230072969 + 3 ^ 40 * 361891 * 2
def baseEnd_361891 : Nat := 165176913365643407553955

theorem tailTrace_361891 : CollatzResearch.WordTrace tailWord_361891 prefixEnd_361891 165176913365643407553955 := by
  unfold tailWord_361891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199249131938187907277527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8799499421292125271518351 13199249131938187907277527)
  ·
    refine ⟨19798873697907281860916291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13199249131938187907277527 19798873697907281860916291)
    ·
      refine ⟨29698310546860922791374437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19798873697907281860916291 29698310546860922791374437)
      ·
        refine ⟨5568433227536423023382707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29698310546860922791374437 5568433227536423023382707)
        ·
          refine ⟨8352649841304634535074061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568433227536423023382707 8352649841304634535074061)
          ·
            refine ⟨3132243690489237950652773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8352649841304634535074061 3132243690489237950652773)
            ·
              refine ⟨587295691966732115747395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3132243690489237950652773 587295691966732115747395)
              ·
                refine ⟨880943537950098173621093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587295691966732115747395 880943537950098173621093)
                ·
                  refine ⟨165176913365643407553955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880943537950098173621093 165176913365643407553955)
                  ·
                    rfl

theorem cell20_361891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_361891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361891 prefixEnd_361891 := by exact prefixLift 361891
  have htrace : WordTrace (prefixWord ++ tailWord_361891) baseStart_361891 baseEnd_361891 := by
    simpa [prefixWord, tailWord_361891, baseEnd_361891] using wordTrace_append hprefix tailTrace_361891
  have hstable : (prefixWord ++ tailWord_361891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361891).length < 2 ^ (prefixWord ++ tailWord_361891).sum := by decide
  have hdescent : baseEnd_361891 < baseStart_361891 := by decide
  rcases family_descends (prefixWord ++ tailWord_361891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361946 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_361946 : Nat := 118140960795 + 361946 * 2 ^ 59
def prefixEnd_361946 : Nat := 4983230072969 + 3 ^ 40 * 361946 * 2
def baseEnd_361946 : Nat := 165202016864307660720397

theorem tailTrace_361946 : CollatzResearch.WordTrace tailWord_361946 prefixEnd_361946 165202016864307660720397 := by
  unfold tailWord_361946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300313786684733075132423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8800836764492621533686461 3300313786684733075132423)
  ·
    refine ⟨4950470680027099612698635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300313786684733075132423 4950470680027099612698635)
    ·
      refine ⟨7425706020040649419047953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950470680027099612698635 7425706020040649419047953)
      ·
        refine ⟨5569279515030487064285965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7425706020040649419047953 5569279515030487064285965)
        ·
          refine ⟨2088479818136432649107237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5569279515030487064285965 2088479818136432649107237)
          ·
            refine ⟨391589965900581121707607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2088479818136432649107237 391589965900581121707607)
            ·
              refine ⟨587384948850871682561411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391589965900581121707607 587384948850871682561411)
              ·
                refine ⟨881077423276307523842117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587384948850871682561411 881077423276307523842117)
                ·
                  refine ⟨165202016864307660720397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881077423276307523842117 165202016864307660720397)
                  ·
                    rfl

theorem cell20_361946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_361946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361946 prefixEnd_361946 := by exact prefixLift 361946
  have htrace : WordTrace (prefixWord ++ tailWord_361946) baseStart_361946 baseEnd_361946 := by
    simpa [prefixWord, tailWord_361946, baseEnd_361946] using wordTrace_append hprefix tailTrace_361946
  have hstable : (prefixWord ++ tailWord_361946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361946).length < 2 ^ (prefixWord ++ tailWord_361946).sum := by decide
  have hdescent : baseEnd_361946 < baseStart_361946 := by decide
  rcases family_descends (prefixWord ++ tailWord_361946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361960 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_361960 : Nat := 118140960795 + 361960 * 2 ^ 59
def prefixEnd_361960 : Nat := 4983230072969 + 3 ^ 40 * 361960 * 2
def baseEnd_361960 : Nat := 165208406845785834253673

theorem tailTrace_361960 : CollatzResearch.WordTrace tailWord_361960 prefixEnd_361960 165208406845785834253673 := by
  unfold tailWord_361960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600882884344106345769667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8801177179125475127692889 6600882884344106345769667)
  ·
    refine ⟨9901324326516159518654501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6600882884344106345769667 9901324326516159518654501)
    ·
      refine ⟨1856498311221779909747719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9901324326516159518654501 1856498311221779909747719)
      ·
        refine ⟨2784747466832669864621579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856498311221779909747719 2784747466832669864621579)
        ·
          refine ⟨4177121200249004796932369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2784747466832669864621579 4177121200249004796932369)
          ·
            refine ⟨3132840900186753597699277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4177121200249004796932369 3132840900186753597699277)
            ·
              refine ⟨1174815337570032599137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132840900186753597699277 1174815337570032599137229)
              ·
                refine ⟨440555751588762224676461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174815337570032599137229 440555751588762224676461)
                ·
                  refine ⟨165208406845785834253673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440555751588762224676461 165208406845785834253673)
                  ·
                    rfl

theorem cell20_361960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_361960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361960 prefixEnd_361960 := by exact prefixLift 361960
  have htrace : WordTrace (prefixWord ++ tailWord_361960) baseStart_361960 baseEnd_361960 := by
    simpa [prefixWord, tailWord_361960, baseEnd_361960] using wordTrace_append hprefix tailTrace_361960
  have hstable : (prefixWord ++ tailWord_361960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361960).length < 2 ^ (prefixWord ++ tailWord_361960).sum := by decide
  have hdescent : baseEnd_361960 < baseStart_361960 := by decide
  rcases family_descends (prefixWord ++ tailWord_361960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361990 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_361990 : Nat := 118140960795 + 361990 * 2 ^ 59
def prefixEnd_361990 : Nat := 4983230072969 + 3 ^ 40 * 361990 * 2
def baseEnd_361990 : Nat := 165222099663239063253551

theorem tailTrace_361990 : CollatzResearch.WordTrace tailWord_361990 prefixEnd_361990 165222099663239063253551 := by
  unfold tailWord_361990
  simp only [CollatzResearch.WordTrace]
  refine ⟨412589373705610244222857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8801906639053018543420949 412589373705610244222857)
  ·
    refine ⟨309442030279207683167143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412589373705610244222857 309442030279207683167143)
    ·
      refine ⟨464163045418811524750715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309442030279207683167143 464163045418811524750715)
      ·
        refine ⟨696244568128217287126073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464163045418811524750715 696244568128217287126073)
        ·
          refine ⟨522183426096162965344555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696244568128217287126073 522183426096162965344555)
          ·
            refine ⟨783275139144244448016833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522183426096162965344555 783275139144244448016833)
            ·
              refine ⟨587456354358183336012625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783275139144244448016833 587456354358183336012625)
              ·
                refine ⟨440592265768637502009469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587456354358183336012625 440592265768637502009469)
                ·
                  refine ⟨165222099663239063253551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440592265768637502009469 165222099663239063253551)
                  ·
                    rfl

theorem cell20_361990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_361990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361990 prefixEnd_361990 := by exact prefixLift 361990
  have htrace : WordTrace (prefixWord ++ tailWord_361990) baseStart_361990 baseEnd_361990 := by
    simpa [prefixWord, tailWord_361990, baseEnd_361990] using wordTrace_append hprefix tailTrace_361990
  have hstable : (prefixWord ++ tailWord_361990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361990).length < 2 ^ (prefixWord ++ tailWord_361990).sum := by decide
  have hdescent : baseEnd_361990 < baseStart_361990 := by decide
  rcases family_descends (prefixWord ++ tailWord_361990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361995 : List Nat := [1, 1, 1, 1, 16]
def baseStart_361995 : Nat := 118140960795 + 361995 * 2 ^ 59
def prefixEnd_361995 : Nat := 4983230072969 + 3 ^ 40 * 361995 * 2
def baseEnd_361995 : Nat := 2039807182709645285023

theorem tailTrace_361995 : CollatzResearch.WordTrace tailWord_361995 prefixEnd_361995 2039807182709645285023 := by
  unfold tailWord_361995
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203042323561413669063439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8802028215707609112708959 13203042323561413669063439)
  ·
    refine ⟨19804563485342120503595159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13203042323561413669063439 19804563485342120503595159)
    ·
      refine ⟨29706845228013180755392739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804563485342120503595159 29706845228013180755392739)
      ·
        refine ⟨44560267842019771133089109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29706845228013180755392739 44560267842019771133089109)
        ·
          refine ⟨2039807182709645285023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 44560267842019771133089109 2039807182709645285023)
          ·
            rfl

theorem cell20_361995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 16].length) (baseStart_361995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361995 prefixEnd_361995 := by exact prefixLift 361995
  have htrace : WordTrace (prefixWord ++ tailWord_361995) baseStart_361995 baseEnd_361995 := by
    simpa [prefixWord, tailWord_361995, baseEnd_361995] using wordTrace_append hprefix tailTrace_361995
  have hstable : (prefixWord ++ tailWord_361995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361995).length < 2 ^ (prefixWord ++ tailWord_361995).sum := by decide
  have hdescent : baseEnd_361995 < baseStart_361995 := by decide
  rcases family_descends (prefixWord ++ tailWord_361995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361997 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 2]
def baseStart_361997 : Nat := 118140960795 + 361997 * 2 ^ 59
def prefixEnd_361997 : Nat := 4983230072969 + 3 ^ 40 * 361997 * 2
def baseEnd_361997 : Nat := 165225294653978150020189

theorem tailTrace_361997 : CollatzResearch.WordTrace tailWord_361997 prefixEnd_361997 165225294653978150020189 := by
  unfold tailWord_361997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203115269554168010636245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8802076846369445340424163 13203115269554168010636245)
  ·
    refine ⟨309448014130175812749287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13203115269554168010636245 309448014130175812749287)
    ·
      refine ⟨464172021195263719123931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309448014130175812749287 464172021195263719123931)
      ·
        refine ⟨696258031792895578685897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464172021195263719123931 696258031792895578685897)
        ·
          refine ⟨522193523844671684014423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696258031792895578685897 522193523844671684014423)
          ·
            refine ⟨783290285767007526021635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522193523844671684014423 783290285767007526021635)
            ·
              refine ⟨1174935428650511289032453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783290285767007526021635 1174935428650511289032453)
              ·
                refine ⟨220300392871970866693585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1174935428650511289032453 220300392871970866693585)
                ·
                  refine ⟨165225294653978150020189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220300392871970866693585 165225294653978150020189)
                  ·
                    rfl

theorem cell20_361997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_361997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_361997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_361997 prefixEnd_361997 := by exact prefixLift 361997
  have htrace : WordTrace (prefixWord ++ tailWord_361997) baseStart_361997 baseEnd_361997 := by
    simpa [prefixWord, tailWord_361997, baseEnd_361997] using wordTrace_append hprefix tailTrace_361997
  have hstable : (prefixWord ++ tailWord_361997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361997).length < 2 ^ (prefixWord ++ tailWord_361997).sum := by decide
  have hdescent : baseEnd_361997 < baseStart_361997 := by decide
  rcases family_descends (prefixWord ++ tailWord_361997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362008 : List Nat := [2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_362008 : Nat := 118140960795 + 362008 * 2 ^ 59
def prefixEnd_362008 : Nat := 4983230072969 + 3 ^ 40 * 362008 * 2
def baseEnd_362008 : Nat := 55076771784570333551159

theorem tailTrace_362008 : CollatzResearch.WordTrace tailWord_362008 prefixEnd_362008 55076771784570333551159 := by
  unfold tailWord_362008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6601758236257158444643339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8802344315009544592857785 6601758236257158444643339)
  ·
    refine ⟨9902637354385737666965009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6601758236257158444643339 9902637354385737666965009)
    ·
      refine ⟨7426978015789303250223757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9902637354385737666965009 7426978015789303250223757)
      ·
        refine ⟨2785116755920988718833909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7426978015789303250223757 2785116755920988718833909)
        ·
          refine ⟨261104695867592692390679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2785116755920988718833909 261104695867592692390679)
          ·
            refine ⟨391657043801389038586019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261104695867592692390679 391657043801389038586019)
            ·
              refine ⟨587485565702083557879029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391657043801389038586019 587485565702083557879029)
              ·
                refine ⟨55076771784570333551159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587485565702083557879029 55076771784570333551159)
                ·
                  rfl

theorem cell20_362008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_362008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362008 prefixEnd_362008 := by exact prefixLift 362008
  have htrace : WordTrace (prefixWord ++ tailWord_362008) baseStart_362008 baseEnd_362008 := by
    simpa [prefixWord, tailWord_362008, baseEnd_362008] using wordTrace_append hprefix tailTrace_362008
  have hstable : (prefixWord ++ tailWord_362008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362008).length < 2 ^ (prefixWord ++ tailWord_362008).sum := by decide
  have hdescent : baseEnd_362008 < baseStart_362008 := by decide
  rcases family_descends (prefixWord ++ tailWord_362008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362060 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_362060 : Nat := 118140960795 + 362060 * 2 ^ 59
def prefixEnd_362060 : Nat := 4983230072969 + 3 ^ 40 * 362060 * 2
def baseEnd_362060 : Nat := 165254049570629930919931

theorem tailTrace_362060 : CollatzResearch.WordTrace tailWord_362060 prefixEnd_362060 165254049570629930919931 := by
  unfold tailWord_362060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602706534162964885089817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8803608712217286513453089 6602706534162964885089817)
  ·
    refine ⟨4952029900622223663817363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6602706534162964885089817 4952029900622223663817363)
    ·
      refine ⟨7428044850933335495726045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4952029900622223663817363 7428044850933335495726045)
      ·
        refine ⟨2785516819100000810897267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7428044850933335495726045 2785516819100000810897267)
        ·
          refine ⟨4178275228650001216345901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785516819100000810897267 4178275228650001216345901)
          ·
            refine ⟨1566853210743750456129713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4178275228650001216345901 1566853210743750456129713)
            ·
              refine ⟨1175139908057812842097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566853210743750456129713 1175139908057812842097285)
              ·
                refine ⟨220338732760839907893241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1175139908057812842097285 220338732760839907893241)
                ·
                  refine ⟨165254049570629930919931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220338732760839907893241 165254049570629930919931)
                  ·
                    rfl

theorem cell20_362060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_362060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362060 prefixEnd_362060 := by exact prefixLift 362060
  have htrace : WordTrace (prefixWord ++ tailWord_362060) baseStart_362060 baseEnd_362060 := by
    simpa [prefixWord, tailWord_362060, baseEnd_362060] using wordTrace_append hprefix tailTrace_362060
  have hstable : (prefixWord ++ tailWord_362060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362060).length < 2 ^ (prefixWord ++ tailWord_362060).sum := by decide
  have hdescent : baseEnd_362060 < baseStart_362060 := by decide
  rcases family_descends (prefixWord ++ tailWord_362060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362094 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_362094 : Nat := 118140960795 + 362094 * 2 ^ 59
def prefixEnd_362094 : Nat := 4983230072969 + 3 ^ 40 * 362094 * 2
def baseEnd_362094 : Nat := 165269568097076923786459

theorem tailTrace_362094 : CollatzResearch.WordTrace tailWord_362094 prefixEnd_362094 165269568097076923786459 := by
  unfold tailWord_362094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650831643775344197114667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8804435433468502384611557 1650831643775344197114667)
  ·
    refine ⟨2476247465663016295672001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1650831643775344197114667 2476247465663016295672001)
    ·
      refine ⟨1857185599247262221754001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476247465663016295672001 1857185599247262221754001)
      ·
        refine ⟨1392889199435446666315501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857185599247262221754001 1392889199435446666315501)
        ·
          refine ⟨522333449788292499868313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1392889199435446666315501 522333449788292499868313)
          ·
            refine ⟨391750087341219374901235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522333449788292499868313 391750087341219374901235)
            ·
              refine ⟨587625131011829062351853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391750087341219374901235 587625131011829062351853)
              ·
                refine ⟨220359424129435898381945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587625131011829062351853 220359424129435898381945)
                ·
                  refine ⟨165269568097076923786459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220359424129435898381945 165269568097076923786459)
                  ·
                    rfl

theorem cell20_362094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_362094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362094 prefixEnd_362094 := by exact prefixLift 362094
  have htrace : WordTrace (prefixWord ++ tailWord_362094) baseStart_362094 baseEnd_362094 := by
    simpa [prefixWord, tailWord_362094, baseEnd_362094] using wordTrace_append hprefix tailTrace_362094
  have hstable : (prefixWord ++ tailWord_362094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362094).length < 2 ^ (prefixWord ++ tailWord_362094).sum := by decide
  have hdescent : baseEnd_362094 < baseStart_362094 := by decide
  rcases family_descends (prefixWord ++ tailWord_362094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362119 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_362119 : Nat := 118140960795 + 362119 * 2 ^ 59
def prefixEnd_362119 : Nat := 4983230072969 + 3 ^ 40 * 362119 * 2
def baseEnd_362119 : Nat := 165280978778287947953023

theorem tailTrace_362119 : CollatzResearch.WordTrace tailWord_362119 prefixEnd_362119 165280978778287947953023 := by
  unfold tailWord_362119
  simp only [CollatzResearch.WordTrace]
  refine ⟨13207564975112182846577411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8805043316741455231051607 13207564975112182846577411)
  ·
    refine ⟨19811347462668274269866117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13207564975112182846577411 19811347462668274269866117)
    ·
      refine ⟨3714627649250301425599897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19811347462668274269866117 3714627649250301425599897)
      ·
        refine ⟨2785970736937726069199923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714627649250301425599897 2785970736937726069199923)
        ·
          refine ⟨4178956105406589103799885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785970736937726069199923 4178956105406589103799885)
          ·
            refine ⟨1567108539527470913924957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4178956105406589103799885 1567108539527470913924957)
            ·
              refine ⟨587665702322801592721859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1567108539527470913924957 587665702322801592721859)
              ·
                refine ⟨881498553484202389082789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587665702322801592721859 881498553484202389082789)
                ·
                  refine ⟨165280978778287947953023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881498553484202389082789 165280978778287947953023)
                  ·
                    rfl

theorem cell20_362119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_362119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362119 prefixEnd_362119 := by exact prefixLift 362119
  have htrace : WordTrace (prefixWord ++ tailWord_362119) baseStart_362119 baseEnd_362119 := by
    simpa [prefixWord, tailWord_362119, baseEnd_362119] using wordTrace_append hprefix tailTrace_362119
  have hstable : (prefixWord ++ tailWord_362119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362119).length < 2 ^ (prefixWord ++ tailWord_362119).sum := by decide
  have hdescent : baseEnd_362119 < baseStart_362119 := by decide
  rcases family_descends (prefixWord ++ tailWord_362119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362126 : List Nat := [4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_362126 : Nat := 118140960795 + 362126 * 2 ^ 59
def prefixEnd_362126 : Nat := 4983230072969 + 3 ^ 40 * 362126 * 2
def baseEnd_362126 : Nat := 55094724589675678239887

theorem tailTrace_362126 : CollatzResearch.WordTrace tailWord_362126 prefixEnd_362126 55094724589675678239887 := by
  unfold tailWord_362126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650977535760852880260279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8805213524057882028054821 1650977535760852880260279)
  ·
    refine ⟨2476466303641279320390419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1650977535760852880260279 2476466303641279320390419)
    ·
      refine ⟨3714699455461918980585629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476466303641279320390419 3714699455461918980585629)
      ·
        refine ⟨1393012295798219617719611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3714699455461918980585629 1393012295798219617719611)
        ·
          refine ⟨2089518443697329426579417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393012295798219617719611 2089518443697329426579417)
          ·
            refine ⟨1567138832772997069934563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089518443697329426579417 1567138832772997069934563)
            ·
              refine ⟨2350708249159495604901845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567138832772997069934563 2350708249159495604901845)
              ·
                refine ⟨55094724589675678239887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2350708249159495604901845 55094724589675678239887)
                ·
                  rfl

theorem cell20_362126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_362126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362126 prefixEnd_362126 := by exact prefixLift 362126
  have htrace : WordTrace (prefixWord ++ tailWord_362126) baseStart_362126 baseEnd_362126 := by
    simpa [prefixWord, tailWord_362126, baseEnd_362126] using wordTrace_append hprefix tailTrace_362126
  have hstable : (prefixWord ++ tailWord_362126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362126).length < 2 ^ (prefixWord ++ tailWord_362126).sum := by decide
  have hdescent : baseEnd_362126 < baseStart_362126 := by decide
  rcases family_descends (prefixWord ++ tailWord_362126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362147 : List Nat := [1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_362147 : Nat := 118140960795 + 362147 * 2 ^ 59
def prefixEnd_362147 : Nat := 4983230072969 + 3 ^ 40 * 362147 * 2
def baseEnd_362147 : Nat := 55097919580414765006525

theorem tailTrace_362147 : CollatzResearch.WordTrace tailWord_362147 prefixEnd_362147 55097919580414765006525 := by
  unfold tailWord_362147
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208586219010743628596695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8805724146007162419064463 13208586219010743628596695)
  ·
    refine ⟨19812879328516115442895043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13208586219010743628596695 19812879328516115442895043)
    ·
      refine ⟨29719318992774173164342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19812879328516115442895043 29719318992774173164342565)
      ·
        refine ⟨5572372311145157468314231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29719318992774173164342565 5572372311145157468314231)
        ·
          refine ⟨8358558466717736202471347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572372311145157468314231 8358558466717736202471347)
          ·
            refine ⟨12537837700076604303707021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8358558466717736202471347 12537837700076604303707021)
            ·
              refine ⟨4701689137528726613890133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12537837700076604303707021 4701689137528726613890133)
              ·
                refine ⟨55097919580414765006525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4701689137528726613890133 55097919580414765006525)
                ·
                  rfl

theorem cell20_362147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_362147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362147 prefixEnd_362147 := by exact prefixLift 362147
  have htrace : WordTrace (prefixWord ++ tailWord_362147) baseStart_362147 baseEnd_362147 := by
    simpa [prefixWord, tailWord_362147, baseEnd_362147] using wordTrace_append hprefix tailTrace_362147
  have hstable : (prefixWord ++ tailWord_362147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362147).length < 2 ^ (prefixWord ++ tailWord_362147).sum := by decide
  have hdescent : baseEnd_362147 < baseStart_362147 := by decide
  rcases family_descends (prefixWord ++ tailWord_362147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362212 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_362212 : Nat := 118140960795 + 362212 * 2 ^ 59
def prefixEnd_362212 : Nat := 4983230072969 + 3 ^ 40 * 362212 * 2
def baseEnd_362212 : Nat := 165323426512392957852643

theorem tailTrace_362212 : CollatzResearch.WordTrace tailWord_362212 prefixEnd_362212 165323426512392957852643 := by
  unfold tailWord_362212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605478481887629864856445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8807304642516839819808593 6605478481887629864856445)
  ·
    refine ⟨2477054430707861199321167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6605478481887629864856445 2477054430707861199321167)
    ·
      refine ⟨3715581646061791798981751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477054430707861199321167 3715581646061791798981751)
      ·
        refine ⟨5573372469092687698472627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715581646061791798981751 5573372469092687698472627)
        ·
          refine ⟨8360058703639031547708941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573372469092687698472627 8360058703639031547708941)
          ·
            refine ⟨3135022013864636830390853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8360058703639031547708941 3135022013864636830390853)
            ·
              refine ⟨587816627599619405698285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3135022013864636830390853 587816627599619405698285)
              ·
                refine ⟨220431235349857277136857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587816627599619405698285 220431235349857277136857)
                ·
                  refine ⟨165323426512392957852643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220431235349857277136857 165323426512392957852643)
                  ·
                    rfl

theorem cell20_362212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_362212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362212 prefixEnd_362212 := by exact prefixLift 362212
  have htrace : WordTrace (prefixWord ++ tailWord_362212) baseStart_362212 baseEnd_362212 := by
    simpa [prefixWord, tailWord_362212, baseEnd_362212] using wordTrace_append hprefix tailTrace_362212
  have hstable : (prefixWord ++ tailWord_362212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362212).length < 2 ^ (prefixWord ++ tailWord_362212).sum := by decide
  have hdescent : baseEnd_362212 < baseStart_362212 := by decide
  rcases family_descends (prefixWord ++ tailWord_362212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362223 : List Nat := [1, 1, 2, 1, 5, 1, 9]
def baseStart_362223 : Nat := 118140960795 + 362223 * 2 ^ 59
def prefixEnd_362223 : Nat := 4983230072969 + 3 ^ 40 * 362223 * 2
def baseEnd_362223 : Nat := 18369827468013978720659

theorem tailTrace_362223 : CollatzResearch.WordTrace tailWord_362223 prefixEnd_362223 18369827468013978720659 := by
  unfold tailWord_362223
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211358166735408608363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8807572111156939072242215 13211358166735408608363323)
  ·
    refine ⟨19817037250103112912544985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211358166735408608363323 19817037250103112912544985)
    ·
      refine ⟨14862777937577334684408739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19817037250103112912544985 14862777937577334684408739)
      ·
        refine ⟨22294166906366002026613109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14862777937577334684408739 22294166906366002026613109)
        ·
          refine ⟨2090078147471812689994979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22294166906366002026613109 2090078147471812689994979)
          ·
            refine ⟨3135117221207719034992469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090078147471812689994979 3135117221207719034992469)
            ·
              refine ⟨18369827468013978720659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3135117221207719034992469 18369827468013978720659)
              ·
                rfl

theorem cell20_362223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_362223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362223 prefixEnd_362223 := by exact prefixLift 362223
  have htrace : WordTrace (prefixWord ++ tailWord_362223) baseStart_362223 baseEnd_362223 := by
    simpa [prefixWord, tailWord_362223, baseEnd_362223] using wordTrace_append hprefix tailTrace_362223
  have hstable : (prefixWord ++ tailWord_362223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362223).length < 2 ^ (prefixWord ++ tailWord_362223).sum := by decide
  have hdescent : baseEnd_362223 < baseStart_362223 := by decide
  rcases family_descends (prefixWord ++ tailWord_362223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362361 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_362361 : Nat := 118140960795 + 362361 * 2 ^ 59
def prefixEnd_362361 : Nat := 4983230072969 + 3 ^ 40 * 362361 * 2
def baseEnd_362361 : Nat := 165391434172410661885367

theorem tailTrace_362361 : CollatzResearch.WordTrace tailWord_362361 prefixEnd_362361 165391434172410661885367 := by
  unfold tailWord_362361
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216391440235458176886937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8810927626823638784591291 13216391440235458176886937)
  ·
    refine ⟨9912293580176593632665203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13216391440235458176886937 9912293580176593632665203)
    ·
      refine ⟨14868440370264890448997805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912293580176593632665203 14868440370264890448997805)
      ·
        refine ⟨5575665138849333918374177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14868440370264890448997805 5575665138849333918374177)
        ·
          refine ⟨4181748854137000438780633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575665138849333918374177 4181748854137000438780633)
          ·
            refine ⟨3136311640602750329085475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181748854137000438780633 3136311640602750329085475)
            ·
              refine ⟨4704467460904125493628213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136311640602750329085475 4704467460904125493628213)
              ·
                refine ⟨441043824459761765027645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4704467460904125493628213 441043824459761765027645)
                ·
                  refine ⟨165391434172410661885367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441043824459761765027645 165391434172410661885367)
                  ·
                    rfl

theorem cell20_362361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_362361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362361 prefixEnd_362361 := by exact prefixLift 362361
  have htrace : WordTrace (prefixWord ++ tailWord_362361) baseStart_362361 baseEnd_362361 := by
    simpa [prefixWord, tailWord_362361, baseEnd_362361] using wordTrace_append hprefix tailTrace_362361
  have hstable : (prefixWord ++ tailWord_362361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362361).length < 2 ^ (prefixWord ++ tailWord_362361).sum := by decide
  have hdescent : baseEnd_362361 < baseStart_362361 := by decide
  rcases family_descends (prefixWord ++ tailWord_362361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362368 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_362368 : Nat := 118140960795 + 362368 * 2 ^ 59
def prefixEnd_362368 : Nat := 4983230072969 + 3 ^ 40 * 362368 * 2
def baseEnd_362368 : Nat := 165394629163149748652005

theorem tailTrace_362368 : CollatzResearch.WordTrace tailWord_362368 prefixEnd_362368 165394629163149748652005 := by
  unfold tailWord_362368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608323375605049186195879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8811097834140065581594505 6608323375605049186195879)
  ·
    refine ⟨9912485063407573779293819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608323375605049186195879 9912485063407573779293819)
    ·
      refine ⟨14868727595111360668940729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912485063407573779293819 14868727595111360668940729)
      ·
        refine ⟨11151545696333520501705547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14868727595111360668940729 11151545696333520501705547)
        ·
          refine ⟨16727318544500280752558321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151545696333520501705547 16727318544500280752558321)
          ·
            refine ⟨12545488908375210564418741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16727318544500280752558321 12545488908375210564418741)
            ·
              refine ⟨1176139585160175990414257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12545488908375210564418741 1176139585160175990414257)
              ·
                refine ⟨882104688870131992810693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176139585160175990414257 882104688870131992810693)
                ·
                  refine ⟨165394629163149748652005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882104688870131992810693 165394629163149748652005)
                  ·
                    rfl

theorem cell20_362368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_362368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362368 prefixEnd_362368 := by exact prefixLift 362368
  have htrace : WordTrace (prefixWord ++ tailWord_362368) baseStart_362368 baseEnd_362368 := by
    simpa [prefixWord, tailWord_362368, baseEnd_362368] using wordTrace_append hprefix tailTrace_362368
  have hstable : (prefixWord ++ tailWord_362368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362368).length < 2 ^ (prefixWord ++ tailWord_362368).sum := by decide
  have hdescent : baseEnd_362368 < baseStart_362368 := by decide
  rcases family_descends (prefixWord ++ tailWord_362368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362385 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 2]
def baseStart_362385 : Nat := 118140960795 + 362385 * 2 ^ 59
def prefixEnd_362385 : Nat := 4983230072969 + 3 ^ 40 * 362385 * 2
def baseEnd_362385 : Nat := 165402388426373245085269

theorem tailTrace_362385 : CollatzResearch.WordTrace tailWord_362385 prefixEnd_362385 165402388426373245085269 := by
  unfold tailWord_362385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217266792148510275760609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8811511194765673517173739 13217266792148510275760609)
  ·
    refine ⟨9912950094111382706820457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13217266792148510275760609 9912950094111382706820457)
    ·
      refine ⟨7434712570583537030115343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9912950094111382706820457 7434712570583537030115343)
      ·
        refine ⟨11152068855875305545173015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434712570583537030115343 11152068855875305545173015)
        ·
          refine ⟨16728103283812958317759523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11152068855875305545173015 16728103283812958317759523)
          ·
            refine ⟨25092154925719437476639285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16728103283812958317759523 25092154925719437476639285)
            ·
              refine ⟨2352389524286197263434933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25092154925719437476639285 2352389524286197263434933)
              ·
                refine ⟨220536517901830993447025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2352389524286197263434933 220536517901830993447025)
                ·
                  refine ⟨165402388426373245085269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220536517901830993447025 165402388426373245085269)
                  ·
                    rfl

theorem cell20_362385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_362385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362385 prefixEnd_362385 := by exact prefixLift 362385
  have htrace : WordTrace (prefixWord ++ tailWord_362385) baseStart_362385 baseEnd_362385 := by
    simpa [prefixWord, tailWord_362385, baseEnd_362385] using wordTrace_append hprefix tailTrace_362385
  have hstable : (prefixWord ++ tailWord_362385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362385).length < 2 ^ (prefixWord ++ tailWord_362385).sum := by decide
  have hdescent : baseEnd_362385 < baseStart_362385 := by decide
  rcases family_descends (prefixWord ++ tailWord_362385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362402 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_362402 : Nat := 118140960795 + 362402 * 2 ^ 59
def prefixEnd_362402 : Nat := 4983230072969 + 3 ^ 40 * 362402 * 2
def baseEnd_362402 : Nat := 165410147689596741518533

theorem tailTrace_362402 : CollatzResearch.WordTrace tailWord_362402 prefixEnd_362402 165410147689596741518533 := by
  unfold tailWord_362402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304471708271730544782365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8811924555391281452752973 3304471708271730544782365)
  ·
    refine ⟨1239176890601898954293387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3304471708271730544782365 1239176890601898954293387)
    ·
      refine ⟨1858765335902848431440081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239176890601898954293387 1858765335902848431440081)
      ·
        refine ⟨1394074001927136323580061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1858765335902848431440081 1394074001927136323580061)
        ·
          refine ⟨522777750722676121342523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1394074001927136323580061 522777750722676121342523)
          ·
            refine ⟨784166626084014182013785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522777750722676121342523 784166626084014182013785)
            ·
              refine ⟨588124969563010636510339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784166626084014182013785 588124969563010636510339)
              ·
                refine ⟨882187454344515954765509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588124969563010636510339 882187454344515954765509)
                ·
                  refine ⟨165410147689596741518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882187454344515954765509 165410147689596741518533)
                  ·
                    rfl

theorem cell20_362402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_362402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362402 prefixEnd_362402 := by exact prefixLift 362402
  have htrace : WordTrace (prefixWord ++ tailWord_362402) baseStart_362402 baseEnd_362402 := by
    simpa [prefixWord, tailWord_362402, baseEnd_362402] using wordTrace_append hprefix tailTrace_362402
  have hstable : (prefixWord ++ tailWord_362402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362402).length < 2 ^ (prefixWord ++ tailWord_362402).sum := by decide
  have hdescent : baseEnd_362402 < baseStart_362402 := by decide
  rcases family_descends (prefixWord ++ tailWord_362402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362430 : List Nat := [4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_362430 : Nat := 118140960795 + 362430 * 2 ^ 59
def prefixEnd_362430 : Nat := 4983230072969 + 3 ^ 40 * 362430 * 2
def baseEnd_362430 : Nat := 55140975884184362861695

theorem tailTrace_362430 : CollatzResearch.WordTrace tailWord_362430 prefixEnd_362430 55140975884184362861695 := by
  unfold tailWord_362430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652363509623185370143593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8812605384656988640765829 1652363509623185370143593)
  ·
    refine ⟨1239272632217389027607695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652363509623185370143593 1239272632217389027607695)
    ·
      refine ⟨1858908948326083541411543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239272632217389027607695 1858908948326083541411543)
      ·
        refine ⟨2788363422489125312117315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858908948326083541411543 2788363422489125312117315)
        ·
          refine ⟨4182545133733687968175973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788363422489125312117315 4182545133733687968175973)
          ·
            refine ⟨784227212575066494032995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4182545133733687968175973 784227212575066494032995)
            ·
              refine ⟨1176340818862599741049493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784227212575066494032995 1176340818862599741049493)
              ·
                refine ⟨55140975884184362861695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1176340818862599741049493 55140975884184362861695)
                ·
                  rfl

theorem cell20_362430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_362430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362430 prefixEnd_362430 := by exact prefixLift 362430
  have htrace : WordTrace (prefixWord ++ tailWord_362430) baseStart_362430 baseEnd_362430 := by
    simpa [prefixWord, tailWord_362430, baseEnd_362430] using wordTrace_append hprefix tailTrace_362430
  have hstable : (prefixWord ++ tailWord_362430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362430).length < 2 ^ (prefixWord ++ tailWord_362430).sum := by decide
  have hdescent : baseEnd_362430 < baseStart_362430 := by decide
  rcases family_descends (prefixWord ++ tailWord_362430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362440 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_362440 : Nat := 118140960795 + 362440 * 2 ^ 59
def prefixEnd_362440 : Nat := 4983230072969 + 3 ^ 40 * 362440 * 2
def baseEnd_362440 : Nat := 165427491925037498251711

theorem tailTrace_362440 : CollatzResearch.WordTrace tailWord_362440 prefixEnd_362440 165427491925037498251711 := by
  unfold tailWord_362440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609636403474627334506387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8812848537966169779341849 6609636403474627334506387)
  ·
    refine ⟨9914454605211941001759581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609636403474627334506387 9914454605211941001759581)
    ·
      refine ⟨3717920476954477875659843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9914454605211941001759581 3717920476954477875659843)
      ·
        refine ⟨5576880715431716813489765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717920476954477875659843 5576880715431716813489765)
        ·
          refine ⟨1045665134143446902529331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5576880715431716813489765 1045665134143446902529331)
          ·
            refine ⟨1568497701215170353793997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045665134143446902529331 1568497701215170353793997)
            ·
              refine ⟨588186637955688882672749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568497701215170353793997 588186637955688882672749)
              ·
                refine ⟨220569989233383331002281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588186637955688882672749 220569989233383331002281)
                ·
                  refine ⟨165427491925037498251711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220569989233383331002281 165427491925037498251711)
                  ·
                    rfl

theorem cell20_362440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_362440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362440 prefixEnd_362440 := by exact prefixLift 362440
  have htrace : WordTrace (prefixWord ++ tailWord_362440) baseStart_362440 baseEnd_362440 := by
    simpa [prefixWord, tailWord_362440, baseEnd_362440] using wordTrace_append hprefix tailTrace_362440
  have hstable : (prefixWord ++ tailWord_362440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362440).length < 2 ^ (prefixWord ++ tailWord_362440).sum := by decide
  have hdescent : baseEnd_362440 < baseStart_362440 := by decide
  rcases family_descends (prefixWord ++ tailWord_362440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362457 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 2]
def baseStart_362457 : Nat := 118140960795 + 362457 * 2 ^ 59
def prefixEnd_362457 : Nat := 4983230072969 + 3 ^ 40 * 362457 * 2
def baseEnd_362457 : Nat := 165435251188260994684975

theorem tailTrace_362457 : CollatzResearch.WordTrace tailWord_362457 prefixEnd_362457 165435251188260994684975 := by
  unfold tailWord_362457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219892847887666572381625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8813261898591777714921083 13219892847887666572381625)
  ·
    refine ⟨9914919635915749929286219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13219892847887666572381625 9914919635915749929286219)
    ·
      refine ⟨14872379453873624893929329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914919635915749929286219 14872379453873624893929329)
      ·
        refine ⟨11154284590405218670446997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14872379453873624893929329 11154284590405218670446997)
        ·
          refine ⟨522857090175244625177203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11154284590405218670446997 522857090175244625177203)
          ·
            refine ⟨784285635262866937765805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522857090175244625177203 784285635262866937765805)
            ·
              refine ⟨294107113223575101662177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784285635262866937765805 294107113223575101662177)
              ·
                refine ⟨220580334917681326246633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294107113223575101662177 220580334917681326246633)
                ·
                  refine ⟨165435251188260994684975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220580334917681326246633 165435251188260994684975)
                  ·
                    rfl

theorem cell20_362457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_362457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362457 prefixEnd_362457 := by exact prefixLift 362457
  have htrace : WordTrace (prefixWord ++ tailWord_362457) baseStart_362457 baseEnd_362457 := by
    simpa [prefixWord, tailWord_362457, baseEnd_362457] using wordTrace_append hprefix tailTrace_362457
  have hstable : (prefixWord ++ tailWord_362457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362457).length < 2 ^ (prefixWord ++ tailWord_362457).sum := by decide
  have hdescent : baseEnd_362457 < baseStart_362457 := by decide
  rcases family_descends (prefixWord ++ tailWord_362457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362489 : List Nat := [1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_362489 : Nat := 118140960795 + 362489 * 2 ^ 59
def prefixEnd_362489 : Nat := 4983230072969 + 3 ^ 40 * 362489 * 2
def baseEnd_362489 : Nat := 55149952286737035206059

theorem tailTrace_362489 : CollatzResearch.WordTrace tailWord_362489 prefixEnd_362489 55149952286737035206059 := by
  unfold tailWord_362489
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221059983771736037546521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8814039989181157358364347 13221059983771736037546521)
  ·
    refine ⟨9915794987828802028159891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13221059983771736037546521 9915794987828802028159891)
    ·
      refine ⟨14873692481743203042239837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9915794987828802028159891 14873692481743203042239837)
      ·
        refine ⟨5577634680653701140839939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14873692481743203042239837 5577634680653701140839939)
        ·
          refine ⟨8366452020980551711259909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577634680653701140839939 8366452020980551711259909)
          ·
            refine ⟨1568709753933853445861233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8366452020980551711259909 1568709753933853445861233)
            ·
              refine ⟨1176532315450390084395925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568709753933853445861233 1176532315450390084395925)
              ·
                refine ⟨55149952286737035206059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1176532315450390084395925 55149952286737035206059)
                ·
                  rfl

theorem cell20_362489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_362489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362489 prefixEnd_362489 := by exact prefixLift 362489
  have htrace : WordTrace (prefixWord ++ tailWord_362489) baseStart_362489 baseEnd_362489 := by
    simpa [prefixWord, tailWord_362489, baseEnd_362489] using wordTrace_append hprefix tailTrace_362489
  have hstable : (prefixWord ++ tailWord_362489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362489).length < 2 ^ (prefixWord ++ tailWord_362489).sum := by decide
  have hdescent : baseEnd_362489 < baseStart_362489 := by decide
  rcases family_descends (prefixWord ++ tailWord_362489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362496 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_362496 : Nat := 118140960795 + 362496 * 2 ^ 59
def prefixEnd_362496 : Nat := 4983230072969 + 3 ^ 40 * 362496 * 2
def baseEnd_362496 : Nat := 165453051850950192384815

theorem tailTrace_362496 : CollatzResearch.WordTrace tailWord_362496 prefixEnd_362496 165453051850950192384815 := by
  unfold tailWord_362496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610657647373188116525671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8814210196497584155367561 6610657647373188116525671)
  ·
    refine ⟨9915986471059782174788507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6610657647373188116525671 9915986471059782174788507)
    ·
      refine ⟨14873979706589673262182761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9915986471059782174788507 14873979706589673262182761)
      ·
        refine ⟨11155484779942254946637071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14873979706589673262182761 11155484779942254946637071)
        ·
          refine ⟨16733227169913382419955607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11155484779942254946637071 16733227169913382419955607)
          ·
            refine ⟨25099840754870073629933411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733227169913382419955607 25099840754870073629933411)
            ·
              refine ⟨37649761132305110444900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25099840754870073629933411 37649761132305110444900117)
              ·
                refine ⟨1764832553076802052104693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37649761132305110444900117 1764832553076802052104693)
                ·
                  refine ⟨165453051850950192384815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764832553076802052104693 165453051850950192384815)
                  ·
                    rfl

theorem cell20_362496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_362496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362496 prefixEnd_362496 := by exact prefixLift 362496
  have htrace : WordTrace (prefixWord ++ tailWord_362496) baseStart_362496 baseEnd_362496 := by
    simpa [prefixWord, tailWord_362496, baseEnd_362496] using wordTrace_append hprefix tailTrace_362496
  have hstable : (prefixWord ++ tailWord_362496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362496).length < 2 ^ (prefixWord ++ tailWord_362496).sum := by decide
  have hdescent : baseEnd_362496 < baseStart_362496 := by decide
  rcases family_descends (prefixWord ++ tailWord_362496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362502 : List Nat := [6, 2, 1, 2, 9]
def baseStart_362502 : Nat := 118140960795 + 362502 * 2 ^ 59
def prefixEnd_362502 : Nat := 4983230072969 + 3 ^ 40 * 362502 * 2
def baseEnd_362502 : Nat := 2042664079190627631911

theorem tailTrace_362502 : CollatzResearch.WordTrace tailWord_362502 prefixEnd_362502 2042664079190627631911 := by
  unfold tailWord_362502
  simp only [CollatzResearch.WordTrace]
  refine ⟨413172941647644976805305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8814356088483092838513173 413172941647644976805305)
  ·
    refine ⟨309879706235733732603979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 413172941647644976805305 309879706235733732603979)
    ·
      refine ⟨464819559353600598905969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309879706235733732603979 464819559353600598905969)
      ·
        refine ⟨348614669515200449179477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464819559353600598905969 348614669515200449179477)
        ·
          refine ⟨2042664079190627631911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 348614669515200449179477 2042664079190627631911)
          ·
            rfl

theorem cell20_362502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 9].length) (baseStart_362502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362502 prefixEnd_362502 := by exact prefixLift 362502
  have htrace : WordTrace (prefixWord ++ tailWord_362502) baseStart_362502 baseEnd_362502 := by
    simpa [prefixWord, tailWord_362502, baseEnd_362502] using wordTrace_append hprefix tailTrace_362502
  have hstable : (prefixWord ++ tailWord_362502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362502).length < 2 ^ (prefixWord ++ tailWord_362502).sum := by decide
  have hdescent : baseEnd_362502 < baseStart_362502 := by decide
  rcases family_descends (prefixWord ++ tailWord_362502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362506 : List Nat := [3, 1, 2, 2, 5, 7]
def baseStart_362506 : Nat := 118140960795 + 362506 * 2 ^ 59
def prefixEnd_362506 : Nat := 4983230072969 + 3 ^ 40 * 362506 * 2
def baseEnd_362506 : Nat := 6128059856423503779683

theorem tailTrace_362506 : CollatzResearch.WordTrace tailWord_362506 prefixEnd_362506 6128059856423503779683 := by
  unfold tailWord_362506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3305420006177536985228843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8814453349806765293943581 3305420006177536985228843)
  ·
    refine ⟨4958130009266305477843265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3305420006177536985228843 4958130009266305477843265)
    ·
      refine ⟨3718597506949729108382449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4958130009266305477843265 3718597506949729108382449)
      ·
        refine ⟨2788948130212296831286837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3718597506949729108382449 2788948130212296831286837)
        ·
          refine ⟨261463887207402827933141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2788948130212296831286837 261463887207402827933141)
          ·
            refine ⟨6128059856423503779683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 261463887207402827933141 6128059856423503779683)
            ·
              rfl

theorem cell20_362506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 7].length) (baseStart_362506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362506 prefixEnd_362506 := by exact prefixLift 362506
  have htrace : WordTrace (prefixWord ++ tailWord_362506) baseStart_362506 baseEnd_362506 := by
    simpa [prefixWord, tailWord_362506, baseEnd_362506] using wordTrace_append hprefix tailTrace_362506
  have hstable : (prefixWord ++ tailWord_362506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362506).length < 2 ^ (prefixWord ++ tailWord_362506).sum := by decide
  have hdescent : baseEnd_362506 < baseStart_362506 := by decide
  rcases family_descends (prefixWord ++ tailWord_362506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362520 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_362520 : Nat := 118140960795 + 362520 * 2 ^ 59
def prefixEnd_362520 : Nat := 4983230072969 + 3 ^ 40 * 362520 * 2
def baseEnd_362520 : Nat := 165464006104912775584717

theorem tailTrace_362520 : CollatzResearch.WordTrace tailWord_362520 prefixEnd_362520 165464006104912775584717 := by
  unfold tailWord_362520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611095323329714165962507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8814793764439618887950009 6611095323329714165962507)
  ·
    refine ⟨9916642984994571248943761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611095323329714165962507 9916642984994571248943761)
    ·
      refine ⟨7437482238745928436707821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9916642984994571248943761 7437482238745928436707821)
      ·
        refine ⟨2789055839529723163765433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7437482238745928436707821 2789055839529723163765433)
        ·
          refine ⟨2091791879647292372824075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789055839529723163765433 2091791879647292372824075)
          ·
            refine ⟨3137687819470938559236113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091791879647292372824075 3137687819470938559236113)
            ·
              refine ⟨2353265864603203919427085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137687819470938559236113 2353265864603203919427085)
              ·
                refine ⟨882474699226201469785157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353265864603203919427085 882474699226201469785157)
                ·
                  refine ⟨165464006104912775584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882474699226201469785157 165464006104912775584717)
                  ·
                    rfl

theorem cell20_362520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_362520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362520 prefixEnd_362520 := by exact prefixLift 362520
  have htrace : WordTrace (prefixWord ++ tailWord_362520) baseStart_362520 baseEnd_362520 := by
    simpa [prefixWord, tailWord_362520, baseEnd_362520] using wordTrace_append hprefix tailTrace_362520
  have hstable : (prefixWord ++ tailWord_362520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362520).length < 2 ^ (prefixWord ++ tailWord_362520).sum := by decide
  have hdescent : baseEnd_362520 < baseStart_362520 := by decide
  rcases family_descends (prefixWord ++ tailWord_362520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362544 : List Nat := [2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_362544 : Nat := 118140960795 + 362544 * 2 ^ 59
def prefixEnd_362544 : Nat := 4983230072969 + 3 ^ 40 * 362544 * 2
def baseEnd_362544 : Nat := 55158320119625119594873

theorem tailTrace_362544 : CollatzResearch.WordTrace tailWord_362544 prefixEnd_362544 55158320119625119594873 := by
  unfold tailWord_362544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611532999286240215399343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8815377332381653620532457 6611532999286240215399343)
  ·
    refine ⟨9917299498929360323099015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611532999286240215399343 9917299498929360323099015)
    ·
      refine ⟨14875949248394040484648523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917299498929360323099015 14875949248394040484648523)
      ·
        refine ⟨22313923872591060726972785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14875949248394040484648523 22313923872591060726972785)
        ·
          refine ⟨16735442904443295545229589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22313923872591060726972785 16735442904443295545229589)
          ·
            refine ⟨784473886145779478682637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16735442904443295545229589 784473886145779478682637)
            ·
              refine ⟨294177707304667304505989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784473886145779478682637 294177707304667304505989)
              ·
                refine ⟨55158320119625119594873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294177707304667304505989 55158320119625119594873)
                ·
                  rfl

theorem cell20_362544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_362544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362544 prefixEnd_362544 := by exact prefixLift 362544
  have htrace : WordTrace (prefixWord ++ tailWord_362544) baseStart_362544 baseEnd_362544 := by
    simpa [prefixWord, tailWord_362544, baseEnd_362544] using wordTrace_append hprefix tailTrace_362544
  have hstable : (prefixWord ++ tailWord_362544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362544).length < 2 ^ (prefixWord ++ tailWord_362544).sum := by decide
  have hdescent : baseEnd_362544 < baseStart_362544 := by decide
  rcases family_descends (prefixWord ++ tailWord_362544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362596 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_362596 : Nat := 118140960795 + 362596 * 2 ^ 59
def prefixEnd_362596 : Nat := 4983230072969 + 3 ^ 40 * 362596 * 2
def baseEnd_362596 : Nat := 165498694575794289051073

theorem tailTrace_362596 : CollatzResearch.WordTrace tailWord_362596 prefixEnd_362596 165498694575794289051073 := by
  unfold tailWord_362596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6612481297192046655845821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8816641729589395541127761 6612481297192046655845821)
  ·
    refine ⟨2479680486447017495942183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6612481297192046655845821 2479680486447017495942183)
    ·
      refine ⟨3719520729670526243913275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479680486447017495942183 3719520729670526243913275)
      ·
        refine ⟨5579281094505789365869913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719520729670526243913275 5579281094505789365869913)
        ·
          refine ⟨4184460820879342024402435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5579281094505789365869913 4184460820879342024402435)
          ·
            refine ⟨6276691231319013036603653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184460820879342024402435 6276691231319013036603653)
            ·
              refine ⟨1176879605872314944363185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6276691231319013036603653 1176879605872314944363185)
              ·
                refine ⟨882659704404236208272389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176879605872314944363185 882659704404236208272389)
                ·
                  refine ⟨165498694575794289051073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882659704404236208272389 165498694575794289051073)
                  ·
                    rfl

theorem cell20_362596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_362596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362596 prefixEnd_362596 := by exact prefixLift 362596
  have htrace : WordTrace (prefixWord ++ tailWord_362596) baseStart_362596 baseEnd_362596 := by
    simpa [prefixWord, tailWord_362596, baseEnd_362596] using wordTrace_append hprefix tailTrace_362596
  have hstable : (prefixWord ++ tailWord_362596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362596).length < 2 ^ (prefixWord ++ tailWord_362596).sum := by decide
  have hdescent : baseEnd_362596 < baseStart_362596 := by decide
  rcases family_descends (prefixWord ++ tailWord_362596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362658 : List Nat := [3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_362658 : Nat := 118140960795 + 362658 * 2 ^ 59
def prefixEnd_362658 : Nat := 4983230072969 + 3 ^ 40 * 362658 * 2
def baseEnd_362658 : Nat := 55175664355065876328051

theorem tailTrace_362658 : CollatzResearch.WordTrace tailWord_362658 prefixEnd_362658 55175664355065876328051 := by
  unfold tailWord_362658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306805980039869475112157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8818149280106318600299085 3306805980039869475112157)
  ·
    refine ⟨1240052242514951053167059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3306805980039869475112157 1240052242514951053167059)
    ·
      refine ⟨1860078363772426579750589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240052242514951053167059 1860078363772426579750589)
      ·
        refine ⟨697529386414659967406471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860078363772426579750589 697529386414659967406471)
        ·
          refine ⟨1046294079621989951109707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697529386414659967406471 1046294079621989951109707)
          ·
            refine ⟨1569441119432984926664561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046294079621989951109707 1569441119432984926664561)
            ·
              refine ⟨1177080839574738694998421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569441119432984926664561 1177080839574738694998421)
              ·
                refine ⟨55175664355065876328051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1177080839574738694998421 55175664355065876328051)
                ·
                  rfl

theorem cell20_362658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_362658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362658 prefixEnd_362658 := by exact prefixLift 362658
  have htrace : WordTrace (prefixWord ++ tailWord_362658) baseStart_362658 baseEnd_362658 := by
    simpa [prefixWord, tailWord_362658, baseEnd_362658] using wordTrace_append hprefix tailTrace_362658
  have hstable : (prefixWord ++ tailWord_362658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362658).length < 2 ^ (prefixWord ++ tailWord_362658).sum := by decide
  have hdescent : baseEnd_362658 < baseStart_362658 := by decide
  rcases family_descends (prefixWord ++ tailWord_362658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362723 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 2]
def baseStart_362723 : Nat := 118140960795 + 362723 * 2 ^ 59
def prefixEnd_362723 : Nat := 4983230072969 + 3 ^ 40 * 362723 * 2
def baseEnd_362723 : Nat := 165556660836346291817221

theorem tailTrace_362723 : CollatzResearch.WordTrace tailWord_362723 prefixEnd_362723 165556660836346291817221 := by
  unfold tailWord_362723
  simp only [CollatzResearch.WordTrace]
  refine ⟨13229594664923994001564823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819729776615996001043215 13229594664923994001564823)
  ·
    refine ⟨19844391997385991002347235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13229594664923994001564823 19844391997385991002347235)
    ·
      refine ⟨29766587996078986503520853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19844391997385991002347235 29766587996078986503520853)
      ·
        refine ⟨348827203079050623088135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 29766587996078986503520853 348827203079050623088135)
        ·
          refine ⟨523240804618575934632203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348827203079050623088135 523240804618575934632203)
          ·
            refine ⟨784861206927863901948305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523240804618575934632203 784861206927863901948305)
            ·
              refine ⟨588645905195897926461229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784861206927863901948305 588645905195897926461229)
              ·
                refine ⟨220742214448461722422961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588645905195897926461229 220742214448461722422961)
                ·
                  refine ⟨165556660836346291817221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220742214448461722422961 165556660836346291817221)
                  ·
                    rfl

theorem cell20_362723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2].length) (baseStart_362723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362723 prefixEnd_362723 := by exact prefixLift 362723
  have htrace : WordTrace (prefixWord ++ tailWord_362723) baseStart_362723 baseEnd_362723 := by
    simpa [prefixWord, tailWord_362723, baseEnd_362723] using wordTrace_append hprefix tailTrace_362723
  have hstable : (prefixWord ++ tailWord_362723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362723).length < 2 ^ (prefixWord ++ tailWord_362723).sum := by decide
  have hdescent : baseEnd_362723 < baseStart_362723 := by decide
  rcases family_descends (prefixWord ++ tailWord_362723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362724 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_362724 : Nat := 118140960795 + 362724 * 2 ^ 59
def prefixEnd_362724 : Nat := 4983230072969 + 3 ^ 40 * 362724 * 2
def baseEnd_362724 : Nat := 165557117263594732783883

theorem tailTrace_362724 : CollatzResearch.WordTrace tailWord_362724 prefixEnd_362724 165557117263594732783883 := by
  unfold tailWord_362724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614815568960185586175613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8819754091946914114900817 6614815568960185586175613)
  ·
    refine ⟨2480555838360069594815855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6614815568960185586175613 2480555838360069594815855)
    ·
      refine ⟨3720833757540104392223783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480555838360069594815855 3720833757540104392223783)
      ·
        refine ⟨5581250636310156588335675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720833757540104392223783 5581250636310156588335675)
        ·
          refine ⟨8371875954465234882503513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581250636310156588335675 8371875954465234882503513)
          ·
            refine ⟨6278906965848926161877635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371875954465234882503513 6278906965848926161877635)
            ·
              refine ⟨9418360448773389242816453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278906965848926161877635 9418360448773389242816453)
              ·
                refine ⟨1765942584145010483028085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9418360448773389242816453 1765942584145010483028085)
                ·
                  refine ⟨165557117263594732783883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1765942584145010483028085 165557117263594732783883)
                  ·
                    rfl

theorem cell20_362724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_362724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362724 prefixEnd_362724 := by exact prefixLift 362724
  have htrace : WordTrace (prefixWord ++ tailWord_362724) baseStart_362724 baseEnd_362724 := by
    simpa [prefixWord, tailWord_362724, baseEnd_362724] using wordTrace_append hprefix tailTrace_362724
  have hstable : (prefixWord ++ tailWord_362724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362724).length < 2 ^ (prefixWord ++ tailWord_362724).sum := by decide
  have hdescent : baseEnd_362724 < baseStart_362724 := by decide
  rcases family_descends (prefixWord ++ tailWord_362724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362731 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_362731 : Nat := 118140960795 + 362731 * 2 ^ 59
def prefixEnd_362731 : Nat := 4983230072969 + 3 ^ 40 * 362731 * 2
def baseEnd_362731 : Nat := 165560312254333819550521

theorem tailTrace_362731 : CollatzResearch.WordTrace tailWord_362731 prefixEnd_362731 165560312254333819550521 := by
  unfold tailWord_362731
  simp only [CollatzResearch.WordTrace]
  refine ⟨13229886448895011367856047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819924299263340911904031 13229886448895011367856047)
  ·
    refine ⟨19844829673342517051784071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13229886448895011367856047 19844829673342517051784071)
    ·
      refine ⟨29767244510013775577676107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19844829673342517051784071 29767244510013775577676107)
      ·
        refine ⟨44650866765020663366514161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29767244510013775577676107 44650866765020663366514161)
        ·
          refine ⟨33488150073765497524885621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44650866765020663366514161 33488150073765497524885621)
          ·
            refine ⟨3139514069415515392958027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33488150073765497524885621 3139514069415515392958027)
            ·
              refine ⟨4709271104123273089437041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139514069415515392958027 4709271104123273089437041)
              ·
                refine ⟨3531953328092454817077781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709271104123273089437041 3531953328092454817077781)
                ·
                  refine ⟨165560312254333819550521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3531953328092454817077781 165560312254333819550521)
                  ·
                    rfl

theorem cell20_362731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_362731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362731 prefixEnd_362731 := by exact prefixLift 362731
  have htrace : WordTrace (prefixWord ++ tailWord_362731) baseStart_362731 baseEnd_362731 := by
    simpa [prefixWord, tailWord_362731, baseEnd_362731] using wordTrace_append hprefix tailTrace_362731
  have hstable : (prefixWord ++ tailWord_362731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362731).length < 2 ^ (prefixWord ++ tailWord_362731).sum := by decide
  have hdescent : baseEnd_362731 < baseStart_362731 := by decide
  rcases family_descends (prefixWord ++ tailWord_362731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362748 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_362748 : Nat := 118140960795 + 362748 * 2 ^ 59
def prefixEnd_362748 : Nat := 4983230072969 + 3 ^ 40 * 362748 * 2
def baseEnd_362748 : Nat := 165568071517557315983785

theorem tailTrace_362748 : CollatzResearch.WordTrace tailWord_362748 prefixEnd_362748 165568071517557315983785 := by
  unfold tailWord_362748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615253244916711635612449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8820337659888948847483265 6615253244916711635612449)
  ·
    refine ⟨4961439933687533726709337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6615253244916711635612449 4961439933687533726709337)
    ·
      refine ⟨3721079950265650295032003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4961439933687533726709337 3721079950265650295032003)
      ·
        refine ⟨5581619925398475442548005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721079950265650295032003 5581619925398475442548005)
        ·
          refine ⟨1046553736012214145477751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5581619925398475442548005 1046553736012214145477751)
          ·
            refine ⟨1569830604018321218216627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046553736012214145477751 1569830604018321218216627)
            ·
              refine ⟨2354745906027481827324941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569830604018321218216627 2354745906027481827324941)
              ·
                refine ⟨883029714760305685246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354745906027481827324941 883029714760305685246853)
                ·
                  refine ⟨165568071517557315983785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883029714760305685246853 165568071517557315983785)
                  ·
                    rfl

theorem cell20_362748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_362748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362748 prefixEnd_362748 := by exact prefixLift 362748
  have htrace : WordTrace (prefixWord ++ tailWord_362748) baseStart_362748 baseEnd_362748 := by
    simpa [prefixWord, tailWord_362748, baseEnd_362748] using wordTrace_append hprefix tailTrace_362748
  have hstable : (prefixWord ++ tailWord_362748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362748).length < 2 ^ (prefixWord ++ tailWord_362748).sum := by decide
  have hdescent : baseEnd_362748 < baseStart_362748 := by decide
  rcases family_descends (prefixWord ++ tailWord_362748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362855 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_362855 : Nat := 118140960795 + 362855 * 2 ^ 59
def prefixEnd_362855 : Nat := 4983230072969 + 3 ^ 40 * 362855 * 2
def baseEnd_362855 : Nat := 165616909233140499416681

theorem tailTrace_362855 : CollatzResearch.WordTrace tailWord_362855 prefixEnd_362855 165616909233140499416681 := by
  unfold tailWord_362855
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234409100445780545370019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8822939400297187030246679 13234409100445780545370019)
  ·
    refine ⟨19851613650668670818055029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13234409100445780545370019 19851613650668670818055029)
    ·
      refine ⟨1861088779750187889192659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19851613650668670818055029 1861088779750187889192659)
      ·
        refine ⟨2791633169625281833788989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861088779750187889192659 2791633169625281833788989)
        ·
          refine ⟨1046862438609480687670871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2791633169625281833788989 1046862438609480687670871)
          ·
            refine ⟨1570293657914221031506307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046862438609480687670871 1570293657914221031506307)
            ·
              refine ⟨2355440486871331547259461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570293657914221031506307 2355440486871331547259461)
              ·
                refine ⟨441645091288374665111149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2355440486871331547259461 441645091288374665111149)
                ·
                  refine ⟨165616909233140499416681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441645091288374665111149 165616909233140499416681)
                  ·
                    rfl

theorem cell20_362855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_362855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362855 prefixEnd_362855 := by exact prefixLift 362855
  have htrace : WordTrace (prefixWord ++ tailWord_362855) baseStart_362855 baseEnd_362855 := by
    simpa [prefixWord, tailWord_362855, baseEnd_362855] using wordTrace_append hprefix tailTrace_362855
  have hstable : (prefixWord ++ tailWord_362855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362855).length < 2 ^ (prefixWord ++ tailWord_362855).sum := by decide
  have hdescent : baseEnd_362855 < baseStart_362855 := by decide
  rcases family_descends (prefixWord ++ tailWord_362855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362858 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_362858 : Nat := 118140960795 + 362858 * 2 ^ 59
def prefixEnd_362858 : Nat := 4983230072969 + 3 ^ 40 * 362858 * 2
def baseEnd_362858 : Nat := 165618278514885822316669

theorem tailTrace_362858 : CollatzResearch.WordTrace tailWord_362858 prefixEnd_362858 165618278514885822316669 := by
  unfold tailWord_362858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308629629858728014432307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8823012346289941371819485 3308629629858728014432307)
  ·
    refine ⟨4962944444788092021648461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308629629858728014432307 4962944444788092021648461)
    ·
      refine ⟨1861104166795534508118173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4962944444788092021648461 1861104166795534508118173)
      ·
        refine ⟨697914062548325440544315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1861104166795534508118173 697914062548325440544315)
        ·
          refine ⟨1046871093822488160816473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697914062548325440544315 1046871093822488160816473)
          ·
            refine ⟨785153320366866120612355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046871093822488160816473 785153320366866120612355)
            ·
              refine ⟨1177729980550299180918533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785153320366866120612355 1177729980550299180918533)
              ·
                refine ⟨220824371353181096422225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1177729980550299180918533 220824371353181096422225)
                ·
                  refine ⟨165618278514885822316669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220824371353181096422225 165618278514885822316669)
                  ·
                    rfl

theorem cell20_362858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_362858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362858 prefixEnd_362858 := by exact prefixLift 362858
  have htrace : WordTrace (prefixWord ++ tailWord_362858) baseStart_362858 baseEnd_362858 := by
    simpa [prefixWord, tailWord_362858, baseEnd_362858] using wordTrace_append hprefix tailTrace_362858
  have hstable : (prefixWord ++ tailWord_362858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362858).length < 2 ^ (prefixWord ++ tailWord_362858).sum := by decide
  have hdescent : baseEnd_362858 < baseStart_362858 := by decide
  rcases family_descends (prefixWord ++ tailWord_362858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362882 : List Nat := [3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_362882 : Nat := 118140960795 + 362882 * 2 ^ 59
def prefixEnd_362882 : Nat := 4983230072969 + 3 ^ 40 * 362882 * 2
def baseEnd_362882 : Nat := 55209744256282801838857

theorem tailTrace_362882 : CollatzResearch.WordTrace tailWord_362882 prefixEnd_362882 55209744256282801838857 := by
  unfold tailWord_362882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308848467836991039150725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8823595914231976104401933 3308848467836991039150725)
  ·
    refine ⟨620409087719435819840761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3308848467836991039150725 620409087719435819840761)
    ·
      refine ⟨465306815789576864880571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 620409087719435819840761 465306815789576864880571)
      ·
        refine ⟨697960223684365297320857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465306815789576864880571 697960223684365297320857)
        ·
          refine ⟨523470167763273972990643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697960223684365297320857 523470167763273972990643)
          ·
            refine ⟨785205251644910959485965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523470167763273972990643 785205251644910959485965)
            ·
              refine ⟨294451969366841609807237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785205251644910959485965 294451969366841609807237)
              ·
                refine ⟨55209744256282801838857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294451969366841609807237 55209744256282801838857)
                ·
                  rfl

theorem cell20_362882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_362882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362882 prefixEnd_362882 := by exact prefixLift 362882
  have htrace : WordTrace (prefixWord ++ tailWord_362882) baseStart_362882 baseEnd_362882 := by
    simpa [prefixWord, tailWord_362882, baseEnd_362882] using wordTrace_append hprefix tailTrace_362882
  have hstable : (prefixWord ++ tailWord_362882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362882).length < 2 ^ (prefixWord ++ tailWord_362882).sum := by decide
  have hdescent : baseEnd_362882 < baseStart_362882 := by decide
  rcases family_descends (prefixWord ++ tailWord_362882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362902 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_362902 : Nat := 118140960795 + 362902 * 2 ^ 59
def prefixEnd_362902 : Nat := 4983230072969 + 3 ^ 40 * 362902 * 2
def baseEnd_362902 : Nat := 165638361313817224849823

theorem tailTrace_362902 : CollatzResearch.WordTrace tailWord_362902 prefixEnd_362902 165638361313817224849823 := by
  unfold tailWord_362902
  simp only [CollatzResearch.WordTrace]
  refine ⟨827257708204719223270685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8824082220850338381553973 827257708204719223270685)
  ·
    refine ⟨310221640576769708726507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 827257708204719223270685 310221640576769708726507)
    ·
      refine ⟨465332460865154563089761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310221640576769708726507 465332460865154563089761)
      ·
        refine ⟨348999345648865922317321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465332460865154563089761 348999345648865922317321)
        ·
          refine ⟨261749509236649441737991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348999345648865922317321 261749509236649441737991)
          ·
            refine ⟨392624263854974162606987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261749509236649441737991 392624263854974162606987)
            ·
              refine ⟨588936395782461243910481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392624263854974162606987 588936395782461243910481)
              ·
                refine ⟨441702296836845932932861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588936395782461243910481 441702296836845932932861)
                ·
                  refine ⟨165638361313817224849823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441702296836845932932861 165638361313817224849823)
                  ·
                    rfl

theorem cell20_362902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_362902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362902 prefixEnd_362902 := by exact prefixLift 362902
  have htrace : WordTrace (prefixWord ++ tailWord_362902) baseStart_362902 baseEnd_362902 := by
    simpa [prefixWord, tailWord_362902, baseEnd_362902] using wordTrace_append hprefix tailTrace_362902
  have hstable : (prefixWord ++ tailWord_362902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362902).length < 2 ^ (prefixWord ++ tailWord_362902).sum := by decide
  have hdescent : baseEnd_362902 < baseStart_362902 := by decide
  rcases family_descends (prefixWord ++ tailWord_362902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362910 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_362910 : Nat := 118140960795 + 362910 * 2 ^ 59
def prefixEnd_362910 : Nat := 4983230072969 + 3 ^ 40 * 362910 * 2
def baseEnd_362910 : Nat := 165642012731804752583123

theorem tailTrace_362910 : CollatzResearch.WordTrace tailWord_362910 prefixEnd_362910 165642012731804752583123 := by
  unfold tailWord_362910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654551889405815617327773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8824276743497683292414789 1654551889405815617327773)
  ·
    refine ⟨620456958527180856497915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1654551889405815617327773 620456958527180856497915)
    ·
      refine ⟨930685437790771284746873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620456958527180856497915 930685437790771284746873)
      ·
        refine ⟨698014078343078463560155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930685437790771284746873 698014078343078463560155)
        ·
          refine ⟨1047021117514617695340233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698014078343078463560155 1047021117514617695340233)
          ·
            refine ⟨785265838135963271505175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047021117514617695340233 785265838135963271505175)
            ·
              refine ⟨1177898757203944907257763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785265838135963271505175 1177898757203944907257763)
              ·
                refine ⟨1766848135805917360886645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177898757203944907257763 1766848135805917360886645)
                ·
                  refine ⟨165642012731804752583123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1766848135805917360886645 165642012731804752583123)
                  ·
                    rfl

theorem cell20_362910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_362910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362910 prefixEnd_362910 := by exact prefixLift 362910
  have htrace : WordTrace (prefixWord ++ tailWord_362910) baseStart_362910 baseEnd_362910 := by
    simpa [prefixWord, tailWord_362910, baseEnd_362910] using wordTrace_append hprefix tailTrace_362910
  have hstable : (prefixWord ++ tailWord_362910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362910).length < 2 ^ (prefixWord ++ tailWord_362910).sum := by decide
  have hdescent : baseEnd_362910 < baseStart_362910 := by decide
  rcases family_descends (prefixWord ++ tailWord_362910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362952 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_362952 : Nat := 118140960795 + 362952 * 2 ^ 59
def prefixEnd_362952 : Nat := 4983230072969 + 3 ^ 40 * 362952 * 2
def baseEnd_362952 : Nat := 165661182676239273182951

theorem tailTrace_362952 : CollatzResearch.WordTrace tailWord_362952 prefixEnd_362952 165661182676239273182951 := by
  unfold tailWord_362952
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618973490547183055825555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8825297987396244074434073 6618973490547183055825555)
  ·
    refine ⟨9928460235820774583738333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6618973490547183055825555 9928460235820774583738333)
    ·
      refine ⟨3723172588432790468901875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9928460235820774583738333 3723172588432790468901875)
      ·
        refine ⟨5584758882649185703352813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3723172588432790468901875 5584758882649185703352813)
        ·
          refine ⟨2094284580993444638757305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5584758882649185703352813 2094284580993444638757305)
          ·
            refine ⟨1570713435745083479067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094284580993444638757305 1570713435745083479067979)
            ·
              refine ⟨2356070153617625218601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570713435745083479067979 2356070153617625218601969)
              ·
                refine ⟨1767052615213218913951477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356070153617625218601969 1767052615213218913951477)
                ·
                  refine ⟨165661182676239273182951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767052615213218913951477 165661182676239273182951)
                  ·
                    rfl

theorem cell20_362952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_362952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362952 prefixEnd_362952 := by exact prefixLift 362952
  have htrace : WordTrace (prefixWord ++ tailWord_362952) baseStart_362952 baseEnd_362952 := by
    simpa [prefixWord, tailWord_362952, baseEnd_362952] using wordTrace_append hprefix tailTrace_362952
  have hstable : (prefixWord ++ tailWord_362952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362952).length < 2 ^ (prefixWord ++ tailWord_362952).sum := by decide
  have hdescent : baseEnd_362952 < baseStart_362952 := by decide
  rcases family_descends (prefixWord ++ tailWord_362952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362983 : List Nat := [1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_362983 : Nat := 118140960795 + 362983 * 2 ^ 59
def prefixEnd_362983 : Nat := 4983230072969 + 3 ^ 40 * 362983 * 2
def baseEnd_362983 : Nat := 55225110640313647716497

theorem tailTrace_362983 : CollatzResearch.WordTrace tailWord_362983 prefixEnd_362983 55225110640313647716497 := by
  unfold tailWord_362983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239077643982058406029603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8826051762654705604019735 13239077643982058406029603)
  ·
    refine ⟨19858616465973087609044405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13239077643982058406029603 19858616465973087609044405)
    ·
      refine ⟨1861745293684976963347913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19858616465973087609044405 1861745293684976963347913)
      ·
        refine ⟨1396308970263732722510935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861745293684976963347913 1396308970263732722510935)
        ·
          refine ⟨2094463455395599083766403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396308970263732722510935 2094463455395599083766403)
          ·
            refine ⟨3141695183093398625649605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094463455395599083766403 3141695183093398625649605)
            ·
              refine ⟨589067846830012242309301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3141695183093398625649605 589067846830012242309301)
              ·
                refine ⟨55225110640313647716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 589067846830012242309301 55225110640313647716497)
                ·
                  rfl

theorem cell20_362983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_362983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362983 prefixEnd_362983 := by exact prefixLift 362983
  have htrace : WordTrace (prefixWord ++ tailWord_362983) baseStart_362983 baseEnd_362983 := by
    simpa [prefixWord, tailWord_362983, baseEnd_362983] using wordTrace_append hprefix tailTrace_362983
  have hstable : (prefixWord ++ tailWord_362983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362983).length < 2 ^ (prefixWord ++ tailWord_362983).sum := by decide
  have hdescent : baseEnd_362983 < baseStart_362983 := by decide
  rcases family_descends (prefixWord ++ tailWord_362983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362986 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_362986 : Nat := 118140960795 + 362986 * 2 ^ 59
def prefixEnd_362986 : Nat := 4983230072969 + 3 ^ 40 * 362986 * 2
def baseEnd_362986 : Nat := 165676701202686266049479

theorem tailTrace_362986 : CollatzResearch.WordTrace tailWord_362986 prefixEnd_362986 165676701202686266049479 := by
  unfold tailWord_362986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309796765742797479597203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8826124708647459945592541 3309796765742797479597203)
  ·
    refine ⟨4964695148614196219395805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3309796765742797479597203 4964695148614196219395805)
    ·
      refine ⟨1861760680730323582273427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4964695148614196219395805 1861760680730323582273427)
      ·
        refine ⟨2792641021095485373410141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861760680730323582273427 2792641021095485373410141)
        ·
          refine ⟨1047240382910807015028803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2792641021095485373410141 1047240382910807015028803)
          ·
            refine ⟨1570860574366210522543205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047240382910807015028803 1570860574366210522543205)
            ·
              refine ⟨294536357693664472976851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1570860574366210522543205 294536357693664472976851)
              ·
                refine ⟨441804536540496709465277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294536357693664472976851 441804536540496709465277)
                ·
                  refine ⟨165676701202686266049479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441804536540496709465277 165676701202686266049479)
                  ·
                    rfl

theorem cell20_362986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_362986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_362986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_362986 prefixEnd_362986 := by exact prefixLift 362986
  have htrace : WordTrace (prefixWord ++ tailWord_362986) baseStart_362986 baseEnd_362986 := by
    simpa [prefixWord, tailWord_362986, baseEnd_362986] using wordTrace_append hprefix tailTrace_362986
  have hstable : (prefixWord ++ tailWord_362986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362986).length < 2 ^ (prefixWord ++ tailWord_362986).sum := by decide
  have hdescent : baseEnd_362986 < baseStart_362986 := by decide
  rcases family_descends (prefixWord ++ tailWord_362986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363059 : List Nat := [1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_363059 : Nat := 118140960795 + 363059 * 2 ^ 59
def prefixEnd_363059 : Nat := 4983230072969 + 3 ^ 40 * 363059 * 2
def baseEnd_363059 : Nat := 55236673463940818871949

theorem tailTrace_363059 : CollatzResearch.WordTrace tailWord_363059 prefixEnd_363059 55236673463940818871949 := by
  unfold tailWord_363059
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241849591706723385796231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8827899727804482257197487 13241849591706723385796231)
  ·
    refine ⟨19862774387560085078694347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241849591706723385796231 19862774387560085078694347)
    ·
      refine ⟨29794161581340127618041521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19862774387560085078694347 29794161581340127618041521)
      ·
        refine ⟨22345621186005095713531141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29794161581340127618041521 22345621186005095713531141)
        ·
          refine ⟨4189803972375955446287089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22345621186005095713531141 4189803972375955446287089)
          ·
            refine ⟨3142352979281966584715317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4189803972375955446287089 3142352979281966584715317)
            ·
              refine ⟨294595591807684367317061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3142352979281966584715317 294595591807684367317061)
              ·
                refine ⟨55236673463940818871949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294595591807684367317061 55236673463940818871949)
                ·
                  rfl

theorem cell20_363059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_363059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363059 prefixEnd_363059 := by exact prefixLift 363059
  have htrace : WordTrace (prefixWord ++ tailWord_363059) baseStart_363059 baseEnd_363059 := by
    simpa [prefixWord, tailWord_363059, baseEnd_363059] using wordTrace_append hprefix tailTrace_363059
  have hstable : (prefixWord ++ tailWord_363059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363059).length < 2 ^ (prefixWord ++ tailWord_363059).sum := by decide
  have hdescent : baseEnd_363059 < baseStart_363059 := by decide
  rcases family_descends (prefixWord ++ tailWord_363059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363069 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 2]
def baseStart_363069 : Nat := 118140960795 + 363069 * 2 ^ 59
def prefixEnd_363069 : Nat := 4983230072969 + 3 ^ 40 * 363069 * 2
def baseEnd_363069 : Nat := 165714584664306866282473

theorem tailTrace_363069 : CollatzResearch.WordTrace tailWord_363069 prefixEnd_363069 165714584664306866282473 := by
  unfold tailWord_363069
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242214321670495093660261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8828142881113663395773507 13242214321670495093660261)
  ·
    refine ⟨2482915185313217830061299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13242214321670495093660261 2482915185313217830061299)
    ·
      refine ⟨3724372777969826745091949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482915185313217830061299 3724372777969826745091949)
      ·
        refine ⟨1396639791738685029409481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3724372777969826745091949 1396639791738685029409481)
        ·
          refine ⟨1047479843804013772057111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396639791738685029409481 1047479843804013772057111)
          ·
            refine ⟨1571219765706020658085667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047479843804013772057111 1571219765706020658085667)
            ·
              refine ⟨2356829648559030987128501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571219765706020658085667 2356829648559030987128501)
              ·
                refine ⟨220952779552409155043297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2356829648559030987128501 220952779552409155043297)
                ·
                  refine ⟨165714584664306866282473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220952779552409155043297 165714584664306866282473)
                  ·
                    rfl

theorem cell20_363069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_363069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363069 prefixEnd_363069 := by exact prefixLift 363069
  have htrace : WordTrace (prefixWord ++ tailWord_363069) baseStart_363069 baseEnd_363069 := by
    simpa [prefixWord, tailWord_363069, baseEnd_363069] using wordTrace_append hprefix tailTrace_363069
  have hstable : (prefixWord ++ tailWord_363069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363069).length < 2 ^ (prefixWord ++ tailWord_363069).sum := by decide
  have hdescent : baseEnd_363069 < baseStart_363069 := by decide
  rcases family_descends (prefixWord ++ tailWord_363069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363090 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_363090 : Nat := 118140960795 + 363090 * 2 ^ 59
def prefixEnd_363090 : Nat := 4983230072969 + 3 ^ 40 * 363090 * 2
def baseEnd_363090 : Nat := 165724169636524126582387

theorem tailTrace_363090 : CollatzResearch.WordTrace tailWord_363090 prefixEnd_363090 165724169636524126582387 := by
  unfold tailWord_363090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310745063648603920043681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8828653503062943786783149 3310745063648603920043681)
  ·
    refine ⟨2483058797736452940032761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3310745063648603920043681 2483058797736452940032761)
    ·
      refine ⟨1862294098302339705024571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2483058797736452940032761 1862294098302339705024571)
      ·
        refine ⟨2793441147453509557536857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862294098302339705024571 2793441147453509557536857)
        ·
          refine ⟨2095080860590132168152643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2793441147453509557536857 2095080860590132168152643)
          ·
            refine ⟨3142621290885198252228965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095080860590132168152643 3142621290885198252228965)
            ·
              refine ⟨589241492040974672292931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3142621290885198252228965 589241492040974672292931)
              ·
                refine ⟨883862238061462008439397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589241492040974672292931 883862238061462008439397)
                ·
                  refine ⟨165724169636524126582387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883862238061462008439397 165724169636524126582387)
                  ·
                    rfl

theorem cell20_363090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_363090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363090 prefixEnd_363090 := by exact prefixLift 363090
  have htrace : WordTrace (prefixWord ++ tailWord_363090) baseStart_363090 baseEnd_363090 := by
    simpa [prefixWord, tailWord_363090, baseEnd_363090] using wordTrace_append hprefix tailTrace_363090
  have hstable : (prefixWord ++ tailWord_363090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363090).length < 2 ^ (prefixWord ++ tailWord_363090).sum := by decide
  have hdescent : baseEnd_363090 < baseStart_363090 := by decide
  rcases family_descends (prefixWord ++ tailWord_363090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363104 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_363104 : Nat := 118140960795 + 363104 * 2 ^ 59
def prefixEnd_363104 : Nat := 4983230072969 + 3 ^ 40 * 363104 * 2
def baseEnd_363104 : Nat := 165730559618002300115663

theorem tailTrace_363104 : CollatzResearch.WordTrace tailWord_363104 prefixEnd_363104 165730559618002300115663 := by
  unfold tailWord_363104
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621745438271848035592183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8828993917695797380789577 6621745438271848035592183)
  ·
    refine ⟨9932618157407772053388275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6621745438271848035592183 9932618157407772053388275)
    ·
      refine ⟨14898927236111658080082413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9932618157407772053388275 14898927236111658080082413)
      ·
        refine ⟨5587097713541871780030905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14898927236111658080082413 5587097713541871780030905)
        ·
          refine ⟨4190323285156403835023179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5587097713541871780030905 4190323285156403835023179)
          ·
            refine ⟨6285484927734605752534769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190323285156403835023179 6285484927734605752534769)
            ·
              refine ⟨4714113695800954314401077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285484927734605752534769 4714113695800954314401077)
              ·
                refine ⟨441948158981339466975101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4714113695800954314401077 441948158981339466975101)
                ·
                  refine ⟨165730559618002300115663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441948158981339466975101 165730559618002300115663)
                  ·
                    rfl

theorem cell20_363104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_363104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363104 prefixEnd_363104 := by exact prefixLift 363104
  have htrace : WordTrace (prefixWord ++ tailWord_363104) baseStart_363104 baseEnd_363104 := by
    simpa [prefixWord, tailWord_363104, baseEnd_363104] using wordTrace_append hprefix tailTrace_363104
  have hstable : (prefixWord ++ tailWord_363104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363104).length < 2 ^ (prefixWord ++ tailWord_363104).sum := by decide
  have hdescent : baseEnd_363104 < baseStart_363104 := by decide
  rcases family_descends (prefixWord ++ tailWord_363104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363166 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_363166 : Nat := 118140960795 + 363166 * 2 ^ 59
def prefixEnd_363166 : Nat := 4983230072969 + 3 ^ 40 * 363166 * 2
def baseEnd_363166 : Nat := 165758858107405640048743

theorem tailTrace_363166 : CollatzResearch.WordTrace tailWord_363166 prefixEnd_363166 165758858107405640048743 := by
  unfold tailWord_363166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655719025289885082492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8830501468212720439960901 1655719025289885082492669)
  ·
    refine ⟨620894634483706905934751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1655719025289885082492669 620894634483706905934751)
    ·
      refine ⟨931341951725560358902127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620894634483706905934751 931341951725560358902127)
      ·
        refine ⟨1397012927588340538353191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931341951725560358902127 1397012927588340538353191)
        ·
          refine ⟨2095519391382510807529787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397012927588340538353191 2095519391382510807529787)
          ·
            refine ⟨3143279087073766211294681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095519391382510807529787 3143279087073766211294681)
            ·
              refine ⟨2357459315305324658471011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143279087073766211294681 2357459315305324658471011)
              ·
                refine ⟨3536188972957986987706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357459315305324658471011 3536188972957986987706517)
                ·
                  refine ⟨165758858107405640048743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3536188972957986987706517 165758858107405640048743)
                  ·
                    rfl

theorem cell20_363166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_363166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363166 prefixEnd_363166 := by exact prefixLift 363166
  have htrace : WordTrace (prefixWord ++ tailWord_363166) baseStart_363166 baseEnd_363166 := by
    simpa [prefixWord, tailWord_363166, baseEnd_363166] using wordTrace_append hprefix tailTrace_363166
  have hstable : (prefixWord ++ tailWord_363166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363166).length < 2 ^ (prefixWord ++ tailWord_363166).sum := by decide
  have hdescent : baseEnd_363166 < baseStart_363166 := by decide
  rcases family_descends (prefixWord ++ tailWord_363166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363190 : List Nat := [5, 1, 3, 1, 2, 8]
def baseStart_363190 : Nat := 118140960795 + 363190 * 2 ^ 59
def prefixEnd_363190 : Nat := 4983230072969 + 3 ^ 40 * 363190 * 2
def baseEnd_363190 : Nat := 6139622680050674935135

theorem tailTrace_363190 : CollatzResearch.WordTrace tailWord_363190 prefixEnd_363190 6139622680050674935135 := by
  unfold tailWord_363190
  simp only [CollatzResearch.WordTrace]
  refine ⟨827914222139508297425939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8831085036154755172543349 827914222139508297425939)
  ·
    refine ⟨1241871333209262446138909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 827914222139508297425939 1241871333209262446138909)
    ·
      refine ⟨465701749953473417302091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1241871333209262446138909 465701749953473417302091)
      ·
        refine ⟨698552624930210125953137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465701749953473417302091 698552624930210125953137)
        ·
          refine ⟨523914468697657594464853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698552624930210125953137 523914468697657594464853)
          ·
            refine ⟨6139622680050674935135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 523914468697657594464853 6139622680050674935135)
            ·
              rfl

theorem cell20_363190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 8].length) (baseStart_363190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363190 prefixEnd_363190 := by exact prefixLift 363190
  have htrace : WordTrace (prefixWord ++ tailWord_363190) baseStart_363190 baseEnd_363190 := by
    simpa [prefixWord, tailWord_363190, baseEnd_363190] using wordTrace_append hprefix tailTrace_363190
  have hstable : (prefixWord ++ tailWord_363190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363190).length < 2 ^ (prefixWord ++ tailWord_363190).sum := by decide
  have hdescent : baseEnd_363190 < baseStart_363190 := by decide
  rcases family_descends (prefixWord ++ tailWord_363190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363197 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_363197 : Nat := 118140960795 + 363197 * 2 ^ 59
def prefixEnd_363197 : Nat := 4983230072969 + 3 ^ 40 * 363197 * 2
def baseEnd_363197 : Nat := 165773007352107310015283

theorem tailTrace_363197 : CollatzResearch.WordTrace tailWord_363197 prefixEnd_363197 165773007352107310015283 := by
  unfold tailWord_363197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246882865206772954319845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8831255243471181969546563 13246882865206772954319845)
  ·
    refine ⟨2483790537226269928934971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13246882865206772954319845 2483790537226269928934971)
    ·
      refine ⟨3725685805839404893402457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483790537226269928934971 3725685805839404893402457)
      ·
        refine ⟨2794264354379553670051843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725685805839404893402457 2794264354379553670051843)
        ·
          refine ⟨4191396531569330505077765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794264354379553670051843 4191396531569330505077765)
          ·
            refine ⟨785886849669249469702081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4191396531569330505077765 785886849669249469702081)
            ·
              refine ⟨589415137251937102276561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785886849669249469702081 589415137251937102276561)
              ·
                refine ⟨442061352938952826707421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589415137251937102276561 442061352938952826707421)
                ·
                  refine ⟨165773007352107310015283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442061352938952826707421 165773007352107310015283)
                  ·
                    rfl

theorem cell20_363197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_363197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363197 prefixEnd_363197 := by exact prefixLift 363197
  have htrace : WordTrace (prefixWord ++ tailWord_363197) baseStart_363197 baseEnd_363197 := by
    simpa [prefixWord, tailWord_363197, baseEnd_363197] using wordTrace_append hprefix tailTrace_363197
  have hstable : (prefixWord ++ tailWord_363197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363197).length < 2 ^ (prefixWord ++ tailWord_363197).sum := by decide
  have hdescent : baseEnd_363197 < baseStart_363197 := by decide
  rcases family_descends (prefixWord ++ tailWord_363197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363200 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_363200 : Nat := 118140960795 + 363200 * 2 ^ 59
def prefixEnd_363200 : Nat := 4983230072969 + 3 ^ 40 * 363200 * 2
def baseEnd_363200 : Nat := 165774376633852632915271

theorem tailTrace_363200 : CollatzResearch.WordTrace tailWord_363200 prefixEnd_363200 165774376633852632915271 := by
  unfold tailWord_363200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623496142097952233339527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8831328189463936311119369 6623496142097952233339527)
  ·
    refine ⟨9935244213146928350009291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623496142097952233339527 9935244213146928350009291)
    ·
      refine ⟨14902866319720392525013937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935244213146928350009291 14902866319720392525013937)
      ·
        refine ⟨11177149739790294393760453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14902866319720392525013937 11177149739790294393760453)
        ·
          refine ⟨2095715576210680198830085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11177149739790294393760453 2095715576210680198830085)
          ·
            refine ⟨392946670539502537280641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2095715576210680198830085 392946670539502537280641)
            ·
              refine ⟨294710002904626902960481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392946670539502537280641 294710002904626902960481)
              ·
                refine ⟨221032502178470177220361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294710002904626902960481 221032502178470177220361)
                ·
                  refine ⟨165774376633852632915271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221032502178470177220361 165774376633852632915271)
                  ·
                    rfl

theorem cell20_363200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_363200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363200 prefixEnd_363200 := by exact prefixLift 363200
  have htrace : WordTrace (prefixWord ++ tailWord_363200) baseStart_363200 baseEnd_363200 := by
    simpa [prefixWord, tailWord_363200, baseEnd_363200] using wordTrace_append hprefix tailTrace_363200
  have hstable : (prefixWord ++ tailWord_363200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363200).length < 2 ^ (prefixWord ++ tailWord_363200).sum := by decide
  have hdescent : baseEnd_363200 < baseStart_363200 := by decide
  rcases family_descends (prefixWord ++ tailWord_363200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363221 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_363221 : Nat := 118140960795 + 363221 * 2 ^ 59
def prefixEnd_363221 : Nat := 4983230072969 + 3 ^ 40 * 363221 * 2
def baseEnd_363221 : Nat := 165783961606069893215185

theorem tailTrace_363221 : CollatzResearch.WordTrace tailWord_363221 prefixEnd_363221 165783961606069893215185 := by
  unfold tailWord_363221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247758217119825053193517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8831838811413216702129011 13247758217119825053193517)
  ·
    refine ⟨4967909331419934394947569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13247758217119825053193517 4967909331419934394947569)
    ·
      refine ⟨3725931998564950796210677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4967909331419934394947569 3725931998564950796210677)
      ·
        refine ⟨349306124865464137144751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3725931998564950796210677 349306124865464137144751)
        ·
          refine ⟨523959187298196205717127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349306124865464137144751 523959187298196205717127)
          ·
            refine ⟨785938780947294308575691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523959187298196205717127 785938780947294308575691)
            ·
              refine ⟨1178908171420941462863537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785938780947294308575691 1178908171420941462863537)
              ·
                refine ⟨884181128565706097147653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178908171420941462863537 884181128565706097147653)
                ·
                  refine ⟨165783961606069893215185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884181128565706097147653 165783961606069893215185)
                  ·
                    rfl

theorem cell20_363221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_363221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363221 prefixEnd_363221 := by exact prefixLift 363221
  have htrace : WordTrace (prefixWord ++ tailWord_363221) baseStart_363221 baseEnd_363221 := by
    simpa [prefixWord, tailWord_363221, baseEnd_363221] using wordTrace_append hprefix tailTrace_363221
  have hstable : (prefixWord ++ tailWord_363221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363221).length < 2 ^ (prefixWord ++ tailWord_363221).sum := by decide
  have hdescent : baseEnd_363221 < baseStart_363221 := by decide
  rcases family_descends (prefixWord ++ tailWord_363221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363225 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_363225 : Nat := 118140960795 + 363225 * 2 ^ 59
def prefixEnd_363225 : Nat := 4983230072969 + 3 ^ 40 * 363225 * 2
def baseEnd_363225 : Nat := 165785787315063657081835

theorem tailTrace_363225 : CollatzResearch.WordTrace tailWord_363225 prefixEnd_363225 165785787315063657081835 := by
  unfold tailWord_363225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247904109105333736339129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8831936072736889157559419 13247904109105333736339129)
  ·
    refine ⟨9935928081829000302254347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13247904109105333736339129 9935928081829000302254347)
    ·
      refine ⟨14903892122743500453381521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935928081829000302254347 14903892122743500453381521)
      ·
        refine ⟨11177919092057625340036141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14903892122743500453381521 11177919092057625340036141)
        ·
          refine ⟨4191719659521609502513553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11177919092057625340036141 4191719659521609502513553)
          ·
            refine ⟨3143789744641207126885165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191719659521609502513553 3143789744641207126885165)
            ·
              refine ⟨1178921154240452672581937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143789744641207126885165 1178921154240452672581937)
              ·
                refine ⟨884190865680339504436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178921154240452672581937 884190865680339504436453)
                ·
                  refine ⟨165785787315063657081835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884190865680339504436453 165785787315063657081835)
                  ·
                    rfl

theorem cell20_363225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_363225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363225 prefixEnd_363225 := by exact prefixLift 363225
  have htrace : WordTrace (prefixWord ++ tailWord_363225) baseStart_363225 baseEnd_363225 := by
    simpa [prefixWord, tailWord_363225, baseEnd_363225] using wordTrace_append hprefix tailTrace_363225
  have hstable : (prefixWord ++ tailWord_363225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363225).length < 2 ^ (prefixWord ++ tailWord_363225).sum := by decide
  have hdescent : baseEnd_363225 < baseStart_363225 := by decide
  rcases family_descends (prefixWord ++ tailWord_363225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363287 : List Nat := [1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_363287 : Nat := 118140960795 + 363287 * 2 ^ 59
def prefixEnd_363287 : Nat := 4983230072969 + 3 ^ 40 * 363287 * 2
def baseEnd_363287 : Nat := 55271361934822332338305

theorem tailTrace_363287 : CollatzResearch.WordTrace tailWord_363287 prefixEnd_363287 55271361934822332338305 := by
  unfold tailWord_363287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250165434880718325096115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8833443623253812216730743 13250165434880718325096115)
  ·
    refine ⟨19875248152321077487644173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13250165434880718325096115 19875248152321077487644173)
    ·
      refine ⟨7453218057120404057866565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19875248152321077487644173 7453218057120404057866565)
      ·
        refine ⟨1397478385710075760849981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7453218057120404057866565 1397478385710075760849981)
        ·
          refine ⟨524054394641278410318743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1397478385710075760849981 524054394641278410318743)
          ·
            refine ⟨786081591961917615478115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524054394641278410318743 786081591961917615478115)
            ·
              refine ⟨1179122387942876423217173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786081591961917615478115 1179122387942876423217173)
              ·
                refine ⟨55271361934822332338305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1179122387942876423217173 55271361934822332338305)
                ·
                  rfl

theorem cell20_363287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_363287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363287 prefixEnd_363287 := by exact prefixLift 363287
  have htrace : WordTrace (prefixWord ++ tailWord_363287) baseStart_363287 baseEnd_363287 := by
    simpa [prefixWord, tailWord_363287, baseEnd_363287] using wordTrace_append hprefix tailTrace_363287
  have hstable : (prefixWord ++ tailWord_363287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363287).length < 2 ^ (prefixWord ++ tailWord_363287).sum := by decide
  have hdescent : baseEnd_363287 < baseStart_363287 := by decide
  rcases family_descends (prefixWord ++ tailWord_363287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363293 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 2]
def baseStart_363293 : Nat := 118140960795 + 363293 * 2 ^ 59
def prefixEnd_363293 : Nat := 4983230072969 + 3 ^ 40 * 363293 * 2
def baseEnd_363293 : Nat := 165816824367957642814891

theorem tailTrace_363293 : CollatzResearch.WordTrace tailWord_363293 prefixEnd_363293 165816824367957642814891 := by
  unfold tailWord_363293
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250384272858981349814533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8833589515239320899876355 13250384272858981349814533)
  ·
    refine ⟨2484447051161059003090225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13250384272858981349814533 2484447051161059003090225)
    ·
      refine ⟨1863335288370794252317669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2484447051161059003090225 1863335288370794252317669)
      ·
        refine ⟨349375366569523922309563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1863335288370794252317669 349375366569523922309563)
        ·
          refine ⟨524063049854285883464345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349375366569523922309563 524063049854285883464345)
          ·
            refine ⟨393047287390714412598259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524063049854285883464345 393047287390714412598259)
            ·
              refine ⟨589570931086071618897389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393047287390714412598259 589570931086071618897389)
              ·
                refine ⟨221089099157276857086521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589570931086071618897389 221089099157276857086521)
                ·
                  refine ⟨165816824367957642814891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221089099157276857086521 165816824367957642814891)
                  ·
                    rfl

theorem cell20_363293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_363293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363293 prefixEnd_363293 := by exact prefixLift 363293
  have htrace : WordTrace (prefixWord ++ tailWord_363293) baseStart_363293 baseEnd_363293 := by
    simpa [prefixWord, tailWord_363293, baseEnd_363293] using wordTrace_append hprefix tailTrace_363293
  have hstable : (prefixWord ++ tailWord_363293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363293).length < 2 ^ (prefixWord ++ tailWord_363293).sum := by decide
  have hdescent : baseEnd_363293 < baseStart_363293 := by decide
  rcases family_descends (prefixWord ++ tailWord_363293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363346 : List Nat := [3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_363346 : Nat := 118140960795 + 363346 * 2 ^ 59
def prefixEnd_363346 : Nat := 4983230072969 + 3 ^ 40 * 363346 * 2
def baseEnd_363346 : Nat := 55280338337375004682669

theorem tailTrace_363346 : CollatzResearch.WordTrace tailWord_363346 prefixEnd_363346 55280338337375004682669 := by
  unfold tailWord_363346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313079335416742850373473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8834878227777980934329261 3313079335416742850373473)
  ·
    refine ⟨2484809501562557137780105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3313079335416742850373473 2484809501562557137780105)
    ·
      refine ⟨1863607126171917853335079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2484809501562557137780105 1863607126171917853335079)
      ·
        refine ⟨2795410689257876780002619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863607126171917853335079 2795410689257876780002619)
        ·
          refine ⟨4193116033886815170003929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795410689257876780002619 4193116033886815170003929)
          ·
            refine ⟨3144837025415111377502947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193116033886815170003929 3144837025415111377502947)
            ·
              refine ⟨4717255538122667066254421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144837025415111377502947 4717255538122667066254421)
              ·
                refine ⟨55280338337375004682669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4717255538122667066254421 55280338337375004682669)
                ·
                  rfl

theorem cell20_363346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_363346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363346 prefixEnd_363346 := by exact prefixLift 363346
  have htrace : WordTrace (prefixWord ++ tailWord_363346) baseStart_363346 baseEnd_363346 := by
    simpa [prefixWord, tailWord_363346, baseEnd_363346] using wordTrace_append hprefix tailTrace_363346
  have hstable : (prefixWord ++ tailWord_363346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363346).length < 2 ^ (prefixWord ++ tailWord_363346).sum := by decide
  have hdescent : baseEnd_363346 < baseStart_363346 := by decide
  rcases family_descends (prefixWord ++ tailWord_363346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363401 : List Nat := [1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_363401 : Nat := 118140960795 + 363401 * 2 ^ 59
def prefixEnd_363401 : Nat := 4983230072969 + 3 ^ 40 * 363401 * 2
def baseEnd_363401 : Nat := 55288706170263089071483

theorem tailTrace_363401 : CollatzResearch.WordTrace tailWord_363401 prefixEnd_363401 55288706170263089071483 := by
  unfold tailWord_363401
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254323356467715794746057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836215570978477196497371 13254323356467715794746057)
  ·
    refine ⟨9940742517350786846059543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13254323356467715794746057 9940742517350786846059543)
    ·
      refine ⟨14911113776026180269089315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9940742517350786846059543 14911113776026180269089315)
      ·
        refine ⟨22366670664039270403633973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911113776026180269089315 22366670664039270403633973)
        ·
          refine ⟨2096875374753681600340685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22366670664039270403633973 2096875374753681600340685)
          ·
            refine ⟨786328265532630600127757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2096875374753681600340685 786328265532630600127757)
            ·
              refine ⟨294873099574736475047909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786328265532630600127757 294873099574736475047909)
              ·
                refine ⟨55288706170263089071483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294873099574736475047909 55288706170263089071483)
                ·
                  rfl

theorem cell20_363401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_363401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363401 prefixEnd_363401 := by exact prefixLift 363401
  have htrace : WordTrace (prefixWord ++ tailWord_363401) baseStart_363401 baseEnd_363401 := by
    simpa [prefixWord, tailWord_363401, baseEnd_363401] using wordTrace_append hprefix tailTrace_363401
  have hstable : (prefixWord ++ tailWord_363401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363401).length < 2 ^ (prefixWord ++ tailWord_363401).sum := by decide
  have hdescent : baseEnd_363401 < baseStart_363401 := by decide
  rcases family_descends (prefixWord ++ tailWord_363401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363425 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_363425 : Nat := 118140960795 + 363425 * 2 ^ 59
def prefixEnd_363425 : Nat := 4983230072969 + 3 ^ 40 * 363425 * 2
def baseEnd_363425 : Nat := 165877072764751850414351

theorem tailTrace_363425 : CollatzResearch.WordTrace tailWord_363425 prefixEnd_363425 165877072764751850414351 := by
  unfold tailWord_363425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255198708380767893619729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836799138920511929079819 13255198708380767893619729)
  ·
    refine ⟨9941399031285575920214797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13255198708380767893619729 9941399031285575920214797)
    ·
      refine ⟨3728024636732090970080549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9941399031285575920214797 3728024636732090970080549)
      ·
        refine ⟨699004619387267056890103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3728024636732090970080549 699004619387267056890103)
        ·
          refine ⟨1048506929080900585335155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699004619387267056890103 1048506929080900585335155)
          ·
            refine ⟨1572760393621350878002733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048506929080900585335155 1572760393621350878002733)
            ·
              refine ⟨589785147608006579251025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572760393621350878002733 589785147608006579251025)
              ·
                refine ⟨442338860706004934438269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589785147608006579251025 442338860706004934438269)
                ·
                  refine ⟨165877072764751850414351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442338860706004934438269 165877072764751850414351)
                  ·
                    rfl

theorem cell20_363425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_363425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363425 prefixEnd_363425 := by exact prefixLift 363425
  have htrace : WordTrace (prefixWord ++ tailWord_363425) baseStart_363425 baseEnd_363425 := by
    simpa [prefixWord, tailWord_363425, baseEnd_363425] using wordTrace_append hprefix tailTrace_363425
  have hstable : (prefixWord ++ tailWord_363425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363425).length < 2 ^ (prefixWord ++ tailWord_363425).sum := by decide
  have hdescent : baseEnd_363425 < baseStart_363425 := by decide
  rcases family_descends (prefixWord ++ tailWord_363425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363436 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_363436 : Nat := 118140960795 + 363436 * 2 ^ 59
def prefixEnd_363436 : Nat := 4983230072969 + 3 ^ 40 * 363436 * 2
def baseEnd_363436 : Nat := 165882093464484701047639

theorem tailTrace_363436 : CollatzResearch.WordTrace tailWord_363436 prefixEnd_363436 165882093464484701047639 := by
  unfold tailWord_363436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627799955670458386135081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8837066607560611181513441 6627799955670458386135081)
  ·
    refine ⟨4970849966752843789601311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6627799955670458386135081 4970849966752843789601311)
    ·
      refine ⟨7456274950129265684401967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970849966752843789601311 7456274950129265684401967)
      ·
        refine ⟨11184412425193898526602951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456274950129265684401967 11184412425193898526602951)
        ·
          refine ⟨16776618637790847789904427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11184412425193898526602951 16776618637790847789904427)
          ·
            refine ⟨25164927956686271684856641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16776618637790847789904427 25164927956686271684856641)
            ·
              refine ⟨18873695967514703763642481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25164927956686271684856641 18873695967514703763642481)
              ·
                refine ⟨14155271975636027822731861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18873695967514703763642481 14155271975636027822731861)
                ·
                  refine ⟨165882093464484701047639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14155271975636027822731861 165882093464484701047639)
                  ·
                    rfl

theorem cell20_363436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_363436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363436 prefixEnd_363436 := by exact prefixLift 363436
  have htrace : WordTrace (prefixWord ++ tailWord_363436) baseStart_363436 baseEnd_363436 := by
    simpa [prefixWord, tailWord_363436, baseEnd_363436] using wordTrace_append hprefix tailTrace_363436
  have hstable : (prefixWord ++ tailWord_363436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363436).length < 2 ^ (prefixWord ++ tailWord_363436).sum := by decide
  have hdescent : baseEnd_363436 < baseStart_363436 := by decide
  rcases family_descends (prefixWord ++ tailWord_363436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363467 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_363467 : Nat := 118140960795 + 363467 * 2 ^ 59
def prefixEnd_363467 : Nat := 4983230072969 + 3 ^ 40 * 363467 * 2
def baseEnd_363467 : Nat := 165896242709186371014179

theorem tailTrace_363467 : CollatzResearch.WordTrace tailWord_363467 prefixEnd_363467 165896242709186371014179 := by
  unfold tailWord_363467
  simp only [CollatzResearch.WordTrace]
  refine ⟨13256730574228609066648655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8837820382819072711099103 13256730574228609066648655)
  ·
    refine ⟨19885095861342913599972983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13256730574228609066648655 19885095861342913599972983)
    ·
      refine ⟨29827643792014370399959475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19885095861342913599972983 29827643792014370399959475)
      ·
        refine ⟨44741465688021555599939213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29827643792014370399959475 44741465688021555599939213)
        ·
          refine ⟨16778049633008083349977205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44741465688021555599939213 16778049633008083349977205)
          ·
            refine ⟨1572942153094507814060363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16778049633008083349977205 1572942153094507814060363)
            ·
              refine ⟨2359413229641761721090545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572942153094507814060363 2359413229641761721090545)
              ·
                refine ⟨1769559922231321290817909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359413229641761721090545 1769559922231321290817909)
                ·
                  refine ⟨165896242709186371014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769559922231321290817909 165896242709186371014179)
                  ·
                    rfl

theorem cell20_363467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_363467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363467 prefixEnd_363467 := by exact prefixLift 363467
  have htrace : WordTrace (prefixWord ++ tailWord_363467) baseStart_363467 baseEnd_363467 := by
    simpa [prefixWord, tailWord_363467, baseEnd_363467] using wordTrace_append hprefix tailTrace_363467
  have hstable : (prefixWord ++ tailWord_363467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363467).length < 2 ^ (prefixWord ++ tailWord_363467).sum := by decide
  have hdescent : baseEnd_363467 < baseStart_363467 := by decide
  rcases family_descends (prefixWord ++ tailWord_363467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363477 : List Nat := [1, 3, 2, 3, 3, 2, 6]
def baseStart_363477 : Nat := 118140960795 + 363477 * 2 ^ 59
def prefixEnd_363477 : Nat := 4983230072969 + 3 ^ 40 * 363477 * 2
def baseEnd_363477 : Nat := 18433422997963420075645

theorem tailTrace_363477 : CollatzResearch.WordTrace tailWord_363477 prefixEnd_363477 18433422997963420075645 := by
  unfold tailWord_363477
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257095304192380774512685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8838063536128253849675123 13257095304192380774512685)
  ·
    refine ⟨4971410739072142790442257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13257095304192380774512685 4971410739072142790442257)
    ·
      refine ⟨3728558054304107092831693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4971410739072142790442257 3728558054304107092831693)
      ·
        refine ⟨1398209270364040159811885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3728558054304107092831693 1398209270364040159811885)
        ·
          refine ⟨524328476386515059929457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398209270364040159811885 524328476386515059929457)
          ·
            refine ⟨393246357289886294947093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524328476386515059929457 393246357289886294947093)
            ·
              refine ⟨18433422997963420075645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 393246357289886294947093 18433422997963420075645)
              ·
                rfl

theorem cell20_363477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_363477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363477 prefixEnd_363477 := by exact prefixLift 363477
  have htrace : WordTrace (prefixWord ++ tailWord_363477) baseStart_363477 baseEnd_363477 := by
    simpa [prefixWord, tailWord_363477, baseEnd_363477] using wordTrace_append hprefix tailTrace_363477
  have hstable : (prefixWord ++ tailWord_363477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363477).length < 2 ^ (prefixWord ++ tailWord_363477).sum := by decide
  have hdescent : baseEnd_363477 < baseStart_363477 := by decide
  rcases family_descends (prefixWord ++ tailWord_363477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363487 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 4]
def baseStart_363487 : Nat := 118140960795 + 363487 * 2 ^ 59
def prefixEnd_363487 : Nat := 4983230072969 + 3 ^ 40 * 363487 * 2
def baseEnd_363487 : Nat := 165905371254155190347431

theorem tailTrace_363487 : CollatzResearch.WordTrace tailWord_363487 prefixEnd_363487 165905371254155190347431 := by
  unfold tailWord_363487
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257460034156152482376715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8838306689437434988251143 13257460034156152482376715)
  ·
    refine ⟨19886190051234228723565073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13257460034156152482376715 19886190051234228723565073)
    ·
      refine ⟨14914642538425671542673805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19886190051234228723565073 14914642538425671542673805)
      ·
        refine ⟨5592990951909626828502677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14914642538425671542673805 5592990951909626828502677)
        ·
          refine ⟨262171450870763757586063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5592990951909626828502677 262171450870763757586063)
          ·
            refine ⟨393257176306145636379095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262171450870763757586063 393257176306145636379095)
            ·
              refine ⟨589885764459218454568643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393257176306145636379095 589885764459218454568643)
              ·
                refine ⟨884828646688827681852965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589885764459218454568643 884828646688827681852965)
                ·
                  refine ⟨165905371254155190347431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884828646688827681852965 165905371254155190347431)
                  ·
                    rfl

theorem cell20_363487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4].length) (baseStart_363487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363487 prefixEnd_363487 := by exact prefixLift 363487
  have htrace : WordTrace (prefixWord ++ tailWord_363487) baseStart_363487 baseEnd_363487 := by
    simpa [prefixWord, tailWord_363487, baseEnd_363487] using wordTrace_append hprefix tailTrace_363487
  have hstable : (prefixWord ++ tailWord_363487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363487).length < 2 ^ (prefixWord ++ tailWord_363487).sum := by decide
  have hdescent : baseEnd_363487 < baseStart_363487 := by decide
  rcases family_descends (prefixWord ++ tailWord_363487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363498 : List Nat := [3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_363498 : Nat := 118140960795 + 363498 * 2 ^ 59
def prefixEnd_363498 : Nat := 4983230072969 + 3 ^ 40 * 363498 * 2
def baseEnd_363498 : Nat := 55303463984629346993573

theorem tailTrace_363498 : CollatzResearch.WordTrace tailWord_363498 prefixEnd_363498 55303463984629346993573 := by
  unfold tailWord_363498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314465309279075340256787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8838574158077534240684765 3314465309279075340256787)
  ·
    refine ⟨4971697963918613010385181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314465309279075340256787 4971697963918613010385181)
    ·
      refine ⟨1864386736469479878894443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4971697963918613010385181 1864386736469479878894443)
      ·
        refine ⟨2796580104704219818341665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864386736469479878894443 2796580104704219818341665)
        ·
          refine ⟨2097435078528164863756249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796580104704219818341665 2097435078528164863756249)
          ·
            refine ⟨1573076308896123647817187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097435078528164863756249 1573076308896123647817187)
            ·
              refine ⟨2359614463344185471725781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573076308896123647817187 2359614463344185471725781)
              ·
                refine ⟨55303463984629346993573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2359614463344185471725781 55303463984629346993573)
                ·
                  rfl

theorem cell20_363498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_363498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363498 prefixEnd_363498 := by exact prefixLift 363498
  have htrace : WordTrace (prefixWord ++ tailWord_363498) baseStart_363498 baseEnd_363498 := by
    simpa [prefixWord, tailWord_363498, baseEnd_363498] using wordTrace_append hprefix tailTrace_363498
  have hstable : (prefixWord ++ tailWord_363498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363498).length < 2 ^ (prefixWord ++ tailWord_363498).sum := by decide
  have hdescent : baseEnd_363498 < baseStart_363498 := by decide
  rcases family_descends (prefixWord ++ tailWord_363498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363512 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_363512 : Nat := 118140960795 + 363512 * 2 ^ 59
def prefixEnd_363512 : Nat := 4983230072969 + 3 ^ 40 * 363512 * 2
def baseEnd_363512 : Nat := 165916781935366214513995

theorem tailTrace_363512 : CollatzResearch.WordTrace tailWord_363512 prefixEnd_363512 165916781935366214513995 := by
  unfold tailWord_363512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629185929532790876018395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8838914572710387834691193 6629185929532790876018395)
  ·
    refine ⟨9943778894299186314027593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629185929532790876018395 9943778894299186314027593)
    ·
      refine ⟨7457834170724389735520695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9943778894299186314027593 7457834170724389735520695)
      ·
        refine ⟨11186751256086584603281043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457834170724389735520695 11186751256086584603281043)
        ·
          refine ⟨16780126884129876904921565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11186751256086584603281043 16780126884129876904921565)
          ·
            refine ⟨6292547581548703839345587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16780126884129876904921565 6292547581548703839345587)
            ·
              refine ⟨9438821372323055759018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292547581548703839345587 9438821372323055759018381)
              ·
                refine ⟨3539558014621145909631893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9438821372323055759018381 3539558014621145909631893)
                ·
                  refine ⟨165916781935366214513995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3539558014621145909631893 165916781935366214513995)
                  ·
                    rfl

theorem cell20_363512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_363512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363512 prefixEnd_363512 := by exact prefixLift 363512
  have htrace : WordTrace (prefixWord ++ tailWord_363512) baseStart_363512 baseEnd_363512 := by
    simpa [prefixWord, tailWord_363512, baseEnd_363512] using wordTrace_append hprefix tailTrace_363512
  have hstable : (prefixWord ++ tailWord_363512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363512).length < 2 ^ (prefixWord ++ tailWord_363512).sum := by decide
  have hdescent : baseEnd_363512 < baseStart_363512 := by decide
  rcases family_descends (prefixWord ++ tailWord_363512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363546 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_363546 : Nat := 118140960795 + 363546 * 2 ^ 59
def prefixEnd_363546 : Nat := 4983230072969 + 3 ^ 40 * 363546 * 2
def baseEnd_363546 : Nat := 165932300461813207380523

theorem tailTrace_363546 : CollatzResearch.WordTrace tailWord_363546 prefixEnd_363546 165932300461813207380523 := by
  unfold tailWord_363546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314902985235601389693623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8839741293961603705849661 3314902985235601389693623)
  ·
    refine ⟨4972354477853402084540435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314902985235601389693623 4972354477853402084540435)
    ·
      refine ⟨7458531716780103126810653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972354477853402084540435 7458531716780103126810653)
      ·
        refine ⟨2796949393792538672553995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7458531716780103126810653 2796949393792538672553995)
        ·
          refine ⟨4195424090688808008830993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796949393792538672553995 4195424090688808008830993)
          ·
            refine ⟨3146568068016606006623245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195424090688808008830993 3146568068016606006623245)
            ·
              refine ⟨1179963025506227252483717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3146568068016606006623245 1179963025506227252483717)
              ·
                refine ⟨221243067282417609840697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1179963025506227252483717 221243067282417609840697)
                ·
                  refine ⟨165932300461813207380523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221243067282417609840697 165932300461813207380523)
                  ·
                    rfl

theorem cell20_363546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_363546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363546 prefixEnd_363546 := by exact prefixLift 363546
  have htrace : WordTrace (prefixWord ++ tailWord_363546) baseStart_363546 baseEnd_363546 := by
    simpa [prefixWord, tailWord_363546, baseEnd_363546] using wordTrace_append hprefix tailTrace_363546
  have hstable : (prefixWord ++ tailWord_363546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363546).length < 2 ^ (prefixWord ++ tailWord_363546).sum := by decide
  have hdescent : baseEnd_363546 < baseStart_363546 := by decide
  rcases family_descends (prefixWord ++ tailWord_363546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363553 : List Nat := [1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_363553 : Nat := 118140960795 + 363553 * 2 ^ 59
def prefixEnd_363553 : Nat := 4983230072969 + 3 ^ 40 * 363553 * 2
def baseEnd_363553 : Nat := 55311831817517431382387

theorem tailTrace_363553 : CollatzResearch.WordTrace tailWord_363553 prefixEnd_363553 55311831817517431382387 := by
  unfold tailWord_363553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259867251917045754279313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8839911501278030502852875 13259867251917045754279313)
  ·
    refine ⟨9944900438937784315709485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13259867251917045754279313 9944900438937784315709485)
    ·
      refine ⟨3729337664601669118391057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9944900438937784315709485 3729337664601669118391057)
      ·
        refine ⟨2797003248451251838793293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3729337664601669118391057 2797003248451251838793293)
        ·
          refine ⟨1048876218169219439547485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2797003248451251838793293 1048876218169219439547485)
          ·
            refine ⟨393328581813457289830307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1048876218169219439547485 393328581813457289830307)
            ·
              refine ⟨589992872720185934745461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393328581813457289830307 589992872720185934745461)
              ·
                refine ⟨55311831817517431382387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 589992872720185934745461 55311831817517431382387)
                ·
                  rfl

theorem cell20_363553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_363553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363553 prefixEnd_363553 := by exact prefixLift 363553
  have htrace : WordTrace (prefixWord ++ tailWord_363553) baseStart_363553 baseEnd_363553 := by
    simpa [prefixWord, tailWord_363553, baseEnd_363553] using wordTrace_append hprefix tailTrace_363553
  have hstable : (prefixWord ++ tailWord_363553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363553).length < 2 ^ (prefixWord ++ tailWord_363553).sum := by decide
  have hdescent : baseEnd_363553 < baseStart_363553 := by decide
  rcases family_descends (prefixWord ++ tailWord_363553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363584 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_363584 : Nat := 118140960795 + 363584 * 2 ^ 59
def prefixEnd_363584 : Nat := 4983230072969 + 3 ^ 40 * 363584 * 2
def baseEnd_363584 : Nat := 165949644697253964113701

theorem tailTrace_363584 : CollatzResearch.WordTrace tailWord_363584 prefixEnd_363584 165949644697253964113701 := by
  unfold tailWord_363584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630498957402369024328903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8840665276536492032438537 6630498957402369024328903)
  ·
    refine ⟨9945748436103553536493355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6630498957402369024328903 9945748436103553536493355)
    ·
      refine ⟨14918622654155330304740033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9945748436103553536493355 14918622654155330304740033)
      ·
        refine ⟨11188966990616497728555025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14918622654155330304740033 11188966990616497728555025)
        ·
          refine ⟨8391725242962373296416269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11188966990616497728555025 8391725242962373296416269)
          ·
            refine ⟨3146896966110889986156101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8391725242962373296416269 3146896966110889986156101)
            ·
              refine ⟨590043181145791872404269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3146896966110889986156101 590043181145791872404269)
              ·
                refine ⟨221266192929671952151601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590043181145791872404269 221266192929671952151601)
                ·
                  refine ⟨165949644697253964113701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221266192929671952151601 165949644697253964113701)
                  ·
                    rfl

theorem cell20_363584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_363584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363584 prefixEnd_363584 := by exact prefixLift 363584
  have htrace : WordTrace (prefixWord ++ tailWord_363584) baseStart_363584 baseEnd_363584 := by
    simpa [prefixWord, tailWord_363584, baseEnd_363584] using wordTrace_append hprefix tailTrace_363584
  have hstable : (prefixWord ++ tailWord_363584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363584).length < 2 ^ (prefixWord ++ tailWord_363584).sum := by decide
  have hdescent : baseEnd_363584 < baseStart_363584 := by decide
  rcases family_descends (prefixWord ++ tailWord_363584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363605 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_363605 : Nat := 118140960795 + 363605 * 2 ^ 59
def prefixEnd_363605 : Nat := 4983230072969 + 3 ^ 40 * 363605 * 2
def baseEnd_363605 : Nat := 165959229669471224413615

theorem tailTrace_363605 : CollatzResearch.WordTrace tailWord_363605 prefixEnd_363605 165959229669471224413615 := by
  unfold tailWord_363605
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261763847728658635172269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8841175898485772423448179 13261763847728658635172269)
  ·
    refine ⟨4973161442898246988189601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13261763847728658635172269 4973161442898246988189601)
    ·
      refine ⟨3729871082173685241142201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4973161442898246988189601 3729871082173685241142201)
      ·
        refine ⟨2797403311630263930856651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3729871082173685241142201 2797403311630263930856651)
        ·
          refine ⟨4196104967445395896284977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797403311630263930856651 4196104967445395896284977)
          ·
            refine ⟨3147078725584046922213733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4196104967445395896284977 3147078725584046922213733)
            ·
              refine ⟨590077261047008797915075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3147078725584046922213733 590077261047008797915075)
              ·
                refine ⟨885115891570513196872613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590077261047008797915075 885115891570513196872613)
                ·
                  refine ⟨165959229669471224413615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885115891570513196872613 165959229669471224413615)
                  ·
                    rfl

theorem cell20_363605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_363605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363605 prefixEnd_363605 := by exact prefixLift 363605
  have htrace : WordTrace (prefixWord ++ tailWord_363605) baseStart_363605 baseEnd_363605 := by
    simpa [prefixWord, tailWord_363605, baseEnd_363605] using wordTrace_append hprefix tailTrace_363605
  have hstable : (prefixWord ++ tailWord_363605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363605).length < 2 ^ (prefixWord ++ tailWord_363605).sum := by decide
  have hdescent : baseEnd_363605 < baseStart_363605 := by decide
  rcases family_descends (prefixWord ++ tailWord_363605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363612 : List Nat := [2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_363612 : Nat := 118140960795 + 363612 * 2 ^ 59
def prefixEnd_363612 : Nat := 4983230072969 + 3 ^ 40 * 363612 * 2
def baseEnd_363612 : Nat := 55320808220070103726751

theorem tailTrace_363612 : CollatzResearch.WordTrace tailWord_363612 prefixEnd_363612 55320808220070103726751 := by
  unfold tailWord_363612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631009579351649415338545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8841346105802199220451393 6631009579351649415338545)
  ·
    refine ⟨4973257184513737061503909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6631009579351649415338545 4973257184513737061503909)
    ·
      refine ⟨932485722096325699031983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4973257184513737061503909 932485722096325699031983)
      ·
        refine ⟨1398728583144488548547975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932485722096325699031983 1398728583144488548547975)
        ·
          refine ⟨2098092874716732822821963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398728583144488548547975 2098092874716732822821963)
          ·
            refine ⟨3147139312075099234232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098092874716732822821963 3147139312075099234232945)
            ·
              refine ⟨2360354484056324425674709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3147139312075099234232945 2360354484056324425674709)
              ·
                refine ⟨55320808220070103726751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2360354484056324425674709 55320808220070103726751)
                ·
                  rfl

theorem cell20_363612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_363612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363612 prefixEnd_363612 := by exact prefixLift 363612
  have htrace : WordTrace (prefixWord ++ tailWord_363612) baseStart_363612 baseEnd_363612 := by
    simpa [prefixWord, tailWord_363612, baseEnd_363612] using wordTrace_append hprefix tailTrace_363612
  have hstable : (prefixWord ++ tailWord_363612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363612).length < 2 ^ (prefixWord ++ tailWord_363612).sum := by decide
  have hdescent : baseEnd_363612 < baseStart_363612 := by decide
  rcases family_descends (prefixWord ++ tailWord_363612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363629 : List Nat := [1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_363629 : Nat := 118140960795 + 363629 * 2 ^ 59
def prefixEnd_363629 : Nat := 4983230072969 + 3 ^ 40 * 363629 * 2
def baseEnd_363629 : Nat := 55323394641144602537839

theorem tailTrace_363629 : CollatzResearch.WordTrace tailWord_363629 prefixEnd_363629 55323394641144602537839 := by
  unfold tailWord_363629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262639199641710734045941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8841759466427807156030627 13262639199641710734045941)
  ·
    refine ⟨1243372424966410381316807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13262639199641710734045941 1243372424966410381316807)
    ·
      refine ⟨1865058637449615571975211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243372424966410381316807 1865058637449615571975211)
      ·
        refine ⟨2797587956174423357962817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865058637449615571975211 2797587956174423357962817)
        ·
          refine ⟨2098190967130817518472113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797587956174423357962817 2098190967130817518472113)
          ·
            refine ⟨1573643225348113138854085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098190967130817518472113 1573643225348113138854085)
            ·
              refine ⟨295058104752771213535141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1573643225348113138854085 295058104752771213535141)
              ·
                refine ⟨55323394641144602537839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295058104752771213535141 55323394641144602537839)
                ·
                  rfl

theorem cell20_363629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_363629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363629 prefixEnd_363629 := by exact prefixLift 363629
  have htrace : WordTrace (prefixWord ++ tailWord_363629) baseStart_363629 baseEnd_363629 := by
    simpa [prefixWord, tailWord_363629, baseEnd_363629] using wordTrace_append hprefix tailTrace_363629
  have hstable : (prefixWord ++ tailWord_363629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363629).length < 2 ^ (prefixWord ++ tailWord_363629).sum := by decide
  have hdescent : baseEnd_363629 < baseStart_363629 := by decide
  rcases family_descends (prefixWord ++ tailWord_363629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363656 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_363656 : Nat := 118140960795 + 363656 * 2 ^ 59
def prefixEnd_363656 : Nat := 4983230072969 + 3 ^ 40 * 363656 * 2
def baseEnd_363656 : Nat := 165982507459141713713407

theorem tailTrace_363656 : CollatzResearch.WordTrace tailWord_363656 prefixEnd_363656 165982507459141713713407 := by
  unfold tailWord_363656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631811985271947172639411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8842415980362596230185881 6631811985271947172639411)
  ·
    refine ⟨9947717977907920758959117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631811985271947172639411 9947717977907920758959117)
    ·
      refine ⟨3730394241715470284609669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9947717977907920758959117 3730394241715470284609669)
      ·
        refine ⟨699448920321650678364313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3730394241715470284609669 699448920321650678364313)
        ·
          refine ⟨524586690241238008773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699448920321650678364313 524586690241238008773235)
          ·
            refine ⟨786880035361857013159853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524586690241238008773235 786880035361857013159853)
            ·
              refine ⟨295080013260696379934945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786880035361857013159853 295080013260696379934945)
              ·
                refine ⟨221310009945522284951209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295080013260696379934945 221310009945522284951209)
                ·
                  refine ⟨165982507459141713713407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221310009945522284951209 165982507459141713713407)
                  ·
                    rfl

theorem cell20_363656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_363656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363656 prefixEnd_363656 := by exact prefixLift 363656
  have htrace : WordTrace (prefixWord ++ tailWord_363656) baseStart_363656 baseEnd_363656 := by
    simpa [prefixWord, tailWord_363656, baseEnd_363656] using wordTrace_append hprefix tailTrace_363656
  have hstable : (prefixWord ++ tailWord_363656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363656).length < 2 ^ (prefixWord ++ tailWord_363656).sum := by decide
  have hdescent : baseEnd_363656 < baseStart_363656 := by decide
  rcases family_descends (prefixWord ++ tailWord_363656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363657 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_363657 : Nat := 118140960795 + 363657 * 2 ^ 59
def prefixEnd_363657 : Nat := 4983230072969 + 3 ^ 40 * 363657 * 2
def baseEnd_363657 : Nat := 165982963886390154680069

theorem tailTrace_363657 : CollatzResearch.WordTrace tailWord_363657 prefixEnd_363657 165982963886390154680069 := by
  unfold tailWord_363657
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263660443540271516065225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8842440295693514344043483 13263660443540271516065225)
  ·
    refine ⟨9947745332655203637048919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13263660443540271516065225 9947745332655203637048919)
    ·
      refine ⟨14921617998982805455573379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947745332655203637048919 14921617998982805455573379)
      ·
        refine ⟨22382426998474208183360069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921617998982805455573379 22382426998474208183360069)
        ·
          refine ⟨4196705062213914034380013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22382426998474208183360069 4196705062213914034380013)
          ·
            refine ⟨1573764398330217762892505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4196705062213914034380013 1573764398330217762892505)
            ·
              refine ⟨1180323298747663322169379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573764398330217762892505 1180323298747663322169379)
              ·
                refine ⟨1770484948121494983254069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180323298747663322169379 1770484948121494983254069)
                ·
                  refine ⟨165982963886390154680069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1770484948121494983254069 165982963886390154680069)
                  ·
                    rfl

theorem cell20_363657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_363657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363657 prefixEnd_363657 := by exact prefixLift 363657
  have htrace : WordTrace (prefixWord ++ tailWord_363657) baseStart_363657 baseEnd_363657 := by
    simpa [prefixWord, tailWord_363657, baseEnd_363657] using wordTrace_append hprefix tailTrace_363657
  have hstable : (prefixWord ++ tailWord_363657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363657).length < 2 ^ (prefixWord ++ tailWord_363657).sum := by decide
  have hdescent : baseEnd_363657 < baseStart_363657 := by decide
  rcases family_descends (prefixWord ++ tailWord_363657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363664 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_363664 : Nat := 118140960795 + 363664 * 2 ^ 59
def prefixEnd_363664 : Nat := 4983230072969 + 3 ^ 40 * 363664 * 2
def baseEnd_363664 : Nat := 165986158877129241446707

theorem tailTrace_363664 : CollatzResearch.WordTrace tailWord_363664 prefixEnd_363664 165986158877129241446707 := by
  unfold tailWord_363664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631957877257455855785023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8842610503009941141046697 6631957877257455855785023)
  ·
    refine ⟨9947936815886183783677535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631957877257455855785023 9947936815886183783677535)
    ·
      refine ⟨14921905223829275675516303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947936815886183783677535 14921905223829275675516303)
      ·
        refine ⟨22382857835743913513274455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921905223829275675516303 22382857835743913513274455)
        ·
          refine ⟨33574286753615870269911683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22382857835743913513274455 33574286753615870269911683)
          ·
            refine ⟨50361430130423805404867525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33574286753615870269911683 50361430130423805404867525)
            ·
              refine ⟨9442768149454463513412661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50361430130423805404867525 9442768149454463513412661)
              ·
                refine ⟨885259514011355954382437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9442768149454463513412661 885259514011355954382437)
                ·
                  refine ⟨165986158877129241446707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885259514011355954382437 165986158877129241446707)
                  ·
                    rfl

theorem cell20_363664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_363664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363664 prefixEnd_363664 := by exact prefixLift 363664
  have htrace : WordTrace (prefixWord ++ tailWord_363664) baseStart_363664 baseEnd_363664 := by
    simpa [prefixWord, tailWord_363664, baseEnd_363664] using wordTrace_append hprefix tailTrace_363664
  have hstable : (prefixWord ++ tailWord_363664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363664).length < 2 ^ (prefixWord ++ tailWord_363664).sum := by decide
  have hdescent : baseEnd_363664 < baseStart_363664 := by decide
  rcases family_descends (prefixWord ++ tailWord_363664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363718 : List Nat := [6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_363718 : Nat := 118140960795 + 363718 * 2 ^ 59
def prefixEnd_363718 : Nat := 4983230072969 + 3 ^ 40 * 363718 * 2
def baseEnd_363718 : Nat := 55336935316181684548829

theorem tailTrace_363718 : CollatzResearch.WordTrace tailWord_363718 prefixEnd_363718 55336935316181684548829 := by
  unfold tailWord_363718
  simp only [CollatzResearch.WordTrace]
  refine ⟨414558915509977466688619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8843923530879519289357205 414558915509977466688619)
  ·
    refine ⟨621838373264966200032929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414558915509977466688619 621838373264966200032929)
    ·
      refine ⟨466378779948724650024697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621838373264966200032929 466378779948724650024697)
      ·
        refine ⟨349784084961543487518523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466378779948724650024697 349784084961543487518523)
        ·
          refine ⟨524676127442315231277785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349784084961543487518523 524676127442315231277785)
          ·
            refine ⟨393507095581736423458339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524676127442315231277785 393507095581736423458339)
            ·
              refine ⟨590260643372604635187509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393507095581736423458339 590260643372604635187509)
              ·
                refine ⟨55336935316181684548829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 590260643372604635187509 55336935316181684548829)
                ·
                  rfl

theorem cell20_363718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_363718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363718 prefixEnd_363718 := by exact prefixLift 363718
  have htrace : WordTrace (prefixWord ++ tailWord_363718) baseStart_363718 baseEnd_363718 := by
    simpa [prefixWord, tailWord_363718, baseEnd_363718] using wordTrace_append hprefix tailTrace_363718
  have hstable : (prefixWord ++ tailWord_363718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363718).length < 2 ^ (prefixWord ++ tailWord_363718).sum := by decide
  have hdescent : baseEnd_363718 < baseStart_363718 := by decide
  rcases family_descends (prefixWord ++ tailWord_363718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363774 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_363774 : Nat := 118140960795 + 363774 * 2 ^ 59
def prefixEnd_363774 : Nat := 4983230072969 + 3 ^ 40 * 363774 * 2
def baseEnd_363774 : Nat := 166036365874457747779591

theorem tailTrace_363774 : CollatzResearch.WordTrace tailWord_363774 prefixEnd_363774 166036365874457747779591 := by
  unfold tailWord_363774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658490973014550062259297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8845285189410933665382917 1658490973014550062259297)
  ·
    refine ⟨1243868229760912546694473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1658490973014550062259297 1243868229760912546694473)
    ·
      refine ⟨932901172320684410020855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243868229760912546694473 932901172320684410020855)
      ·
        refine ⟨1399351758481026615031283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932901172320684410020855 1399351758481026615031283)
        ·
          refine ⟨2099027637721539922546925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399351758481026615031283 2099027637721539922546925)
          ·
            refine ⟨787135364145577470955097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2099027637721539922546925 787135364145577470955097)
            ·
              refine ⟨590351523109183103216323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787135364145577470955097 590351523109183103216323)
              ·
                refine ⟨885527284663774654824485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590351523109183103216323 885527284663774654824485)
                ·
                  refine ⟨166036365874457747779591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885527284663774654824485 166036365874457747779591)
                  ·
                    rfl

theorem cell20_363774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_363774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363774 prefixEnd_363774 := by exact prefixLift 363774
  have htrace : WordTrace (prefixWord ++ tailWord_363774) baseStart_363774 baseEnd_363774 := by
    simpa [prefixWord, tailWord_363774, baseEnd_363774] using wordTrace_append hprefix tailTrace_363774
  have hstable : (prefixWord ++ tailWord_363774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363774).length < 2 ^ (prefixWord ++ tailWord_363774).sum := by decide
  have hdescent : baseEnd_363774 < baseStart_363774 := by decide
  rcases family_descends (prefixWord ++ tailWord_363774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363785 : List Nat := [1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_363785 : Nat := 118140960795 + 363785 * 2 ^ 59
def prefixEnd_363785 : Nat := 4983230072969 + 3 ^ 40 * 363785 * 2
def baseEnd_363785 : Nat := 55347128858063532804293

theorem tailTrace_363785 : CollatzResearch.WordTrace tailWord_363785 prefixEnd_363785 55347128858063532804293 := by
  unfold tailWord_363785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268328987076549376724809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8845552658051032917816539 13268328987076549376724809)
  ·
    refine ⟨9951246740307412032543607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13268328987076549376724809 9951246740307412032543607)
    ·
      refine ⟨14926870110461118048815411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951246740307412032543607 14926870110461118048815411)
      ·
        refine ⟨22390305165691677073223117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926870110461118048815411 22390305165691677073223117)
        ·
          refine ⟨8396364437134378902458669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22390305165691677073223117 8396364437134378902458669)
          ·
            refine ⟨3148636663925392088422001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8396364437134378902458669 3148636663925392088422001)
            ·
              refine ⟨2361477497944044066316501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148636663925392088422001 2361477497944044066316501)
              ·
                refine ⟨55347128858063532804293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2361477497944044066316501 55347128858063532804293)
                ·
                  rfl

theorem cell20_363785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_363785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363785 prefixEnd_363785 := by exact prefixLift 363785
  have htrace : WordTrace (prefixWord ++ tailWord_363785) baseStart_363785 baseEnd_363785 := by
    simpa [prefixWord, tailWord_363785, baseEnd_363785] using wordTrace_append hprefix tailTrace_363785
  have hstable : (prefixWord ++ tailWord_363785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363785).length < 2 ^ (prefixWord ++ tailWord_363785).sum := by decide
  have hdescent : baseEnd_363785 < baseStart_363785 := by decide
  rcases family_descends (prefixWord ++ tailWord_363785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363794 : List Nat := [3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_363794 : Nat := 118140960795 + 363794 * 2 ^ 59
def prefixEnd_363794 : Nat := 4983230072969 + 3 ^ 40 * 363794 * 2
def baseEnd_363794 : Nat := 55348498139808855704281

theorem tailTrace_363794 : CollatzResearch.WordTrace tailWord_363794 prefixEnd_363794 55348498139808855704281 := by
  unfold tailWord_363794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317164311010985978450609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8845771496029295942534957 3317164311010985978450609)
  ·
    refine ⟨2487873233258239483837957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317164311010985978450609 2487873233258239483837957)
    ·
      refine ⟨466476231235919903219617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2487873233258239483837957 466476231235919903219617)
      ·
        refine ⟨349857173426939927414713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466476231235919903219617 349857173426939927414713)
        ·
          refine ⟨262392880070204945561035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349857173426939927414713 262392880070204945561035)
          ·
            refine ⟨393589320105307418341553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262392880070204945561035 393589320105307418341553)
            ·
              refine ⟨295191990078980563756165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393589320105307418341553 295191990078980563756165)
              ·
                refine ⟨55348498139808855704281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295191990078980563756165 55348498139808855704281)
                ·
                  rfl

theorem cell20_363794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_363794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363794 prefixEnd_363794 := by exact prefixLift 363794
  have htrace : WordTrace (prefixWord ++ tailWord_363794) baseStart_363794 baseEnd_363794 := by
    simpa [prefixWord, tailWord_363794, baseEnd_363794] using wordTrace_append hprefix tailTrace_363794
  have hstable : (prefixWord ++ tailWord_363794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363794).length < 2 ^ (prefixWord ++ tailWord_363794).sum := by decide
  have hdescent : baseEnd_363794 < baseStart_363794 := by decide
  rcases family_descends (prefixWord ++ tailWord_363794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363802 : List Nat := [3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_363802 : Nat := 118140960795 + 363802 * 2 ^ 59
def prefixEnd_363802 : Nat := 4983230072969 + 3 ^ 40 * 363802 * 2
def baseEnd_363802 : Nat := 55349715279138031615381

theorem tailTrace_363802 : CollatzResearch.WordTrace tailWord_363802 prefixEnd_363802 55349715279138031615381 := by
  unfold tailWord_363802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317237257003740320023415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8845966018676640853395773 3317237257003740320023415)
  ·
    refine ⟨4975855885505610480035123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3317237257003740320023415 4975855885505610480035123)
    ·
      refine ⟨7463783828258415720052685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4975855885505610480035123 7463783828258415720052685)
      ·
        refine ⟨2798918935596905895019757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7463783828258415720052685 2798918935596905895019757)
        ·
          refine ⟨1049594600848839710632409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2798918935596905895019757 1049594600848839710632409)
          ·
            refine ⟨787195950636629782974307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049594600848839710632409 787195950636629782974307)
            ·
              refine ⟨1180793925954944674461461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787195950636629782974307 1180793925954944674461461)
              ·
                refine ⟨55349715279138031615381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1180793925954944674461461 55349715279138031615381)
                ·
                  rfl

theorem cell20_363802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_363802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363802 prefixEnd_363802 := by exact prefixLift 363802
  have htrace : WordTrace (prefixWord ++ tailWord_363802) baseStart_363802 baseEnd_363802 := by
    simpa [prefixWord, tailWord_363802, baseEnd_363802] using wordTrace_append hprefix tailTrace_363802
  have hstable : (prefixWord ++ tailWord_363802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363802).length < 2 ^ (prefixWord ++ tailWord_363802).sum := by decide
  have hdescent : baseEnd_363802 < baseStart_363802 := by decide
  rcases family_descends (prefixWord ++ tailWord_363802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363808 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_363808 : Nat := 118140960795 + 363808 * 2 ^ 59
def prefixEnd_363808 : Nat := 4983230072969 + 3 ^ 40 * 363808 * 2
def baseEnd_363808 : Nat := 166051884400904740646119

theorem tailTrace_363808 : CollatzResearch.WordTrace tailWord_363808 prefixEnd_363808 166051884400904740646119 := by
  unfold tailWord_363808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634583932996612152406039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8846111910662149536541385 6634583932996612152406039)
  ·
    refine ⟨9951875899494918228609059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634583932996612152406039 9951875899494918228609059)
    ·
      refine ⟨14927813849242377342913589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951875899494918228609059 14927813849242377342913589)
      ·
        refine ⟨1399482548366472875898149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14927813849242377342913589 1399482548366472875898149)
        ·
          refine ⟨262402977818713664230903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1399482548366472875898149 262402977818713664230903)
          ·
            refine ⟨393604466728070496346355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262402977818713664230903 393604466728070496346355)
            ·
              refine ⟨590406700092105744519533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393604466728070496346355 590406700092105744519533)
              ·
                refine ⟨221402512534539654194825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590406700092105744519533 221402512534539654194825)
                ·
                  refine ⟨166051884400904740646119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221402512534539654194825 166051884400904740646119)
                  ·
                    rfl

theorem cell20_363808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_363808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363808 prefixEnd_363808 := by exact prefixLift 363808
  have htrace : WordTrace (prefixWord ++ tailWord_363808) baseStart_363808 baseEnd_363808 := by
    simpa [prefixWord, tailWord_363808, baseEnd_363808] using wordTrace_append hprefix tailTrace_363808
  have hstable : (prefixWord ++ tailWord_363808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363808).length < 2 ^ (prefixWord ++ tailWord_363808).sum := by decide
  have hdescent : baseEnd_363808 < baseStart_363808 := by decide
  rcases family_descends (prefixWord ++ tailWord_363808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363829 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 2]
def baseStart_363829 : Nat := 118140960795 + 363829 * 2 ^ 59
def prefixEnd_363829 : Nat := 4983230072969 + 3 ^ 40 * 363829 * 2
def baseEnd_363829 : Nat := 166061469373122000946033

theorem tailTrace_363829 : CollatzResearch.WordTrace tailWord_363829 prefixEnd_363829 166061469373122000946033 := by
  unfold tailWord_363829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269933798917144891326541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8846622532611429927551027 13269933798917144891326541)
  ·
    refine ⟨4976225174593929334247453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13269933798917144891326541 4976225174593929334247453)
    ·
      refine ⟨1866084440472723500342795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4976225174593929334247453 1866084440472723500342795)
      ·
        refine ⟨2799126660709085250514193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866084440472723500342795 2799126660709085250514193)
        ·
          refine ⟨2099344995531813937885645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799126660709085250514193 2099344995531813937885645)
          ·
            refine ⟨787254373324430226707117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2099344995531813937885645 787254373324430226707117)
            ·
              refine ⟨295220389996661335015169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787254373324430226707117 295220389996661335015169)
              ·
                refine ⟨221415292497496001261377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295220389996661335015169 221415292497496001261377)
                ·
                  refine ⟨166061469373122000946033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221415292497496001261377 166061469373122000946033)
                  ·
                    rfl

theorem cell20_363829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_363829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363829 prefixEnd_363829 := by exact prefixLift 363829
  have htrace : WordTrace (prefixWord ++ tailWord_363829) baseStart_363829 baseEnd_363829 := by
    simpa [prefixWord, tailWord_363829, baseEnd_363829] using wordTrace_append hprefix tailTrace_363829
  have hstable : (prefixWord ++ tailWord_363829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363829).length < 2 ^ (prefixWord ++ tailWord_363829).sum := by decide
  have hdescent : baseEnd_363829 < baseStart_363829 := by decide
  rcases family_descends (prefixWord ++ tailWord_363829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363854 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_363854 : Nat := 118140960795 + 363854 * 2 ^ 59
def prefixEnd_363854 : Nat := 4983230072969 + 3 ^ 40 * 363854 * 2
def baseEnd_363854 : Nat := 166072880054333025112597

theorem tailTrace_363854 : CollatzResearch.WordTrace tailWord_363854 prefixEnd_363854 166072880054333025112597 := by
  unfold tailWord_363854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658855702978321770123327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8847230415884382773991077 1658855702978321770123327)
  ·
    refine ⟨2488283554467482655184991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1658855702978321770123327 2488283554467482655184991)
    ·
      refine ⟨3732425331701223982777487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488283554467482655184991 3732425331701223982777487)
      ·
        refine ⟨5598637997551835974166231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732425331701223982777487 5598637997551835974166231)
        ·
          refine ⟨8397956996327753961249347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598637997551835974166231 8397956996327753961249347)
          ·
            refine ⟨12596935494491630941874021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8397956996327753961249347 12596935494491630941874021)
            ·
              refine ⟨2361925405217180801601379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12596935494491630941874021 2361925405217180801601379)
              ·
                refine ⟨3542888107825771202402069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361925405217180801601379 3542888107825771202402069)
                ·
                  refine ⟨166072880054333025112597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3542888107825771202402069 166072880054333025112597)
                  ·
                    rfl

theorem cell20_363854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_363854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363854 prefixEnd_363854 := by exact prefixLift 363854
  have htrace : WordTrace (prefixWord ++ tailWord_363854) baseStart_363854 baseEnd_363854 := by
    simpa [prefixWord, tailWord_363854, baseEnd_363854] using wordTrace_append hprefix tailTrace_363854
  have hstable : (prefixWord ++ tailWord_363854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363854).length < 2 ^ (prefixWord ++ tailWord_363854).sum := by decide
  have hdescent : baseEnd_363854 < baseStart_363854 := by decide
  rcases family_descends (prefixWord ++ tailWord_363854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363871 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 2]
def baseStart_363871 : Nat := 118140960795 + 363871 * 2 ^ 59
def prefixEnd_363871 : Nat := 4983230072969 + 3 ^ 40 * 363871 * 2
def baseEnd_363871 : Nat := 166080639317556521545861

theorem tailTrace_363871 : CollatzResearch.WordTrace tailWord_363871 prefixEnd_363871 166080639317556521545861 := by
  unfold tailWord_363871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271465664764986064355467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8847643776509990709570311 13271465664764986064355467)
  ·
    refine ⟨19907198497147479096533201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271465664764986064355467 19907198497147479096533201)
    ·
      refine ⟨14930398872860609322399901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19907198497147479096533201 14930398872860609322399901)
      ·
        refine ⟨5598899577322728495899963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14930398872860609322399901 5598899577322728495899963)
        ·
          refine ⟨8398349365984092743849945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598899577322728495899963 8398349365984092743849945)
          ·
            refine ⟨6298762024488069557887459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8398349365984092743849945 6298762024488069557887459)
            ·
              refine ⟨9448143036732104336831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298762024488069557887459 9448143036732104336831189)
              ·
                refine ⟨221440852423408695394481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9448143036732104336831189 221440852423408695394481)
                ·
                  refine ⟨166080639317556521545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221440852423408695394481 166080639317556521545861)
                  ·
                    rfl

theorem cell20_363871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2].length) (baseStart_363871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363871 prefixEnd_363871 := by exact prefixLift 363871
  have htrace : WordTrace (prefixWord ++ tailWord_363871) baseStart_363871 baseEnd_363871 := by
    simpa [prefixWord, tailWord_363871, baseEnd_363871] using wordTrace_append hprefix tailTrace_363871
  have hstable : (prefixWord ++ tailWord_363871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363871).length < 2 ^ (prefixWord ++ tailWord_363871).sum := by decide
  have hdescent : baseEnd_363871 < baseStart_363871 := by decide
  rcases family_descends (prefixWord ++ tailWord_363871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363916 : List Nat := [2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_363916 : Nat := 118140960795 + 363916 * 2 ^ 59
def prefixEnd_363916 : Nat := 4983230072969 + 3 ^ 40 * 363916 * 2
def baseEnd_363916 : Nat := 55367059514578788348559

theorem tailTrace_363916 : CollatzResearch.WordTrace tailWord_363916 prefixEnd_363916 55367059514578788348559 := by
  unfold tailWord_363916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636553474800979374871801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8848737966401305833162401 6636553474800979374871801)
  ·
    refine ⟨4977415106100734531153851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6636553474800979374871801 4977415106100734531153851)
    ·
      refine ⟨7466122659151101796730777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977415106100734531153851 7466122659151101796730777)
      ·
        refine ⟨5599591994363326347548083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466122659151101796730777 5599591994363326347548083)
        ·
          refine ⟨8399387991544989521322125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599591994363326347548083 8399387991544989521322125)
          ·
            refine ⟨3149770496829371070495797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8399387991544989521322125 3149770496829371070495797)
            ·
              refine ⟨295290984077753537858981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3149770496829371070495797 295290984077753537858981)
              ·
                refine ⟨55367059514578788348559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295290984077753537858981 55367059514578788348559)
                ·
                  rfl

theorem cell20_363916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_363916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363916 prefixEnd_363916 := by exact prefixLift 363916
  have htrace : WordTrace (prefixWord ++ tailWord_363916) baseStart_363916 baseEnd_363916 := by
    simpa [prefixWord, tailWord_363916, baseEnd_363916] using wordTrace_append hprefix tailTrace_363916
  have hstable : (prefixWord ++ tailWord_363916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363916).length < 2 ^ (prefixWord ++ tailWord_363916).sum := by decide
  have hdescent : baseEnd_363916 < baseStart_363916 := by decide
  rcases family_descends (prefixWord ++ tailWord_363916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363922 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_363922 : Nat := 118140960795 + 363922 * 2 ^ 59
def prefixEnd_363922 : Nat := 4983230072969 + 3 ^ 40 * 363922 * 2
def baseEnd_363922 : Nat := 166103917107227010845653

theorem tailTrace_363922 : CollatzResearch.WordTrace tailWord_363922 prefixEnd_363922 166103917107227010845653 := by
  unfold tailWord_363922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318331446895055443615505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8848883858386814516308013 3318331446895055443615505)
  ·
    refine ⟨2488748585171291582711629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3318331446895055443615505 2488748585171291582711629)
    ·
      refine ⟨933280719439234343516861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2488748585171291582711629 933280719439234343516861)
      ·
        refine ⟨349980269789712878818823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 933280719439234343516861 349980269789712878818823)
        ·
          refine ⟨524970404684569318228235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349980269789712878818823 524970404684569318228235)
          ·
            refine ⟨787455607026853977342353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524970404684569318228235 787455607026853977342353)
            ·
              refine ⟨590591705270140483006765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787455607026853977342353 590591705270140483006765)
              ·
                refine ⟨221471889476302681127537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590591705270140483006765 221471889476302681127537)
                ·
                  refine ⟨166103917107227010845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221471889476302681127537 166103917107227010845653)
                  ·
                    rfl

theorem cell20_363922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_363922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363922 prefixEnd_363922 := by exact prefixLift 363922
  have htrace : WordTrace (prefixWord ++ tailWord_363922) baseStart_363922 baseEnd_363922 := by
    simpa [prefixWord, tailWord_363922, baseEnd_363922] using wordTrace_append hprefix tailTrace_363922
  have hstable : (prefixWord ++ tailWord_363922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363922).length < 2 ^ (prefixWord ++ tailWord_363922).sum := by decide
  have hdescent : baseEnd_363922 < baseStart_363922 := by decide
  rcases family_descends (prefixWord ++ tailWord_363922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363930 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_363930 : Nat := 118140960795 + 363930 * 2 ^ 59
def prefixEnd_363930 : Nat := 4983230072969 + 3 ^ 40 * 363930 * 2
def baseEnd_363930 : Nat := 166107568525214538578953

theorem tailTrace_363930 : CollatzResearch.WordTrace tailWord_363930 prefixEnd_363930 166107568525214538578953 := by
  unfold tailWord_363930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318404392887809785188311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8849078381034159427168829 3318404392887809785188311)
  ·
    refine ⟨4977606589331714677782467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318404392887809785188311 4977606589331714677782467)
    ·
      refine ⟨7466409883997572016673701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977606589331714677782467 7466409883997572016673701)
      ·
        refine ⟨1399951853249544753126319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7466409883997572016673701 1399951853249544753126319)
        ·
          refine ⟨2099927779874317129689479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399951853249544753126319 2099927779874317129689479)
          ·
            refine ⟨3149891669811475694534219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099927779874317129689479 3149891669811475694534219)
            ·
              refine ⟨4724837504717213541801329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149891669811475694534219 4724837504717213541801329)
              ·
                refine ⟨3543628128537910156350997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724837504717213541801329 3543628128537910156350997)
                ·
                  refine ⟨166107568525214538578953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3543628128537910156350997 166107568525214538578953)
                  ·
                    rfl

theorem cell20_363930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_363930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363930 prefixEnd_363930 := by exact prefixLift 363930
  have htrace : WordTrace (prefixWord ++ tailWord_363930) baseStart_363930 baseEnd_363930 := by
    simpa [prefixWord, tailWord_363930, baseEnd_363930] using wordTrace_append hprefix tailTrace_363930
  have hstable : (prefixWord ++ tailWord_363930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363930).length < 2 ^ (prefixWord ++ tailWord_363930).sum := by decide
  have hdescent : baseEnd_363930 < baseStart_363930 := by decide
  rcases family_descends (prefixWord ++ tailWord_363930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363957 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_363957 : Nat := 118140960795 + 363957 * 2 ^ 59
def prefixEnd_363957 : Nat := 4983230072969 + 3 ^ 40 * 363957 * 2
def baseEnd_363957 : Nat := 166119892060922444678843

theorem tailTrace_363957 : CollatzResearch.WordTrace tailWord_363957 prefixEnd_363957 166119892060922444678843 := by
  unfold tailWord_363957
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274602342453422751986125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8849734894968948501324083 13274602342453422751986125)
  ·
    refine ⟨4977975878420033531994797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13274602342453422751986125 4977975878420033531994797)
    ·
      refine ⟨1866740954407512574498049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4977975878420033531994797 1866740954407512574498049)
      ·
        refine ⟨1400055715805634430873537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1866740954407512574498049 1400055715805634430873537)
        ·
          refine ⟨1050041786854225823155153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400055715805634430873537 1050041786854225823155153)
          ·
            refine ⟨787531340140669367366365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050041786854225823155153 787531340140669367366365)
            ·
              refine ⟨295324252552751012762387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787531340140669367366365 295324252552751012762387)
              ·
                refine ⟨442986378829126519143581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295324252552751012762387 442986378829126519143581)
                ·
                  refine ⟨166119892060922444678843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442986378829126519143581 166119892060922444678843)
                  ·
                    rfl

theorem cell20_363957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_363957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363957 prefixEnd_363957 := by exact prefixLift 363957
  have htrace : WordTrace (prefixWord ++ tailWord_363957) baseStart_363957 baseEnd_363957 := by
    simpa [prefixWord, tailWord_363957, baseEnd_363957] using wordTrace_append hprefix tailTrace_363957
  have hstable : (prefixWord ++ tailWord_363957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363957).length < 2 ^ (prefixWord ++ tailWord_363957).sum := by decide
  have hdescent : baseEnd_363957 < baseStart_363957 := by decide
  rcases family_descends (prefixWord ++ tailWord_363957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363968 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_363968 : Nat := 118140960795 + 363968 * 2 ^ 59
def prefixEnd_363968 : Nat := 4983230072969 + 3 ^ 40 * 363968 * 2
def baseEnd_363968 : Nat := 166124912760655295312131

theorem tailTrace_363968 : CollatzResearch.WordTrace tailWord_363968 prefixEnd_363968 166124912760655295312131 := by
  unfold tailWord_363968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637501772706785815318279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8850002363609047753757705 6637501772706785815318279)
  ·
    refine ⟨9956252659060178722977419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637501772706785815318279 9956252659060178722977419)
    ·
      refine ⟨14934378988590268084466129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956252659060178722977419 14934378988590268084466129)
      ·
        refine ⟨11200784241442701063349597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14934378988590268084466129 11200784241442701063349597)
        ·
          refine ⟨4200294090541012898756099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11200784241442701063349597 4200294090541012898756099)
          ·
            refine ⟨6300441135811519348134149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200294090541012898756099 6300441135811519348134149)
            ·
              refine ⟨1181332712964659877775153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6300441135811519348134149 1181332712964659877775153)
              ·
                refine ⟨885999534723494908331365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181332712964659877775153 885999534723494908331365)
                ·
                  refine ⟨166124912760655295312131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885999534723494908331365 166124912760655295312131)
                  ·
                    rfl

theorem cell20_363968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_363968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363968 prefixEnd_363968 := by exact prefixLift 363968
  have htrace : WordTrace (prefixWord ++ tailWord_363968) baseStart_363968 baseEnd_363968 := by
    simpa [prefixWord, tailWord_363968, baseEnd_363968] using wordTrace_append hprefix tailTrace_363968
  have hstable : (prefixWord ++ tailWord_363968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363968).length < 2 ^ (prefixWord ++ tailWord_363968).sum := by decide
  have hdescent : baseEnd_363968 < baseStart_363968 := by decide
  rcases family_descends (prefixWord ++ tailWord_363968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363975 : List Nat := [1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_363975 : Nat := 118140960795 + 363975 * 2 ^ 59
def prefixEnd_363975 : Nat := 4983230072969 + 3 ^ 40 * 363975 * 2
def baseEnd_363975 : Nat := 55376035917131460692923

theorem tailTrace_363975 : CollatzResearch.WordTrace tailWord_363975 prefixEnd_363975 55376035917131460692923 := by
  unfold tailWord_363975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275258856388211826141379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850172570925474550760919 13275258856388211826141379)
  ·
    refine ⟨19912888284582317739212069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13275258856388211826141379 19912888284582317739212069)
    ·
      refine ⟨3733666553359184576102263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19912888284582317739212069 3733666553359184576102263)
      ·
        refine ⟨5600499830038776864153395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733666553359184576102263 5600499830038776864153395)
        ·
          refine ⟨8400749745058165296230093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600499830038776864153395 8400749745058165296230093)
          ·
            refine ⟨3150281154396811986086285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8400749745058165296230093 3150281154396811986086285)
            ·
              refine ⟨1181355432898804494782357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3150281154396811986086285 1181355432898804494782357)
              ·
                refine ⟨55376035917131460692923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1181355432898804494782357 55376035917131460692923)
                ·
                  rfl

theorem cell20_363975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_363975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363975 prefixEnd_363975 := by exact prefixLift 363975
  have htrace : WordTrace (prefixWord ++ tailWord_363975) baseStart_363975 baseEnd_363975 := by
    simpa [prefixWord, tailWord_363975, baseEnd_363975] using wordTrace_append hprefix tailTrace_363975
  have hstable : (prefixWord ++ tailWord_363975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363975).length < 2 ^ (prefixWord ++ tailWord_363975).sum := by decide
  have hdescent : baseEnd_363975 < baseStart_363975 := by decide
  rcases family_descends (prefixWord ++ tailWord_363975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363999 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_363999 : Nat := 118140960795 + 363999 * 2 ^ 59
def prefixEnd_363999 : Nat := 4983230072969 + 3 ^ 40 * 363999 * 2
def baseEnd_363999 : Nat := 166139062005356965278671

theorem tailTrace_363999 : CollatzResearch.WordTrace tailWord_363999 prefixEnd_363999 166139062005356965278671 := by
  unfold tailWord_363999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276134208301263925015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850756138867509283343367 13276134208301263925015051)
  ·
    refine ⟨19914201312451895887522577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276134208301263925015051 19914201312451895887522577)
    ·
      refine ⟨14935650984338921915641933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19914201312451895887522577 14935650984338921915641933)
      ·
        refine ⟨5600869119127095718365725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14935650984338921915641933 5600869119127095718365725)
        ·
          refine ⟨2100325919672660894387147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5600869119127095718365725 2100325919672660894387147)
          ·
            refine ⟨3150488879508991341580721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100325919672660894387147 3150488879508991341580721)
            ·
              refine ⟨2362866659631743506185541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150488879508991341580721 2362866659631743506185541)
              ·
                refine ⟨443037498680951907409789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2362866659631743506185541 443037498680951907409789)
                ·
                  refine ⟨166139062005356965278671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443037498680951907409789 166139062005356965278671)
                  ·
                    rfl

theorem cell20_363999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_363999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_363999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_363999 prefixEnd_363999 := by exact prefixLift 363999
  have htrace : WordTrace (prefixWord ++ tailWord_363999) baseStart_363999 baseEnd_363999 := by
    simpa [prefixWord, tailWord_363999, baseEnd_363999] using wordTrace_append hprefix tailTrace_363999
  have hstable : (prefixWord ++ tailWord_363999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363999).length < 2 ^ (prefixWord ++ tailWord_363999).sum := by decide
  have hdescent : baseEnd_363999 < baseStart_363999 := by decide
  rcases family_descends (prefixWord ++ tailWord_363999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364016 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_364016 : Nat := 118140960795 + 364016 * 2 ^ 59
def prefixEnd_364016 : Nat := 4983230072969 + 3 ^ 40 * 364016 * 2
def baseEnd_364016 : Nat := 166146821268580461711935

theorem tailTrace_364016 : CollatzResearch.WordTrace tailWord_364016 prefixEnd_364016 166146821268580461711935 := by
  unfold tailWord_364016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638377124619837914191951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8851169499493117218922601 6638377124619837914191951)
  ·
    refine ⟨9957565686929756871287927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6638377124619837914191951 9957565686929756871287927)
    ·
      refine ⟨14936348530394635306931891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9957565686929756871287927 14936348530394635306931891)
      ·
        refine ⟨22404522795591952960397837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936348530394635306931891 22404522795591952960397837)
        ·
          refine ⟨8401696048346982360149189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22404522795591952960397837 8401696048346982360149189)
          ·
            refine ⟨1575318009065059192527973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8401696048346982360149189 1575318009065059192527973)
            ·
              refine ⟨295372126699698598598995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1575318009065059192527973 295372126699698598598995)
              ·
                refine ⟨443058190049547897898493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295372126699698598598995 443058190049547897898493)
                ·
                  refine ⟨166146821268580461711935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443058190049547897898493 166146821268580461711935)
                  ·
                    rfl

theorem cell20_364016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_364016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364016 prefixEnd_364016 := by exact prefixLift 364016
  have htrace : WordTrace (prefixWord ++ tailWord_364016) baseStart_364016 baseEnd_364016 := by
    simpa [prefixWord, tailWord_364016, baseEnd_364016] using wordTrace_append hprefix tailTrace_364016
  have hstable : (prefixWord ++ tailWord_364016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364016).length < 2 ^ (prefixWord ++ tailWord_364016).sum := by decide
  have hdescent : baseEnd_364016 < baseStart_364016 := by decide
  rcases family_descends (prefixWord ++ tailWord_364016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364096 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_364096 : Nat := 118140960795 + 364096 * 2 ^ 59
def prefixEnd_364096 : Nat := 4983230072969 + 3 ^ 40 * 364096 * 2
def baseEnd_364096 : Nat := 166183335448455739044941

theorem tailTrace_364096 : CollatzResearch.WordTrace tailWord_364096 prefixEnd_364096 166183335448455739044941 := by
  unfold tailWord_364096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639836044474924745648071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8853114725966566327530761 6639836044474924745648071)
  ·
    refine ⟨9959754066712387118472107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639836044474924745648071 9959754066712387118472107)
    ·
      refine ⟨14939631100068580677708161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9959754066712387118472107 14939631100068580677708161)
      ·
        refine ⟨11204723325051435508281121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14939631100068580677708161 11204723325051435508281121)
        ·
          refine ⟨8403542493788576631210841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11204723325051435508281121 8403542493788576631210841)
          ·
            refine ⟨6302656870341432473408131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8403542493788576631210841 6302656870341432473408131)
            ·
              refine ⟨9453985305512148710112197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302656870341432473408131 9453985305512148710112197)
              ·
                refine ⟨1772622244783527883146037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9453985305512148710112197 1772622244783527883146037)
                ·
                  refine ⟨166183335448455739044941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1772622244783527883146037 166183335448455739044941)
                  ·
                    rfl

theorem cell20_364096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_364096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364096 prefixEnd_364096 := by exact prefixLift 364096
  have htrace : WordTrace (prefixWord ++ tailWord_364096) baseStart_364096 baseEnd_364096 := by
    simpa [prefixWord, tailWord_364096, baseEnd_364096] using wordTrace_append hprefix tailTrace_364096
  have hstable : (prefixWord ++ tailWord_364096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364096).length < 2 ^ (prefixWord ++ tailWord_364096).sum := by decide
  have hdescent : baseEnd_364096 < baseStart_364096 := by decide
  rcases family_descends (prefixWord ++ tailWord_364096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364144 : List Nat := [2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_364144 : Nat := 118140960795 + 364144 * 2 ^ 59
def prefixEnd_364144 : Nat := 4983230072969 + 3 ^ 40 * 364144 * 2
def baseEnd_364144 : Nat := 55401747985460301814915

theorem tailTrace_364144 : CollatzResearch.WordTrace tailWord_364144 prefixEnd_364144 55401747985460301814915 := by
  unfold tailWord_364144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640711396387976844521743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8854281861850635792695657 6640711396387976844521743)
  ·
    refine ⟨9961067094581965266782615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640711396387976844521743 9961067094581965266782615)
    ·
      refine ⟨14941600641872947900173923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9961067094581965266782615 14941600641872947900173923)
      ·
        refine ⟨22412400962809421850260885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941600641872947900173923 22412400962809421850260885)
        ·
          refine ⟨1050581295131691649230979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22412400962809421850260885 1050581295131691649230979)
          ·
            refine ⟨1575871942697537473846469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050581295131691649230979 1575871942697537473846469)
            ·
              refine ⟨295475989255788276346213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1575871942697537473846469 295475989255788276346213)
              ·
                refine ⟨55401747985460301814915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295475989255788276346213 55401747985460301814915)
                ·
                  rfl

theorem cell20_364144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_364144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364144 prefixEnd_364144 := by exact prefixLift 364144
  have htrace : WordTrace (prefixWord ++ tailWord_364144) baseStart_364144 baseEnd_364144 := by
    simpa [prefixWord, tailWord_364144, baseEnd_364144] using wordTrace_append hprefix tailTrace_364144
  have hstable : (prefixWord ++ tailWord_364144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364144).length < 2 ^ (prefixWord ++ tailWord_364144).sum := by decide
  have hdescent : baseEnd_364144 < baseStart_364144 := by decide
  rcases family_descends (prefixWord ++ tailWord_364144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364172 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_364172 : Nat := 118140960795 + 364172 * 2 ^ 59
def prefixEnd_364172 : Nat := 4983230072969 + 3 ^ 40 * 364172 * 2
def baseEnd_364172 : Nat := 166218023919337252511297

theorem tailTrace_364172 : CollatzResearch.WordTrace tailWord_364172 prefixEnd_364172 166218023919337252511297 := by
  unfold tailWord_364172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641222018337257235531385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8854962691116342980708513 6641222018337257235531385)
  ·
    refine ⟨4980916513752942926648539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6641222018337257235531385 4980916513752942926648539)
    ·
      refine ⟨7471374770629414389972809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980916513752942926648539 7471374770629414389972809)
      ·
        refine ⟨5603531077972060792479607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7471374770629414389972809 5603531077972060792479607)
        ·
          refine ⟨8405296616958091188719411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603531077972060792479607 8405296616958091188719411)
          ·
            refine ⟨12607944925437136783079117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8405296616958091188719411 12607944925437136783079117)
            ·
              refine ⟨4727979347038926293654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12607944925437136783079117 4727979347038926293654669)
              ·
                refine ⟨1772992255139597360120501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727979347038926293654669 1772992255139597360120501)
                ·
                  refine ⟨166218023919337252511297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1772992255139597360120501 166218023919337252511297)
                  ·
                    rfl

theorem cell20_364172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_364172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364172 prefixEnd_364172 := by exact prefixLift 364172
  have htrace : WordTrace (prefixWord ++ tailWord_364172) baseStart_364172 baseEnd_364172 := by
    simpa [prefixWord, tailWord_364172, baseEnd_364172] using wordTrace_append hprefix tailTrace_364172
  have hstable : (prefixWord ++ tailWord_364172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364172).length < 2 ^ (prefixWord ++ tailWord_364172).sum := by decide
  have hdescent : baseEnd_364172 < baseStart_364172 := by decide
  rcases family_descends (prefixWord ++ tailWord_364172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364210 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_364210 : Nat := 118140960795 + 364210 * 2 ^ 59
def prefixEnd_364210 : Nat := 4983230072969 + 3 ^ 40 * 364210 * 2
def baseEnd_364210 : Nat := 166235368154778009244475

theorem tailTrace_364210 : CollatzResearch.WordTrace tailWord_364210 prefixEnd_364210 166235368154778009244475 := by
  unfold tailWord_364210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320957502634211740236521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8855886673691231307297389 3320957502634211740236521)
  ·
    refine ⟨2490718126975658805177391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3320957502634211740236521 2490718126975658805177391)
    ·
      refine ⟨3736077190463488207766087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490718126975658805177391 3736077190463488207766087)
      ·
        refine ⟨5604115785695232311649131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736077190463488207766087 5604115785695232311649131)
        ·
          refine ⟨8406173678542848467473697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604115785695232311649131 8406173678542848467473697)
          ·
            refine ⟨6304630258907136350605273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406173678542848467473697 6304630258907136350605273)
            ·
              refine ⟨4728472694180352262953955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304630258907136350605273 4728472694180352262953955)
              ·
                refine ⟨7092709041270528394430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728472694180352262953955 7092709041270528394430933)
                ·
                  refine ⟨166235368154778009244475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7092709041270528394430933 166235368154778009244475)
                  ·
                    rfl

theorem cell20_364210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_364210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364210 prefixEnd_364210 := by exact prefixLift 364210
  have htrace : WordTrace (prefixWord ++ tailWord_364210) baseStart_364210 baseEnd_364210 := by
    simpa [prefixWord, tailWord_364210, baseEnd_364210] using wordTrace_append hprefix tailTrace_364210
  have hstable : (prefixWord ++ tailWord_364210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364210).length < 2 ^ (prefixWord ++ tailWord_364210).sum := by decide
  have hdescent : baseEnd_364210 < baseStart_364210 := by decide
  rcases family_descends (prefixWord ++ tailWord_364210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364237 : List Nat := [1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_364237 : Nat := 118140960795 + 364237 * 2 ^ 59
def prefixEnd_364237 : Nat := 4983230072969 + 3 ^ 40 * 364237 * 2
def baseEnd_364237 : Nat := 55415897230161971781455

theorem tailTrace_364237 : CollatzResearch.WordTrace tailWord_364237 prefixEnd_364237 55415897230161971781455 := by
  unfold tailWord_364237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284814781439030572178965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8856543187626020381452643 13284814781439030572178965)
  ·
    refine ⟨622725692879954558070889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13284814781439030572178965 622725692879954558070889)
    ·
      refine ⟨467044269659965918553167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622725692879954558070889 467044269659965918553167)
      ·
        refine ⟨700566404489948877829751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467044269659965918553167 700566404489948877829751)
        ·
          refine ⟨1050849606734923316744627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700566404489948877829751 1050849606734923316744627)
          ·
            refine ⟨1576274410102384975116941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050849606734923316744627 1576274410102384975116941)
            ·
              refine ⟨591102903788394365668853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576274410102384975116941 591102903788394365668853)
              ·
                refine ⟨55415897230161971781455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 591102903788394365668853 55415897230161971781455)
                ·
                  rfl

theorem cell20_364237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_364237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364237 prefixEnd_364237 := by exact prefixLift 364237
  have htrace : WordTrace (prefixWord ++ tailWord_364237) baseStart_364237 baseEnd_364237 := by
    simpa [prefixWord, tailWord_364237, baseEnd_364237] using wordTrace_append hprefix tailTrace_364237
  have hstable : (prefixWord ++ tailWord_364237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364237).length < 2 ^ (prefixWord ++ tailWord_364237).sum := by decide
  have hdescent : baseEnd_364237 < baseStart_364237 := by decide
  rcases family_descends (prefixWord ++ tailWord_364237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364241 : List Nat := [1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_364241 : Nat := 118140960795 + 364241 * 2 ^ 59
def prefixEnd_364241 : Nat := 4983230072969 + 3 ^ 40 * 364241 * 2
def baseEnd_364241 : Nat := 55416505799826559737005

theorem tailTrace_364241 : CollatzResearch.WordTrace tailWord_364241 prefixEnd_364241 55416505799826559737005 := by
  unfold tailWord_364241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284960673424539255324577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8856640448949692836883051 13284960673424539255324577)
  ·
    refine ⟨9963720505068404441493433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13284960673424539255324577 9963720505068404441493433)
    ·
      refine ⟨7472790378801303331120075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9963720505068404441493433 7472790378801303331120075)
      ·
        refine ⟨11209185568201954996680113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7472790378801303331120075 11209185568201954996680113)
        ·
          refine ⟨8406889176151466247510085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11209185568201954996680113 8406889176151466247510085)
          ·
            refine ⟨1576291720528399921408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8406889176151466247510085 1576291720528399921408141)
            ·
              refine ⟨591109395198149970528053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576291720528399921408141 591109395198149970528053)
              ·
                refine ⟨55416505799826559737005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 591109395198149970528053 55416505799826559737005)
                ·
                  rfl

theorem cell20_364241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_364241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364241 prefixEnd_364241 := by exact prefixLift 364241
  have htrace : WordTrace (prefixWord ++ tailWord_364241) baseStart_364241 baseEnd_364241 := by
    simpa [prefixWord, tailWord_364241, baseEnd_364241] using wordTrace_append hprefix tailTrace_364241
  have hstable : (prefixWord ++ tailWord_364241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364241).length < 2 ^ (prefixWord ++ tailWord_364241).sum := by decide
  have hdescent : baseEnd_364241 < baseStart_364241 := by decide
  rcases family_descends (prefixWord ++ tailWord_364241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364244 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_364244 : Nat := 118140960795 + 364244 * 2 ^ 59
def prefixEnd_364244 : Nat := 4983230072969 + 3 ^ 40 * 364244 * 2
def baseEnd_364244 : Nat := 166250886681225002111003

theorem tailTrace_364244 : CollatzResearch.WordTrace tailWord_364244 prefixEnd_364244 166250886681225002111003 := by
  unfold tailWord_364244
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642535046206835383841893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8856713394942447178455857 6642535046206835383841893)
  ·
    refine ⟨1245475321163781634470355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6642535046206835383841893 1245475321163781634470355)
    ·
      refine ⟨1868212981745672451705533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245475321163781634470355 1868212981745672451705533)
      ·
        refine ⟨700579868154627169389575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1868212981745672451705533 700579868154627169389575)
        ·
          refine ⟨1050869802231940754084363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700579868154627169389575 1050869802231940754084363)
          ·
            refine ⟨1576304703347911131126545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050869802231940754084363 1576304703347911131126545)
            ·
              refine ⟨1182228527510933348344909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576304703347911131126545 1182228527510933348344909)
              ·
                refine ⟨443335697816600005629341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182228527510933348344909 443335697816600005629341)
                ·
                  refine ⟨166250886681225002111003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443335697816600005629341 166250886681225002111003)
                  ·
                    rfl

theorem cell20_364244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_364244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364244 prefixEnd_364244 := by exact prefixLift 364244
  have htrace : WordTrace (prefixWord ++ tailWord_364244) baseStart_364244 baseEnd_364244 := by
    simpa [prefixWord, tailWord_364244, baseEnd_364244] using wordTrace_append hprefix tailTrace_364244
  have hstable : (prefixWord ++ tailWord_364244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364244).length < 2 ^ (prefixWord ++ tailWord_364244).sum := by decide
  have hdescent : baseEnd_364244 < baseStart_364244 := by decide
  rcases family_descends (prefixWord ++ tailWord_364244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364289 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 2]
def baseStart_364289 : Nat := 118140960795 + 364289 * 2 ^ 59
def prefixEnd_364289 : Nat := 4983230072969 + 3 ^ 40 * 364289 * 2
def baseEnd_364289 : Nat := 166271425907404845610819

theorem tailTrace_364289 : CollatzResearch.WordTrace tailWord_364289 prefixEnd_364289 166271425907404845610819 := by
  unfold tailWord_364289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286711377250643453071921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8857807584833762302047947 13286711377250643453071921)
  ·
    refine ⟨9965033532937982589803941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13286711377250643453071921 9965033532937982589803941)
    ·
      refine ⟨1868443787425871735588239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9965033532937982589803941 1868443787425871735588239)
      ·
        refine ⟨2802665681138807603382359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868443787425871735588239 2802665681138807603382359)
        ·
          refine ⟨4203998521708211405073539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802665681138807603382359 4203998521708211405073539)
          ·
            refine ⟨6305997782562317107610309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203998521708211405073539 6305997782562317107610309)
            ·
              refine ⟨1182374584230434457676933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6305997782562317107610309 1182374584230434457676933)
              ·
                refine ⟨221695234543206460814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1182374584230434457676933 221695234543206460814425)
                ·
                  refine ⟨166271425907404845610819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221695234543206460814425 166271425907404845610819)
                  ·
                    rfl

theorem cell20_364289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_364289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364289 prefixEnd_364289 := by exact prefixLift 364289
  have htrace : WordTrace (prefixWord ++ tailWord_364289) baseStart_364289 baseEnd_364289 := by
    simpa [prefixWord, tailWord_364289, baseEnd_364289] using wordTrace_append hprefix tailTrace_364289
  have hstable : (prefixWord ++ tailWord_364289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364289).length < 2 ^ (prefixWord ++ tailWord_364289).sum := by decide
  have hdescent : baseEnd_364289 < baseStart_364289 := by decide
  rcases family_descends (prefixWord ++ tailWord_364289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364344 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_364344 : Nat := 118140960795 + 364344 * 2 ^ 59
def prefixEnd_364344 : Nat := 4983230072969 + 3 ^ 40 * 364344 * 2
def baseEnd_364344 : Nat := 166296529406069098777261

theorem tailTrace_364344 : CollatzResearch.WordTrace tailWord_364344 prefixEnd_364344 166296529406069098777261 := by
  unfold tailWord_364344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644358696025693923162043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8859144928034258564216057 6644358696025693923162043)
  ·
    refine ⟨9966538044038540884743065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644358696025693923162043 9966538044038540884743065)
    ·
      refine ⟨7474903533028905663557299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9966538044038540884743065 7474903533028905663557299)
      ·
        refine ⟨11212355299543358495335949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474903533028905663557299 11212355299543358495335949)
        ·
          refine ⟨4204633237328759435750981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11212355299543358495335949 4204633237328759435750981)
          ·
            refine ⟨788368731999142394203309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4204633237328759435750981 788368731999142394203309)
            ·
              refine ⟨295638274499678397826241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 788368731999142394203309 295638274499678397826241)
              ·
                refine ⟨221728705874758798369681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295638274499678397826241 221728705874758798369681)
                ·
                  refine ⟨166296529406069098777261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221728705874758798369681 166296529406069098777261)
                  ·
                    rfl

theorem cell20_364344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_364344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364344 prefixEnd_364344 := by exact prefixLift 364344
  have htrace : WordTrace (prefixWord ++ tailWord_364344) baseStart_364344 baseEnd_364344 := by
    simpa [prefixWord, tailWord_364344, baseEnd_364344] using wordTrace_append hprefix tailTrace_364344
  have hstable : (prefixWord ++ tailWord_364344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364344).length < 2 ^ (prefixWord ++ tailWord_364344).sum := by decide
  have hdescent : baseEnd_364344 < baseStart_364344 := by decide
  rcases family_descends (prefixWord ++ tailWord_364344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364348 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_364348 : Nat := 118140960795 + 364348 * 2 ^ 59
def prefixEnd_364348 : Nat := 4983230072969 + 3 ^ 40 * 364348 * 2
def baseEnd_364348 : Nat := 166298355115062862643911

theorem tailTrace_364348 : CollatzResearch.WordTrace tailWord_364348 prefixEnd_364348 166298355115062862643911 := by
  unfold tailWord_364348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644431642018448264734849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8859242189357931019646465 6644431642018448264734849)
  ·
    refine ⟨4983323731513836198551137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6644431642018448264734849 4983323731513836198551137)
    ·
      refine ⟨3737492798635377148913353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983323731513836198551137 3737492798635377148913353)
      ·
        refine ⟨2803119598976532861685015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737492798635377148913353 2803119598976532861685015)
        ·
          refine ⟨4204679398464799292527523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803119598976532861685015 4204679398464799292527523)
          ·
            refine ⟨6307019097697198938791285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204679398464799292527523 6307019097697198938791285)
            ·
              refine ⟨591283040409112400511683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6307019097697198938791285 591283040409112400511683)
              ·
                refine ⟨886924560613668600767525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591283040409112400511683 886924560613668600767525)
                ·
                  refine ⟨166298355115062862643911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886924560613668600767525 166298355115062862643911)
                  ·
                    rfl

theorem cell20_364348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_364348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364348 prefixEnd_364348 := by exact prefixLift 364348
  have htrace : WordTrace (prefixWord ++ tailWord_364348) baseStart_364348 baseEnd_364348 := by
    simpa [prefixWord, tailWord_364348, baseEnd_364348] using wordTrace_append hprefix tailTrace_364348
  have hstable : (prefixWord ++ tailWord_364348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364348).length < 2 ^ (prefixWord ++ tailWord_364348).sum := by decide
  have hdescent : baseEnd_364348 < baseStart_364348 := by decide
  rcases family_descends (prefixWord ++ tailWord_364348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364355 : List Nat := [1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_364355 : Nat := 118140960795 + 364355 * 2 ^ 59
def prefixEnd_364355 : Nat := 4983230072969 + 3 ^ 40 * 364355 * 2
def baseEnd_364355 : Nat := 55433850035267316470183

theorem tailTrace_364355 : CollatzResearch.WordTrace tailWord_364355 prefixEnd_364355 55433850035267316470183 := by
  unfold tailWord_364355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13289118595011536724974519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8859412396674357816649679 13289118595011536724974519)
  ·
    refine ⟨19933677892517305087461779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13289118595011536724974519 19933677892517305087461779)
    ·
      refine ⟨29900516838775957631192669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19933677892517305087461779 29900516838775957631192669)
      ·
        refine ⟨11212693814540984111697251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29900516838775957631192669 11212693814540984111697251)
        ·
          refine ⟨16819040721811476167545877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212693814540984111697251 16819040721811476167545877)
          ·
            refine ⟨788392533834912945353713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16819040721811476167545877 788392533834912945353713)
            ·
              refine ⟨591294400376184709015285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788392533834912945353713 591294400376184709015285)
              ·
                refine ⟨55433850035267316470183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 591294400376184709015285 55433850035267316470183)
                ·
                  rfl

theorem cell20_364355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_364355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364355 prefixEnd_364355 := by exact prefixLift 364355
  have htrace : WordTrace (prefixWord ++ tailWord_364355) baseStart_364355 baseEnd_364355 := by
    simpa [prefixWord, tailWord_364355, baseEnd_364355] using wordTrace_append hprefix tailTrace_364355
  have hstable : (prefixWord ++ tailWord_364355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364355).length < 2 ^ (prefixWord ++ tailWord_364355).sum := by decide
  have hdescent : baseEnd_364355 < baseStart_364355 := by decide
  rcases family_descends (prefixWord ++ tailWord_364355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364406 : List Nat := [5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_364406 : Nat := 118140960795 + 364406 * 2 ^ 59
def prefixEnd_364406 : Nat := 4983230072969 + 3 ^ 40 * 364406 * 2
def baseEnd_364406 : Nat := 55441609298490812903447

theorem tailTrace_364406 : CollatzResearch.WordTrace tailWord_364406 prefixEnd_364406 55441609298490812903447 := by
  unfold tailWord_364406
  simp only [CollatzResearch.WordTrace]
  refine ⟨830686169864173277192567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8860652478551181623387381 830686169864173277192567)
  ·
    refine ⟨1246029254796259915788851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830686169864173277192567 1246029254796259915788851)
    ·
      refine ⟨1869043882194389873683277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246029254796259915788851 1869043882194389873683277)
      ·
        refine ⟨700891455822896202631229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1869043882194389873683277 700891455822896202631229)
        ·
          refine ⟨262834295933586075986711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700891455822896202631229 262834295933586075986711)
          ·
            refine ⟨394251443900379113980067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262834295933586075986711 394251443900379113980067)
            ·
              refine ⟨591377165850568670970101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394251443900379113980067 591377165850568670970101)
              ·
                refine ⟨55441609298490812903447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 591377165850568670970101 55441609298490812903447)
                ·
                  rfl

theorem cell20_364406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_364406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364406 prefixEnd_364406 := by exact prefixLift 364406
  have htrace : WordTrace (prefixWord ++ tailWord_364406) baseStart_364406 baseEnd_364406 := by
    simpa [prefixWord, tailWord_364406, baseEnd_364406] using wordTrace_append hprefix tailTrace_364406
  have hstable : (prefixWord ++ tailWord_364406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364406).length < 2 ^ (prefixWord ++ tailWord_364406).sum := by decide
  have hdescent : baseEnd_364406 < baseStart_364406 := by decide
  rcases family_descends (prefixWord ++ tailWord_364406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364455 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_364455 : Nat := 118140960795 + 364455 * 2 ^ 59
def prefixEnd_364455 : Nat := 4983230072969 + 3 ^ 40 * 364455 * 2
def baseEnd_364455 : Nat := 166347192830646046076807

theorem tailTrace_364455 : CollatzResearch.WordTrace tailWord_364455 prefixEnd_364455 166347192830646046076807 := by
  unfold tailWord_364455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292765894649253803614819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8861843929766169202409879 13292765894649253803614819)
  ·
    refine ⟨19939148841973880705422229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13292765894649253803614819 19939148841973880705422229)
    ·
      refine ⟨934647601967525658066667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19939148841973880705422229 934647601967525658066667)
      ·
        refine ⟨1401971402951288487100001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934647601967525658066667 1401971402951288487100001)
        ·
          refine ⟨1051478552213466365325001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401971402951288487100001 1051478552213466365325001)
          ·
            refine ⟨788608914160099773993751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051478552213466365325001 788608914160099773993751)
            ·
              refine ⟨1182913371240149660990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788608914160099773993751 1182913371240149660990627)
              ·
                refine ⟨1774370056860224491485941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182913371240149660990627 1774370056860224491485941)
                ·
                  refine ⟨166347192830646046076807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774370056860224491485941 166347192830646046076807)
                  ·
                    rfl

theorem cell20_364455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_364455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364455 prefixEnd_364455 := by exact prefixLift 364455
  have htrace : WordTrace (prefixWord ++ tailWord_364455) baseStart_364455 baseEnd_364455 := by
    simpa [prefixWord, tailWord_364455, baseEnd_364455] using wordTrace_append hprefix tailTrace_364455
  have hstable : (prefixWord ++ tailWord_364455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364455).length < 2 ^ (prefixWord ++ tailWord_364455).sum := by decide
  have hdescent : baseEnd_364455 < baseStart_364455 := by decide
  rcases family_descends (prefixWord ++ tailWord_364455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364468 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_364468 : Nat := 118140960795 + 364468 * 2 ^ 59
def prefixEnd_364468 : Nat := 4983230072969 + 3 ^ 40 * 364468 * 2
def baseEnd_364468 : Nat := 166353126384875778643421

theorem tailTrace_364468 : CollatzResearch.WordTrace tailWord_364468 prefixEnd_364468 166353126384875778643421 := by
  unfold tailWord_364468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646620021801078511919029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8862160029068104682558705 6646620021801078511919029)
  ·
    refine ⟨623120627043851110492409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6646620021801078511919029 623120627043851110492409)
    ·
      refine ⟨467340470282888332869307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623120627043851110492409 467340470282888332869307)
      ·
        refine ⟨701010705424332499303961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467340470282888332869307 701010705424332499303961)
        ·
          refine ⟨525758029068249374477971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701010705424332499303961 525758029068249374477971)
          ·
            refine ⟨788637043602374061716957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525758029068249374477971 788637043602374061716957)
            ·
              refine ⟨295738891350890273143859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 788637043602374061716957 295738891350890273143859)
              ·
                refine ⟨443608337026335409715789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295738891350890273143859 443608337026335409715789)
                ·
                  refine ⟨166353126384875778643421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443608337026335409715789 166353126384875778643421)
                  ·
                    rfl

theorem cell20_364468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_364468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364468 prefixEnd_364468 := by exact prefixLift 364468
  have htrace : WordTrace (prefixWord ++ tailWord_364468) baseStart_364468 baseEnd_364468 := by
    simpa [prefixWord, tailWord_364468, baseEnd_364468] using wordTrace_append hprefix tailTrace_364468
  have hstable : (prefixWord ++ tailWord_364468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364468).length < 2 ^ (prefixWord ++ tailWord_364468).sum := by decide
  have hdescent : baseEnd_364468 < baseStart_364468 := by decide
  rcases family_descends (prefixWord ++ tailWord_364468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364528 : List Nat := [2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_364528 : Nat := 118140960795 + 364528 * 2 ^ 59
def prefixEnd_364528 : Nat := 4983230072969 + 3 ^ 40 * 364528 * 2
def baseEnd_364528 : Nat := 55460170673260745547725

theorem tailTrace_364528 : CollatzResearch.WordTrace tailWord_364528 prefixEnd_364528 55460170673260745547725 := by
  unfold tailWord_364528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647714211692393635511119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8863618948923191514014825 6647714211692393635511119)
  ·
    refine ⟨9971571317538590453266679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6647714211692393635511119 9971571317538590453266679)
    ·
      refine ⟨14957356976307885679900019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9971571317538590453266679 14957356976307885679900019)
      ·
        refine ⟨22436035464461828519850029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957356976307885679900019 22436035464461828519850029)
        ·
          refine ⟨8413513299173185694943761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22436035464461828519850029 8413513299173185694943761)
          ·
            refine ⟨6310134974379889271207821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8413513299173185694943761 6310134974379889271207821)
            ·
              refine ⟨2366300615392458476702933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6310134974379889271207821 2366300615392458476702933)
              ·
                refine ⟨55460170673260745547725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2366300615392458476702933 55460170673260745547725)
                ·
                  rfl

theorem cell20_364528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_364528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364528 prefixEnd_364528 := by exact prefixLift 364528
  have htrace : WordTrace (prefixWord ++ tailWord_364528) baseStart_364528 baseEnd_364528 := by
    simpa [prefixWord, tailWord_364528, baseEnd_364528] using wordTrace_append hprefix tailTrace_364528
  have hstable : (prefixWord ++ tailWord_364528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364528).length < 2 ^ (prefixWord ++ tailWord_364528).sum := by decide
  have hdescent : baseEnd_364528 < baseStart_364528 := by decide
  rcases family_descends (prefixWord ++ tailWord_364528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364566 : List Nat := [5, 15]
def baseStart_364566 : Nat := 118140960795 + 364566 * 2 ^ 59
def prefixEnd_364566 : Nat := 4983230072969 + 3 ^ 40 * 364566 * 2
def baseEnd_364566 : Nat := 76084982284052580419

theorem tailTrace_364566 : CollatzResearch.WordTrace tailWord_364566 prefixEnd_364566 76084982284052580419 := by
  unfold tailWord_364566
  simp only [CollatzResearch.WordTrace]
  refine ⟨831050899827944985056597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8864542931498079840603701 831050899827944985056597)
  ·
    refine ⟨76084982284052580419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 15 831050899827944985056597 76084982284052580419)
    ·
      rfl

theorem cell20_364566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 15].length) (baseStart_364566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364566 prefixEnd_364566 := by exact prefixLift 364566
  have htrace : WordTrace (prefixWord ++ tailWord_364566) baseStart_364566 baseEnd_364566 := by
    simpa [prefixWord, tailWord_364566, baseEnd_364566] using wordTrace_append hprefix tailTrace_364566
  have hstable : (prefixWord ++ tailWord_364566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364566).length < 2 ^ (prefixWord ++ tailWord_364566).sum := by decide
  have hdescent : baseEnd_364566 < baseStart_364566 := by decide
  rcases family_descends (prefixWord ++ tailWord_364566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364572 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_364572 : Nat := 118140960795 + 364572 * 2 ^ 59
def prefixEnd_364572 : Nat := 4983230072969 + 3 ^ 40 * 364572 * 2
def baseEnd_364572 : Nat := 166400594818713639176329

theorem tailTrace_364572 : CollatzResearch.WordTrace tailWord_364572 prefixEnd_364572 166400594818713639176329 := by
  unfold tailWord_364572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648516617612691392811985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8864688823483588523749313 6648516617612691392811985)
  ·
    refine ⟨4986387463209518544608989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6648516617612691392811985 4986387463209518544608989)
    ·
      refine ⟨1869895298703569454228371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4986387463209518544608989 1869895298703569454228371)
      ·
        refine ⟨2804842948055354181342557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869895298703569454228371 2804842948055354181342557)
        ·
          refine ⟨1051816105520757818003459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2804842948055354181342557 1051816105520757818003459)
          ·
            refine ⟨1577724158281136727005189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051816105520757818003459 1577724158281136727005189)
            ·
              refine ⟨295823279677713136313473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1577724158281136727005189 295823279677713136313473)
              ·
                refine ⟨221867459758284852235105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295823279677713136313473 221867459758284852235105)
                ·
                  refine ⟨166400594818713639176329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221867459758284852235105 166400594818713639176329)
                  ·
                    rfl

theorem cell20_364572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_364572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364572 prefixEnd_364572 := by exact prefixLift 364572
  have htrace : WordTrace (prefixWord ++ tailWord_364572) baseStart_364572 baseEnd_364572 := by
    simpa [prefixWord, tailWord_364572, baseEnd_364572] using wordTrace_append hprefix tailTrace_364572
  have hstable : (prefixWord ++ tailWord_364572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364572).length < 2 ^ (prefixWord ++ tailWord_364572).sum := by decide
  have hdescent : baseEnd_364572 < baseStart_364572 := by decide
  rcases family_descends (prefixWord ++ tailWord_364572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364597 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_364597 : Nat := 118140960795 + 364597 * 2 ^ 59
def prefixEnd_364597 : Nat := 4983230072969 + 3 ^ 40 * 364597 * 2
def baseEnd_364597 : Nat := 166412005499924663342893

theorem tailTrace_364597 : CollatzResearch.WordTrace tailWord_364597 prefixEnd_364597 166412005499924663342893 := by
  unfold tailWord_364597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13297945060134812055284045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8865296706756541370189363 13297945060134812055284045)
  ·
    refine ⟨4986729397550554520731517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13297945060134812055284045 4986729397550554520731517)
    ·
      refine ⟨1870023524081457945274319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4986729397550554520731517 1870023524081457945274319)
      ·
        refine ⟨2805035286122186917911479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870023524081457945274319 2805035286122186917911479)
        ·
          refine ⟨4207552929183280376867219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805035286122186917911479 4207552929183280376867219)
          ·
            refine ⟨6311329393774920565300829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207552929183280376867219 6311329393774920565300829)
            ·
              refine ⟨2366748522665595211987811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6311329393774920565300829 2366748522665595211987811)
              ·
                refine ⟨3550122783998392817981717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366748522665595211987811 3550122783998392817981717)
                ·
                  refine ⟨166412005499924663342893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3550122783998392817981717 166412005499924663342893)
                  ·
                    rfl

theorem cell20_364597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_364597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364597 prefixEnd_364597 := by exact prefixLift 364597
  have htrace : WordTrace (prefixWord ++ tailWord_364597) baseStart_364597 baseEnd_364597 := by
    simpa [prefixWord, tailWord_364597, baseEnd_364597] using wordTrace_append hprefix tailTrace_364597
  have hstable : (prefixWord ++ tailWord_364597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364597).length < 2 ^ (prefixWord ++ tailWord_364597).sum := by decide
  have hdescent : baseEnd_364597 < baseStart_364597 := by decide
  rcases family_descends (prefixWord ++ tailWord_364597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364600 : List Nat := [2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_364600 : Nat := 118140960795 + 364600 * 2 ^ 59
def prefixEnd_364600 : Nat := 4983230072969 + 3 ^ 40 * 364600 * 2
def baseEnd_364600 : Nat := 55471124927223328747627

theorem tailTrace_364600 : CollatzResearch.WordTrace tailWord_364600 prefixEnd_364600 55471124927223328747627 := by
  unfold tailWord_364600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649027239561971783821627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8865369652749295711762169 6649027239561971783821627)
  ·
    refine ⟨9973540859342957675732441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6649027239561971783821627 9973540859342957675732441)
    ·
      refine ⟨7480155644507218256799331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9973540859342957675732441 7480155644507218256799331)
      ·
        refine ⟨11220233466760827385198997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480155644507218256799331 11220233466760827385198997)
        ·
          refine ⟨525948443754413783681203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11220233466760827385198997 525948443754413783681203)
          ·
            refine ⟨788922665631620675521805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525948443754413783681203 788922665631620675521805)
            ·
              refine ⟨295845999611857753320677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 788922665631620675521805 295845999611857753320677)
              ·
                refine ⟨55471124927223328747627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295845999611857753320677 55471124927223328747627)
                ·
                  rfl

theorem cell20_364600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_364600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364600 prefixEnd_364600 := by exact prefixLift 364600
  have htrace : WordTrace (prefixWord ++ tailWord_364600) baseStart_364600 baseEnd_364600 := by
    simpa [prefixWord, tailWord_364600, baseEnd_364600] using wordTrace_append hprefix tailTrace_364600
  have hstable : (prefixWord ++ tailWord_364600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364600).length < 2 ^ (prefixWord ++ tailWord_364600).sum := by decide
  have hdescent : baseEnd_364600 < baseStart_364600 := by decide
  rcases family_descends (prefixWord ++ tailWord_364600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364621 : List Nat := [1, 6, 1, 1, 1, 1, 9]
def baseStart_364621 : Nat := 118140960795 + 364621 * 2 ^ 59
def prefixEnd_364621 : Nat := 4983230072969 + 3 ^ 40 * 364621 * 2
def baseEnd_364621 : Nat := 18491439972654138504755

theorem tailTrace_364621 : CollatzResearch.WordTrace tailWord_364621 prefixEnd_364621 18491439972654138504755 := by
  unfold tailWord_364621
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298820412047864154157717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8865880274698576102771811 13298820412047864154157717)
  ·
    refine ⟨623382206814743632226143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13298820412047864154157717 623382206814743632226143)
    ·
      refine ⟨935073310222115448339215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623382206814743632226143 935073310222115448339215)
      ·
        refine ⟨1402609965333173172508823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935073310222115448339215 1402609965333173172508823)
        ·
          refine ⟨2103914947999759758763235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402609965333173172508823 2103914947999759758763235)
          ·
            refine ⟨3155872421999639638144853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103914947999759758763235 3155872421999639638144853)
            ·
              refine ⟨18491439972654138504755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3155872421999639638144853 18491439972654138504755)
              ·
                rfl

theorem cell20_364621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_364621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364621 prefixEnd_364621 := by exact prefixLift 364621
  have htrace : WordTrace (prefixWord ++ tailWord_364621) baseStart_364621 baseEnd_364621 := by
    simpa [prefixWord, tailWord_364621, baseEnd_364621] using wordTrace_append hprefix tailTrace_364621
  have hstable : (prefixWord ++ tailWord_364621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364621).length < 2 ^ (prefixWord ++ tailWord_364621).sum := by decide
  have hdescent : baseEnd_364621 < baseStart_364621 := by decide
  rcases family_descends (prefixWord ++ tailWord_364621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364669 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 2]
def baseStart_364669 : Nat := 118140960795 + 364669 * 2 ^ 59
def prefixEnd_364669 : Nat := 4983230072969 + 3 ^ 40 * 364669 * 2
def baseEnd_364669 : Nat := 166444868261812412942599

theorem tailTrace_364669 : CollatzResearch.WordTrace tailWord_364669 prefixEnd_364669 166444868261812412942599 := by
  unfold tailWord_364669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13300571115873968351905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8867047410582645567936707 13300571115873968351905061)
  ·
    refine ⟨2493857084226369065982199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13300571115873968351905061 2493857084226369065982199)
    ·
      refine ⟨3740785626339553598973299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493857084226369065982199 3740785626339553598973299)
      ·
        refine ⟨5611178439509330398459949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740785626339553598973299 5611178439509330398459949)
        ·
          refine ⟨2104191914815998899422481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5611178439509330398459949 2104191914815998899422481)
          ·
            refine ⟨1578143936111999174566861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104191914815998899422481 1578143936111999174566861)
            ·
              refine ⟨591803976041999690462573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1578143936111999174566861 591803976041999690462573)
              ·
                refine ⟨221926491015749883923465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591803976041999690462573 221926491015749883923465)
                ·
                  refine ⟨166444868261812412942599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221926491015749883923465 166444868261812412942599)
                  ·
                    rfl

theorem cell20_364669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_364669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364669 prefixEnd_364669 := by exact prefixLift 364669
  have htrace : WordTrace (prefixWord ++ tailWord_364669) baseStart_364669 baseEnd_364669 := by
    simpa [prefixWord, tailWord_364669, baseEnd_364669] using wordTrace_append hprefix tailTrace_364669
  have hstable : (prefixWord ++ tailWord_364669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364669).length < 2 ^ (prefixWord ++ tailWord_364669).sum := by decide
  have hdescent : baseEnd_364669 < baseStart_364669 := by decide
  rcases family_descends (prefixWord ++ tailWord_364669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364686 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_364686 : Nat := 118140960795 + 364686 * 2 ^ 59
def prefixEnd_364686 : Nat := 4983230072969 + 3 ^ 40 * 364686 * 2
def baseEnd_364686 : Nat := 166452627525035909375863

theorem tailTrace_364686 : CollatzResearch.WordTrace tailWord_364686 prefixEnd_364686 166452627525035909375863 := by
  unfold tailWord_364686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662648894601547531909239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8867460771208253503515941 1662648894601547531909239)
  ·
    refine ⟨2493973341902321297863859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662648894601547531909239 2493973341902321297863859)
    ·
      refine ⟨3740960012853481946795789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493973341902321297863859 3740960012853481946795789)
      ·
        refine ⟨1402860004820055730048421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3740960012853481946795789 1402860004820055730048421)
        ·
          refine ⟨263036250903760449384079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1402860004820055730048421 263036250903760449384079)
          ·
            refine ⟨394554376355640674076119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263036250903760449384079 394554376355640674076119)
            ·
              refine ⟨591831564533461011114179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394554376355640674076119 591831564533461011114179)
              ·
                refine ⟨887747346800191516671269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591831564533461011114179 887747346800191516671269)
                ·
                  refine ⟨166452627525035909375863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887747346800191516671269 166452627525035909375863)
                  ·
                    rfl

theorem cell20_364686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_364686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364686 prefixEnd_364686 := by exact prefixLift 364686
  have htrace : WordTrace (prefixWord ++ tailWord_364686) baseStart_364686 baseEnd_364686 := by
    simpa [prefixWord, tailWord_364686, baseEnd_364686] using wordTrace_append hprefix tailTrace_364686
  have hstable : (prefixWord ++ tailWord_364686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364686).length < 2 ^ (prefixWord ++ tailWord_364686).sum := by decide
  have hdescent : baseEnd_364686 < baseStart_364686 := by decide
  rcases family_descends (prefixWord ++ tailWord_364686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364728 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_364728 : Nat := 118140960795 + 364728 * 2 ^ 59
def prefixEnd_364728 : Nat := 4983230072969 + 3 ^ 40 * 364728 * 2
def baseEnd_364728 : Nat := 166471797469470429975691

theorem tailTrace_364728 : CollatzResearch.WordTrace tailWord_364728 prefixEnd_364728 166471797469470429975691 := by
  unfold tailWord_364728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651361511330110714151419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8868482015106814285535225 6651361511330110714151419)
  ·
    refine ⟨9977042266995166071227129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6651361511330110714151419 9977042266995166071227129)
    ·
      refine ⟨7482781700246374553420347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9977042266995166071227129 7482781700246374553420347)
      ·
        refine ⟨11224172550369561830130521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482781700246374553420347 11224172550369561830130521)
        ·
          refine ⟨8418129412777171372597891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11224172550369561830130521 8418129412777171372597891)
          ·
            refine ⟨12627194119165757058896837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418129412777171372597891 12627194119165757058896837)
            ·
              refine ⟨2367598897343579448543157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12627194119165757058896837 2367598897343579448543157)
              ·
                refine ⟨221962396625960573300921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2367598897343579448543157 221962396625960573300921)
                ·
                  refine ⟨166471797469470429975691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221962396625960573300921 166471797469470429975691)
                  ·
                    rfl

theorem cell20_364728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_364728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364728 prefixEnd_364728 := by exact prefixLift 364728
  have htrace : WordTrace (prefixWord ++ tailWord_364728) baseStart_364728 baseEnd_364728 := by
    simpa [prefixWord, tailWord_364728, baseEnd_364728] using wordTrace_append hprefix tailTrace_364728
  have hstable : (prefixWord ++ tailWord_364728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364728).length < 2 ^ (prefixWord ++ tailWord_364728).sum := by decide
  have hdescent : baseEnd_364728 < baseStart_364728 := by decide
  rcases family_descends (prefixWord ++ tailWord_364728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364783 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 2]
def baseStart_364783 : Nat := 118140960795 + 364783 * 2 ^ 59
def prefixEnd_364783 : Nat := 4983230072969 + 3 ^ 40 * 364783 * 2
def baseEnd_364783 : Nat := 166496900968134683142133

theorem tailTrace_364783 : CollatzResearch.WordTrace tailWord_364783 prefixEnd_364783 166496900968134683142133 := by
  unfold tailWord_364783
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304729037460965821555003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869819358307310547703335 13304729037460965821555003)
  ·
    refine ⟨19957093556191448732332505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13304729037460965821555003 19957093556191448732332505)
    ·
      refine ⟨14967820167143586549249379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19957093556191448732332505 14967820167143586549249379)
      ·
        refine ⟨22451730250715379823874069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967820167143586549249379 22451730250715379823874069)
        ·
          refine ⟨1052424855502283429244097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22451730250715379823874069 1052424855502283429244097)
          ·
            refine ⟨789318641626712571933073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052424855502283429244097 789318641626712571933073)
            ·
              refine ⟨591988981220034428949805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789318641626712571933073 591988981220034428949805)
              ·
                refine ⟨221995867957512910856177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591988981220034428949805 221995867957512910856177)
                ·
                  refine ⟨166496900968134683142133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221995867957512910856177 166496900968134683142133)
                  ·
                    rfl

theorem cell20_364783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2].length) (baseStart_364783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364783 prefixEnd_364783 := by exact prefixLift 364783
  have htrace : WordTrace (prefixWord ++ tailWord_364783) baseStart_364783 baseEnd_364783 := by
    simpa [prefixWord, tailWord_364783, baseEnd_364783] using wordTrace_append hprefix tailTrace_364783
  have hstable : (prefixWord ++ tailWord_364783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364783).length < 2 ^ (prefixWord ++ tailWord_364783).sum := by decide
  have hdescent : baseEnd_364783 < baseStart_364783 := by decide
  rcases family_descends (prefixWord ++ tailWord_364783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364794 : List Nat := [3, 1, 1, 1, 1, 6, 7]
def baseStart_364794 : Nat := 118140960795 + 364794 * 2 ^ 59
def prefixEnd_364794 : Nat := 4983230072969 + 3 ^ 40 * 364794 * 2
def baseEnd_364794 : Nat := 18500213518651948197269

theorem tailTrace_364794 : CollatzResearch.WordTrace tailWord_364794 prefixEnd_364794 18500213518651948197269 := by
  unfold tailWord_364794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326282560105278675051359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8870086826947409800136957 3326282560105278675051359)
  ·
    refine ⟨4989423840157918012577039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326282560105278675051359 4989423840157918012577039)
    ·
      refine ⟨7484135760236877018865559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4989423840157918012577039 7484135760236877018865559)
      ·
        refine ⟨11226203640355315528298339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484135760236877018865559 11226203640355315528298339)
        ·
          refine ⟨16839305460532973292447509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226203640355315528298339 16839305460532973292447509)
          ·
            refine ⟨789342443462483123083477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16839305460532973292447509 789342443462483123083477)
            ·
              refine ⟨18500213518651948197269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 789342443462483123083477 18500213518651948197269)
              ·
                rfl

theorem cell20_364794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_364794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364794 prefixEnd_364794 := by exact prefixLift 364794
  have htrace : WordTrace (prefixWord ++ tailWord_364794) baseStart_364794 baseEnd_364794 := by
    simpa [prefixWord, tailWord_364794, baseEnd_364794] using wordTrace_append hprefix tailTrace_364794
  have hstable : (prefixWord ++ tailWord_364794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364794).length < 2 ^ (prefixWord ++ tailWord_364794).sum := by decide
  have hdescent : baseEnd_364794 < baseStart_364794 := by decide
  rcases family_descends (prefixWord ++ tailWord_364794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364845 : List Nat := [1, 5, 3, 1, 3, 1, 6]
def baseStart_364845 : Nat := 118140960795 + 364845 * 2 ^ 59
def prefixEnd_364845 : Nat := 4983230072969 + 3 ^ 40 * 364845 * 2
def baseEnd_364845 : Nat := 18502799939726447008357

theorem tailTrace_364845 : CollatzResearch.WordTrace tailWord_364845 prefixEnd_364845 18502799939726447008357 := by
  unfold tailWord_364845
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306990363236350410311989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8871326908824233606874659 13306990363236350410311989)
  ·
    refine ⟨1247530346553407850966749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13306990363236350410311989 1247530346553407850966749)
    ·
      refine ⟨467823879957527944112531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1247530346553407850966749 467823879957527944112531)
      ·
        refine ⟨701735819936291916168797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467823879957527944112531 701735819936291916168797)
        ·
          refine ⟨263150932476109468563299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701735819936291916168797 263150932476109468563299)
          ·
            refine ⟨394726398714164202844949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263150932476109468563299 394726398714164202844949)
            ·
              refine ⟨18502799939726447008357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 394726398714164202844949 18502799939726447008357)
              ·
                rfl

theorem cell20_364845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_364845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364845 prefixEnd_364845 := by exact prefixLift 364845
  have htrace : WordTrace (prefixWord ++ tailWord_364845) baseStart_364845 baseEnd_364845 := by
    simpa [prefixWord, tailWord_364845, baseEnd_364845] using wordTrace_append hprefix tailTrace_364845
  have hstable : (prefixWord ++ tailWord_364845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364845).length < 2 ^ (prefixWord ++ tailWord_364845).sum := by decide
  have hdescent : baseEnd_364845 < baseStart_364845 := by decide
  rcases family_descends (prefixWord ++ tailWord_364845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364849 : List Nat := [1, 2, 2, 3, 4, 2, 6]
def baseStart_364849 : Nat := 118140960795 + 364849 * 2 ^ 59
def prefixEnd_364849 : Nat := 4983230072969 + 3 ^ 40 * 364849 * 2
def baseEnd_364849 : Nat := 18503002796281309660207

theorem tailTrace_364849 : CollatzResearch.WordTrace tailWord_364849 prefixEnd_364849 18503002796281309660207 := by
  unfold tailWord_364849
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307136255221859093457601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8871424170147906062305067 13307136255221859093457601)
  ·
    refine ⟨9980352191416394320093201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13307136255221859093457601 9980352191416394320093201)
    ·
      refine ⟨7485264143562295740069901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9980352191416394320093201 7485264143562295740069901)
      ·
        refine ⟨2806974053835860902526213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7485264143562295740069901 2806974053835860902526213)
        ·
          refine ⟨526307635094223919223665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2806974053835860902526213 526307635094223919223665)
          ·
            refine ⟨394730726320667939417749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526307635094223919223665 394730726320667939417749)
            ·
              refine ⟨18503002796281309660207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 394730726320667939417749 18503002796281309660207)
              ·
                rfl

theorem cell20_364849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_364849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364849 prefixEnd_364849 := by exact prefixLift 364849
  have htrace : WordTrace (prefixWord ++ tailWord_364849) baseStart_364849 baseEnd_364849 := by
    simpa [prefixWord, tailWord_364849, baseEnd_364849] using wordTrace_append hprefix tailTrace_364849
  have hstable : (prefixWord ++ tailWord_364849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364849).length < 2 ^ (prefixWord ++ tailWord_364849).sum := by decide
  have hdescent : baseEnd_364849 < baseStart_364849 := by decide
  rcases family_descends (prefixWord ++ tailWord_364849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364908 : List Nat := [2, 2, 1, 1, 6, 8]
def baseStart_364908 : Nat := 118140960795 + 364908 * 2 ^ 59
def prefixEnd_364908 : Nat := 4983230072969 + 3 ^ 40 * 364908 * 2
def baseEnd_364908 : Nat := 6168664976821844591665

theorem tailTrace_364908 : CollatzResearch.WordTrace tailWord_364908 prefixEnd_364908 6168664976821844591665 := by
  unfold tailWord_364908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654644081004056084927689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8872858774672074779903585 6654644081004056084927689)
  ·
    refine ⟨4990983060753042063695767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6654644081004056084927689 4990983060753042063695767)
    ·
      refine ⟨7486474591129563095543651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990983060753042063695767 7486474591129563095543651)
      ·
        refine ⟨11229711886694344643315477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486474591129563095543651 11229711886694344643315477)
        ·
          refine ⟨526392744688797405155413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11229711886694344643315477 526392744688797405155413)
          ·
            refine ⟨6168664976821844591665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 526392744688797405155413 6168664976821844591665)
            ·
              rfl

theorem cell20_364908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 8].length) (baseStart_364908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364908 prefixEnd_364908 := by exact prefixLift 364908
  have htrace : WordTrace (prefixWord ++ tailWord_364908) baseStart_364908 baseEnd_364908 := by
    simpa [prefixWord, tailWord_364908, baseEnd_364908] using wordTrace_append hprefix tailTrace_364908
  have hstable : (prefixWord ++ tailWord_364908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364908).length < 2 ^ (prefixWord ++ tailWord_364908).sum := by decide
  have hdescent : baseEnd_364908 < baseStart_364908 := by decide
  rcases family_descends (prefixWord ++ tailWord_364908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364914 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_364914 : Nat := 118140960795 + 364914 * 2 ^ 59
def prefixEnd_364914 : Nat := 4983230072969 + 3 ^ 40 * 364914 * 2
def baseEnd_364914 : Nat := 166556692937680449774931

theorem tailTrace_364914 : CollatzResearch.WordTrace tailWord_364914 prefixEnd_364914 166556692937680449774931 := by
  unfold tailWord_364914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327376749996593798643449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8873004666657583463049197 3327376749996593798643449)
  ·
    refine ⟨2495532562497445348982587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3327376749996593798643449 2495532562497445348982587)
    ·
      refine ⟨3743298843746168023473881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495532562497445348982587 3743298843746168023473881)
      ·
        refine ⟨2807474132809626017605411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743298843746168023473881 2807474132809626017605411)
        ·
          refine ⟨4211211199214439026408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807474132809626017605411 4211211199214439026408117)
          ·
            refine ⟨394801049926353658725761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4211211199214439026408117 394801049926353658725761)
            ·
              refine ⟨296100787444765244044321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394801049926353658725761 296100787444765244044321)
              ·
                refine ⟨222075590583573933033241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296100787444765244044321 222075590583573933033241)
                ·
                  refine ⟨166556692937680449774931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222075590583573933033241 166556692937680449774931)
                  ·
                    rfl

theorem cell20_364914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_364914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364914 prefixEnd_364914 := by exact prefixLift 364914
  have htrace : WordTrace (prefixWord ++ tailWord_364914) baseStart_364914 baseEnd_364914 := by
    simpa [prefixWord, tailWord_364914, baseEnd_364914] using wordTrace_append hprefix tailTrace_364914
  have hstable : (prefixWord ++ tailWord_364914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364914).length < 2 ^ (prefixWord ++ tailWord_364914).sum := by decide
  have hdescent : baseEnd_364914 < baseStart_364914 := by decide
  rcases family_descends (prefixWord ++ tailWord_364914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364925 : List Nat := [1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_364925 : Nat := 118140960795 + 364925 * 2 ^ 59
def prefixEnd_364925 : Nat := 4983230072969 + 3 ^ 40 * 364925 * 2
def baseEnd_364925 : Nat := 55520571212471100136073

theorem tailTrace_364925 : CollatzResearch.WordTrace tailWord_364925 prefixEnd_364925 55520571212471100136073 := by
  unfold tailWord_364925
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309908202946524073224229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8873272135297682715482819 13309908202946524073224229)
  ·
    refine ⟨2495607788052473263729543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13309908202946524073224229 2495607788052473263729543)
    ·
      refine ⟨3743411682078709895594315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495607788052473263729543 3743411682078709895594315)
      ·
        refine ⟨5615117523118064843391473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743411682078709895594315 5615117523118064843391473)
        ·
          refine ⟨4211338142338548632543605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615117523118064843391473 4211338142338548632543605)
          ·
            refine ⟨394812950844238934300963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4211338142338548632543605 394812950844238934300963)
            ·
              refine ⟨592219426266358401451445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394812950844238934300963 592219426266358401451445)
              ·
                refine ⟨55520571212471100136073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592219426266358401451445 55520571212471100136073)
                ·
                  rfl

theorem cell20_364925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_364925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364925 prefixEnd_364925 := by exact prefixLift 364925
  have htrace : WordTrace (prefixWord ++ tailWord_364925) baseStart_364925 baseEnd_364925 := by
    simpa [prefixWord, tailWord_364925, baseEnd_364925] using wordTrace_append hprefix tailTrace_364925
  have hstable : (prefixWord ++ tailWord_364925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364925).length < 2 ^ (prefixWord ++ tailWord_364925).sum := by decide
  have hdescent : baseEnd_364925 < baseStart_364925 := by decide
  rcases family_descends (prefixWord ++ tailWord_364925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364932 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_364932 : Nat := 118140960795 + 364932 * 2 ^ 59
def prefixEnd_364932 : Nat := 4983230072969 + 3 ^ 40 * 364932 * 2
def baseEnd_364932 : Nat := 166564908628152387174857

theorem tailTrace_364932 : CollatzResearch.WordTrace tailWord_364932 prefixEnd_364932 166564908628152387174857 := by
  unfold tailWord_364932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655081756960582134364525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8873442342614109512486033 6655081756960582134364525)
  ·
    refine ⟨2495655658860218300386697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6655081756960582134364525 2495655658860218300386697)
    ·
      refine ⟨1871741744145163725290023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2495655658860218300386697 1871741744145163725290023)
      ·
        refine ⟨2807612616217745587935035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871741744145163725290023 2807612616217745587935035)
        ·
          refine ⟨4211418924326618381902553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807612616217745587935035 4211418924326618381902553)
          ·
            refine ⟨3158564193244963786426915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211418924326618381902553 3158564193244963786426915)
            ·
              refine ⟨4737846289867445679640373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158564193244963786426915 4737846289867445679640373)
              ·
                refine ⟨444173089675073032466285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4737846289867445679640373 444173089675073032466285)
                ·
                  refine ⟨166564908628152387174857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444173089675073032466285 166564908628152387174857)
                  ·
                    rfl

theorem cell20_364932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_364932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364932 prefixEnd_364932 := by exact prefixLift 364932
  have htrace : WordTrace (prefixWord ++ tailWord_364932) baseStart_364932 baseEnd_364932 := by
    simpa [prefixWord, tailWord_364932, baseEnd_364932] using wordTrace_append hprefix tailTrace_364932
  have hstable : (prefixWord ++ tailWord_364932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364932).length < 2 ^ (prefixWord ++ tailWord_364932).sum := by decide
  have hdescent : baseEnd_364932 < baseStart_364932 := by decide
  rcases family_descends (prefixWord ++ tailWord_364932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364939 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_364939 : Nat := 118140960795 + 364939 * 2 ^ 59
def prefixEnd_364939 : Nat := 4983230072969 + 3 ^ 40 * 364939 * 2
def baseEnd_364939 : Nat := 166568103618891473941495

theorem tailTrace_364939 : CollatzResearch.WordTrace tailWord_364939 prefixEnd_364939 166568103618891473941495 := by
  unfold tailWord_364939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310418824895804464233871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8873612549930536309489247 13310418824895804464233871)
  ·
    refine ⟨19965628237343706696350807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13310418824895804464233871 19965628237343706696350807)
    ·
      refine ⟨29948442356015560044526211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19965628237343706696350807 29948442356015560044526211)
      ·
        refine ⟨44922663534023340066789317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29948442356015560044526211 44922663534023340066789317)
        ·
          refine ⟨8422999412629376262522997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44922663534023340066789317 8422999412629376262522997)
          ·
            refine ⟨789656194934004024611531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8422999412629376262522997 789656194934004024611531)
            ·
              refine ⟨1184484292401006036917297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789656194934004024611531 1184484292401006036917297)
              ·
                refine ⟨888363219300754527687973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184484292401006036917297 888363219300754527687973)
                ·
                  refine ⟨166568103618891473941495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888363219300754527687973 166568103618891473941495)
                  ·
                    rfl

theorem cell20_364939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_364939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364939 prefixEnd_364939 := by exact prefixLift 364939
  have htrace : WordTrace (prefixWord ++ tailWord_364939) baseStart_364939 baseEnd_364939 := by
    simpa [prefixWord, tailWord_364939, baseEnd_364939] using wordTrace_append hprefix tailTrace_364939
  have hstable : (prefixWord ++ tailWord_364939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364939).length < 2 ^ (prefixWord ++ tailWord_364939).sum := by decide
  have hdescent : baseEnd_364939 < baseStart_364939 := by decide
  rcases family_descends (prefixWord ++ tailWord_364939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364942 : List Nat := [4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_364942 : Nat := 118140960795 + 364942 * 2 ^ 59
def prefixEnd_364942 : Nat := 4983230072969 + 3 ^ 40 * 364942 * 2
def baseEnd_364942 : Nat := 55523157633545598947161

theorem tailTrace_364942 : CollatzResearch.WordTrace tailWord_364942 prefixEnd_364942 55523157633545598947161 := by
  unfold tailWord_364942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663816030485616997074135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8873685495923290651062053 1663816030485616997074135)
  ·
    refine ⟨2495724045728425495611203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663816030485616997074135 2495724045728425495611203)
    ·
      refine ⟨3743586068592638243416805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495724045728425495611203 3743586068592638243416805)
      ·
        refine ⟨701922387861119670640651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3743586068592638243416805 701922387861119670640651)
        ·
          refine ⟨1052883581791679505960977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701922387861119670640651 1052883581791679505960977)
          ·
            refine ⟨789662686343759629470733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052883581791679505960977 789662686343759629470733)
            ·
              refine ⟨296123507378909861051525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789662686343759629470733 296123507378909861051525)
              ·
                refine ⟨55523157633545598947161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296123507378909861051525 55523157633545598947161)
                ·
                  rfl

theorem cell20_364942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_364942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364942 prefixEnd_364942 := by exact prefixLift 364942
  have htrace : WordTrace (prefixWord ++ tailWord_364942) baseStart_364942 baseEnd_364942 := by
    simpa [prefixWord, tailWord_364942, baseEnd_364942] using wordTrace_append hprefix tailTrace_364942
  have hstable : (prefixWord ++ tailWord_364942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364942).length < 2 ^ (prefixWord ++ tailWord_364942).sum := by decide
  have hdescent : baseEnd_364942 < baseStart_364942 := by decide
  rcases family_descends (prefixWord ++ tailWord_364942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364953 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_364953 : Nat := 118140960795 + 364953 * 2 ^ 59
def prefixEnd_364953 : Nat := 4983230072969 + 3 ^ 40 * 364953 * 2
def baseEnd_364953 : Nat := 166574493600369647474771

theorem tailTrace_364953 : CollatzResearch.WordTrace tailWord_364953 prefixEnd_364953 166574493600369647474771 := by
  unfold tailWord_364953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310929446845084855243513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8873952964563389903495675 13310929446845084855243513)
  ·
    refine ⟨9983197085133813641432635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13310929446845084855243513 9983197085133813641432635)
    ·
      refine ⟨14974795627700720462148953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983197085133813641432635 14974795627700720462148953)
      ·
        refine ⟨11231096720775540346611715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14974795627700720462148953 11231096720775540346611715)
        ·
          refine ⟨16846645081163310519917573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231096720775540346611715 16846645081163310519917573)
          ·
            refine ⟨3158745952718120722484545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16846645081163310519917573 3158745952718120722484545)
            ·
              refine ⟨2369059464538590541863409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158745952718120722484545 2369059464538590541863409)
              ·
                refine ⟨1776794598403942906397557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369059464538590541863409 1776794598403942906397557)
                ·
                  refine ⟨166574493600369647474771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776794598403942906397557 166574493600369647474771)
                  ·
                    rfl

theorem cell20_364953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_364953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364953 prefixEnd_364953 := by exact prefixLift 364953
  have htrace : WordTrace (prefixWord ++ tailWord_364953) baseStart_364953 baseEnd_364953 := by
    simpa [prefixWord, tailWord_364953, baseEnd_364953] using wordTrace_append hprefix tailTrace_364953
  have hstable : (prefixWord ++ tailWord_364953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364953).length < 2 ^ (prefixWord ++ tailWord_364953).sum := by decide
  have hdescent : baseEnd_364953 < baseStart_364953 := by decide
  rcases family_descends (prefixWord ++ tailWord_364953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364973 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_364973 : Nat := 118140960795 + 364973 * 2 ^ 59
def prefixEnd_364973 : Nat := 4983230072969 + 3 ^ 40 * 364973 * 2
def baseEnd_364973 : Nat := 166583622145338466808023

theorem tailTrace_364973 : CollatzResearch.WordTrace tailWord_364973 prefixEnd_364973 166583622145338466808023 := by
  unfold tailWord_364973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311658906772628270971573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8874439271181752180647715 13311658906772628270971573)
  ·
    refine ⟨1247968022509933900403585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13311658906772628270971573 1247968022509933900403585)
    ·
      refine ⟨935976016882450425302689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247968022509933900403585 935976016882450425302689)
      ·
        refine ⟨701982012661837818977017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935976016882450425302689 701982012661837818977017)
        ·
          refine ⟨526486509496378364232763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701982012661837818977017 526486509496378364232763)
          ·
            refine ⟨789729764244567546349145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526486509496378364232763 789729764244567546349145)
            ·
              refine ⟨592297323183425659761859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789729764244567546349145 592297323183425659761859)
              ·
                refine ⟨888445984775138489642789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592297323183425659761859 888445984775138489642789)
                ·
                  refine ⟨166583622145338466808023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888445984775138489642789 166583622145338466808023)
                  ·
                    rfl

theorem cell20_364973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_364973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364973 prefixEnd_364973 := by exact prefixLift 364973
  have htrace : WordTrace (prefixWord ++ tailWord_364973) baseStart_364973 baseEnd_364973 := by
    simpa [prefixWord, tailWord_364973, baseEnd_364973] using wordTrace_append hprefix tailTrace_364973
  have hstable : (prefixWord ++ tailWord_364973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364973).length < 2 ^ (prefixWord ++ tailWord_364973).sum := by decide
  have hdescent : baseEnd_364973 < baseStart_364973 := by decide
  rcases family_descends (prefixWord ++ tailWord_364973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364977 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_364977 : Nat := 118140960795 + 364977 * 2 ^ 59
def prefixEnd_364977 : Nat := 4983230072969 + 3 ^ 40 * 364977 * 2
def baseEnd_364977 : Nat := 166585447854332230674673

theorem tailTrace_364977 : CollatzResearch.WordTrace tailWord_364977 prefixEnd_364977 166585447854332230674673 := by
  unfold tailWord_364977
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311804798758136954117185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8874536532505424636078123 13311804798758136954117185)
  ·
    refine ⟨9983853599068602715587889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13311804798758136954117185 9983853599068602715587889)
    ·
      refine ⟨7487890199301452036690917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9983853599068602715587889 7487890199301452036690917)
      ·
        refine ⟨1403979412369022256879547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7487890199301452036690917 1403979412369022256879547)
        ·
          refine ⟨2105969118553533385319321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403979412369022256879547 2105969118553533385319321)
          ·
            refine ⟨1579476838915150038989491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105969118553533385319321 1579476838915150038989491)
            ·
              refine ⟨2369215258372725058484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579476838915150038989491 2369215258372725058484237)
              ·
                refine ⟨888455721889771896931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2369215258372725058484237 888455721889771896931589)
                ·
                  refine ⟨166585447854332230674673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888455721889771896931589 166585447854332230674673)
                  ·
                    rfl

theorem cell20_364977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_364977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364977 prefixEnd_364977 := by exact prefixLift 364977
  have htrace : WordTrace (prefixWord ++ tailWord_364977) baseStart_364977 baseEnd_364977 := by
    simpa [prefixWord, tailWord_364977, baseEnd_364977] using wordTrace_append hprefix tailTrace_364977
  have hstable : (prefixWord ++ tailWord_364977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364977).length < 2 ^ (prefixWord ++ tailWord_364977).sum := by decide
  have hdescent : baseEnd_364977 < baseStart_364977 := by decide
  rcases family_descends (prefixWord ++ tailWord_364977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364993 : List Nat := [1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_364993 : Nat := 118140960795 + 364993 * 2 ^ 59
def prefixEnd_364993 : Nat := 4983230072969 + 3 ^ 40 * 364993 * 2
def baseEnd_364993 : Nat := 55530916896769095380425

theorem tailTrace_364993 : CollatzResearch.WordTrace tailWord_364993 prefixEnd_364993 55530916896769095380425 := by
  unfold tailWord_364993
  simp only [CollatzResearch.WordTrace]
  refine ⟨13312388366700171686699633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8874925577800114457799755 13312388366700171686699633)
  ·
    refine ⟨9984291275025128765024725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13312388366700171686699633 9984291275025128765024725)
    ·
      refine ⟨234006826758401455430267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9984291275025128765024725 234006826758401455430267)
      ·
        refine ⟨351010240137602183145401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234006826758401455430267 351010240137602183145401)
        ·
          refine ⟨263257680103201637359051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351010240137602183145401 263257680103201637359051)
          ·
            refine ⟨394886520154802456038577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263257680103201637359051 394886520154802456038577)
            ·
              refine ⟨296164890116101842028933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394886520154802456038577 296164890116101842028933)
              ·
                refine ⟨55530916896769095380425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296164890116101842028933 55530916896769095380425)
                ·
                  rfl

theorem cell20_364993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_364993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_364993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_364993 prefixEnd_364993 := by exact prefixLift 364993
  have htrace : WordTrace (prefixWord ++ tailWord_364993) baseStart_364993 baseEnd_364993 := by
    simpa [prefixWord, tailWord_364993, baseEnd_364993] using wordTrace_append hprefix tailTrace_364993
  have hstable : (prefixWord ++ tailWord_364993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364993).length < 2 ^ (prefixWord ++ tailWord_364993).sum := by decide
  have hdescent : baseEnd_364993 < baseStart_364993 := by decide
  rcases family_descends (prefixWord ++ tailWord_364993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365032 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_365032 : Nat := 118140960795 + 365032 * 2 ^ 59
def prefixEnd_365032 : Nat := 4983230072969 + 3 ^ 40 * 365032 * 2
def baseEnd_365032 : Nat := 166610551352996483841115

theorem tailTrace_365032 : CollatzResearch.WordTrace tailWord_365032 prefixEnd_365032 166610551352996483841115 := by
  unfold tailWord_365032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656905406779440673684675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8875873875705920898246233 6656905406779440673684675)
  ·
    refine ⟨9985358110169161010527013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6656905406779440673684675 9985358110169161010527013)
    ·
      refine ⟨1872254645656717689473815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9985358110169161010527013 1872254645656717689473815)
      ·
        refine ⟨2808381968485076534210723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872254645656717689473815 2808381968485076534210723)
        ·
          refine ⟨4212572952727614801316085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808381968485076534210723 4212572952727614801316085)
          ·
            refine ⟨394928714318213887623383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4212572952727614801316085 394928714318213887623383)
            ·
              refine ⟨592393071477320831435075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394928714318213887623383 592393071477320831435075)
              ·
                refine ⟨888589607215981247152613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592393071477320831435075 888589607215981247152613)
                ·
                  refine ⟨166610551352996483841115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888589607215981247152613 166610551352996483841115)
                  ·
                    rfl

theorem cell20_365032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_365032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365032 prefixEnd_365032 := by exact prefixLift 365032
  have htrace : WordTrace (prefixWord ++ tailWord_365032) baseStart_365032 baseEnd_365032 := by
    simpa [prefixWord, tailWord_365032, baseEnd_365032] using wordTrace_append hprefix tailTrace_365032
  have hstable : (prefixWord ++ tailWord_365032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365032).length < 2 ^ (prefixWord ++ tailWord_365032).sum := by decide
  have hdescent : baseEnd_365032 < baseStart_365032 := by decide
  rcases family_descends (prefixWord ++ tailWord_365032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365084 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_365084 : Nat := 118140960795 + 365084 * 2 ^ 59
def prefixEnd_365084 : Nat := 4983230072969 + 3 ^ 40 * 365084 * 2
def baseEnd_365084 : Nat := 166634285569915414107569

theorem tailTrace_365084 : CollatzResearch.WordTrace tailWord_365084 prefixEnd_365084 166634285569915414107569 := by
  unfold tailWord_365084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657853704685247114131153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8877138272913662818841537 6657853704685247114131153)
  ·
    refine ⟨4993390278513935335598365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6657853704685247114131153 4993390278513935335598365)
    ·
      refine ⟨1872521354442725750849387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4993390278513935335598365 1872521354442725750849387)
      ·
        refine ⟨2808782031664088626274081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872521354442725750849387 2808782031664088626274081)
        ·
          refine ⟨2106586523748066469705561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808782031664088626274081 2106586523748066469705561)
          ·
            refine ⟨1579939892811049852279171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2106586523748066469705561 1579939892811049852279171)
            ·
              refine ⟨2369909839216574778418757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579939892811049852279171 2369909839216574778418757)
              ·
                refine ⟨444358094853107770953517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2369909839216574778418757 444358094853107770953517)
                ·
                  refine ⟨166634285569915414107569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444358094853107770953517 166634285569915414107569)
                  ·
                    rfl

theorem cell20_365084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_365084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365084 prefixEnd_365084 := by exact prefixLift 365084
  have htrace : WordTrace (prefixWord ++ tailWord_365084) baseStart_365084 baseEnd_365084 := by
    simpa [prefixWord, tailWord_365084, baseEnd_365084] using wordTrace_append hprefix tailTrace_365084
  have hstable : (prefixWord ++ tailWord_365084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365084).length < 2 ^ (prefixWord ++ tailWord_365084).sum := by decide
  have hdescent : baseEnd_365084 < baseStart_365084 := by decide
  rcases family_descends (prefixWord ++ tailWord_365084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365143 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_365143 : Nat := 118140960795 + 365143 * 2 ^ 59
def prefixEnd_365143 : Nat := 4983230072969 + 3 ^ 40 * 365143 * 2
def baseEnd_365143 : Nat := 166661214777573431140661

theorem tailTrace_365143 : CollatzResearch.WordTrace tailWord_365143 prefixEnd_365143 166661214777573431140661 := by
  unfold tailWord_365143
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317859316156747304660083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8878572877437831536440055 13317859316156747304660083)
  ·
    refine ⟨19976788974235120956990125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13317859316156747304660083 19976788974235120956990125)
    ·
      refine ⟨7491295865338170358871297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19976788974235120956990125 7491295865338170358871297)
      ·
        refine ⟨5618471899003627769153473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491295865338170358871297 5618471899003627769153473)
        ·
          refine ⟨4213853924252720826865105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618471899003627769153473 4213853924252720826865105)
          ·
            refine ⟨3160390443189540620148829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213853924252720826865105 3160390443189540620148829)
            ·
              refine ⟨1185146416196077732555811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3160390443189540620148829 1185146416196077732555811)
              ·
                refine ⟨1777719624294116598833717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185146416196077732555811 1777719624294116598833717)
                ·
                  refine ⟨166661214777573431140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777719624294116598833717 166661214777573431140661)
                  ·
                    rfl

theorem cell20_365143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_365143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365143 prefixEnd_365143 := by exact prefixLift 365143
  have htrace : WordTrace (prefixWord ++ tailWord_365143) baseStart_365143 baseEnd_365143 := by
    simpa [prefixWord, tailWord_365143, baseEnd_365143] using wordTrace_append hprefix tailTrace_365143
  have hstable : (prefixWord ++ tailWord_365143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365143).length < 2 ^ (prefixWord ++ tailWord_365143).sum := by decide
  have hdescent : baseEnd_365143 < baseStart_365143 := by decide
  rcases family_descends (prefixWord ++ tailWord_365143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365170 : List Nat := [3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_365170 : Nat := 118140960795 + 365170 * 2 ^ 59
def prefixEnd_365170 : Nat := 4983230072969 + 3 ^ 40 * 365170 * 2
def baseEnd_365170 : Nat := 55557846104427112413517

theorem tailTrace_365170 : CollatzResearch.WordTrace tailWord_365170 prefixEnd_365170 55557846104427112413517 := by
  unfold tailWord_365170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329711021764732728973241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8879229391372620610595309 3329711021764732728973241)
  ·
    refine ⟨2497283266323549546729931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3329711021764732728973241 2497283266323549546729931)
    ·
      refine ⟨3745924899485324320094897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497283266323549546729931 3745924899485324320094897)
      ·
        refine ⟨2809443674613993240071173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745924899485324320094897 2809443674613993240071173)
        ·
          refine ⟨526770688990123732513345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2809443674613993240071173 526770688990123732513345)
          ·
            refine ⟨395078016742592799385009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526770688990123732513345 395078016742592799385009)
            ·
              refine ⟨296308512556944599538757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395078016742592799385009 296308512556944599538757)
              ·
                refine ⟨55557846104427112413517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296308512556944599538757 55557846104427112413517)
                ·
                  rfl

theorem cell20_365170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_365170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365170 prefixEnd_365170 := by exact prefixLift 365170
  have htrace : WordTrace (prefixWord ++ tailWord_365170) baseStart_365170 baseEnd_365170 := by
    simpa [prefixWord, tailWord_365170, baseEnd_365170] using wordTrace_append hprefix tailTrace_365170
  have hstable : (prefixWord ++ tailWord_365170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365170).length < 2 ^ (prefixWord ++ tailWord_365170).sum := by decide
  have hdescent : baseEnd_365170 < baseStart_365170 := by decide
  rcases family_descends (prefixWord ++ tailWord_365170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365184 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_365184 : Nat := 118140960795 + 365184 * 2 ^ 59
def prefixEnd_365184 : Nat := 4983230072969 + 3 ^ 40 * 365184 * 2
def baseEnd_365184 : Nat := 166679928294759510773827

theorem tailTrace_365184 : CollatzResearch.WordTrace tailWord_365184 prefixEnd_365184 166679928294759510773827 := by
  unfold tailWord_365184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659677354504105653451303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8879569806005474204601737 6659677354504105653451303)
  ·
    refine ⟨9989516031756158480176955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6659677354504105653451303 9989516031756158480176955)
    ·
      refine ⟨14984274047634237720265433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9989516031756158480176955 14984274047634237720265433)
      ·
        refine ⟨11238205535725678290199075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14984274047634237720265433 11238205535725678290199075)
        ·
          refine ⟨16857308303588517435298613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238205535725678290199075 16857308303588517435298613)
          ·
            refine ⟨1580372653461423509559245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16857308303588517435298613 1580372653461423509559245)
            ·
              refine ⟨592639745048033816084717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1580372653461423509559245 592639745048033816084717)
              ·
                refine ⟨222239904393012681031769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592639745048033816084717 222239904393012681031769)
                ·
                  refine ⟨166679928294759510773827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222239904393012681031769 166679928294759510773827)
                  ·
                    rfl

theorem cell20_365184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_365184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365184 prefixEnd_365184 := by exact prefixLift 365184
  have htrace : WordTrace (prefixWord ++ tailWord_365184) baseStart_365184 baseEnd_365184 := by
    simpa [prefixWord, tailWord_365184, baseEnd_365184] using wordTrace_append hprefix tailTrace_365184
  have hstable : (prefixWord ++ tailWord_365184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365184).length < 2 ^ (prefixWord ++ tailWord_365184).sum := by decide
  have hdescent : baseEnd_365184 < baseStart_365184 := by decide
  rcases family_descends (prefixWord ++ tailWord_365184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365198 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_365198 : Nat := 118140960795 + 365198 * 2 ^ 59
def prefixEnd_365198 : Nat := 4983230072969 + 3 ^ 40 * 365198 * 2
def baseEnd_365198 : Nat := 166686318276237684307103

theorem tailTrace_365198 : CollatzResearch.WordTrace tailWord_365198 prefixEnd_365198 166686318276237684307103 := by
  unfold tailWord_365198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664983166369686462239031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8879910220638327798608165 1664983166369686462239031)
  ·
    refine ⟨2497474749554529693358547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1664983166369686462239031 2497474749554529693358547)
    ·
      refine ⟨3746212124331794540037821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497474749554529693358547 3746212124331794540037821)
      ·
        refine ⟨1404829546624422952514183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3746212124331794540037821 1404829546624422952514183)
        ·
          refine ⟨2107244319936634428771275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404829546624422952514183 2107244319936634428771275)
          ·
            refine ⟨3160866479904951643156913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107244319936634428771275 3160866479904951643156913)
            ·
              refine ⟨2370649859928713732367685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160866479904951643156913 2370649859928713732367685)
              ·
                refine ⟨444496848736633824818941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2370649859928713732367685 444496848736633824818941)
                ·
                  refine ⟨166686318276237684307103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444496848736633824818941 166686318276237684307103)
                  ·
                    rfl

theorem cell20_365198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_365198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365198 prefixEnd_365198 := by exact prefixLift 365198
  have htrace : WordTrace (prefixWord ++ tailWord_365198) baseStart_365198 baseEnd_365198 := by
    simpa [prefixWord, tailWord_365198, baseEnd_365198] using wordTrace_append hprefix tailTrace_365198
  have hstable : (prefixWord ++ tailWord_365198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365198).length < 2 ^ (prefixWord ++ tailWord_365198).sum := by decide
  have hdescent : baseEnd_365198 < baseStart_365198 := by decide
  rcases family_descends (prefixWord ++ tailWord_365198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365212 : List Nat := [2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_365212 : Nat := 118140960795 + 365212 * 2 ^ 59
def prefixEnd_365212 : Nat := 4983230072969 + 3 ^ 40 * 365212 * 2
def baseEnd_365212 : Nat := 55564236085905285946793

theorem tailTrace_365212 : CollatzResearch.WordTrace tailWord_365212 prefixEnd_365212 55564236085905285946793 := by
  unfold tailWord_365212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6660187976453386044460945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8880250635271181392614593 6660187976453386044460945)
  ·
    refine ⟨4995140982340039533345709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6660187976453386044460945 4995140982340039533345709)
    ·
      refine ⟨1873177868377514825004641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4995140982340039533345709 1873177868377514825004641)
      ·
        refine ⟨1404883401283136118753481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1873177868377514825004641 1404883401283136118753481)
        ·
          refine ⟨1053662550962352089065111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404883401283136118753481 1053662550962352089065111)
          ·
            refine ⟨1580493826443528133597667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053662550962352089065111 1580493826443528133597667)
            ·
              refine ⟨2370740739665292200396501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580493826443528133597667 2370740739665292200396501)
              ·
                refine ⟨55564236085905285946793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370740739665292200396501 55564236085905285946793)
                ·
                  rfl

theorem cell20_365212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_365212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365212 prefixEnd_365212 := by exact prefixLift 365212
  have htrace : WordTrace (prefixWord ++ tailWord_365212) baseStart_365212 baseEnd_365212 := by
    simpa [prefixWord, tailWord_365212, baseEnd_365212] using wordTrace_append hprefix tailTrace_365212
  have hstable : (prefixWord ++ tailWord_365212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365212).length < 2 ^ (prefixWord ++ tailWord_365212).sum := by decide
  have hdescent : baseEnd_365212 < baseStart_365212 := by decide
  rcases family_descends (prefixWord ++ tailWord_365212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365281 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_365281 : Nat := 118140960795 + 365281 * 2 ^ 59
def prefixEnd_365281 : Nat := 4983230072969 + 3 ^ 40 * 365281 * 2
def baseEnd_365281 : Nat := 166724201737858284540097

theorem tailTrace_365281 : CollatzResearch.WordTrace tailWord_365281 prefixEnd_365281 166724201737858284540097 := by
  unfold tailWord_365281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13322892589656796873183697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8881928393104531248789131 13322892589656796873183697)
  ·
    refine ⟨9992169442242597654887773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13322892589656796873183697 9992169442242597654887773)
    ·
      refine ⟨3747063540840974120582915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9992169442242597654887773 3747063540840974120582915)
      ·
        refine ⟨5620595311261461180874373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747063540840974120582915 5620595311261461180874373)
        ·
          refine ⟨1053861620861523971413945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5620595311261461180874373 1053861620861523971413945)
          ·
            refine ⟨790396215646142978560459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053861620861523971413945 790396215646142978560459)
            ·
              refine ⟨1185594323469214467840689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790396215646142978560459 1185594323469214467840689)
              ·
                refine ⟨889195742601910850880517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185594323469214467840689 889195742601910850880517)
                ·
                  refine ⟨166724201737858284540097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889195742601910850880517 166724201737858284540097)
                  ·
                    rfl

theorem cell20_365281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_365281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365281 prefixEnd_365281 := by exact prefixLift 365281
  have htrace : WordTrace (prefixWord ++ tailWord_365281) baseStart_365281 baseEnd_365281 := by
    simpa [prefixWord, tailWord_365281, baseEnd_365281] using wordTrace_append hprefix tailTrace_365281
  have hstable : (prefixWord ++ tailWord_365281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365281).length < 2 ^ (prefixWord ++ tailWord_365281).sum := by decide
  have hdescent : baseEnd_365281 < baseStart_365281 := by decide
  rcases family_descends (prefixWord ++ tailWord_365281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365298 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_365298 : Nat := 118140960795 + 365298 * 2 ^ 59
def prefixEnd_365298 : Nat := 4983230072969 + 3 ^ 40 * 365298 * 2
def baseEnd_365298 : Nat := 166731961001081780973361

theorem tailTrace_365298 : CollatzResearch.WordTrace tailWord_365298 prefixEnd_365298 166731961001081780973361 := by
  unfold tailWord_365298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330878157648802194138137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8882341753730139184368365 3330878157648802194138137)
  ·
    refine ⟨2498158618236601645603603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3330878157648802194138137 2498158618236601645603603)
    ·
      refine ⟨3747237927354902468405405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498158618236601645603603 3747237927354902468405405)
      ·
        refine ⟨1405214222758088425652027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3747237927354902468405405 1405214222758088425652027)
        ·
          refine ⟨2107821334137132638478041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405214222758088425652027 2107821334137132638478041)
          ·
            refine ⟨1580866000602849478858531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107821334137132638478041 1580866000602849478858531)
            ·
              refine ⟨2371299000904274218287797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580866000602849478858531 2371299000904274218287797)
              ·
                refine ⟨222309281334775707964481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2371299000904274218287797 222309281334775707964481)
                ·
                  refine ⟨166731961001081780973361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222309281334775707964481 166731961001081780973361)
                  ·
                    rfl

theorem cell20_365298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_365298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365298 prefixEnd_365298 := by exact prefixLift 365298
  have htrace : WordTrace (prefixWord ++ tailWord_365298) baseStart_365298 baseEnd_365298 := by
    simpa [prefixWord, tailWord_365298, baseEnd_365298] using wordTrace_append hprefix tailTrace_365298
  have hstable : (prefixWord ++ tailWord_365298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365298).length < 2 ^ (prefixWord ++ tailWord_365298).sum := by decide
  have hdescent : baseEnd_365298 < baseStart_365298 := by decide
  rcases family_descends (prefixWord ++ tailWord_365298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365309 : List Nat := [1, 4, 1, 1, 1, 1, 11]
def baseStart_365309 : Nat := 118140960795 + 365309 * 2 ^ 59
def prefixEnd_365309 : Nat := 4983230072969 + 3 ^ 40 * 365309 * 2
def baseEnd_365309 : Nat := 18526331300090514622961

theorem tailTrace_365309 : CollatzResearch.WordTrace tailWord_365309 prefixEnd_365309 18526331300090514622961 := by
  unfold tailWord_365309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323913833555357655202981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8882609222370238436801987 13323913833555357655202981)
  ·
    refine ⟨2498233843791629560350559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13323913833555357655202981 2498233843791629560350559)
    ·
      refine ⟨3747350765687444340525839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498233843791629560350559 3747350765687444340525839)
      ·
        refine ⟨5621026148531166510788759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747350765687444340525839 5621026148531166510788759)
        ·
          refine ⟨8431539222796749766183139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621026148531166510788759 8431539222796749766183139)
          ·
            refine ⟨12647308834195124649274709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431539222796749766183139 12647308834195124649274709)
            ·
              refine ⟨18526331300090514622961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12647308834195124649274709 18526331300090514622961)
              ·
                rfl

theorem cell20_365309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_365309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365309 prefixEnd_365309 := by exact prefixLift 365309
  have htrace : WordTrace (prefixWord ++ tailWord_365309) baseStart_365309 baseEnd_365309 := by
    simpa [prefixWord, tailWord_365309, baseEnd_365309] using wordTrace_append hprefix tailTrace_365309
  have hstable : (prefixWord ++ tailWord_365309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365309).length < 2 ^ (prefixWord ++ tailWord_365309).sum := by decide
  have hdescent : baseEnd_365309 < baseStart_365309 := by decide
  rcases family_descends (prefixWord ++ tailWord_365309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365319 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_365319 : Nat := 118140960795 + 365319 * 2 ^ 59
def prefixEnd_365319 : Nat := 4983230072969 + 3 ^ 40 * 365319 * 2
def baseEnd_365319 : Nat := 166741545973299041273275

theorem tailTrace_365319 : CollatzResearch.WordTrace tailWord_365319 prefixEnd_365319 166741545973299041273275 := by
  unfold tailWord_365319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324278563519129363067011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8882852375679419575378007 13324278563519129363067011)
  ·
    refine ⟨19986417845278694044600517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13324278563519129363067011 19986417845278694044600517)
    ·
      refine ⟨3747453345989755133362597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19986417845278694044600517 3747453345989755133362597)
      ·
        refine ⟨702647502373079087505487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3747453345989755133362597 702647502373079087505487)
        ·
          refine ⟨1053971253559618631258231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702647502373079087505487 1053971253559618631258231)
          ·
            refine ⟨1580956880339427946887347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053971253559618631258231 1580956880339427946887347)
            ·
              refine ⟨2371435320509141920331021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580956880339427946887347 2371435320509141920331021)
              ·
                refine ⟨889288245190928220124133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371435320509141920331021 889288245190928220124133)
                ·
                  refine ⟨166741545973299041273275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889288245190928220124133 166741545973299041273275)
                  ·
                    rfl

theorem cell20_365319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_365319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365319 prefixEnd_365319 := by exact prefixLift 365319
  have htrace : WordTrace (prefixWord ++ tailWord_365319) baseStart_365319 baseEnd_365319 := by
    simpa [prefixWord, tailWord_365319, baseEnd_365319] using wordTrace_append hprefix tailTrace_365319
  have hstable : (prefixWord ++ tailWord_365319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365319).length < 2 ^ (prefixWord ++ tailWord_365319).sum := by decide
  have hdescent : baseEnd_365319 < baseStart_365319 := by decide
  rcases family_descends (prefixWord ++ tailWord_365319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365343 : List Nat := [1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_365343 : Nat := 118140960795 + 365343 * 2 ^ 59
def prefixEnd_365343 : Nat := 4983230072969 + 3 ^ 40 * 365343 * 2
def baseEnd_365343 : Nat := 55584166742420541491059

theorem tailTrace_365343 : CollatzResearch.WordTrace tailWord_365343 prefixEnd_365343 55584166742420541491059 := by
  unfold tailWord_365343
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325153915432181461940683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8883435943621454307960455 13325153915432181461940683)
  ·
    refine ⟨19987730873148272192911025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13325153915432181461940683 19987730873148272192911025)
    ·
      refine ⟨14990798154861204144683269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19987730873148272192911025 14990798154861204144683269)
      ·
        refine ⟨2810774654036475777128113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14990798154861204144683269 2810774654036475777128113)
        ·
          refine ⟨2108080990527356832846085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810774654036475777128113 2108080990527356832846085)
          ·
            refine ⟨395265185723879406158641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2108080990527356832846085 395265185723879406158641)
            ·
              refine ⟨296448889292909554618981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395265185723879406158641 296448889292909554618981)
              ·
                refine ⟨55584166742420541491059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296448889292909554618981 55584166742420541491059)
                ·
                  rfl

theorem cell20_365343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_365343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365343 prefixEnd_365343 := by exact prefixLift 365343
  have htrace : WordTrace (prefixWord ++ tailWord_365343) baseStart_365343 baseEnd_365343 := by
    simpa [prefixWord, tailWord_365343, baseEnd_365343] using wordTrace_append hprefix tailTrace_365343
  have hstable : (prefixWord ++ tailWord_365343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365343).length < 2 ^ (prefixWord ++ tailWord_365343).sum := by decide
  have hdescent : baseEnd_365343 < baseStart_365343 := by decide
  rcases family_descends (prefixWord ++ tailWord_365343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365380 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_365380 : Nat := 118140960795 + 365380 * 2 ^ 59
def prefixEnd_365380 : Nat := 4983230072969 + 3 ^ 40 * 365380 * 2
def baseEnd_365380 : Nat := 166769388035453940239693

theorem tailTrace_365380 : CollatzResearch.WordTrace tailWord_365380 prefixEnd_365380 166769388035453940239693 := by
  unfold tailWord_365380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663251708149068390518797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8884335610865424520691729 6663251708149068390518797)
  ·
    refine ⟨2498719390555900646444549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6663251708149068390518797 2498719390555900646444549)
    ·
      refine ⟨468509885729231371208353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2498719390555900646444549 468509885729231371208353)
      ·
        refine ⟨351382414296923528406265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468509885729231371208353 351382414296923528406265)
        ·
          refine ⟨263536810722692646304699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351382414296923528406265 263536810722692646304699)
          ·
            refine ⟨395305216084038969457049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263536810722692646304699 395305216084038969457049)
            ·
              refine ⟨296478912063029227092787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395305216084038969457049 296478912063029227092787)
              ·
                refine ⟨444718368094543840639181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296478912063029227092787 444718368094543840639181)
                ·
                  refine ⟨166769388035453940239693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444718368094543840639181 166769388035453940239693)
                  ·
                    rfl

theorem cell20_365380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_365380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365380 prefixEnd_365380 := by exact prefixLift 365380
  have htrace : WordTrace (prefixWord ++ tailWord_365380) baseStart_365380 baseEnd_365380 := by
    simpa [prefixWord, tailWord_365380, baseEnd_365380] using wordTrace_append hprefix tailTrace_365380
  have hstable : (prefixWord ++ tailWord_365380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365380).length < 2 ^ (prefixWord ++ tailWord_365380).sum := by decide
  have hdescent : baseEnd_365380 < baseStart_365380 := by decide
  rcases family_descends (prefixWord ++ tailWord_365380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365385 : List Nat := [1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_365385 : Nat := 118140960795 + 365385 * 2 ^ 59
def prefixEnd_365385 : Nat := 4983230072969 + 3 ^ 40 * 365385 * 2
def baseEnd_365385 : Nat := 55590556723898715024335

theorem tailTrace_365385 : CollatzResearch.WordTrace tailWord_365385 prefixEnd_365385 55590556723898715024335 := by
  unfold tailWord_365385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326685781280022634969609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884457187520015089979739 13326685781280022634969609)
  ·
    refine ⟨9995014335960016976227207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13326685781280022634969609 9995014335960016976227207)
    ·
      refine ⟨14992521503940025464340811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995014335960016976227207 14992521503940025464340811)
      ·
        refine ⟨22488782255910038196511217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992521503940025464340811 22488782255910038196511217)
        ·
          refine ⟨16866586691932528647383413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22488782255910038196511217 16866586691932528647383413)
          ·
            refine ⟨1581242502368674560692195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16866586691932528647383413 1581242502368674560692195)
            ·
              refine ⟨2371863753553011841038293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581242502368674560692195 2371863753553011841038293)
              ·
                refine ⟨55590556723898715024335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2371863753553011841038293 55590556723898715024335)
                ·
                  rfl

theorem cell20_365385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_365385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365385 prefixEnd_365385 := by exact prefixLift 365385
  have htrace : WordTrace (prefixWord ++ tailWord_365385) baseStart_365385 baseEnd_365385 := by
    simpa [prefixWord, tailWord_365385, baseEnd_365385] using wordTrace_append hprefix tailTrace_365385
  have hstable : (prefixWord ++ tailWord_365385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365385).length < 2 ^ (prefixWord ++ tailWord_365385).sum := by decide
  have hdescent : baseEnd_365385 < baseStart_365385 := by decide
  rcases family_descends (prefixWord ++ tailWord_365385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365388 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_365388 : Nat := 118140960795 + 365388 * 2 ^ 59
def prefixEnd_365388 : Nat := 4983230072969 + 3 ^ 40 * 365388 * 2
def baseEnd_365388 : Nat := 166773039453441467972993

theorem tailTrace_365388 : CollatzResearch.WordTrace tailWord_365388 prefixEnd_365388 166773039453441467972993 := by
  unfold tailWord_365388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663397600134577073664409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8884530133512769431552545 6663397600134577073664409)
  ·
    refine ⟨4997548200100932805248307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6663397600134577073664409 4997548200100932805248307)
    ·
      refine ⟨7496322300151399207872461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997548200100932805248307 7496322300151399207872461)
      ·
        refine ⟨2811120862556774702952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7496322300151399207872461 2811120862556774702952173)
        ·
          refine ⟨1054170323458790513607065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811120862556774702952173 1054170323458790513607065)
          ·
            refine ⟨790627742594092885205299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054170323458790513607065 790627742594092885205299)
            ·
              refine ⟨1185941613891139327807949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790627742594092885205299 1185941613891139327807949)
              ·
                refine ⟨444728105209177247927981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185941613891139327807949 444728105209177247927981)
                ·
                  refine ⟨166773039453441467972993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444728105209177247927981 166773039453441467972993)
                  ·
                    rfl

theorem cell20_365388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_365388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365388 prefixEnd_365388 := by exact prefixLift 365388
  have htrace : WordTrace (prefixWord ++ tailWord_365388) baseStart_365388 baseEnd_365388 := by
    simpa [prefixWord, tailWord_365388, baseEnd_365388] using wordTrace_append hprefix tailTrace_365388
  have hstable : (prefixWord ++ tailWord_365388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365388).length < 2 ^ (prefixWord ++ tailWord_365388).sum := by decide
  have hdescent : baseEnd_365388 < baseStart_365388 := by decide
  rcases family_descends (prefixWord ++ tailWord_365388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365429 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 2]
def baseStart_365429 : Nat := 118140960795 + 365429 * 2 ^ 59
def prefixEnd_365429 : Nat := 4983230072969 + 3 ^ 40 * 365429 * 2
def baseEnd_365429 : Nat := 166791752970627547606159

theorem tailTrace_365429 : CollatzResearch.WordTrace tailWord_365429 prefixEnd_365429 166791752970627547606159 := by
  unfold tailWord_365429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328290593120618149571341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8885527062080412099714227 13328290593120618149571341)
  ·
    refine ⟨4998108972420231806089253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13328290593120618149571341 4998108972420231806089253)
    ·
      refine ⟨937145432328793463641735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4998108972420231806089253 937145432328793463641735)
      ·
        refine ⟨1405718148493190195462603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937145432328793463641735 1405718148493190195462603)
        ·
          refine ⟨2108577222739785293193905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405718148493190195462603 2108577222739785293193905)
          ·
            refine ⟨1581432917054838969895429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108577222739785293193905 1581432917054838969895429)
            ·
              refine ⟨296518671947782306855393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1581432917054838969895429 296518671947782306855393)
              ·
                refine ⟨222389003960836730141545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296518671947782306855393 222389003960836730141545)
                ·
                  refine ⟨166791752970627547606159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222389003960836730141545 166791752970627547606159)
                  ·
                    rfl

theorem cell20_365429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_365429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365429 prefixEnd_365429 := by exact prefixLift 365429
  have htrace : WordTrace (prefixWord ++ tailWord_365429) baseStart_365429 baseEnd_365429 := by
    simpa [prefixWord, tailWord_365429, baseEnd_365429] using wordTrace_append hprefix tailTrace_365429
  have hstable : (prefixWord ++ tailWord_365429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365429).length < 2 ^ (prefixWord ++ tailWord_365429).sum := by decide
  have hdescent : baseEnd_365429 < baseStart_365429 := by decide
  rcases family_descends (prefixWord ++ tailWord_365429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365494 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_365494 : Nat := 118140960795 + 365494 * 2 ^ 59
def prefixEnd_365494 : Nat := 4983230072969 + 3 ^ 40 * 365494 * 2
def baseEnd_365494 : Nat := 166821420741776210439227

theorem tailTrace_365494 : CollatzResearch.WordTrace tailWord_365494 prefixEnd_365494 166821420741776210439227 := by
  unfold tailWord_365494
  simp only [CollatzResearch.WordTrace]
  refine ⟨833166333617820890667971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8887107558590089500458357 833166333617820890667971)
  ·
    refine ⟨1249749500426731336001957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833166333617820890667971 1249749500426731336001957)
    ·
      refine ⟨234328031330012125500367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1249749500426731336001957 234328031330012125500367)
      ·
        refine ⟨351492046995018188250551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234328031330012125500367 351492046995018188250551)
        ·
          refine ⟨527238070492527282375827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351492046995018188250551 527238070492527282375827)
          ·
            refine ⟨790857105738790923563741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527238070492527282375827 790857105738790923563741)
            ·
              refine ⟨296571414652046596336403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790857105738790923563741 296571414652046596336403)
              ·
                refine ⟨444857121978069894504605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296571414652046596336403 444857121978069894504605)
                ·
                  refine ⟨166821420741776210439227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444857121978069894504605 166821420741776210439227)
                  ·
                    rfl

theorem cell20_365494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_365494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365494 prefixEnd_365494 := by exact prefixLift 365494
  have htrace : WordTrace (prefixWord ++ tailWord_365494) baseStart_365494 baseEnd_365494 := by
    simpa [prefixWord, tailWord_365494, baseEnd_365494] using wordTrace_append hprefix tailTrace_365494
  have hstable : (prefixWord ++ tailWord_365494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365494).length < 2 ^ (prefixWord ++ tailWord_365494).sum := by decide
  have hdescent : baseEnd_365494 < baseStart_365494 := by decide
  rcases family_descends (prefixWord ++ tailWord_365494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365512 : List Nat := [2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_365512 : Nat := 118140960795 + 365512 * 2 ^ 59
def prefixEnd_365512 : Nat := 4983230072969 + 3 ^ 40 * 365512 * 2
def baseEnd_365512 : Nat := 55609878810749382613051

theorem tailTrace_365512 : CollatzResearch.WordTrace tailWord_365512 prefixEnd_365512 55609878810749382613051 := by
  unfold tailWord_365512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665658925909961662421395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8887545234546615549895193 6665658925909961662421395)
  ·
    refine ⟨9998488388864942493632093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6665658925909961662421395 9998488388864942493632093)
    ·
      refine ⟨3749433145824353435112035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9998488388864942493632093 3749433145824353435112035)
      ·
        refine ⟨5624149718736530152668053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749433145824353435112035 5624149718736530152668053)
        ·
          refine ⟨263632018065774850906315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5624149718736530152668053 263632018065774850906315)
          ·
            refine ⟨395448027098662276359473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263632018065774850906315 395448027098662276359473)
            ·
              refine ⟨296586020323996707269605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395448027098662276359473 296586020323996707269605)
              ·
                refine ⟨55609878810749382613051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296586020323996707269605 55609878810749382613051)
                ·
                  rfl

theorem cell20_365512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_365512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365512 prefixEnd_365512 := by exact prefixLift 365512
  have htrace : WordTrace (prefixWord ++ tailWord_365512) baseStart_365512 baseEnd_365512 := by
    simpa [prefixWord, tailWord_365512, baseEnd_365512] using wordTrace_append hprefix tailTrace_365512
  have hstable : (prefixWord ++ tailWord_365512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365512).length < 2 ^ (prefixWord ++ tailWord_365512).sum := by decide
  have hdescent : baseEnd_365512 < baseStart_365512 := by decide
  rcases family_descends (prefixWord ++ tailWord_365512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365543 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 2]
def baseStart_365543 : Nat := 118140960795 + 365543 * 2 ^ 59
def prefixEnd_365543 : Nat := 4983230072969 + 3 ^ 40 * 365543 * 2
def baseEnd_365543 : Nat := 166843785676949817805693

theorem tailTrace_365543 : CollatzResearch.WordTrace tailWord_365543 prefixEnd_365543 166843785676949817805693 := by
  unfold tailWord_365543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332448514707615619221283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8888299009805077079480855 13332448514707615619221283)
  ·
    refine ⟨19998672772061423428831925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332448514707615619221283 19998672772061423428831925)
    ·
      refine ⟨1874875572380758446452993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19998672772061423428831925 1874875572380758446452993)
      ·
        refine ⟨1406156679285568834839745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874875572380758446452993 1406156679285568834839745)
        ·
          refine ⟨1054617509464176626129809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406156679285568834839745 1054617509464176626129809)
          ·
            refine ⟨790963132098132469597357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054617509464176626129809 790963132098132469597357)
            ·
              refine ⟨296611174536799676099009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790963132098132469597357 296611174536799676099009)
              ·
                refine ⟨222458380902599757074257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296611174536799676099009 222458380902599757074257)
                ·
                  refine ⟨166843785676949817805693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222458380902599757074257 166843785676949817805693)
                  ·
                    rfl

theorem cell20_365543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2].length) (baseStart_365543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_365543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_365543 prefixEnd_365543 := by exact prefixLift 365543
  have htrace : WordTrace (prefixWord ++ tailWord_365543) baseStart_365543 baseEnd_365543 := by
    simpa [prefixWord, tailWord_365543, baseEnd_365543] using wordTrace_append hprefix tailTrace_365543
  have hstable : (prefixWord ++ tailWord_365543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365543).length < 2 ^ (prefixWord ++ tailWord_365543).sum := by decide
  have hdescent : baseEnd_365543 < baseStart_365543 := by decide
  rcases family_descends (prefixWord ++ tailWord_365543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
