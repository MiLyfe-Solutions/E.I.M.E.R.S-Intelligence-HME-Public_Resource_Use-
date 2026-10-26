import V185TrunkScan22Chunk085

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_771582 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_771582 : Nat := 118140960795 + 771582 * 2 ^ 59
def prefixEnd_771582 : Nat := 4983230072969 + 3 ^ 40 * 771582 * 2
def baseEnd_771582 : Nat := 264128286905003610384377

theorem tailTrace_771582 : CollatzResearch.WordTrace tailWord_771582 prefixEnd_771582 264128286905003610384377 := by
  unfold tailWord_771582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517738436337208069938625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18761271660465109706339333 3517738436337208069938625)
  ·
    refine ⟨2638303827252906052453969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3517738436337208069938625 2638303827252906052453969)
    ·
      refine ⟨1978727870439679539340477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2638303827252906052453969 1978727870439679539340477)
      ·
        refine ⟨742022951414879827252679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1978727870439679539340477 742022951414879827252679)
        ·
          refine ⟨1113034427122319740879019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742022951414879827252679 1113034427122319740879019)
          ·
            refine ⟨1669551640683479611318529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113034427122319740879019 1669551640683479611318529)
            ·
              refine ⟨1252163730512609708488897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669551640683479611318529 1252163730512609708488897)
              ·
                refine ⟨939122797884457281366673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252163730512609708488897 939122797884457281366673)
                ·
                  refine ⟨704342098413342961025005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939122797884457281366673 704342098413342961025005)
                  ·
                    refine ⟨264128286905003610384377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704342098413342961025005 264128286905003610384377)
                    ·
                      rfl

theorem cell22_771582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_771582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771582 prefixEnd_771582 := by exact prefixLift 771582
  have htrace : WordTrace (prefixWord ++ tailWord_771582) baseStart_771582 baseEnd_771582 := by
    simpa [prefixWord, tailWord_771582, baseEnd_771582] using wordTrace_append hprefix tailTrace_771582
  have hstable : (prefixWord ++ tailWord_771582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771582).length < 2 ^ (prefixWord ++ tailWord_771582).sum := by decide
  have hdescent : baseEnd_771582 < baseStart_771582 := by decide
  rcases family_descends (prefixWord ++ tailWord_771582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771593 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_771593 : Nat := 118140960795 + 771593 * 2 ^ 59
def prefixEnd_771593 : Nat := 4983230072969 + 3 ^ 40 * 771593 * 2
def baseEnd_771593 : Nat := 264132052429803248359343

theorem tailTrace_771593 : CollatzResearch.WordTrace tailWord_771593 prefixEnd_771593 264132052429803248359343 := by
  unfold tailWord_771593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28142308693657813438159433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18761539129105208958772955 28142308693657813438159433)
  ·
    refine ⟨21106731520243360078619575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28142308693657813438159433 21106731520243360078619575)
    ·
      refine ⟨31660097280365040117929363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21106731520243360078619575 31660097280365040117929363)
      ·
        refine ⟨47490145920547560176894045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31660097280365040117929363 47490145920547560176894045)
        ·
          refine ⟨17808804720205335066335267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47490145920547560176894045 17808804720205335066335267)
          ·
            refine ⟨26713207080308002599502901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17808804720205335066335267 26713207080308002599502901)
            ·
              refine ⟨2504363163778875243703397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26713207080308002599502901 2504363163778875243703397)
              ·
                refine ⟨469568093208539108194387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2504363163778875243703397 469568093208539108194387)
                ·
                  refine ⟨704352139812808662291581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469568093208539108194387 704352139812808662291581)
                  ·
                    refine ⟨264132052429803248359343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704352139812808662291581 264132052429803248359343)
                    ·
                      rfl

theorem cell22_771593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_771593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771593 prefixEnd_771593 := by exact prefixLift 771593
  have htrace : WordTrace (prefixWord ++ tailWord_771593) baseStart_771593 baseEnd_771593 := by
    simpa [prefixWord, tailWord_771593, baseEnd_771593] using wordTrace_append hprefix tailTrace_771593
  have hstable : (prefixWord ++ tailWord_771593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771593).length < 2 ^ (prefixWord ++ tailWord_771593).sum := by decide
  have hdescent : baseEnd_771593 < baseStart_771593 := by decide
  rcases family_descends (prefixWord ++ tailWord_771593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771614 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_771614 : Nat := 118140960795 + 771614 * 2 ^ 59
def prefixEnd_771614 : Nat := 4983230072969 + 3 ^ 40 * 771614 * 2
def baseEnd_771614 : Nat := 264139241158966193584279

theorem tailTrace_771614 : CollatzResearch.WordTrace tailWord_771614 prefixEnd_771614 264139241158966193584279 := by
  unfold tailWord_771614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517884328322716753084237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18762049751054489349782597 3517884328322716753084237)
  ·
    refine ⟨1319206623121018782406589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3517884328322716753084237 1319206623121018782406589)
    ·
      refine ⟨494702483670382043402471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1319206623121018782406589 494702483670382043402471)
      ·
        refine ⟨742053725505573065103707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494702483670382043402471 742053725505573065103707)
        ·
          refine ⟨1113080588258359597655561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742053725505573065103707 1113080588258359597655561)
          ·
            refine ⟨834810441193769698241671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113080588258359597655561 834810441193769698241671)
            ·
              refine ⟨1252215661790654547362507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834810441193769698241671 1252215661790654547362507)
              ·
                refine ⟨1878323492685981821043761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252215661790654547362507 1878323492685981821043761)
                ·
                  refine ⟨1408742619514486365782821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878323492685981821043761 1408742619514486365782821)
                  ·
                    refine ⟨264139241158966193584279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408742619514486365782821 264139241158966193584279)
                    ·
                      rfl

theorem cell22_771614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_771614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771614 prefixEnd_771614 := by exact prefixLift 771614
  have htrace : WordTrace (prefixWord ++ tailWord_771614) baseStart_771614 baseEnd_771614 := by
    simpa [prefixWord, tailWord_771614, baseEnd_771614] using wordTrace_append hprefix tailTrace_771614
  have hstable : (prefixWord ++ tailWord_771614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771614).length < 2 ^ (prefixWord ++ tailWord_771614).sum := by decide
  have hdescent : baseEnd_771614 < baseStart_771614 := by decide
  rcases family_descends (prefixWord ++ tailWord_771614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771634 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_771634 : Nat := 118140960795 + 771634 * 2 ^ 59
def prefixEnd_771634 : Nat := 4983230072969 + 3 ^ 40 * 771634 * 2
def baseEnd_771634 : Nat := 88048695855897602694739

theorem tailTrace_771634 : CollatzResearch.WordTrace tailWord_771634 prefixEnd_771634 88048695855897602694739 := by
  unfold tailWord_771634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035951021627319360100489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18762536057672851626934637 7035951021627319360100489)
  ·
    refine ⟨5276963266220489520075367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7035951021627319360100489 5276963266220489520075367)
    ·
      refine ⟨7915444899330734280113051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276963266220489520075367 7915444899330734280113051)
      ·
        refine ⟨11873167348996101420169577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915444899330734280113051 11873167348996101420169577)
        ·
          refine ⟨8904875511747076065127183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11873167348996101420169577 8904875511747076065127183)
          ·
            refine ⟨13357313267620614097690775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904875511747076065127183 13357313267620614097690775)
            ·
              refine ⟨20035969901430921146536163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357313267620614097690775 20035969901430921146536163)
              ·
                refine ⟨30053954852146381719804245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20035969901430921146536163 30053954852146381719804245)
                ·
                  refine ⟨88048695855897602694739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30053954852146381719804245 88048695855897602694739)
                  ·
                    rfl

theorem cell22_771634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_771634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771634 prefixEnd_771634 := by exact prefixLift 771634
  have htrace : WordTrace (prefixWord ++ tailWord_771634) baseStart_771634 baseEnd_771634 := by
    simpa [prefixWord, tailWord_771634, baseEnd_771634] using wordTrace_append hprefix tailTrace_771634
  have hstable : (prefixWord ++ tailWord_771634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771634).length < 2 ^ (prefixWord ++ tailWord_771634).sum := by decide
  have hdescent : baseEnd_771634 < baseStart_771634 := by decide
  rcases family_descends (prefixWord ++ tailWord_771634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771664 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_771664 : Nat := 118140960795 + 771664 * 2 ^ 59
def prefixEnd_771664 : Nat := 4983230072969 + 3 ^ 40 * 771664 * 2
def baseEnd_771664 : Nat := 264156357180782729834125

theorem tailTrace_771664 : CollatzResearch.WordTrace tailWord_771664 prefixEnd_771664 264156357180782729834125 := by
  unfold tailWord_771664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072449138200296281997023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18763265517600395042662697 14072449138200296281997023)
  ·
    refine ⟨21108673707300444422995535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14072449138200296281997023 21108673707300444422995535)
    ·
      refine ⟨31663010560950666634493303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21108673707300444422995535 31663010560950666634493303)
      ·
        refine ⟨47494515841425999951739955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31663010560950666634493303 47494515841425999951739955)
        ·
          refine ⟨71241773762138999927609933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47494515841425999951739955 71241773762138999927609933)
          ·
            refine ⟨26715665160802124972853725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71241773762138999927609933 26715665160802124972853725)
            ·
              refine ⟨10018374435300796864820147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26715665160802124972853725 10018374435300796864820147)
              ·
                refine ⟨15027561652951195297230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10018374435300796864820147 15027561652951195297230221)
                ·
                  refine ⟨5635335619856698236461333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15027561652951195297230221 5635335619856698236461333)
                  ·
                    refine ⟨264156357180782729834125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5635335619856698236461333 264156357180782729834125)
                    ·
                      rfl

theorem cell22_771664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_771664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771664 prefixEnd_771664 := by exact prefixLift 771664
  have htrace : WordTrace (prefixWord ++ tailWord_771664) baseStart_771664 baseEnd_771664 := by
    simpa [prefixWord, tailWord_771664, baseEnd_771664] using wordTrace_append hprefix tailTrace_771664
  have hstable : (prefixWord ++ tailWord_771664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771664).length < 2 ^ (prefixWord ++ tailWord_771664).sum := by decide
  have hdescent : baseEnd_771664 < baseStart_771664 := by decide
  rcases family_descends (prefixWord ++ tailWord_771664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771681 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_771681 : Nat := 118140960795 + 771681 * 2 ^ 59
def prefixEnd_771681 : Nat := 4983230072969 + 3 ^ 40 * 771681 * 2
def baseEnd_771681 : Nat := 264162176628200352159073

theorem tailTrace_771681 : CollatzResearch.WordTrace tailWord_771681 prefixEnd_771681 264162176628200352159073 := by
  unfold tailWord_771681
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145518317339004467362897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18763678878226002978241931 28145518317339004467362897)
  ·
    refine ⟨21109138738004253350522173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28145518317339004467362897 21109138738004253350522173)
    ·
      refine ⟨7915927026751595006445815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21109138738004253350522173 7915927026751595006445815)
      ·
        refine ⟨11873890540127392509668723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915927026751595006445815 11873890540127392509668723)
        ·
          refine ⟨17810835810191088764503085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873890540127392509668723 17810835810191088764503085)
          ·
            refine ⟨6679063428821658286688657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17810835810191088764503085 6679063428821658286688657)
            ·
              refine ⟨5009297571616243715016493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679063428821658286688657 5009297571616243715016493)
              ·
                refine ⟨1878486589356091393131185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5009297571616243715016493 1878486589356091393131185)
                ·
                  refine ⟨1408864942017068544848389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878486589356091393131185 1408864942017068544848389)
                  ·
                    refine ⟨264162176628200352159073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408864942017068544848389 264162176628200352159073)
                    ·
                      rfl

theorem cell22_771681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_771681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771681 prefixEnd_771681 := by exact prefixLift 771681
  have htrace : WordTrace (prefixWord ++ tailWord_771681) baseStart_771681 baseEnd_771681 := by
    simpa [prefixWord, tailWord_771681, baseEnd_771681] using wordTrace_append hprefix tailTrace_771681
  have hstable : (prefixWord ++ tailWord_771681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771681).length < 2 ^ (prefixWord ++ tailWord_771681).sum := by decide
  have hdescent : baseEnd_771681 < baseStart_771681 := by decide
  rcases family_descends (prefixWord ++ tailWord_771681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771685 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 4]
def baseStart_771685 : Nat := 118140960795 + 771685 * 2 ^ 59
def prefixEnd_771685 : Nat := 4983230072969 + 3 ^ 40 * 771685 * 2
def baseEnd_771685 : Nat := 88054515303315225019687

theorem tailTrace_771685 : CollatzResearch.WordTrace tailWord_771685 prefixEnd_771685 88054515303315225019687 := by
  unfold tailWord_771685
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145664209324513150508509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18763776139549675433672339 28145664209324513150508509)
  ·
    refine ⟨10554624078496692431440691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28145664209324513150508509 10554624078496692431440691)
    ·
      refine ⟨15831936117745038647161037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554624078496692431440691 15831936117745038647161037)
      ·
        refine ⟨5936976044154389492685389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15831936117745038647161037 5936976044154389492685389)
        ·
          refine ⟨2226366016557896059757021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5936976044154389492685389 2226366016557896059757021)
          ·
            refine ⟨834887256209211022408883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2226366016557896059757021 834887256209211022408883)
            ·
              refine ⟨1252330884313816533613325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834887256209211022408883 1252330884313816533613325)
              ·
                refine ⟨469624081617681200104997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252330884313816533613325 469624081617681200104997)
                ·
                  refine ⟨88054515303315225019687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469624081617681200104997 88054515303315225019687)
                  ·
                    rfl

theorem cell22_771685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_771685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771685 prefixEnd_771685 := by exact prefixLift 771685
  have htrace : WordTrace (prefixWord ++ tailWord_771685) baseStart_771685 baseEnd_771685 := by
    simpa [prefixWord, tailWord_771685, baseEnd_771685] using wordTrace_append hprefix tailTrace_771685
  have hstable : (prefixWord ++ tailWord_771685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771685).length < 2 ^ (prefixWord ++ tailWord_771685).sum := by decide
  have hdescent : baseEnd_771685 < baseStart_771685 := by decide
  rcases family_descends (prefixWord ++ tailWord_771685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771696 : List Nat := [2, 1, 1, 1, 6, 3, 8]
def baseStart_771696 : Nat := 118140960795 + 771696 * 2 ^ 59
def prefixEnd_771696 : Nat := 4983230072969 + 3 ^ 40 * 771696 * 2
def baseEnd_771696 : Nat := 9783974497583159742001

theorem tailTrace_771696 : CollatzResearch.WordTrace tailWord_771696 prefixEnd_771696 9783974497583159742001 := by
  unfold tailWord_771696
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073032706142331014579471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18764043608189774686105961 14073032706142331014579471)
  ·
    refine ⟨21109549059213496521869207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14073032706142331014579471 21109549059213496521869207)
    ·
      refine ⟨31664323588820244782803811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21109549059213496521869207 31664323588820244782803811)
      ·
        refine ⟨47496485383230367174205717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31664323588820244782803811 47496485383230367174205717)
        ·
          refine ⟨2226397752338923461290893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47496485383230367174205717 2226397752338923461290893)
          ·
            refine ⟨834899157127096297984085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2226397752338923461290893 834899157127096297984085)
            ·
              refine ⟨9783974497583159742001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 834899157127096297984085 9783974497583159742001)
              ·
                rfl

theorem cell22_771696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 8].length) (baseStart_771696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771696 prefixEnd_771696 := by exact prefixLift 771696
  have htrace : WordTrace (prefixWord ++ tailWord_771696) baseStart_771696 baseEnd_771696 := by
    simpa [prefixWord, tailWord_771696, baseEnd_771696] using wordTrace_append hprefix tailTrace_771696
  have hstable : (prefixWord ++ tailWord_771696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771696).length < 2 ^ (prefixWord ++ tailWord_771696).sum := by decide
  have hdescent : baseEnd_771696 < baseStart_771696 := by decide
  rcases family_descends (prefixWord ++ tailWord_771696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771698 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_771698 : Nat := 118140960795 + 771698 * 2 ^ 59
def prefixEnd_771698 : Nat := 4983230072969 + 3 ^ 40 * 771698 * 2
def baseEnd_771698 : Nat := 264167996075617974484021

theorem tailTrace_771698 : CollatzResearch.WordTrace tailWord_771698 prefixEnd_771698 264167996075617974484021 := by
  unfold tailWord_771698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036534589569354092682937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18764092238851610913821165 7036534589569354092682937)
  ·
    refine ⟨5277400942177015569512203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7036534589569354092682937 5277400942177015569512203)
    ·
      refine ⟨7916101413265523354268305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277400942177015569512203 7916101413265523354268305)
      ·
        refine ⟨5937076059949142515701229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916101413265523354268305 5937076059949142515701229)
        ·
          refine ⟨2226403522480928443387961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5937076059949142515701229 2226403522480928443387961)
          ·
            refine ⟨1669802641860696332540971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226403522480928443387961 1669802641860696332540971)
            ·
              refine ⟨2504703962791044498811457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669802641860696332540971 2504703962791044498811457)
              ·
                refine ⟨1878527972093283374108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504703962791044498811457 1878527972093283374108593)
                ·
                  refine ⟨1408895979069962530581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878527972093283374108593 1408895979069962530581445)
                  ·
                    refine ⟨264167996075617974484021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408895979069962530581445 264167996075617974484021)
                    ·
                      rfl

theorem cell22_771698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_771698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771698 prefixEnd_771698 := by exact prefixLift 771698
  have htrace : WordTrace (prefixWord ++ tailWord_771698) baseStart_771698 baseEnd_771698 := by
    simpa [prefixWord, tailWord_771698, baseEnd_771698] using wordTrace_append hprefix tailTrace_771698
  have hstable : (prefixWord ++ tailWord_771698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771698).length < 2 ^ (prefixWord ++ tailWord_771698).sum := by decide
  have hdescent : baseEnd_771698 < baseStart_771698 := by decide
  rcases family_descends (prefixWord ++ tailWord_771698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771702 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_771702 : Nat := 118140960795 + 771702 * 2 ^ 59
def prefixEnd_771702 : Nat := 4983230072969 + 3 ^ 40 * 771702 * 2
def baseEnd_771702 : Nat := 88056455119121099128003

theorem tailTrace_771702 : CollatzResearch.WordTrace tailWord_771702 prefixEnd_771702 88056455119121099128003 := by
  unfold tailWord_771702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759142765641432815867335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18764189500175283369251573 1759142765641432815867335)
  ·
    refine ⟨2638714148462149223801003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759142765641432815867335 2638714148462149223801003)
    ·
      refine ⟨3958071222693223835701505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638714148462149223801003 3958071222693223835701505)
      ·
        refine ⟨2968553417019917876776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3958071222693223835701505 2968553417019917876776129)
        ·
          refine ⟨2226415062764938407582097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2968553417019917876776129 2226415062764938407582097)
          ·
            refine ⟨1669811297073703805686573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226415062764938407582097 1669811297073703805686573)
            ·
              refine ⟨626179236402638927132465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669811297073703805686573 626179236402638927132465)
              ·
                refine ⟨469634427301979195349349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626179236402638927132465 469634427301979195349349)
                ·
                  refine ⟨88056455119121099128003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469634427301979195349349 88056455119121099128003)
                  ·
                    rfl

theorem cell22_771702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_771702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771702 prefixEnd_771702 := by exact prefixLift 771702
  have htrace : WordTrace (prefixWord ++ tailWord_771702) baseStart_771702 baseEnd_771702 := by
    simpa [prefixWord, tailWord_771702, baseEnd_771702] using wordTrace_append hprefix tailTrace_771702
  have hstable : (prefixWord ++ tailWord_771702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771702).length < 2 ^ (prefixWord ++ tailWord_771702).sum := by decide
  have hdescent : baseEnd_771702 < baseStart_771702 := by decide
  rcases family_descends (prefixWord ++ tailWord_771702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771762 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_771762 : Nat := 118140960795 + 771762 * 2 ^ 59
def prefixEnd_771762 : Nat := 4983230072969 + 3 ^ 40 * 771762 * 2
def baseEnd_771762 : Nat := 264189904583543140883825

theorem tailTrace_771762 : CollatzResearch.WordTrace tailWord_771762 prefixEnd_771762 264189904583543140883825 := by
  unfold tailWord_771762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037118157511388825265385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18765648420030370200707693 7037118157511388825265385)
  ·
    refine ⟨5277838618133541618949039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7037118157511388825265385 5277838618133541618949039)
    ·
      refine ⟨7916757927200312428423559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277838618133541618949039 7916757927200312428423559)
      ·
        refine ⟨11875136890800468642635339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916757927200312428423559 11875136890800468642635339)
        ·
          refine ⟨17812705336200702963953009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875136890800468642635339 17812705336200702963953009)
          ·
            refine ⟨13359529002150527222964757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17812705336200702963953009 13359529002150527222964757)
            ·
              refine ⟨626227921975805963576473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13359529002150527222964757 626227921975805963576473)
              ·
                refine ⟨469670941481854472682355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626227921975805963576473 469670941481854472682355)
                ·
                  refine ⟨704506412222781709023533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469670941481854472682355 704506412222781709023533)
                  ·
                    refine ⟨264189904583543140883825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704506412222781709023533 264189904583543140883825)
                    ·
                      rfl

theorem cell22_771762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_771762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771762 prefixEnd_771762 := by exact prefixLift 771762
  have htrace : WordTrace (prefixWord ++ tailWord_771762) baseStart_771762 baseEnd_771762 := by
    simpa [prefixWord, tailWord_771762, baseEnd_771762] using wordTrace_append hprefix tailTrace_771762
  have hstable : (prefixWord ++ tailWord_771762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771762).length < 2 ^ (prefixWord ++ tailWord_771762).sum := by decide
  have hdescent : baseEnd_771762 < baseStart_771762 := by decide
  rcases family_descends (prefixWord ++ tailWord_771762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771886 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_771886 : Nat := 118140960795 + 771886 * 2 ^ 59
def prefixEnd_771886 : Nat := 4983230072969 + 3 ^ 40 * 771886 * 2
def baseEnd_771886 : Nat := 264232352317648150783445

theorem tailTrace_771886 : CollatzResearch.WordTrace tailWord_771886 prefixEnd_771886 264232352317648150783445 := by
  unfold tailWord_771886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519124410199540559821939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18768663521064216319050341 3519124410199540559821939)
  ·
    refine ⟨5278686615299310839732909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519124410199540559821939 5278686615299310839732909)
    ·
      refine ⟨1979507480737241564899841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5278686615299310839732909 1979507480737241564899841)
      ·
        refine ⟨1484630610552931173674881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979507480737241564899841 1484630610552931173674881)
        ·
          refine ⟨1113472957914698380256161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484630610552931173674881 1113472957914698380256161)
          ·
            refine ⟨835104718436023785192121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113472957914698380256161 835104718436023785192121)
            ·
              refine ⟨626328538827017838894091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835104718436023785192121 626328538827017838894091)
              ·
                refine ⟨939492808240526758341137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626328538827017838894091 939492808240526758341137)
                ·
                  refine ⟨704619606180395068755853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939492808240526758341137 704619606180395068755853)
                  ·
                    refine ⟨264232352317648150783445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704619606180395068755853 264232352317648150783445)
                    ·
                      rfl

theorem cell22_771886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_771886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771886 prefixEnd_771886 := by exact prefixLift 771886
  have htrace : WordTrace (prefixWord ++ tailWord_771886) baseStart_771886 baseEnd_771886 := by
    simpa [prefixWord, tailWord_771886, baseEnd_771886] using wordTrace_append hprefix tailTrace_771886
  have hstable : (prefixWord ++ tailWord_771886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771886).length < 2 ^ (prefixWord ++ tailWord_771886).sum := by decide
  have hdescent : baseEnd_771886 < baseStart_771886 := by decide
  rcases family_descends (prefixWord ++ tailWord_771886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771968 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_771968 : Nat := 118140960795 + 771968 * 2 ^ 59
def prefixEnd_771968 : Nat := 4983230072969 + 3 ^ 40 * 771968 * 2
def baseEnd_771968 : Nat := 264260422593427270233193

theorem tailTrace_771968 : CollatzResearch.WordTrace tailWord_771968 prefixEnd_771968 264260422593427270233193 := by
  unfold tailWord_771968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077993033649626241530279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18770657378199501655373705 14077993033649626241530279)
  ·
    refine ⟨21116989550474439362295419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14077993033649626241530279 21116989550474439362295419)
    ·
      refine ⟨31675484325711659043443129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21116989550474439362295419 31675484325711659043443129)
      ·
        refine ⟨23756613244283744282582347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31675484325711659043443129 23756613244283744282582347)
        ·
          refine ⟨35634919866425616423873521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23756613244283744282582347 35634919866425616423873521)
          ·
            refine ⟨26726189899819212317905141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35634919866425616423873521 26726189899819212317905141)
            ·
              refine ⟨2505580303108051154803607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26726189899819212317905141 2505580303108051154803607)
              ·
                refine ⟨3758370454662076732205411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505580303108051154803607 3758370454662076732205411)
                ·
                  refine ⟨5637555681993115098308117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758370454662076732205411 5637555681993115098308117)
                  ·
                    refine ⟨264260422593427270233193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5637555681993115098308117 264260422593427270233193)
                    ·
                      rfl

theorem cell22_771968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_771968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771968 prefixEnd_771968 := by exact prefixLift 771968
  have htrace : WordTrace (prefixWord ++ tailWord_771968) baseStart_771968 baseEnd_771968 := by
    simpa [prefixWord, tailWord_771968, baseEnd_771968] using wordTrace_append hprefix tailTrace_771968
  have hstable : (prefixWord ++ tailWord_771968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771968).length < 2 ^ (prefixWord ++ tailWord_771968).sum := by decide
  have hdescent : baseEnd_771968 < baseStart_771968 := by decide
  rcases family_descends (prefixWord ++ tailWord_771968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772004 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_772004 : Nat := 118140960795 + 772004 * 2 ^ 59
def prefixEnd_772004 : Nat := 4983230072969 + 3 ^ 40 * 772004 * 2
def baseEnd_772004 : Nat := 264272746129135176333083

theorem tailTrace_772004 : CollatzResearch.WordTrace tailWord_772004 prefixEnd_772004 264272746129135176333083 := by
  unfold tailWord_772004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078649547584415315685533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18771532730112553754247377 14078649547584415315685533)
  ·
    refine ⟨5279493580344155743382075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14078649547584415315685533 5279493580344155743382075)
    ·
      refine ⟨7919240370516233615073113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279493580344155743382075 7919240370516233615073113)
      ·
        refine ⟨5939430277887175211304835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7919240370516233615073113 5939430277887175211304835)
        ·
          refine ⟨8909145416830762816957253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939430277887175211304835 8909145416830762816957253)
          ·
            refine ⟨1670464765655768028179485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8909145416830762816957253 1670464765655768028179485)
            ·
              refine ⟨626424287120913010567307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670464765655768028179485 626424287120913010567307)
              ·
                refine ⟨939636430681369515850961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626424287120913010567307 939636430681369515850961)
                ·
                  refine ⟨704727323011027136888221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939636430681369515850961 704727323011027136888221)
                  ·
                    refine ⟨264272746129135176333083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704727323011027136888221 264272746129135176333083)
                    ·
                      rfl

theorem cell22_772004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_772004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772004 prefixEnd_772004 := by exact prefixLift 772004
  have htrace : WordTrace (prefixWord ++ tailWord_772004) baseStart_772004 baseEnd_772004 := by
    simpa [prefixWord, tailWord_772004, baseEnd_772004] using wordTrace_append hprefix tailTrace_772004
  have hstable : (prefixWord ++ tailWord_772004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772004).length < 2 ^ (prefixWord ++ tailWord_772004).sum := by decide
  have hdescent : baseEnd_772004 < baseStart_772004 := by decide
  rcases family_descends (prefixWord ++ tailWord_772004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772015 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 3, 3]
def baseStart_772015 : Nat := 118140960795 + 772015 * 2 ^ 59
def prefixEnd_772015 : Nat := 4983230072969 + 3 ^ 40 * 772015 * 2
def baseEnd_772015 : Nat := 264276511653934814308049

theorem tailTrace_772015 : CollatzResearch.WordTrace tailWord_772015 prefixEnd_772015 264276511653934814308049 := by
  unfold tailWord_772015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28157700298128979510021499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18771800198752653006680999 28157700298128979510021499)
  ·
    refine ⟨42236550447193469265032249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28157700298128979510021499 42236550447193469265032249)
    ·
      refine ⟨31677412835395101948774187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42236550447193469265032249 31677412835395101948774187)
      ·
        refine ⟨47516119253092652923161281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31677412835395101948774187 47516119253092652923161281)
        ·
          refine ⟨35637089439819489692370961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47516119253092652923161281 35637089439819489692370961)
          ·
            refine ⟨26727817079864617269278221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35637089439819489692370961 26727817079864617269278221)
            ·
              refine ⟨10022931404949231475979333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26727817079864617269278221 10022931404949231475979333)
              ·
                refine ⟨1879299638427980901746125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10022931404949231475979333 1879299638427980901746125)
                ·
                  refine ⟨704737364410492838154797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1879299638427980901746125 704737364410492838154797)
                  ·
                    refine ⟨264276511653934814308049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704737364410492838154797 264276511653934814308049)
                    ·
                      rfl

theorem cell22_772015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_772015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772015 prefixEnd_772015 := by exact prefixLift 772015
  have htrace : WordTrace (prefixWord ++ tailWord_772015) baseStart_772015 baseEnd_772015 := by
    simpa [prefixWord, tailWord_772015, baseEnd_772015] using wordTrace_append hprefix tailTrace_772015
  have hstable : (prefixWord ++ tailWord_772015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772015).length < 2 ^ (prefixWord ++ tailWord_772015).sum := by decide
  have hdescent : baseEnd_772015 < baseStart_772015 := by decide
  rcases family_descends (prefixWord ++ tailWord_772015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772017 : List Nat := [1, 2, 2, 4, 2, 3, 2, 6]
def baseStart_772017 : Nat := 118140960795 + 772017 * 2 ^ 59
def prefixEnd_772017 : Nat := 4983230072969 + 3 ^ 40 * 772017 * 2
def baseEnd_772017 : Nat := 29364132921645275084227

theorem tailTrace_772017 : CollatzResearch.WordTrace tailWord_772017 prefixEnd_772017 29364132921645275084227 := by
  unfold tailWord_772017
  simp only [CollatzResearch.WordTrace]
  refine ⟨28157773244121733851594305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18771848829414489234396203 28157773244121733851594305)
  ·
    refine ⟨21118329933091300388695729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28157773244121733851594305 21118329933091300388695729)
    ·
      refine ⟨15838747449818475291521797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21118329933091300388695729 15838747449818475291521797)
      ·
        refine ⟨2969765146840964117160337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15838747449818475291521797 2969765146840964117160337)
        ·
          refine ⟨2227323860130723087870253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969765146840964117160337 2227323860130723087870253)
          ·
            refine ⟨835246447549021157951345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2227323860130723087870253 835246447549021157951345)
            ·
              refine ⟨626434835661765868463509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835246447549021157951345 626434835661765868463509)
              ·
                refine ⟨29364132921645275084227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 626434835661765868463509 29364132921645275084227)
                ·
                  rfl

theorem cell22_772017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 6].length) (baseStart_772017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772017 prefixEnd_772017 := by exact prefixLift 772017
  have htrace : WordTrace (prefixWord ++ tailWord_772017) baseStart_772017 baseEnd_772017 := by
    simpa [prefixWord, tailWord_772017, baseEnd_772017] using wordTrace_append hprefix tailTrace_772017
  have hstable : (prefixWord ++ tailWord_772017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772017).length < 2 ^ (prefixWord ++ tailWord_772017).sum := by decide
  have hdescent : baseEnd_772017 < baseStart_772017 := by decide
  rcases family_descends (prefixWord ++ tailWord_772017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772100 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_772100 : Nat := 118140960795 + 772100 * 2 ^ 59
def prefixEnd_772100 : Nat := 4983230072969 + 3 ^ 40 * 772100 * 2
def baseEnd_772100 : Nat := 264305608891022925932789

theorem tailTrace_772100 : CollatzResearch.WordTrace tailWord_772100 prefixEnd_772100 264305608891022925932789 := by
  unfold tailWord_772100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14080400251410519513432877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18773867001880692684577169 14080400251410519513432877)
  ·
    refine ⟨5280150094278944817537329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14080400251410519513432877 5280150094278944817537329)
    ·
      refine ⟨3960112570709208613152997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5280150094278944817537329 3960112570709208613152997)
      ·
        refine ⟨742521107007976614966187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3960112570709208613152997 742521107007976614966187)
        ·
          refine ⟨1113781660511964922449281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742521107007976614966187 1113781660511964922449281)
          ·
            refine ⟨835336245383973691836961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113781660511964922449281 835336245383973691836961)
            ·
              refine ⟨626502184037980268877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835336245383973691836961 626502184037980268877721)
              ·
                refine ⟨469876638028485201658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626502184037980268877721 469876638028485201658291)
                ·
                  refine ⟨704814957042727802487437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469876638028485201658291 704814957042727802487437)
                  ·
                    refine ⟨264305608891022925932789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704814957042727802487437 264305608891022925932789)
                    ·
                      rfl

theorem cell22_772100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_772100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772100 prefixEnd_772100 := by exact prefixLift 772100
  have htrace : WordTrace (prefixWord ++ tailWord_772100) baseStart_772100 baseEnd_772100 := by
    simpa [prefixWord, tailWord_772100, baseEnd_772100] using wordTrace_append hprefix tailTrace_772100
  have hstable : (prefixWord ++ tailWord_772100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772100).length < 2 ^ (prefixWord ++ tailWord_772100).sum := by decide
  have hdescent : baseEnd_772100 < baseStart_772100 := by decide
  rcases family_descends (prefixWord ++ tailWord_772100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772107 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 4]
def baseStart_772107 : Nat := 118140960795 + 772107 * 2 ^ 59
def prefixEnd_772107 : Nat := 4983230072969 + 3 ^ 40 * 772107 * 2
def baseEnd_772107 : Nat := 88102668378025747002589

theorem tailTrace_772107 : CollatzResearch.WordTrace tailWord_772107 prefixEnd_772107 88102668378025747002589 := by
  unfold tailWord_772107
  simp only [CollatzResearch.WordTrace]
  refine ⟨28161055813795679222370575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18774037209197119481580383 28161055813795679222370575)
  ·
    refine ⟨42241583720693518833555863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28161055813795679222370575 42241583720693518833555863)
    ·
      refine ⟨63362375581040278250333795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42241583720693518833555863 63362375581040278250333795)
      ·
        refine ⟨95043563371560417375500693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63362375581040278250333795 95043563371560417375500693)
        ·
          refine ⟨4455167033041894564476595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95043563371560417375500693 4455167033041894564476595)
          ·
            refine ⟨6682750549562841846714893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455167033041894564476595 6682750549562841846714893)
            ·
              refine ⟨2506031456086065692518085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6682750549562841846714893 2506031456086065692518085)
              ·
                refine ⟨469880898016137317347141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2506031456086065692518085 469880898016137317347141)
                ·
                  refine ⟨88102668378025747002589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469880898016137317347141 88102668378025747002589)
                  ·
                    rfl

theorem cell22_772107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 4].length) (baseStart_772107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772107 prefixEnd_772107 := by exact prefixLift 772107
  have htrace : WordTrace (prefixWord ++ tailWord_772107) baseStart_772107 baseEnd_772107 := by
    simpa [prefixWord, tailWord_772107, baseEnd_772107] using wordTrace_append hprefix tailTrace_772107
  have hstable : (prefixWord ++ tailWord_772107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772107).length < 2 ^ (prefixWord ++ tailWord_772107).sum := by decide
  have hdescent : baseEnd_772107 < baseStart_772107 := by decide
  rcases family_descends (prefixWord ++ tailWord_772107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772120 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_772120 : Nat := 118140960795 + 772120 * 2 ^ 59
def prefixEnd_772120 : Nat := 4983230072969 + 3 ^ 40 * 772120 * 2
def baseEnd_772120 : Nat := 264312455299749540432727

theorem tailTrace_772120 : CollatzResearch.WordTrace tailWord_772120 prefixEnd_772120 264312455299749540432727 := by
  unfold tailWord_772120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14080764981374291221296907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18774353308499054961729209 14080764981374291221296907)
  ·
    refine ⟨21121147472061436831945361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14080764981374291221296907 21121147472061436831945361)
    ·
      refine ⟨15840860604046077623959021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21121147472061436831945361 15840860604046077623959021)
      ·
        refine ⟨5940322726517279108984633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15840860604046077623959021 5940322726517279108984633)
        ·
          refine ⟨4455242044887959331738475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940322726517279108984633 4455242044887959331738475)
          ·
            refine ⟨6682863067331938997607713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455242044887959331738475 6682863067331938997607713)
            ·
              refine ⟨5012147300498954248205785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682863067331938997607713 5012147300498954248205785)
              ·
                refine ⟨3759110475374215686154339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012147300498954248205785 3759110475374215686154339)
                ·
                  refine ⟨5638665713061323529231509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759110475374215686154339 5638665713061323529231509)
                  ·
                    refine ⟨264312455299749540432727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5638665713061323529231509 264312455299749540432727)
                    ·
                      rfl

theorem cell22_772120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_772120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772120 prefixEnd_772120 := by exact prefixLift 772120
  have htrace : WordTrace (prefixWord ++ tailWord_772120) baseStart_772120 baseEnd_772120 := by
    simpa [prefixWord, tailWord_772120, baseEnd_772120] using wordTrace_append hprefix tailTrace_772120
  have hstable : (prefixWord ++ tailWord_772120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772120).length < 2 ^ (prefixWord ++ tailWord_772120).sum := by decide
  have hdescent : baseEnd_772120 < baseStart_772120 := by decide
  rcases family_descends (prefixWord ++ tailWord_772120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772122 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_772122 : Nat := 118140960795 + 772122 * 2 ^ 59
def prefixEnd_772122 : Nat := 4983230072969 + 3 ^ 40 * 772122 * 2
def baseEnd_772122 : Nat := 264313139940622201882721

theorem tailTrace_772122 : CollatzResearch.WordTrace tailWord_772122 prefixEnd_772122 264313139940622201882721 := by
  unfold tailWord_772122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040400727185334196041655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18774401939160891189444413 7040400727185334196041655)
  ·
    refine ⟨10560601090778001294062483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7040400727185334196041655 10560601090778001294062483)
    ·
      refine ⟨15840901636167001941093725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10560601090778001294062483 15840901636167001941093725)
      ·
        refine ⟨5940338113562625727910147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15840901636167001941093725 5940338113562625727910147)
        ·
          refine ⟨8910507170343938591865221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940338113562625727910147 8910507170343938591865221)
          ·
            refine ⟨1670720094439488485974729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8910507170343938591865221 1670720094439488485974729)
            ·
              refine ⟨1253040070829616364481047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670720094439488485974729 1253040070829616364481047)
              ·
                refine ⟨1879560106244424546721571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253040070829616364481047 1879560106244424546721571)
                ·
                  refine ⟨2819340159366636820082357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879560106244424546721571 2819340159366636820082357)
                  ·
                    refine ⟨264313139940622201882721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2819340159366636820082357 264313139940622201882721)
                    ·
                      rfl

theorem cell22_772122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_772122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772122 prefixEnd_772122 := by exact prefixLift 772122
  have htrace : WordTrace (prefixWord ++ tailWord_772122) baseStart_772122 baseEnd_772122 := by
    simpa [prefixWord, tailWord_772122, baseEnd_772122] using wordTrace_append hprefix tailTrace_772122
  have hstable : (prefixWord ++ tailWord_772122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772122).length < 2 ^ (prefixWord ++ tailWord_772122).sum := by decide
  have hdescent : baseEnd_772122 < baseStart_772122 := by decide
  rcases family_descends (prefixWord ++ tailWord_772122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772195 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_772195 : Nat := 118140960795 + 772195 * 2 ^ 59
def prefixEnd_772195 : Nat := 4983230072969 + 3 ^ 40 * 772195 * 2
def baseEnd_772195 : Nat := 264338129332474344807497

theorem tailTrace_772195 : CollatzResearch.WordTrace tailWord_772195 prefixEnd_772195 264338129332474344807497 := by
  unfold tailWord_772195
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164265437476870251574039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18776176958317913501049359 28164265437476870251574039)
  ·
    refine ⟨42246398156215305377361059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28164265437476870251574039 42246398156215305377361059)
    ·
      refine ⟨63369597234322958066041589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42246398156215305377361059 63369597234322958066041589)
      ·
        refine ⟨5940899740717777318691399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63369597234322958066041589 5940899740717777318691399)
        ·
          refine ⟨8911349611076665978037099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940899740717777318691399 8911349611076665978037099)
          ·
            refine ⟨13367024416614998967055649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911349611076665978037099 13367024416614998967055649)
            ·
              refine ⟨10025268312461249225291737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367024416614998967055649 10025268312461249225291737)
              ·
                refine ⟨7518951234345936918968803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025268312461249225291737 7518951234345936918968803)
                ·
                  refine ⟨11278426851518905378453205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518951234345936918968803 11278426851518905378453205)
                  ·
                    refine ⟨264338129332474344807497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11278426851518905378453205 264338129332474344807497)
                    ·
                      rfl

theorem cell22_772195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_772195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772195 prefixEnd_772195 := by exact prefixLift 772195
  have htrace : WordTrace (prefixWord ++ tailWord_772195) baseStart_772195 baseEnd_772195 := by
    simpa [prefixWord, tailWord_772195, baseEnd_772195] using wordTrace_append hprefix tailTrace_772195
  have hstable : (prefixWord ++ tailWord_772195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772195).length < 2 ^ (prefixWord ++ tailWord_772195).sum := by decide
  have hdescent : baseEnd_772195 < baseStart_772195 := by decide
  rcases family_descends (prefixWord ++ tailWord_772195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772242 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_772242 : Nat := 118140960795 + 772242 * 2 ^ 59
def prefixEnd_772242 : Nat := 4983230072969 + 3 ^ 40 * 772242 * 2
def baseEnd_772242 : Nat := 88118072797660629627451

theorem tailTrace_772242 : CollatzResearch.WordTrace tailWord_772242 prefixEnd_772242 88118072797660629627451 := by
  unfold tailWord_772242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041494917076649319633745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18777319778871064852356653 7041494917076649319633745)
  ·
    refine ⟨5281121187807486989725309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7041494917076649319633745 5281121187807486989725309)
    ·
      refine ⟨1980420445427807621146991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5281121187807486989725309 1980420445427807621146991)
      ·
        refine ⟨2970630668141711431720487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980420445427807621146991 2970630668141711431720487)
        ·
          refine ⟨4455946002212567147580731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970630668141711431720487 4455946002212567147580731)
          ·
            refine ⟨6683919003318850721371097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455946002212567147580731 6683919003318850721371097)
            ·
              refine ⟨5012939252489138041028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683919003318850721371097 5012939252489138041028323)
              ·
                refine ⟨7519408878733707061542485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012939252489138041028323 7519408878733707061542485)
                ·
                  refine ⟨88118072797660629627451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7519408878733707061542485 88118072797660629627451)
                  ·
                    rfl

theorem cell22_772242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_772242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772242 prefixEnd_772242 := by exact prefixLift 772242
  have htrace : WordTrace (prefixWord ++ tailWord_772242) baseStart_772242 baseEnd_772242 := by
    simpa [prefixWord, tailWord_772242, baseEnd_772242] using wordTrace_append hprefix tailTrace_772242
  have hstable : (prefixWord ++ tailWord_772242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772242).length < 2 ^ (prefixWord ++ tailWord_772242).sum := by decide
  have hdescent : baseEnd_772242 < baseStart_772242 := by decide
  rcases family_descends (prefixWord ++ tailWord_772242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772257 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_772257 : Nat := 118140960795 + 772257 * 2 ^ 59
def prefixEnd_772257 : Nat := 4983230072969 + 3 ^ 40 * 772257 * 2
def baseEnd_772257 : Nat := 264359353199526849757307

theorem tailTrace_772257 : CollatzResearch.WordTrace tailWord_772257 prefixEnd_772257 264359353199526849757307 := by
  unfold tailWord_772257
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166526763252254840331025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18777684508834836560220683 28166526763252254840331025)
  ·
    refine ⟨21124895072439191130248269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28166526763252254840331025 21124895072439191130248269)
    ·
      refine ⟨7921835652164696673843101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21124895072439191130248269 7921835652164696673843101)
      ·
        refine ⟨2970688369561761252691163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7921835652164696673843101 2970688369561761252691163)
        ·
          refine ⟨4456032554342641879036745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970688369561761252691163 4456032554342641879036745)
          ·
            refine ⟨3342024415756981409277559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456032554342641879036745 3342024415756981409277559)
            ·
              refine ⟨5013036623635472113916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342024415756981409277559 5013036623635472113916339)
              ·
                refine ⟨7519554935453208170874509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013036623635472113916339 7519554935453208170874509)
                ·
                  refine ⟨2819833100794953064077941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7519554935453208170874509 2819833100794953064077941)
                  ·
                    refine ⟨264359353199526849757307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2819833100794953064077941 264359353199526849757307)
                    ·
                      rfl

theorem cell22_772257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_772257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772257 prefixEnd_772257 := by exact prefixLift 772257
  have htrace : WordTrace (prefixWord ++ tailWord_772257) baseStart_772257 baseEnd_772257 := by
    simpa [prefixWord, tailWord_772257, baseEnd_772257] using wordTrace_append hprefix tailTrace_772257
  have hstable : (prefixWord ++ tailWord_772257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772257).length < 2 ^ (prefixWord ++ tailWord_772257).sum := by decide
  have hdescent : baseEnd_772257 < baseStart_772257 := by decide
  rcases family_descends (prefixWord ++ tailWord_772257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772306 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_772306 : Nat := 118140960795 + 772306 * 2 ^ 59
def prefixEnd_772306 : Nat := 4983230072969 + 3 ^ 40 * 772306 * 2
def baseEnd_772306 : Nat := 264376126900907055282157

theorem tailTrace_772306 : CollatzResearch.WordTrace tailWord_772306 prefixEnd_772306 264376126900907055282157 := by
  unfold tailWord_772306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042078485018684052216193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18778875960049824139243181 7042078485018684052216193)
  ·
    refine ⟨5281558863764013039162145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7042078485018684052216193 5281558863764013039162145)
    ·
      refine ⟨3961169147823009779371609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5281558863764013039162145 3961169147823009779371609)
      ·
        refine ⟨2970876860867257334528707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3961169147823009779371609 2970876860867257334528707)
        ·
          refine ⟨4456315291300886001793061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970876860867257334528707 4456315291300886001793061)
          ·
            refine ⟨835559117118916125336199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4456315291300886001793061 835559117118916125336199)
            ·
              refine ⟨1253338675678374188004299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835559117118916125336199 1253338675678374188004299)
              ·
                refine ⟨1880008013517561282006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253338675678374188004299 1880008013517561282006449)
                ·
                  refine ⟨1410006010138170961504837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880008013517561282006449 1410006010138170961504837)
                  ·
                    refine ⟨264376126900907055282157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410006010138170961504837 264376126900907055282157)
                    ·
                      rfl

theorem cell22_772306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_772306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772306 prefixEnd_772306 := by exact prefixLift 772306
  have htrace : WordTrace (prefixWord ++ tailWord_772306) baseStart_772306 baseEnd_772306 := by
    simpa [prefixWord, tailWord_772306, baseEnd_772306] using wordTrace_append hprefix tailTrace_772306
  have hstable : (prefixWord ++ tailWord_772306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772306).length < 2 ^ (prefixWord ++ tailWord_772306).sum := by decide
  have hdescent : baseEnd_772306 < baseStart_772306 := by decide
  rcases family_descends (prefixWord ++ tailWord_772306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772332 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_772332 : Nat := 118140960795 + 772332 * 2 ^ 59
def prefixEnd_772332 : Nat := 4983230072969 + 3 ^ 40 * 772332 * 2
def baseEnd_772332 : Nat := 88128342410750551377359

theorem tailTrace_772332 : CollatzResearch.WordTrace tailWord_772332 prefixEnd_772332 88128342410750551377359 := by
  unfold tailWord_772332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084631118990271324655625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18779508158653695099540833 14084631118990271324655625)
  ·
    refine ⟨10563473339242703493491719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14084631118990271324655625 10563473339242703493491719)
    ·
      refine ⟨15845210008864055240237579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563473339242703493491719 15845210008864055240237579)
      ·
        refine ⟨23767815013296082860356369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15845210008864055240237579 23767815013296082860356369)
        ·
          refine ⟨17825861259972062145267277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23767815013296082860356369 17825861259972062145267277)
          ·
            refine ⟨6684697972489523304475229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17825861259972062145267277 6684697972489523304475229)
            ·
              refine ⟨2506761739683571239178211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6684697972489523304475229 2506761739683571239178211)
              ·
                refine ⟨3760142609525356858767317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506761739683571239178211 3760142609525356858767317)
                ·
                  refine ⟨88128342410750551377359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3760142609525356858767317 88128342410750551377359)
                  ·
                    rfl

theorem cell22_772332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_772332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772332 prefixEnd_772332 := by exact prefixLift 772332
  have htrace : WordTrace (prefixWord ++ tailWord_772332) baseStart_772332 baseEnd_772332 := by
    simpa [prefixWord, tailWord_772332, baseEnd_772332] using wordTrace_append hprefix tailTrace_772332
  have hstable : (prefixWord ++ tailWord_772332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772332).length < 2 ^ (prefixWord ++ tailWord_772332).sum := by decide
  have hdescent : baseEnd_772332 < baseStart_772332 := by decide
  rcases family_descends (prefixWord ++ tailWord_772332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772379 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 1, 4]
def baseStart_772379 : Nat := 118140960795 + 772379 * 2 ^ 59
def prefixEnd_772379 : Nat := 4983230072969 + 3 ^ 40 * 772379 * 2
def baseEnd_772379 : Nat := 264401116292759198206933

theorem tailTrace_772379 : CollatzResearch.WordTrace tailWord_772379 prefixEnd_772379 264401116292759198206933 := by
  unfold tailWord_772379
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170976468810269676272191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18780650979206846450848127 28170976468810269676272191)
  ·
    refine ⟨42256464703215404514408287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28170976468810269676272191 42256464703215404514408287)
    ·
      refine ⟨63384697054823106771612431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42256464703215404514408287 63384697054823106771612431)
      ·
        refine ⟨95077045582234660157418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63384697054823106771612431 95077045582234660157418647)
        ·
          refine ⟨142615568373351990236127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95077045582234660157418647 142615568373351990236127971)
          ·
            refine ⟨213923352560027985354191957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142615568373351990236127971 213923352560027985354191957)
            ·
              refine ⟨2506914287812827953369437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 213923352560027985354191957 2506914287812827953369437)
              ·
                refine ⟨940092857929810482513539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2506914287812827953369437 940092857929810482513539)
                ·
                  refine ⟨1410139286894715723770309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940092857929810482513539 1410139286894715723770309)
                  ·
                    refine ⟨264401116292759198206933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410139286894715723770309 264401116292759198206933)
                    ·
                      rfl

theorem cell22_772379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_772379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772379 prefixEnd_772379 := by exact prefixLift 772379
  have htrace : WordTrace (prefixWord ++ tailWord_772379) baseStart_772379 baseEnd_772379 := by
    simpa [prefixWord, tailWord_772379, baseEnd_772379] using wordTrace_append hprefix tailTrace_772379
  have hstable : (prefixWord ++ tailWord_772379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772379).length < 2 ^ (prefixWord ++ tailWord_772379).sum := by decide
  have hdescent : baseEnd_772379 < baseStart_772379 := by decide
  rcases family_descends (prefixWord ++ tailWord_772379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772407 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_772407 : Nat := 118140960795 + 772407 * 2 ^ 59
def prefixEnd_772407 : Nat := 4983230072969 + 3 ^ 40 * 772407 * 2
def baseEnd_772407 : Nat := 264410701264976458506847

theorem tailTrace_772407 : CollatzResearch.WordTrace tailWord_772407 prefixEnd_772407 264410701264976458506847 := by
  unfold tailWord_772407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28171997712708830458291475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18781331808472553638860983 28171997712708830458291475)
  ·
    refine ⟨42257996569063245687437213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28171997712708830458291475 42257996569063245687437213)
    ·
      refine ⟨15846748713398717132788955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42257996569063245687437213 15846748713398717132788955)
      ·
        refine ⟨23770123070098075699183433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846748713398717132788955 23770123070098075699183433)
        ·
          refine ⟨17827592302573556774387575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23770123070098075699183433 17827592302573556774387575)
          ·
            refine ⟨26741388453860335161581363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17827592302573556774387575 26741388453860335161581363)
            ·
              refine ⟨40112082680790502742372045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26741388453860335161581363 40112082680790502742372045)
              ·
                refine ⟨15042031005296438528389517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40112082680790502742372045 15042031005296438528389517)
                ·
                  refine ⟨5640761626986164448146069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15042031005296438528389517 5640761626986164448146069)
                  ·
                    refine ⟨264410701264976458506847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5640761626986164448146069 264410701264976458506847)
                    ·
                      rfl

theorem cell22_772407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_772407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772407 prefixEnd_772407 := by exact prefixLift 772407
  have htrace : WordTrace (prefixWord ++ tailWord_772407) baseStart_772407 baseEnd_772407 := by
    simpa [prefixWord, tailWord_772407, baseEnd_772407] using wordTrace_append hprefix tailTrace_772407
  have hstable : (prefixWord ++ tailWord_772407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772407).length < 2 ^ (prefixWord ++ tailWord_772407).sum := by decide
  have hdescent : baseEnd_772407 < baseStart_772407 := by decide
  rcases family_descends (prefixWord ++ tailWord_772407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772424 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_772424 : Nat := 118140960795 + 772424 * 2 ^ 59
def prefixEnd_772424 : Nat := 4983230072969 + 3 ^ 40 * 772424 * 2
def baseEnd_772424 : Nat := 264416520712394080831795

theorem tailTrace_772424 : CollatzResearch.WordTrace tailWord_772424 prefixEnd_772424 264416520712394080831795 := by
  unfold tailWord_772424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086308876823621180830163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18781745169098161574440217 14086308876823621180830163)
  ·
    refine ⟨21129463315235431771245245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14086308876823621180830163 21129463315235431771245245)
    ·
      refine ⟨7923548743213286914216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21129463315235431771245245 7923548743213286914216967)
      ·
        refine ⟨11885323114819930371325451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7923548743213286914216967 11885323114819930371325451)
        ·
          refine ⟨17827984672229895556988177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11885323114819930371325451 17827984672229895556988177)
          ·
            refine ⟨13370988504172421667741133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17827984672229895556988177 13370988504172421667741133)
            ·
              refine ⟨5014120689064658125402925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370988504172421667741133 5014120689064658125402925)
              ·
                refine ⟨1880295258399246797026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014120689064658125402925 1880295258399246797026097)
                ·
                  refine ⟨1410221443799435097769573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880295258399246797026097 1410221443799435097769573)
                  ·
                    refine ⟨264416520712394080831795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410221443799435097769573 264416520712394080831795)
                    ·
                      rfl

theorem cell22_772424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_772424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772424 prefixEnd_772424 := by exact prefixLift 772424
  have htrace : WordTrace (prefixWord ++ tailWord_772424) baseStart_772424 baseEnd_772424 := by
    simpa [prefixWord, tailWord_772424, baseEnd_772424] using wordTrace_append hprefix tailTrace_772424
  have hstable : (prefixWord ++ tailWord_772424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772424).length < 2 ^ (prefixWord ++ tailWord_772424).sum := by decide
  have hdescent : baseEnd_772424 < baseStart_772424 := by decide
  rcases family_descends (prefixWord ++ tailWord_772424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772456 : List Nat := [2, 1, 4, 2, 2, 3, 1, 7]
def baseStart_772456 : Nat := 118140960795 + 772456 * 2 ^ 59
def prefixEnd_772456 : Nat := 4983230072969 + 3 ^ 40 * 772456 * 2
def baseEnd_772456 : Nat := 29380830551817407114633

theorem tailTrace_772456 : CollatzResearch.WordTrace tailWord_772456 prefixEnd_772456 29380830551817407114633 := by
  unfold tailWord_772456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086892444765655913412611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18782523259687541217883481 14086892444765655913412611)
  ·
    refine ⟨21130338667148483870118917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14086892444765655913412611 21130338667148483870118917)
    ·
      refine ⟨3961938500090340725647297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21130338667148483870118917 3961938500090340725647297)
      ·
        refine ⟨2971453875067755544235473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3961938500090340725647297 2971453875067755544235473)
        ·
          refine ⟨2228590406300816658176605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2971453875067755544235473 2228590406300816658176605)
          ·
            refine ⟨835721402362806246816227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2228590406300816658176605 835721402362806246816227)
            ·
              refine ⟨1253582103544209370224341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835721402362806246816227 1253582103544209370224341)
              ·
                refine ⟨29380830551817407114633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1253582103544209370224341 29380830551817407114633)
                ·
                  rfl

theorem cell22_772456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_772456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772456 prefixEnd_772456 := by exact prefixLift 772456
  have htrace : WordTrace (prefixWord ++ tailWord_772456) baseStart_772456 baseEnd_772456 := by
    simpa [prefixWord, tailWord_772456, baseEnd_772456] using wordTrace_append hprefix tailTrace_772456
  have hstable : (prefixWord ++ tailWord_772456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772456).length < 2 ^ (prefixWord ++ tailWord_772456).sum := by decide
  have hdescent : baseEnd_772456 < baseStart_772456 := by decide
  rcases family_descends (prefixWord ++ tailWord_772456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772484 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_772484 : Nat := 118140960795 + 772484 * 2 ^ 59
def prefixEnd_772484 : Nat := 4983230072969 + 3 ^ 40 * 772484 * 2
def baseEnd_772484 : Nat := 88145686646191308110537

theorem tailTrace_772484 : CollatzResearch.WordTrace tailWord_772484 prefixEnd_772484 88145686646191308110537 := by
  unfold tailWord_772484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087403066714936304422253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18783204088953248405896337 14087403066714936304422253)
  ·
    refine ⟨5282776150018101114158345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14087403066714936304422253 5282776150018101114158345)
    ·
      refine ⟨3962082112513575835618759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5282776150018101114158345 3962082112513575835618759)
      ·
        refine ⟨5943123168770363753428139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962082112513575835618759 5943123168770363753428139)
        ·
          refine ⟨8914684753155545630142209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943123168770363753428139 8914684753155545630142209)
          ·
            refine ⟨6686013564866659222606657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914684753155545630142209 6686013564866659222606657)
            ·
              refine ⟨5014510173649994416954993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6686013564866659222606657 5014510173649994416954993)
              ·
                refine ⟨3760882630237495812716245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014510173649994416954993 3760882630237495812716245)
                ·
                  refine ⟨88145686646191308110537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3760882630237495812716245 88145686646191308110537)
                  ·
                    rfl

theorem cell22_772484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_772484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772484 prefixEnd_772484 := by exact prefixLift 772484
  have htrace : WordTrace (prefixWord ++ tailWord_772484) baseStart_772484 baseEnd_772484 := by
    simpa [prefixWord, tailWord_772484, baseEnd_772484] using wordTrace_append hprefix tailTrace_772484
  have hstable : (prefixWord ++ tailWord_772484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772484).length < 2 ^ (prefixWord ++ tailWord_772484).sum := by decide
  have hdescent : baseEnd_772484 < baseStart_772484 := by decide
  rcases family_descends (prefixWord ++ tailWord_772484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772544 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_772544 : Nat := 118140960795 + 772544 * 2 ^ 59
def prefixEnd_772544 : Nat := 4983230072969 + 3 ^ 40 * 772544 * 2
def baseEnd_772544 : Nat := 264457599164753767831427

theorem tailTrace_772544 : CollatzResearch.WordTrace tailWord_772544 prefixEnd_772544 264457599164753767831427 := by
  unfold tailWord_772544
  simp only [CollatzResearch.WordTrace]
  refine ⟨14088497256606251428014343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18784663008808335237352457 14088497256606251428014343)
  ·
    refine ⟨21132745884909377142021515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14088497256606251428014343 21132745884909377142021515)
    ·
      refine ⟨31699118827364065713032273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21132745884909377142021515 31699118827364065713032273)
      ·
        refine ⟨23774339120523049284774205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31699118827364065713032273 23774339120523049284774205)
        ·
          refine ⟨8915377170196143481790327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23774339120523049284774205 8915377170196143481790327)
          ·
            refine ⟨13373065755294215222685491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915377170196143481790327 13373065755294215222685491)
            ·
              refine ⟨20059598632941322834028237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13373065755294215222685491 20059598632941322834028237)
              ·
                refine ⟨7522349487352996062760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20059598632941322834028237 7522349487352996062760589)
                ·
                  refine ⟨2820881057757373523535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7522349487352996062760589 2820881057757373523535221)
                  ·
                    refine ⟨264457599164753767831427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2820881057757373523535221 264457599164753767831427)
                    ·
                      rfl

theorem cell22_772544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_772544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772544 prefixEnd_772544 := by exact prefixLift 772544
  have htrace : WordTrace (prefixWord ++ tailWord_772544) baseStart_772544 baseEnd_772544 := by
    simpa [prefixWord, tailWord_772544, baseEnd_772544] using wordTrace_append hprefix tailTrace_772544
  have hstable : (prefixWord ++ tailWord_772544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772544).length < 2 ^ (prefixWord ++ tailWord_772544).sum := by decide
  have hdescent : baseEnd_772544 < baseStart_772544 := by decide
  rcases family_descends (prefixWord ++ tailWord_772544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772614 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_772614 : Nat := 118140960795 + 772614 * 2 ^ 59
def prefixEnd_772614 : Nat := 4983230072969 + 3 ^ 40 * 772614 * 2
def baseEnd_772614 : Nat := 88160520531765639527071

theorem tailTrace_772614 : CollatzResearch.WordTrace tailWord_772614 prefixEnd_772614 88160520531765639527071 := by
  unfold tailWord_772614
  simp only [CollatzResearch.WordTrace]
  refine ⟨880610863217465775346153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18786365081972603207384597 880610863217465775346153)
  ·
    refine ⟨660458147413099331509615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 880610863217465775346153 660458147413099331509615)
    ·
      refine ⟨990687221119648997264423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660458147413099331509615 990687221119648997264423)
      ·
        refine ⟨1486030831679473495896635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990687221119648997264423 1486030831679473495896635)
        ·
          refine ⟨2229046247519210243844953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486030831679473495896635 2229046247519210243844953)
          ·
            refine ⟨1671784685639407682883715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229046247519210243844953 1671784685639407682883715)
            ·
              refine ⟨2507677028459111524325573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671784685639407682883715 2507677028459111524325573)
              ·
                refine ⟨470189442836083410811045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2507677028459111524325573 470189442836083410811045)
                ·
                  refine ⟨88160520531765639527071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470189442836083410811045 88160520531765639527071)
                  ·
                    rfl

theorem cell22_772614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_772614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772614 prefixEnd_772614 := by exact prefixLift 772614
  have htrace : WordTrace (prefixWord ++ tailWord_772614) baseStart_772614 baseEnd_772614 := by
    simpa [prefixWord, tailWord_772614, baseEnd_772614] using wordTrace_append hprefix tailTrace_772614
  have hstable : (prefixWord ++ tailWord_772614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772614).length < 2 ^ (prefixWord ++ tailWord_772614).sum := by decide
  have hdescent : baseEnd_772614 < baseStart_772614 := by decide
  rcases family_descends (prefixWord ++ tailWord_772614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772640 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_772640 : Nat := 118140960795 + 772640 * 2 ^ 59
def prefixEnd_772640 : Nat := 4983230072969 + 3 ^ 40 * 772640 * 2
def baseEnd_772640 : Nat := 264490461926641517431133

theorem tailTrace_772640 : CollatzResearch.WordTrace tailWord_772640 prefixEnd_772640 264490461926641517431133 := by
  unfold tailWord_772640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090247960432355625761687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18786997280576474167682249 14090247960432355625761687)
  ·
    refine ⟨21135371940648533438642531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090247960432355625761687 21135371940648533438642531)
    ·
      refine ⟨31703057910972800157963797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21135371940648533438642531 31703057910972800157963797)
      ·
        refine ⟨1486080839576850007404553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31703057910972800157963797 1486080839576850007404553)
        ·
          refine ⟨1114560629682637505553415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486080839576850007404553 1114560629682637505553415)
          ·
            refine ⟨1671840944523956258330123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114560629682637505553415 1671840944523956258330123)
            ·
              refine ⟨2507761416785934387495185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671840944523956258330123 2507761416785934387495185)
              ·
                refine ⟨1880821062589450790621389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507761416785934387495185 1880821062589450790621389)
                ·
                  refine ⟨705307898471044046483021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1880821062589450790621389 705307898471044046483021)
                  ·
                    refine ⟨264490461926641517431133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 705307898471044046483021 264490461926641517431133)
                    ·
                      rfl

theorem cell22_772640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_772640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772640 prefixEnd_772640 := by exact prefixLift 772640
  have htrace : WordTrace (prefixWord ++ tailWord_772640) baseStart_772640 baseEnd_772640 := by
    simpa [prefixWord, tailWord_772640, baseEnd_772640] using wordTrace_append hprefix tailTrace_772640
  have hstable : (prefixWord ++ tailWord_772640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772640).length < 2 ^ (prefixWord ++ tailWord_772640).sum := by decide
  have hdescent : baseEnd_772640 < baseStart_772640 := by decide
  rcases family_descends (prefixWord ++ tailWord_772640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772670 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_772670 : Nat := 118140960795 + 772670 * 2 ^ 59
def prefixEnd_772670 : Nat := 4983230072969 + 3 ^ 40 * 772670 * 2
def baseEnd_772670 : Nat := 88166910513243813060347

theorem tailTrace_772670 : CollatzResearch.WordTrace tailWord_772670 prefixEnd_772670 88166910513243813060347 := by
  unfold tailWord_772670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522698763844503296889433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18787726740504017583410309 3522698763844503296889433)
  ·
    refine ⟨2642024072883377472667075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3522698763844503296889433 2642024072883377472667075)
    ·
      refine ⟨3963036109325066209000613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642024072883377472667075 3963036109325066209000613)
      ·
        refine ⟨743069270498449914187615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3963036109325066209000613 743069270498449914187615)
        ·
          refine ⟨1114603905747674871281423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743069270498449914187615 1114603905747674871281423)
          ·
            refine ⟨1671905858621512306922135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114603905747674871281423 1671905858621512306922135)
            ·
              refine ⟨2507858787932268460383203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671905858621512306922135 2507858787932268460383203)
              ·
                refine ⟨3761788181898402690574805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507858787932268460383203 3761788181898402690574805)
                ·
                  refine ⟨88166910513243813060347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3761788181898402690574805 88166910513243813060347)
                  ·
                    rfl

theorem cell22_772670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_772670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772670 prefixEnd_772670 := by exact prefixLift 772670
  have htrace : WordTrace (prefixWord ++ tailWord_772670) baseStart_772670 baseEnd_772670 := by
    simpa [prefixWord, tailWord_772670, baseEnd_772670] using wordTrace_append hprefix tailTrace_772670
  have hstable : (prefixWord ++ tailWord_772670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772670).length < 2 ^ (prefixWord ++ tailWord_772670).sum := by decide
  have hdescent : baseEnd_772670 < baseStart_772670 := by decide
  rcases family_descends (prefixWord ++ tailWord_772670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772738 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_772738 : Nat := 118140960795 + 772738 * 2 ^ 59
def prefixEnd_772738 : Nat := 4983230072969 + 3 ^ 40 * 772738 * 2
def baseEnd_772738 : Nat := 88174669776467309493611

theorem tailTrace_772738 : CollatzResearch.WordTrace tailWord_772738 prefixEnd_772738 88174669776467309493611 := by
  unfold tailWord_772738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046017568627418497147717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18789380183006449325727245 7046017568627418497147717)
  ·
    refine ⟨1321128294117640968215197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7046017568627418497147717 1321128294117640968215197)
    ·
      refine ⟨495423110294115363080699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1321128294117640968215197 495423110294115363080699)
      ·
        refine ⟨743134665441173044621049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495423110294115363080699 743134665441173044621049)
        ·
          refine ⟨557350999080879783465787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743134665441173044621049 557350999080879783465787)
          ·
            refine ⟨836026498621319675198681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557350999080879783465787 836026498621319675198681)
            ·
              refine ⟨627019873965989756399011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836026498621319675198681 627019873965989756399011)
              ·
                refine ⟨940529810948984634598517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627019873965989756399011 940529810948984634598517)
                ·
                  refine ⟨88174669776467309493611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 940529810948984634598517 88174669776467309493611)
                  ·
                    rfl

theorem cell22_772738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_772738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772738 prefixEnd_772738 := by exact prefixLift 772738
  have htrace : WordTrace (prefixWord ++ tailWord_772738) baseStart_772738 baseEnd_772738 := by
    simpa [prefixWord, tailWord_772738, baseEnd_772738] using wordTrace_append hprefix tailTrace_772738
  have hstable : (prefixWord ++ tailWord_772738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772738).length < 2 ^ (prefixWord ++ tailWord_772738).sum := by decide
  have hdescent : baseEnd_772738 < baseStart_772738 := by decide
  rcases family_descends (prefixWord ++ tailWord_772738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772762 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_772762 : Nat := 118140960795 + 772762 * 2 ^ 59
def prefixEnd_772762 : Nat := 4983230072969 + 3 ^ 40 * 772762 * 2
def baseEnd_772762 : Nat := 264532225019873865880759

theorem tailTrace_772762 : CollatzResearch.WordTrace tailWord_772762 prefixEnd_772762 264532225019873865880759 := by
  unfold tailWord_772762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046236406605681521866135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18789963750948484058309693 7046236406605681521866135)
  ·
    refine ⟨10569354609908522282799203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046236406605681521866135 10569354609908522282799203)
    ·
      refine ⟨15854031914862783424198805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569354609908522282799203 15854031914862783424198805)
      ·
        refine ⟨743157746009192973009319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15854031914862783424198805 743157746009192973009319)
        ·
          refine ⟨1114736619013789459513979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743157746009192973009319 1114736619013789459513979)
          ·
            refine ⟨1672104928520684189270969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114736619013789459513979 1672104928520684189270969)
            ·
              refine ⟨1254078696390513141953227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672104928520684189270969 1254078696390513141953227)
              ·
                refine ⟨1881118044585769712929841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254078696390513141953227 1881118044585769712929841)
                ·
                  refine ⟨1410838533439327284697381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1881118044585769712929841 1410838533439327284697381)
                  ·
                    refine ⟨264532225019873865880759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410838533439327284697381 264532225019873865880759)
                    ·
                      rfl

theorem cell22_772762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_772762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772762 prefixEnd_772762 := by exact prefixLift 772762
  have htrace : WordTrace (prefixWord ++ tailWord_772762) baseStart_772762 baseEnd_772762 := by
    simpa [prefixWord, tailWord_772762, baseEnd_772762] using wordTrace_append hprefix tailTrace_772762
  have hstable : (prefixWord ++ tailWord_772762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772762).length < 2 ^ (prefixWord ++ tailWord_772762).sum := by decide
  have hdescent : baseEnd_772762 < baseStart_772762 := by decide
  rcases family_descends (prefixWord ++ tailWord_772762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772771 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 7]
def baseStart_772771 : Nat := 118140960795 + 772771 * 2 ^ 59
def prefixEnd_772771 : Nat := 4983230072969 + 3 ^ 40 * 772771 * 2
def baseEnd_772771 : Nat := 88178435301266947468577

theorem tailTrace_772771 : CollatzResearch.WordTrace tailWord_772771 prefixEnd_772771 88178435301266947468577 := by
  unfold tailWord_772771
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185273883390120624542167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18790182588926747083028111 28185273883390120624542167)
  ·
    refine ⟨42277910825085180936813251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28185273883390120624542167 42277910825085180936813251)
    ·
      refine ⟨63416866237627771405219877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42277910825085180936813251 63416866237627771405219877)
      ·
        refine ⟨11890662419555207138478727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63416866237627771405219877 11890662419555207138478727)
        ·
          refine ⟨17835993629332810707718091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11890662419555207138478727 17835993629332810707718091)
          ·
            refine ⟨26753990443999216061577137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17835993629332810707718091 26753990443999216061577137)
            ·
              refine ⟨20065492832999412046182853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26753990443999216061577137 20065492832999412046182853)
              ·
                refine ⟨3762279906187389758659285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20065492832999412046182853 3762279906187389758659285)
                ·
                  refine ⟨88178435301266947468577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3762279906187389758659285 88178435301266947468577)
                  ·
                    rfl

theorem cell22_772771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_772771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772771 prefixEnd_772771 := by exact prefixLift 772771
  have htrace : WordTrace (prefixWord ++ tailWord_772771) baseStart_772771 baseEnd_772771 := by
    simpa [prefixWord, tailWord_772771, baseEnd_772771] using wordTrace_append hprefix tailTrace_772771
  have hstable : (prefixWord ++ tailWord_772771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772771).length < 2 ^ (prefixWord ++ tailWord_772771).sum := by decide
  have hdescent : baseEnd_772771 < baseStart_772771 := by decide
  rcases family_descends (prefixWord ++ tailWord_772771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772850 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_772850 : Nat := 118140960795 + 772850 * 2 ^ 59
def prefixEnd_772850 : Nat := 4983230072969 + 3 ^ 40 * 772850 * 2
def baseEnd_772850 : Nat := 88187449739423656560163

theorem tailTrace_772850 : CollatzResearch.WordTrace tailWord_772850 prefixEnd_772850 88187449739423656560163 := by
  unfold tailWord_772850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047038812525979279167001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18792103500069278077778669 7047038812525979279167001)
  ·
    refine ⟨5285279109394484459375251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7047038812525979279167001 5285279109394484459375251)
    ·
      refine ⟨7927918664091726689062877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285279109394484459375251 7927918664091726689062877)
      ·
        refine ⟨2972969499034397508398579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7927918664091726689062877 2972969499034397508398579)
        ·
          refine ⟨4459454248551596262597869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972969499034397508398579 4459454248551596262597869)
          ·
            refine ⟨1672295343206848598474201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4459454248551596262597869 1672295343206848598474201)
            ·
              refine ⟨1254221507405136448855651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672295343206848598474201 1254221507405136448855651)
              ·
                refine ⟨1881332261107704673283477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254221507405136448855651 1881332261107704673283477)
                ·
                  refine ⟨88187449739423656560163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1881332261107704673283477 88187449739423656560163)
                  ·
                    rfl

theorem cell22_772850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_772850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772850 prefixEnd_772850 := by exact prefixLift 772850
  have htrace : WordTrace (prefixWord ++ tailWord_772850) baseStart_772850 baseEnd_772850 := by
    simpa [prefixWord, tailWord_772850, baseEnd_772850] using wordTrace_append hprefix tailTrace_772850
  have hstable : (prefixWord ++ tailWord_772850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772850).length < 2 ^ (prefixWord ++ tailWord_772850).sum := by decide
  have hdescent : baseEnd_772850 < baseStart_772850 := by decide
  rcases family_descends (prefixWord ++ tailWord_772850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772908 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_772908 : Nat := 118140960795 + 772908 * 2 ^ 59
def prefixEnd_772908 : Nat := 4983230072969 + 3 ^ 40 * 772908 * 2
def baseEnd_772908 : Nat := 264582203803578151730311

theorem tailTrace_772908 : CollatzResearch.WordTrace tailWord_772908 prefixEnd_772908 264582203803578151730311 := by
  unfold tailWord_772908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095135341946896511139689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18793513789262528681519585 14095135341946896511139689)
  ·
    refine ⟨10571351506460172383354767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14095135341946896511139689 10571351506460172383354767)
    ·
      refine ⟨15857027259690258575032151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571351506460172383354767 15857027259690258575032151)
      ·
        refine ⟨23785540889535387862548227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15857027259690258575032151 23785540889535387862548227)
        ·
          refine ⟨35678311334303081793822341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23785540889535387862548227 35678311334303081793822341)
          ·
            refine ⟨6689683375181827836341689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35678311334303081793822341 6689683375181827836341689)
            ·
              refine ⟨5017262531386370877256267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689683375181827836341689 5017262531386370877256267)
              ·
                refine ⟨7525893797079556315884401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017262531386370877256267 7525893797079556315884401)
                ·
                  refine ⟨5644420347809667236913301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525893797079556315884401 5644420347809667236913301)
                  ·
                    refine ⟨264582203803578151730311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5644420347809667236913301 264582203803578151730311)
                    ·
                      rfl

theorem cell22_772908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_772908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772908 prefixEnd_772908 := by exact prefixLift 772908
  have htrace : WordTrace (prefixWord ++ tailWord_772908) baseStart_772908 baseEnd_772908 := by
    simpa [prefixWord, tailWord_772908, baseEnd_772908] using wordTrace_append hprefix tailTrace_772908
  have hstable : (prefixWord ++ tailWord_772908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772908).length < 2 ^ (prefixWord ++ tailWord_772908).sum := by decide
  have hdescent : baseEnd_772908 < baseStart_772908 := by decide
  rcases family_descends (prefixWord ++ tailWord_772908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772938 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_772938 : Nat := 118140960795 + 772938 * 2 ^ 59
def prefixEnd_772938 : Nat := 4983230072969 + 3 ^ 40 * 772938 * 2
def baseEnd_772938 : Nat := 264592473416668073480219

theorem tailTrace_772938 : CollatzResearch.WordTrace tailWord_772938 prefixEnd_772938 264592473416668073480219 := by
  unfold tailWord_772938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047841218446277036467867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18794243249190072097247645 7047841218446277036467867)
  ·
    refine ⟨10571761827669415554701801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047841218446277036467867 10571761827669415554701801)
    ·
      refine ⟨7928821370752061666026351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10571761827669415554701801 7928821370752061666026351)
      ·
        refine ⟨11893232056128092499039527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928821370752061666026351 11893232056128092499039527)
        ·
          refine ⟨17839848084192138748559291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893232056128092499039527 17839848084192138748559291)
          ·
            refine ⟨26759772126288208122838937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17839848084192138748559291 26759772126288208122838937)
            ·
              refine ⟨20069829094716156092129203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26759772126288208122838937 20069829094716156092129203)
              ·
                refine ⟨30104743642074234138193805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20069829094716156092129203 30104743642074234138193805)
                ·
                  refine ⟨11289278865777837801822677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30104743642074234138193805 11289278865777837801822677)
                  ·
                    refine ⟨264592473416668073480219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11289278865777837801822677 264592473416668073480219)
                    ·
                      rfl

theorem cell22_772938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_772938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772938 prefixEnd_772938 := by exact prefixLift 772938
  have htrace : WordTrace (prefixWord ++ tailWord_772938) baseStart_772938 baseEnd_772938 := by
    simpa [prefixWord, tailWord_772938, baseEnd_772938] using wordTrace_append hprefix tailTrace_772938
  have hstable : (prefixWord ++ tailWord_772938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772938).length < 2 ^ (prefixWord ++ tailWord_772938).sum := by decide
  have hdescent : baseEnd_772938 < baseStart_772938 := by decide
  rcases family_descends (prefixWord ++ tailWord_772938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772985 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 6]
def baseStart_772985 : Nat := 118140960795 + 772985 * 2 ^ 59
def prefixEnd_772985 : Nat := 4983230072969 + 3 ^ 40 * 772985 * 2
def baseEnd_772985 : Nat := 88202854159058539185025

theorem tailTrace_772985 : CollatzResearch.WordTrace tailWord_772985 prefixEnd_772985 88202854159058539185025 := by
  unfold tailWord_772985
  simp only [CollatzResearch.WordTrace]
  refine ⟨28193079104614835172832409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18795386069743223448554939 28193079104614835172832409)
  ·
    refine ⟨21144809328461126379624307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28193079104614835172832409 21144809328461126379624307)
    ·
      refine ⟨31717213992691689569436461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21144809328461126379624307 31717213992691689569436461)
      ·
        refine ⟨11893955247259383588538673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31717213992691689569436461 11893955247259383588538673)
        ·
          refine ⟨8920466435444537691404005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11893955247259383588538673 8920466435444537691404005)
          ·
            refine ⟨1672587456645850817138251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8920466435444537691404005 1672587456645850817138251)
            ·
              refine ⟨2508881184968776225707377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672587456645850817138251 2508881184968776225707377)
              ·
                refine ⟨1881660888726582169280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508881184968776225707377 1881660888726582169280533)
                ·
                  refine ⟨88202854159058539185025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1881660888726582169280533 88202854159058539185025)
                  ·
                    rfl

theorem cell22_772985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_772985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772985 prefixEnd_772985 := by exact prefixLift 772985
  have htrace : WordTrace (prefixWord ++ tailWord_772985) baseStart_772985 baseEnd_772985 := by
    simpa [prefixWord, tailWord_772985, baseEnd_772985] using wordTrace_append hprefix tailTrace_772985
  have hstable : (prefixWord ++ tailWord_772985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772985).length < 2 ^ (prefixWord ++ tailWord_772985).sum := by decide
  have hdescent : baseEnd_772985 < baseStart_772985 := by decide
  rcases family_descends (prefixWord ++ tailWord_772985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773015 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_773015 : Nat := 118140960795 + 773015 * 2 ^ 59
def prefixEnd_773015 : Nat := 4983230072969 + 3 ^ 40 * 773015 * 2
def baseEnd_773015 : Nat := 264618832090265539304983

theorem tailTrace_773015 : CollatzResearch.WordTrace tailWord_773015 prefixEnd_773015 264618832090265539304983 := by
  unfold tailWord_773015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28194173294506150296424499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796115529670766864282999 28194173294506150296424499)
  ·
    refine ⟨42291259941759225444636749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28194173294506150296424499 42291259941759225444636749)
    ·
      refine ⟨15859222478159709541738781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42291259941759225444636749 15859222478159709541738781)
      ·
        refine ⟨5947208429309891078152043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15859222478159709541738781 5947208429309891078152043)
        ·
          refine ⟨8920812643964836617228065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947208429309891078152043 8920812643964836617228065)
          ·
            refine ⟨6690609482973627462921049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920812643964836617228065 6690609482973627462921049)
            ·
              refine ⟨5017957112230220597190787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690609482973627462921049 5017957112230220597190787)
              ·
                refine ⟨7526935668345330895786181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017957112230220597190787 7526935668345330895786181)
                ·
                  refine ⟨1411300437814749542959909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7526935668345330895786181 1411300437814749542959909)
                  ·
                    refine ⟨264618832090265539304983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411300437814749542959909 264618832090265539304983)
                    ·
                      rfl

theorem cell22_773015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_773015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773015 prefixEnd_773015 := by exact prefixLift 773015
  have htrace : WordTrace (prefixWord ++ tailWord_773015) baseStart_773015 baseEnd_773015 := by
    simpa [prefixWord, tailWord_773015, baseEnd_773015] using wordTrace_append hprefix tailTrace_773015
  have hstable : (prefixWord ++ tailWord_773015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773015).length < 2 ^ (prefixWord ++ tailWord_773015).sum := by decide
  have hdescent : baseEnd_773015 < baseStart_773015 := by decide
  rcases family_descends (prefixWord ++ tailWord_773015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773045 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_773045 : Nat := 118140960795 + 773045 * 2 ^ 59
def prefixEnd_773045 : Nat := 4983230072969 + 3 ^ 40 * 773045 * 2
def baseEnd_773045 : Nat := 264629101703355461054891

theorem tailTrace_773045 : CollatzResearch.WordTrace tailWord_773045 prefixEnd_773045 264629101703355461054891 := by
  unfold tailWord_773045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28195267484397465420016589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796844989598310280011059 28195267484397465420016589)
  ·
    refine ⟨10573225306649049532506221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28195267484397465420016589 10573225306649049532506221)
    ·
      refine ⟨3964959489993393574689833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10573225306649049532506221 3964959489993393574689833)
      ·
        refine ⟨2973719617495045181017375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3964959489993393574689833 2973719617495045181017375)
        ·
          refine ⟨4460579426242567771526063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973719617495045181017375 4460579426242567771526063)
          ·
            refine ⟨6690869139363851657289095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460579426242567771526063 6690869139363851657289095)
            ·
              refine ⟨10036303709045777485933643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690869139363851657289095 10036303709045777485933643)
              ·
                refine ⟨15054455563568666228900465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10036303709045777485933643 15054455563568666228900465)
                ·
                  refine ⟨11290841672676499671675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15054455563568666228900465 11290841672676499671675349)
                  ·
                    refine ⟨264629101703355461054891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11290841672676499671675349 264629101703355461054891)
                    ·
                      rfl

theorem cell22_773045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_773045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773045 prefixEnd_773045 := by exact prefixLift 773045
  have htrace : WordTrace (prefixWord ++ tailWord_773045) baseStart_773045 baseEnd_773045 := by
    simpa [prefixWord, tailWord_773045, baseEnd_773045] using wordTrace_append hprefix tailTrace_773045
  have hstable : (prefixWord ++ tailWord_773045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773045).length < 2 ^ (prefixWord ++ tailWord_773045).sum := by decide
  have hdescent : baseEnd_773045 < baseStart_773045 := by decide
  rcases family_descends (prefixWord ++ tailWord_773045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773400 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_773400 : Nat := 118140960795 + 773400 * 2 ^ 59
def prefixEnd_773400 : Nat := 4983230072969 + 3 ^ 40 * 773400 * 2
def baseEnd_773400 : Nat := 264750625458252868428803

theorem tailTrace_773400 : CollatzResearch.WordTrace tailWord_773400 prefixEnd_773400 264750625458252868428803 := by
  unfold tailWord_773400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104107699055680524594827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18805476932074240699459769 14104107699055680524594827)
  ·
    refine ⟨21156161548583520786892241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14104107699055680524594827 21156161548583520786892241)
    ·
      refine ⟨15867121161437640590169181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21156161548583520786892241 15867121161437640590169181)
      ·
        refine ⟨5950170435539115221313443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15867121161437640590169181 5950170435539115221313443)
        ·
          refine ⟨8925255653308672831970165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950170435539115221313443 8925255653308672831970165)
          ·
            refine ⟨836742717497688077997203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8925255653308672831970165 836742717497688077997203)
            ·
              refine ⟨1255114076246532116995805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836742717497688077997203 1255114076246532116995805)
              ·
                refine ⟨470667778592449543873427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255114076246532116995805 470667778592449543873427)
                ·
                  refine ⟨706001667888674315810141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470667778592449543873427 706001667888674315810141)
                  ·
                    refine ⟨264750625458252868428803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706001667888674315810141 264750625458252868428803)
                    ·
                      rfl

theorem cell22_773400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_773400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773400 prefixEnd_773400 := by exact prefixLift 773400
  have htrace : WordTrace (prefixWord ++ tailWord_773400) baseStart_773400 baseEnd_773400 := by
    simpa [prefixWord, tailWord_773400, baseEnd_773400] using wordTrace_append hprefix tailTrace_773400
  have hstable : (prefixWord ++ tailWord_773400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773400).length < 2 ^ (prefixWord ++ tailWord_773400).sum := by decide
  have hdescent : baseEnd_773400 < baseStart_773400 := by decide
  rcases family_descends (prefixWord ++ tailWord_773400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_773409 : Nat := 118140960795 + 773409 * 2 ^ 59
def prefixEnd_773409 : Nat := 4983230072969 + 3 ^ 40 * 773409 * 2
def baseEnd_773409 : Nat := 264753706342179844953775

theorem tailTrace_773409 : CollatzResearch.WordTrace tailWord_773409 prefixEnd_773409 264753706342179844953775 := by
  unfold tailWord_773409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28208543655078755586267281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18805695770052503724178187 28208543655078755586267281)
  ·
    refine ⟨21156407741309066689700461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28208543655078755586267281 21156407741309066689700461)
    ·
      refine ⟨7933652902990900008637673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21156407741309066689700461 7933652902990900008637673)
      ·
        refine ⟨5950239677243175006478255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7933652902990900008637673 5950239677243175006478255)
        ·
          refine ⟨8925359515864762509717383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950239677243175006478255 8925359515864762509717383)
          ·
            refine ⟨13388039273797143764576075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925359515864762509717383 13388039273797143764576075)
            ·
              refine ⟨20082058910695715646864113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388039273797143764576075 20082058910695715646864113)
              ·
                refine ⟨15061544183021786735148085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20082058910695715646864113 15061544183021786735148085)
                ·
                  refine ⟨1412019767158292506420133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15061544183021786735148085 1412019767158292506420133)
                  ·
                    refine ⟨264753706342179844953775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412019767158292506420133 264753706342179844953775)
                    ·
                      rfl

theorem cell22_773409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_773409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773409 prefixEnd_773409 := by exact prefixLift 773409
  have htrace : WordTrace (prefixWord ++ tailWord_773409) baseStart_773409 baseEnd_773409 := by
    simpa [prefixWord, tailWord_773409, baseEnd_773409] using wordTrace_append hprefix tailTrace_773409
  have hstable : (prefixWord ++ tailWord_773409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773409).length < 2 ^ (prefixWord ++ tailWord_773409).sum := by decide
  have hdescent : baseEnd_773409 < baseStart_773409 := by decide
  rcases family_descends (prefixWord ++ tailWord_773409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773430 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_773430 : Nat := 118140960795 + 773430 * 2 ^ 59
def prefixEnd_773430 : Nat := 4983230072969 + 3 ^ 40 * 773430 * 2
def baseEnd_773430 : Nat := 88253631690447596726237

theorem tailTrace_773430 : CollatzResearch.WordTrace tailWord_773430 prefixEnd_773430 88253631690447596726237 := by
  unfold tailWord_773430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763081849250167260798859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18806206392001784115187829 1763081849250167260798859)
  ·
    refine ⟨2644622773875250891198289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763081849250167260798859 2644622773875250891198289)
    ·
      refine ⟨1983467080406438168398717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644622773875250891198289 1983467080406438168398717)
      ·
        refine ⟨743800155152414313149519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1983467080406438168398717 743800155152414313149519)
        ·
          refine ⟨1115700232728621469724279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743800155152414313149519 1115700232728621469724279)
          ·
            refine ⟨1673550349092932204586419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115700232728621469724279 1673550349092932204586419)
            ·
              refine ⟨2510325523639398306879629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673550349092932204586419 2510325523639398306879629)
              ·
                refine ⟨941372071364774365079861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510325523639398306879629 941372071364774365079861)
                ·
                  refine ⟨88253631690447596726237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941372071364774365079861 88253631690447596726237)
                  ·
                    rfl

theorem cell22_773430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_773430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773430 prefixEnd_773430 := by exact prefixLift 773430
  have htrace : WordTrace (prefixWord ++ tailWord_773430) baseStart_773430 baseEnd_773430 := by
    simpa [prefixWord, tailWord_773430, baseEnd_773430] using wordTrace_append hprefix tailTrace_773430
  have hstable : (prefixWord ++ tailWord_773430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773430).length < 2 ^ (prefixWord ++ tailWord_773430).sum := by decide
  have hdescent : baseEnd_773430 < baseStart_773430 := by decide
  rcases family_descends (prefixWord ++ tailWord_773430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773475 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 4]
def baseStart_773475 : Nat := 118140960795 + 773475 * 2 ^ 59
def prefixEnd_773475 : Nat := 4983230072969 + 3 ^ 40 * 773475 * 2
def baseEnd_773475 : Nat := 88258766496992557601191

theorem tailTrace_773475 : CollatzResearch.WordTrace tailWord_773475 prefixEnd_773475 88258766496992557601191 := by
  unfold tailWord_773475
  simp only [CollatzResearch.WordTrace]
  refine ⟨28210950872839648858169879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18807300581893099238779919 28210950872839648858169879)
  ·
    refine ⟨42316426309259473287254819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28210950872839648858169879 42316426309259473287254819)
    ·
      refine ⟨63474639463889209930882229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42316426309259473287254819 63474639463889209930882229)
      ·
        refine ⟨5950747449739613431020209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63474639463889209930882229 5950747449739613431020209)
        ·
          refine ⟨4463060587304710073265157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950747449739613431020209 4463060587304710073265157)
          ·
            refine ⟨836823860119633138737217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4463060587304710073265157 836823860119633138737217)
            ·
              refine ⟨627617895089724854052913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836823860119633138737217 627617895089724854052913)
              ·
                refine ⟨470713421317293640539685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627617895089724854052913 470713421317293640539685)
                ·
                  refine ⟨88258766496992557601191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470713421317293640539685 88258766496992557601191)
                  ·
                    rfl

theorem cell22_773475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 4].length) (baseStart_773475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773475 prefixEnd_773475 := by exact prefixLift 773475
  have htrace : WordTrace (prefixWord ++ tailWord_773475) baseStart_773475 baseEnd_773475 := by
    simpa [prefixWord, tailWord_773475, baseEnd_773475] using wordTrace_append hprefix tailTrace_773475
  have hstable : (prefixWord ++ tailWord_773475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773475).length < 2 ^ (prefixWord ++ tailWord_773475).sum := by decide
  have hdescent : baseEnd_773475 < baseStart_773475 := by decide
  rcases family_descends (prefixWord ++ tailWord_773475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773499 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_773499 : Nat := 118140960795 + 773499 * 2 ^ 59
def prefixEnd_773499 : Nat := 4983230072969 + 3 ^ 40 * 773499 * 2
def baseEnd_773499 : Nat := 264784515181449610203499

theorem tailTrace_773499 : CollatzResearch.WordTrace tailWord_773499 prefixEnd_773499 264784515181449610203499 := by
  unfold tailWord_773499
  simp only [CollatzResearch.WordTrace]
  refine ⟨28211826224752700957043551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18807884149835133971362367 28211826224752700957043551)
  ·
    refine ⟨42317739337129051435565327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28211826224752700957043551 42317739337129051435565327)
    ·
      refine ⟨63476609005693577153347991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42317739337129051435565327 63476609005693577153347991)
      ·
        refine ⟨95214913508540365730021987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63476609005693577153347991 95214913508540365730021987)
        ·
          refine ⟨142822370262810548595032981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95214913508540365730021987 142822370262810548595032981)
          ·
            refine ⟨6694798606069244465392171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142822370262810548595032981 6694798606069244465392171)
            ·
              refine ⟨10042197909103866698088257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694798606069244465392171 10042197909103866698088257)
              ·
                refine ⟨7531648431827900023566193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10042197909103866698088257 7531648431827900023566193)
                ·
                  refine ⟨5648736323870925017674645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531648431827900023566193 5648736323870925017674645)
                  ·
                    refine ⟨264784515181449610203499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5648736323870925017674645 264784515181449610203499)
                    ·
                      rfl

theorem cell22_773499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_773499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773499 prefixEnd_773499 := by exact prefixLift 773499
  have htrace : WordTrace (prefixWord ++ tailWord_773499) baseStart_773499 baseEnd_773499 := by
    simpa [prefixWord, tailWord_773499, baseEnd_773499] using wordTrace_append hprefix tailTrace_773499
  have hstable : (prefixWord ++ tailWord_773499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773499).length < 2 ^ (prefixWord ++ tailWord_773499).sum := by decide
  have hdescent : baseEnd_773499 < baseStart_773499 := by decide
  rcases family_descends (prefixWord ++ tailWord_773499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773505 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_773505 : Nat := 118140960795 + 773505 * 2 ^ 59
def prefixEnd_773505 : Nat := 4983230072969 + 3 ^ 40 * 773505 * 2
def baseEnd_773505 : Nat := 264786569104067594553481

theorem tailTrace_773505 : CollatzResearch.WordTrace tailWord_773505 prefixEnd_773505 264786569104067594553481 := by
  unfold tailWord_773505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212045062730963981761969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18808030041820642654507979 28212045062730963981761969)
  ·
    refine ⟨21159033797048222986321477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28212045062730963981761969 21159033797048222986321477)
    ·
      refine ⟨3967318836946541809935277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21159033797048222986321477 3967318836946541809935277)
      ·
        refine ⟨1487744563854953178725729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3967318836946541809935277 1487744563854953178725729)
        ·
          refine ⟨1115808422891214884044297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487744563854953178725729 1115808422891214884044297)
          ·
            refine ⟨836856317168411163033223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115808422891214884044297 836856317168411163033223)
            ·
              refine ⟨1255284475752616744549835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836856317168411163033223 1255284475752616744549835)
              ·
                refine ⟨1882926713628925116824753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255284475752616744549835 1882926713628925116824753)
                ·
                  refine ⟨1412195035221693837618565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882926713628925116824753 1412195035221693837618565)
                  ·
                    refine ⟨264786569104067594553481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412195035221693837618565 264786569104067594553481)
                    ·
                      rfl

theorem cell22_773505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_773505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773505 prefixEnd_773505 := by exact prefixLift 773505
  have htrace : WordTrace (prefixWord ++ tailWord_773505) baseStart_773505 baseEnd_773505 := by
    simpa [prefixWord, tailWord_773505, baseEnd_773505] using wordTrace_append hprefix tailTrace_773505
  have hstable : (prefixWord ++ tailWord_773505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773505).length < 2 ^ (prefixWord ++ tailWord_773505).sum := by decide
  have hdescent : baseEnd_773505 < baseStart_773505 := by decide
  rcases family_descends (prefixWord ++ tailWord_773505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773535 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 1, 3]
def baseStart_773535 : Nat := 118140960795 + 773535 * 2 ^ 59
def prefixEnd_773535 : Nat := 4983230072969 + 3 ^ 40 * 773535 * 2
def baseEnd_773535 : Nat := 264796838717157516303389

theorem tailTrace_773535 : CollatzResearch.WordTrace tailWord_773535 prefixEnd_773535 264796838717157516303389 := by
  unfold tailWord_773535
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213139252622279105354059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18808759501748186070236039 28213139252622279105354059)
  ·
    refine ⟨42319708878933418658031089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28213139252622279105354059 42319708878933418658031089)
    ·
      refine ⟨31739781659200063993523317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42319708878933418658031089 31739781659200063993523317)
      ·
        refine ⟨2975604530550005999392811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31739781659200063993523317 2975604530550005999392811)
        ·
          refine ⟨4463406795825008999089217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975604530550005999392811 4463406795825008999089217)
          ·
            refine ⟨3347555096868756749316913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463406795825008999089217 3347555096868756749316913)
            ·
              refine ⟨2510666322651567561987685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347555096868756749316913 2510666322651567561987685)
              ·
                refine ⟨470749935497168917872691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2510666322651567561987685 470749935497168917872691)
                ·
                  refine ⟨706124903245753376809037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470749935497168917872691 706124903245753376809037)
                  ·
                    refine ⟨264796838717157516303389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706124903245753376809037 264796838717157516303389)
                    ·
                      rfl

theorem cell22_773535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_773535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773535 prefixEnd_773535 := by exact prefixLift 773535
  have htrace : WordTrace (prefixWord ++ tailWord_773535) baseStart_773535 baseEnd_773535 := by
    simpa [prefixWord, tailWord_773535, baseEnd_773535] using wordTrace_append hprefix tailTrace_773535
  have hstable : (prefixWord ++ tailWord_773535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773535).length < 2 ^ (prefixWord ++ tailWord_773535).sum := by decide
  have hdescent : baseEnd_773535 < baseStart_773535 := by decide
  rcases family_descends (prefixWord ++ tailWord_773535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773578 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_773578 : Nat := 118140960795 + 773578 * 2 ^ 59
def prefixEnd_773578 : Nat := 4983230072969 + 3 ^ 40 * 773578 * 2
def baseEnd_773578 : Nat := 264811558495919737478257

theorem tailTrace_773578 : CollatzResearch.WordTrace tailWord_773578 prefixEnd_773578 264811558495919737478257 := by
  unfold tailWord_773578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053676897866624362292347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18809805060977664966112925 7053676897866624362292347)
  ·
    refine ⟨10580515346799936543438521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7053676897866624362292347 10580515346799936543438521)
    ·
      refine ⟨7935386510099952407578891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10580515346799936543438521 7935386510099952407578891)
      ·
        refine ⟨11903079765149928611368337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935386510099952407578891 11903079765149928611368337)
        ·
          refine ⟨8927309823862446458526253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11903079765149928611368337 8927309823862446458526253)
          ·
            refine ⟨3347741183948417421947345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8927309823862446458526253 3347741183948417421947345)
            ·
              refine ⟨2510805887961313066460509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347741183948417421947345 2510805887961313066460509)
              ·
                refine ⟨941552207985492399922691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510805887961313066460509 941552207985492399922691)
                ·
                  refine ⟨1412328311978238599884037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941552207985492399922691 1412328311978238599884037)
                  ·
                    refine ⟨264811558495919737478257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412328311978238599884037 264811558495919737478257)
                    ·
                      rfl

theorem cell22_773578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_773578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773578 prefixEnd_773578 := by exact prefixLift 773578
  have htrace : WordTrace (prefixWord ++ tailWord_773578) baseStart_773578 baseEnd_773578 := by
    simpa [prefixWord, tailWord_773578, baseEnd_773578] using wordTrace_append hprefix tailTrace_773578
  have hstable : (prefixWord ++ tailWord_773578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773578).length < 2 ^ (prefixWord ++ tailWord_773578).sum := by decide
  have hdescent : baseEnd_773578 < baseStart_773578 := by decide
  rcases family_descends (prefixWord ++ tailWord_773578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773593 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 6]
def baseStart_773593 : Nat := 118140960795 + 773593 * 2 ^ 59
def prefixEnd_773593 : Nat := 4983230072969 + 3 ^ 40 * 773593 * 2
def baseEnd_773593 : Nat := 88272231100821566117737

theorem tailTrace_773593 : CollatzResearch.WordTrace tailWord_773593 prefixEnd_773593 88272231100821566117737 := by
  unfold tailWord_773593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215254686412155010965433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810169790941436673976955 28215254686412155010965433)
  ·
    refine ⟨21161441014809116258224075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28215254686412155010965433 21161441014809116258224075)
    ·
      refine ⟨31742161522213674387336113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21161441014809116258224075 31742161522213674387336113)
      ·
        refine ⟨23806621141660255790502085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31742161522213674387336113 23806621141660255790502085)
        ·
          refine ⟨4463741464061297960719141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23806621141660255790502085 4463741464061297960719141)
          ·
            refine ⟨836951524511493367634839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4463741464061297960719141 836951524511493367634839)
            ·
              refine ⟨1255427286767240051452259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836951524511493367634839 1255427286767240051452259)
              ·
                refine ⟨1883140930150860077178389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255427286767240051452259 1883140930150860077178389)
                ·
                  refine ⟨88272231100821566117737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1883140930150860077178389 88272231100821566117737)
                  ·
                    rfl

theorem cell22_773593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_773593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773593 prefixEnd_773593 := by exact prefixLift 773593
  have htrace : WordTrace (prefixWord ++ tailWord_773593) baseStart_773593 baseEnd_773593 := by
    simpa [prefixWord, tailWord_773593, baseEnd_773593] using wordTrace_append hprefix tailTrace_773593
  have hstable : (prefixWord ++ tailWord_773593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773593).length < 2 ^ (prefixWord ++ tailWord_773593).sum := by decide
  have hdescent : baseEnd_773593 < baseStart_773593 := by decide
  rcases family_descends (prefixWord ++ tailWord_773593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773644 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_773644 : Nat := 118140960795 + 773644 * 2 ^ 59
def prefixEnd_773644 : Nat := 4983230072969 + 3 ^ 40 * 773644 * 2
def baseEnd_773644 : Nat := 88278050548239188442685

theorem tailTrace_773644 : CollatzResearch.WordTrace tailWord_773644 prefixEnd_773644 88278050548239188442685 := by
  unfold tailWord_773644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108557404613695360535993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18811409872818260480714657 14108557404613695360535993)
  ·
    refine ⟨10581418053460271520401995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14108557404613695360535993 10581418053460271520401995)
    ·
      refine ⟨15872127080190407280602993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581418053460271520401995 15872127080190407280602993)
      ·
        refine ⟨11904095310142805460452245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15872127080190407280602993 11904095310142805460452245)
        ·
          refine ⟨558004467662944005958699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11904095310142805460452245 558004467662944005958699)
          ·
            refine ⟨837006701494416008938049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558004467662944005958699 837006701494416008938049)
            ·
              refine ⟨627755026120812006703537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837006701494416008938049 627755026120812006703537)
              ·
                refine ⟨470816269590609005027653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627755026120812006703537 470816269590609005027653)
                ·
                  refine ⟨88278050548239188442685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470816269590609005027653 88278050548239188442685)
                  ·
                    rfl

theorem cell22_773644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_773644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773644 prefixEnd_773644 := by exact prefixLift 773644
  have htrace : WordTrace (prefixWord ++ tailWord_773644) baseStart_773644 baseEnd_773644 := by
    simpa [prefixWord, tailWord_773644, baseEnd_773644] using wordTrace_append hprefix tailTrace_773644
  have hstable : (prefixWord ++ tailWord_773644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773644).length < 2 ^ (prefixWord ++ tailWord_773644).sum := by decide
  have hdescent : baseEnd_773644 < baseStart_773644 := by decide
  rcases family_descends (prefixWord ++ tailWord_773644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773651 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_773651 : Nat := 118140960795 + 773651 * 2 ^ 59
def prefixEnd_773651 : Nat := 4983230072969 + 3 ^ 40 * 773651 * 2
def baseEnd_773651 : Nat := 264836547887771880403033

theorem tailTrace_773651 : CollatzResearch.WordTrace tailWord_773651 prefixEnd_773651 264836547887771880403033 := by
  unfold tailWord_773651
  simp only [CollatzResearch.WordTrace]
  refine ⟨28217370120202030916576807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18811580080134687277717871 28217370120202030916576807)
  ·
    refine ⟨42326055180303046374865211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28217370120202030916576807 42326055180303046374865211)
    ·
      refine ⟨63489082770454569562297817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42326055180303046374865211 63489082770454569562297817)
      ·
        refine ⟨47616812077840927171723363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63489082770454569562297817 47616812077840927171723363)
        ·
          refine ⟨71425218116761390757585045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47616812077840927171723363 71425218116761390757585045)
          ·
            refine ⟨3348057099223190191761799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71425218116761390757585045 3348057099223190191761799)
            ·
              refine ⟨5022085648834785287642699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348057099223190191761799 5022085648834785287642699)
              ·
                refine ⟨7533128473252177931464049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022085648834785287642699 7533128473252177931464049)
                ·
                  refine ⟨5649846354939133448598037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7533128473252177931464049 5649846354939133448598037)
                  ·
                    refine ⟨264836547887771880403033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5649846354939133448598037 264836547887771880403033)
                    ·
                      rfl

theorem cell22_773651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_773651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773651 prefixEnd_773651 := by exact prefixLift 773651
  have htrace : WordTrace (prefixWord ++ tailWord_773651) baseStart_773651 baseEnd_773651 := by
    simpa [prefixWord, tailWord_773651, baseEnd_773651] using wordTrace_append hprefix tailTrace_773651
  have hstable : (prefixWord ++ tailWord_773651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773651).length < 2 ^ (prefixWord ++ tailWord_773651).sum := by decide
  have hdescent : baseEnd_773651 < baseStart_773651 := by decide
  rcases family_descends (prefixWord ++ tailWord_773651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773681 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_773681 : Nat := 118140960795 + 773681 * 2 ^ 59
def prefixEnd_773681 : Nat := 4983230072969 + 3 ^ 40 * 773681 * 2
def baseEnd_773681 : Nat := 264846817500861802152941

theorem tailTrace_773681 : CollatzResearch.WordTrace tailWord_773681 prefixEnd_773681 264846817500861802152941 := by
  unfold tailWord_773681
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218464310093346040168897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18812309540062230693445931 28218464310093346040168897)
  ·
    refine ⟨21163848232570009530126673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28218464310093346040168897 21163848232570009530126673)
    ·
      refine ⟨15872886174427507147595005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21163848232570009530126673 15872886174427507147595005)
      ·
        refine ⟨5952332315410315180348127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15872886174427507147595005 5952332315410315180348127)
        ·
          refine ⟨8928498473115472770522191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952332315410315180348127 8928498473115472770522191)
          ·
            refine ⟨13392747709673209155783287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928498473115472770522191 13392747709673209155783287)
            ·
              refine ⟨20089121564509813733674931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13392747709673209155783287 20089121564509813733674931)
              ·
                refine ⟨30133682346764720600512397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20089121564509813733674931 30133682346764720600512397)
                ·
                  refine ⟨11300130880036770225192149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30133682346764720600512397 11300130880036770225192149)
                  ·
                    refine ⟨264846817500861802152941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11300130880036770225192149 264846817500861802152941)
                    ·
                      rfl

theorem cell22_773681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_773681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773681 prefixEnd_773681 := by exact prefixLift 773681
  have htrace : WordTrace (prefixWord ++ tailWord_773681) baseStart_773681 baseEnd_773681 := by
    simpa [prefixWord, tailWord_773681, baseEnd_773681] using wordTrace_append hprefix tailTrace_773681
  have hstable : (prefixWord ++ tailWord_773681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773681).length < 2 ^ (prefixWord ++ tailWord_773681).sum := by decide
  have hdescent : baseEnd_773681 < baseStart_773681 := by decide
  rcases family_descends (prefixWord ++ tailWord_773681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773687 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 1, 3]
def baseStart_773687 : Nat := 118140960795 + 773687 * 2 ^ 59
def prefixEnd_773687 : Nat := 4983230072969 + 3 ^ 40 * 773687 * 2
def baseEnd_773687 : Nat := 264848871423479786502923

theorem tailTrace_773687 : CollatzResearch.WordTrace tailWord_773687 prefixEnd_773687 264848871423479786502923 := by
  unfold tailWord_773687
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218683148071609064887315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18812455432047739376591543 28218683148071609064887315)
  ·
    refine ⟨42328024722107413597330973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28218683148071609064887315 42328024722107413597330973)
    ·
      refine ⟨15873009270790280098999115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42328024722107413597330973 15873009270790280098999115)
      ·
        refine ⟨23809513906185420148498673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15873009270790280098999115 23809513906185420148498673)
        ·
          refine ⟨17857135429639065111374005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23809513906185420148498673 17857135429639065111374005)
          ·
            refine ⟨1674106446528662354191313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17857135429639065111374005 1674106446528662354191313)
            ·
              refine ⟨1255579834896496765643485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674106446528662354191313 1255579834896496765643485)
              ·
                refine ⟨470842438086186287116307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255579834896496765643485 470842438086186287116307)
                ·
                  refine ⟨706263657129279430674461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470842438086186287116307 706263657129279430674461)
                  ·
                    refine ⟨264848871423479786502923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706263657129279430674461 264848871423479786502923)
                    ·
                      rfl

theorem cell22_773687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_773687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773687 prefixEnd_773687 := by exact prefixLift 773687
  have htrace : WordTrace (prefixWord ++ tailWord_773687) baseStart_773687 baseEnd_773687 := by
    simpa [prefixWord, tailWord_773687, baseEnd_773687] using wordTrace_append hprefix tailTrace_773687
  have hstable : (prefixWord ++ tailWord_773687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773687).length < 2 ^ (prefixWord ++ tailWord_773687).sum := by decide
  have hdescent : baseEnd_773687 < baseStart_773687 := by decide
  rcases family_descends (prefixWord ++ tailWord_773687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773760 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_773760 : Nat := 118140960795 + 773760 * 2 ^ 59
def prefixEnd_773760 : Nat := 4983230072969 + 3 ^ 40 * 773760 * 2
def baseEnd_773760 : Nat := 264873860815331929427699

theorem tailTrace_773760 : CollatzResearch.WordTrace tailWord_773760 prefixEnd_773760 264873860815331929427699 := by
  unfold tailWord_773760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14110672838403571266147367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18814230451204761688196489 14110672838403571266147367)
  ·
    refine ⟨21166009257605356899221051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14110672838403571266147367 21166009257605356899221051)
    ·
      refine ⟨31749013886408035348831577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21166009257605356899221051 31749013886408035348831577)
      ·
        refine ⟨23811760414806026511623683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31749013886408035348831577 23811760414806026511623683)
        ·
          refine ⟨35717640622209039767435525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23811760414806026511623683 35717640622209039767435525)
          ·
            refine ⟨6697057616664194956394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35717640622209039767435525 6697057616664194956394161)
            ·
              refine ⟨5022793212498146217295621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697057616664194956394161 5022793212498146217295621)
              ·
                refine ⟨941773727343402415742929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5022793212498146217295621 941773727343402415742929)
                ·
                  refine ⟨706330295507551811807197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941773727343402415742929 706330295507551811807197)
                  ·
                    refine ⟨264873860815331929427699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706330295507551811807197 264873860815331929427699)
                    ·
                      rfl

theorem cell22_773760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_773760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773760 prefixEnd_773760 := by exact prefixLift 773760
  have htrace : WordTrace (prefixWord ++ tailWord_773760) baseStart_773760 baseEnd_773760 := by
    simpa [prefixWord, tailWord_773760, baseEnd_773760] using wordTrace_append hprefix tailTrace_773760
  have hstable : (prefixWord ++ tailWord_773760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773760).length < 2 ^ (prefixWord ++ tailWord_773760).sum := by decide
  have hdescent : baseEnd_773760 < baseStart_773760 := by decide
  rcases family_descends (prefixWord ++ tailWord_773760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773790 : List Nat := [4, 3, 1, 1, 1, 2, 2, 8]
def baseStart_773790 : Nat := 118140960795 + 773790 * 2 ^ 59
def prefixEnd_773790 : Nat := 4983230072969 + 3 ^ 40 * 773790 * 2
def baseEnd_773790 : Nat := 29431570047602427908623

theorem tailTrace_773790 : CollatzResearch.WordTrace tailWord_773790 prefixEnd_773790 29431570047602427908623 := by
  unfold tailWord_773790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527804983337307206985853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18814959911132305103924549 3527804983337307206985853)
  ·
    refine ⟨1322926868751490202619695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3527804983337307206985853 1322926868751490202619695)
    ·
      refine ⟨1984390303127235303929543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322926868751490202619695 1984390303127235303929543)
      ·
        refine ⟨2976585454690852955894315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984390303127235303929543 2976585454690852955894315)
        ·
          refine ⟨4464878182036279433841473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976585454690852955894315 4464878182036279433841473)
          ·
            refine ⟨3348658636527209575381105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464878182036279433841473 3348658636527209575381105)
            ·
              refine ⟨2511493977395407181535829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348658636527209575381105 2511493977395407181535829)
              ·
                refine ⟨29431570047602427908623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2511493977395407181535829 29431570047602427908623)
                ·
                  rfl

theorem cell22_773790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_773790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773790 prefixEnd_773790 := by exact prefixLift 773790
  have htrace : WordTrace (prefixWord ++ tailWord_773790) baseStart_773790 baseEnd_773790 := by
    simpa [prefixWord, tailWord_773790, baseEnd_773790] using wordTrace_append hprefix tailTrace_773790
  have hstable : (prefixWord ++ tailWord_773790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773790).length < 2 ^ (prefixWord ++ tailWord_773790).sum := by decide
  have hdescent : baseEnd_773790 < baseStart_773790 := by decide
  rcases family_descends (prefixWord ++ tailWord_773790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773914 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_773914 : Nat := 118140960795 + 773914 * 2 ^ 59
def prefixEnd_773914 : Nat := 4983230072969 + 3 ^ 40 * 773914 * 2
def baseEnd_773914 : Nat := 88308859387508953692409

theorem tailTrace_773914 : CollatzResearch.WordTrace tailWord_773914 prefixEnd_773914 88308859387508953692409 := by
  unfold tailWord_773914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056740629562306708350199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18817975012166151222267197 7056740629562306708350199)
  ·
    refine ⟨10585110944343460062525299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7056740629562306708350199 10585110944343460062525299)
    ·
      refine ⟨15877666416515190093787949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10585110944343460062525299 15877666416515190093787949)
      ·
        refine ⟨5954124906193196285170481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15877666416515190093787949 5954124906193196285170481)
        ·
          refine ⟨4465593679644897213877861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954124906193196285170481 4465593679644897213877861)
          ·
            refine ⟨837298814933418227602099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4465593679644897213877861 837298814933418227602099)
            ·
              refine ⟨1255948222400127341403149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837298814933418227602099 1255948222400127341403149)
              ·
                refine ⟨470980583400047753026181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255948222400127341403149 470980583400047753026181)
                ·
                  refine ⟨88308859387508953692409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470980583400047753026181 88308859387508953692409)
                  ·
                    rfl

theorem cell22_773914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_773914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773914 prefixEnd_773914 := by exact prefixLift 773914
  have htrace : WordTrace (prefixWord ++ tailWord_773914) baseStart_773914 baseEnd_773914 := by
    simpa [prefixWord, tailWord_773914, baseEnd_773914] using wordTrace_append hprefix tailTrace_773914
  have hstable : (prefixWord ++ tailWord_773914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773914).length < 2 ^ (prefixWord ++ tailWord_773914).sum := by decide
  have hdescent : baseEnd_773914 < baseStart_773914 := by decide
  rcases family_descends (prefixWord ++ tailWord_773914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773925 : List Nat := [1, 3, 1, 2, 3, 4, 8]
def baseStart_773925 : Nat := 118140960795 + 773925 * 2 ^ 59
def prefixEnd_773925 : Nat := 4983230072969 + 3 ^ 40 * 773925 * 2
def baseEnd_773925 : Nat := 9812234951382462927859

theorem tailTrace_773925 : CollatzResearch.WordTrace tailWord_773925 prefixEnd_773925 9812234951382462927859 := by
  unfold tailWord_773925
  simp only [CollatzResearch.WordTrace]
  refine ⟨28227363721209375712051229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18818242480806250474700819 28227363721209375712051229)
  ·
    refine ⟨10585261395453515892019211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28227363721209375712051229 10585261395453515892019211)
    ·
      refine ⟨15877892093180273838028817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10585261395453515892019211 15877892093180273838028817)
      ·
        refine ⟨11908419069885205378521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15877892093180273838028817 11908419069885205378521613)
        ·
          refine ⟨4465657151206952016945605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11908419069885205378521613 4465657151206952016945605)
          ·
            refine ⟨837310715851303503177301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4465657151206952016945605 837310715851303503177301)
            ·
              refine ⟨9812234951382462927859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 837310715851303503177301 9812234951382462927859)
              ·
                rfl

theorem cell22_773925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 8].length) (baseStart_773925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773925 prefixEnd_773925 := by exact prefixLift 773925
  have htrace : WordTrace (prefixWord ++ tailWord_773925) baseStart_773925 baseEnd_773925 := by
    simpa [prefixWord, tailWord_773925, baseEnd_773925] using wordTrace_append hprefix tailTrace_773925
  have hstable : (prefixWord ++ tailWord_773925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773925).length < 2 ^ (prefixWord ++ tailWord_773925).sum := by decide
  have hdescent : baseEnd_773925 < baseStart_773925 := by decide
  rcases family_descends (prefixWord ++ tailWord_773925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773942 : List Nat := [5, 1, 2, 2, 1, 1, 1, 9]
def baseStart_773942 : Nat := 118140960795 + 773942 * 2 ^ 59
def prefixEnd_773942 : Nat := 4983230072969 + 3 ^ 40 * 773942 * 2
def baseEnd_773942 : Nat := 29437351459416013486349

theorem tailTrace_773942 : CollatzResearch.WordTrace tailWord_773942 prefixEnd_773942 29437351459416013486349 := by
  unfold tailWord_773942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764248985134236725963755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18818655841431858410280053 1764248985134236725963755)
  ·
    refine ⟨2646373477701355088945633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764248985134236725963755 2646373477701355088945633)
    ·
      refine ⟨1984780108276016316709225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2646373477701355088945633 1984780108276016316709225)
      ·
        refine ⟨1488585081207012237531919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1984780108276016316709225 1488585081207012237531919)
        ·
          refine ⟨2232877621810518356297879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488585081207012237531919 2232877621810518356297879)
          ·
            refine ⟨3349316432715777534446819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232877621810518356297879 3349316432715777534446819)
            ·
              refine ⟨5023974649073666301670229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349316432715777534446819 5023974649073666301670229)
              ·
                refine ⟨29437351459416013486349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5023974649073666301670229 29437351459416013486349)
                ·
                  rfl

theorem cell22_773942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_773942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773942 prefixEnd_773942 := by exact prefixLift 773942
  have htrace : WordTrace (prefixWord ++ tailWord_773942) baseStart_773942 baseEnd_773942 := by
    simpa [prefixWord, tailWord_773942, baseEnd_773942] using wordTrace_append hprefix tailTrace_773942
  have hstable : (prefixWord ++ tailWord_773942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773942).length < 2 ^ (prefixWord ++ tailWord_773942).sum := by decide
  have hdescent : baseEnd_773942 < baseStart_773942 := by decide
  rcases family_descends (prefixWord ++ tailWord_773942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773946 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_773946 : Nat := 118140960795 + 773946 * 2 ^ 59
def prefixEnd_773946 : Nat := 4983230072969 + 3 ^ 40 * 773946 * 2
def baseEnd_773946 : Nat := 264937532416489444277129

theorem tailTrace_773946 : CollatzResearch.WordTrace tailWord_773946 prefixEnd_773946 264937532416489444277129 := by
  unfold tailWord_773946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057032413533324074641423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18818753102755530865710461 7057032413533324074641423)
  ·
    refine ⟨10585548620299986111962135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7057032413533324074641423 10585548620299986111962135)
    ·
      refine ⟨15878322930449979167943203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10585548620299986111962135 15878322930449979167943203)
      ·
        refine ⟨23817484395674968751914805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878322930449979167943203 23817484395674968751914805)
        ·
          refine ⟨2232889162094528320492013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23817484395674968751914805 2232889162094528320492013)
          ·
            refine ⟨837333435785448120184505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2232889162094528320492013 837333435785448120184505)
            ·
              refine ⟨628000076839086090138379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837333435785448120184505 628000076839086090138379)
              ·
                refine ⟨942000115258629135207569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628000076839086090138379 942000115258629135207569)
                ·
                  refine ⟨706500086443971851405677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942000115258629135207569 706500086443971851405677)
                  ·
                    refine ⟨264937532416489444277129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706500086443971851405677 264937532416489444277129)
                    ·
                      rfl

theorem cell22_773946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_773946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773946 prefixEnd_773946 := by exact prefixLift 773946
  have htrace : WordTrace (prefixWord ++ tailWord_773946) baseStart_773946 baseEnd_773946 := by
    simpa [prefixWord, tailWord_773946, baseEnd_773946] using wordTrace_append hprefix tailTrace_773946
  have hstable : (prefixWord ++ tailWord_773946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773946).length < 2 ^ (prefixWord ++ tailWord_773946).sum := by decide
  have hdescent : baseEnd_773946 < baseStart_773946 := by decide
  rcases family_descends (prefixWord ++ tailWord_773946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773985 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_773985 : Nat := 118140960795 + 773985 * 2 ^ 59
def prefixEnd_773985 : Nat := 4983230072969 + 3 ^ 40 * 773985 * 2
def baseEnd_773985 : Nat := 264950882913506342552009

theorem tailTrace_773985 : CollatzResearch.WordTrace tailWord_773985 prefixEnd_773985 264950882913506342552009 := by
  unfold tailWord_773985
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229552100992005959235409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18819701400661337306156939 28229552100992005959235409)
  ·
    refine ⟨21172164075744004469426557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28229552100992005959235409 21172164075744004469426557)
    ·
      refine ⟨7939561528404001676034959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21172164075744004469426557 7939561528404001676034959)
      ·
        refine ⟨11909342292606002514052439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939561528404001676034959 11909342292606002514052439)
        ·
          refine ⟨17864013438909003771078659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909342292606002514052439 17864013438909003771078659)
          ·
            refine ⟨26796020158363505656617989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17864013438909003771078659 26796020158363505656617989)
            ·
              refine ⟨5024253779693157310615873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26796020158363505656617989 5024253779693157310615873)
              ·
                refine ⟨3768190334769867982961905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024253779693157310615873 3768190334769867982961905)
                ·
                  refine ⟨2826142751077400987221429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3768190334769867982961905 2826142751077400987221429)
                  ·
                    refine ⟨264950882913506342552009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2826142751077400987221429 264950882913506342552009)
                    ·
                      rfl

theorem cell22_773985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_773985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_773985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_773985 prefixEnd_773985 := by exact prefixLift 773985
  have htrace : WordTrace (prefixWord ++ tailWord_773985) baseStart_773985 baseEnd_773985 := by
    simpa [prefixWord, tailWord_773985, baseEnd_773985] using wordTrace_append hprefix tailTrace_773985
  have hstable : (prefixWord ++ tailWord_773985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773985).length < 2 ^ (prefixWord ++ tailWord_773985).sum := by decide
  have hdescent : baseEnd_773985 < baseStart_773985 := by decide
  rcases family_descends (prefixWord ++ tailWord_773985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_774032 : Nat := 118140960795 + 774032 * 2 ^ 59
def prefixEnd_774032 : Nat := 4983230072969 + 3 ^ 40 * 774032 * 2
def baseEnd_774032 : Nat := 88322323991337962208955

theorem tailTrace_774032 : CollatzResearch.WordTrace tailWord_774032 prefixEnd_774032 88322323991337962208955 := by
  unfold tailWord_774032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115633165910866493098175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18820844221214488657464233 14115633165910866493098175)
  ·
    refine ⟨21173449748866299739647263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14115633165910866493098175 21173449748866299739647263)
    ·
      refine ⟨31760174623299449609470895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173449748866299739647263 31760174623299449609470895)
      ·
        refine ⟨47640261934949174414206343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760174623299449609470895 47640261934949174414206343)
        ·
          refine ⟨71460392902423761621309515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47640261934949174414206343 71460392902423761621309515)
          ·
            refine ⟨107190589353635642431964273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71460392902423761621309515 107190589353635642431964273)
            ·
              refine ⟨80392942015226731823973205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107190589353635642431964273 80392942015226731823973205)
              ·
                refine ⟨471052394620469131781093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 80392942015226731823973205 471052394620469131781093)
                ·
                  refine ⟨88322323991337962208955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471052394620469131781093 88322323991337962208955)
                  ·
                    rfl

theorem cell22_774032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_774032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774032 prefixEnd_774032 := by exact prefixLift 774032
  have htrace : WordTrace (prefixWord ++ tailWord_774032) baseStart_774032 baseEnd_774032 := by
    simpa [prefixWord, tailWord_774032, baseEnd_774032] using wordTrace_append hprefix tailTrace_774032
  have hstable : (prefixWord ++ tailWord_774032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774032).length < 2 ^ (prefixWord ++ tailWord_774032).sum := by decide
  have hdescent : baseEnd_774032 < baseStart_774032 := by decide
  rcases family_descends (prefixWord ++ tailWord_774032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774049 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 6]
def baseStart_774049 : Nat := 118140960795 + 774049 * 2 ^ 59
def prefixEnd_774049 : Nat := 4983230072969 + 3 ^ 40 * 774049 * 2
def baseEnd_774049 : Nat := 88324263807143836317271

theorem tailTrace_774049 : CollatzResearch.WordTrace tailWord_774049 prefixEnd_774049 88324263807143836317271 := by
  unfold tailWord_774049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231886372760144889565201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18821257581840096593043467 28231886372760144889565201)
  ·
    refine ⟨21173914779570108667173901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28231886372760144889565201 21173914779570108667173901)
    ·
      refine ⟨7940218042338790750190213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21173914779570108667173901 7940218042338790750190213)
      ·
        refine ⟨1488790882938523265660665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7940218042338790750190213 1488790882938523265660665)
        ·
          refine ⟨1116593162203892449245499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488790882938523265660665 1116593162203892449245499)
          ·
            refine ⟨1674889743305838673868249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116593162203892449245499 1674889743305838673868249)
            ·
              refine ⟨1256167307479379005401187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674889743305838673868249 1256167307479379005401187)
              ·
                refine ⟨1884250961219068508101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256167307479379005401187 1884250961219068508101781)
                ·
                  refine ⟨88324263807143836317271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1884250961219068508101781 88324263807143836317271)
                  ·
                    rfl

theorem cell22_774049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_774049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774049 prefixEnd_774049 := by exact prefixLift 774049
  have htrace : WordTrace (prefixWord ++ tailWord_774049) baseStart_774049 baseEnd_774049 := by
    simpa [prefixWord, tailWord_774049, baseEnd_774049] using wordTrace_append hprefix tailTrace_774049
  have hstable : (prefixWord ++ tailWord_774049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774049).length < 2 ^ (prefixWord ++ tailWord_774049).sum := by decide
  have hdescent : baseEnd_774049 < baseStart_774049 := by decide
  rcases family_descends (prefixWord ++ tailWord_774049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774068 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_774068 : Nat := 118140960795 + 774068 * 2 ^ 59
def prefixEnd_774068 : Nat := 4983230072969 + 3 ^ 40 * 774068 * 2
def baseEnd_774068 : Nat := 264979295509721792726755

theorem tailTrace_774068 : CollatzResearch.WordTrace tailWord_774068 prefixEnd_774068 264979295509721792726755 := by
  unfold tailWord_774068
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116289679845655567253429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18821719573127540756337905 14116289679845655567253429)
  ·
    refine ⟨1323402157485530209430009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14116289679845655567253429 1323402157485530209430009)
    ·
      refine ⟨992551618114147657072507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1323402157485530209430009 992551618114147657072507)
      ·
        refine ⟨1488827427171221485608761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992551618114147657072507 1488827427171221485608761)
        ·
          refine ⟨1116620570378416114206571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488827427171221485608761 1116620570378416114206571)
          ·
            refine ⟨1674930855567624171309857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116620570378416114206571 1674930855567624171309857)
            ·
              refine ⟨1256198141675718128482393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674930855567624171309857 1256198141675718128482393)
              ·
                refine ⟨942148606256788596361795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256198141675718128482393 942148606256788596361795)
                ·
                  refine ⟨1413222909385182894542693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942148606256788596361795 1413222909385182894542693)
                  ·
                    refine ⟨264979295509721792726755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1413222909385182894542693 264979295509721792726755)
                    ·
                      rfl

theorem cell22_774068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_774068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774068 prefixEnd_774068 := by exact prefixLift 774068
  have htrace : WordTrace (prefixWord ++ tailWord_774068) baseStart_774068 baseEnd_774068 := by
    simpa [prefixWord, tailWord_774068, baseEnd_774068] using wordTrace_append hprefix tailTrace_774068
  have hstable : (prefixWord ++ tailWord_774068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774068).length < 2 ^ (prefixWord ++ tailWord_774068).sum := by decide
  have hdescent : baseEnd_774068 < baseStart_774068 := by decide
  rcases family_descends (prefixWord ++ tailWord_774068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774077 : List Nat := [1, 4, 1, 2, 3, 2, 1, 8]
def baseStart_774077 : Nat := 118140960795 + 774077 * 2 ^ 59
def prefixEnd_774077 : Nat := 4983230072969 + 3 ^ 40 * 774077 * 2
def baseEnd_774077 : Nat := 29442486265960974361303

theorem tailTrace_774077 : CollatzResearch.WordTrace tailWord_774077 prefixEnd_774077 29442486265960974361303 := by
  unfold tailWord_774077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232907616658705671584485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18821938411105803781056323 28232907616658705671584485)
  ·
    refine ⟨5293670178123507313422091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28232907616658705671584485 5293670178123507313422091)
    ·
      refine ⟨7940505267185260970133137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293670178123507313422091 7940505267185260970133137)
      ·
        refine ⟨5955378950388945727599853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7940505267185260970133137 5955378950388945727599853)
        ·
          refine ⟨2233267106395854647849945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5955378950388945727599853 2233267106395854647849945)
          ·
            refine ⟨1674950329796890985887459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233267106395854647849945 1674950329796890985887459)
            ·
              refine ⟨2512425494695336478831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674950329796890985887459 2512425494695336478831189)
              ·
                refine ⟨29442486265960974361303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2512425494695336478831189 29442486265960974361303)
                ·
                  rfl

theorem cell22_774077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 8].length) (baseStart_774077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774077 prefixEnd_774077 := by exact prefixLift 774077
  have htrace : WordTrace (prefixWord ++ tailWord_774077) baseStart_774077 baseEnd_774077 := by
    simpa [prefixWord, tailWord_774077, baseEnd_774077] using wordTrace_append hprefix tailTrace_774077
  have hstable : (prefixWord ++ tailWord_774077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774077).length < 2 ^ (prefixWord ++ tailWord_774077).sum := by decide
  have hdescent : baseEnd_774077 < baseStart_774077 := by decide
  rcases family_descends (prefixWord ++ tailWord_774077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774257 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 9]
def baseStart_774257 : Nat := 118140960795 + 774257 * 2 ^ 59
def prefixEnd_774257 : Nat := 4983230072969 + 3 ^ 40 * 774257 * 2
def baseEnd_774257 : Nat := 88347998024062766583725

theorem tailTrace_774257 : CollatzResearch.WordTrace tailWord_774257 prefixEnd_774257 88347998024062766583725 := by
  unfold tailWord_774257
  simp only [CollatzResearch.WordTrace]
  refine ⟨28239472756006596413137025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18826315170671064275424683 28239472756006596413137025)
  ·
    refine ⟨21179604567004947309852769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28239472756006596413137025 21179604567004947309852769)
    ·
      refine ⟨15884703425253710482389577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21179604567004947309852769 15884703425253710482389577)
      ·
        refine ⟨11913527568940282861792183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15884703425253710482389577 11913527568940282861792183)
        ·
          refine ⟨17870291353410424292688275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11913527568940282861792183 17870291353410424292688275)
          ·
            refine ⟨26805437030115636439032413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17870291353410424292688275 26805437030115636439032413)
            ·
              refine ⟨10052038886293363664637155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26805437030115636439032413 10052038886293363664637155)
              ·
                refine ⟨15078058329440045496955733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052038886293363664637155 15078058329440045496955733)
                ·
                  refine ⟨88347998024062766583725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15078058329440045496955733 88347998024062766583725)
                  ·
                    rfl

theorem cell22_774257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_774257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774257 prefixEnd_774257 := by exact prefixLift 774257
  have htrace : WordTrace (prefixWord ++ tailWord_774257) baseStart_774257 baseEnd_774257 := by
    simpa [prefixWord, tailWord_774257, baseEnd_774257] using wordTrace_append hprefix tailTrace_774257
  have hstable : (prefixWord ++ tailWord_774257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774257).length < 2 ^ (prefixWord ++ tailWord_774257).sum := by decide
  have hdescent : baseEnd_774257 < baseStart_774257 := by decide
  rcases family_descends (prefixWord ++ tailWord_774257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774351 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 2, 3]
def baseStart_774351 : Nat := 118140960795 + 774351 * 2 ^ 59
def prefixEnd_774351 : Nat := 4983230072969 + 3 ^ 40 * 774351 * 2
def baseEnd_774351 : Nat := 265076172193203387900887

theorem tailTrace_774351 : CollatzResearch.WordTrace tailWord_774351 prefixEnd_774351 265076172193203387900887 := by
  unfold tailWord_774351
  simp only [CollatzResearch.WordTrace]
  refine ⟨28242901217666050467058907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18828600811777366978039271 28242901217666050467058907)
  ·
    refine ⟨42364351826499075700588361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28242901217666050467058907 42364351826499075700588361)
    ·
      refine ⟨31773263869874306775441271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42364351826499075700588361 31773263869874306775441271)
      ·
        refine ⟨47659895804811460163161907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31773263869874306775441271 47659895804811460163161907)
        ·
          refine ⟨71489843707217190244742861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47659895804811460163161907 71489843707217190244742861)
          ·
            refine ⟨26808691390206446341778573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71489843707217190244742861 26808691390206446341778573)
            ·
              refine ⟨10053259271327417378166965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26808691390206446341778573 10053259271327417378166965)
              ·
                refine ⟨942493056686945379203153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10053259271327417378166965 942493056686945379203153)
                ·
                  refine ⟨706869792515209034402365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942493056686945379203153 706869792515209034402365)
                  ·
                    refine ⟨265076172193203387900887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706869792515209034402365 265076172193203387900887)
                    ·
                      rfl

theorem cell22_774351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_774351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774351 prefixEnd_774351 := by exact prefixLift 774351
  have htrace : WordTrace (prefixWord ++ tailWord_774351) baseStart_774351 baseEnd_774351 := by
    simpa [prefixWord, tailWord_774351, baseEnd_774351] using wordTrace_append hprefix tailTrace_774351
  have hstable : (prefixWord ++ tailWord_774351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774351).length < 2 ^ (prefixWord ++ tailWord_774351).sum := by decide
  have hdescent : baseEnd_774351 < baseStart_774351 := by decide
  rcases family_descends (prefixWord ++ tailWord_774351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774381 : List Nat := [1, 5, 1, 2, 3, 1, 9]
def baseStart_774381 : Nat := 118140960795 + 774381 * 2 ^ 59
def prefixEnd_774381 : Nat := 4983230072969 + 3 ^ 40 * 774381 * 2
def baseEnd_774381 : Nat := 9818016363196048505585

theorem tailTrace_774381 : CollatzResearch.WordTrace tailWord_774381 prefixEnd_774381 9818016363196048505585 := by
  unfold tailWord_774381
  simp only [CollatzResearch.WordTrace]
  refine ⟨28243995407557365590650997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18829330271704910393767331 28243995407557365590650997)
  ·
    refine ⟨2647874569458503024123531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28243995407557365590650997 2647874569458503024123531)
    ·
      refine ⟨3971811854187754536185297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647874569458503024123531 3971811854187754536185297)
      ·
        refine ⟨2978858890640815902138973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971811854187754536185297 2978858890640815902138973)
        ·
          refine ⟨1117072083990305963302115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2978858890640815902138973 1117072083990305963302115)
          ·
            refine ⟨1675608125985458944953173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117072083990305963302115 1675608125985458944953173)
            ·
              refine ⟨9818016363196048505585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1675608125985458944953173 9818016363196048505585)
              ·
                rfl

theorem cell22_774381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 9].length) (baseStart_774381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774381 prefixEnd_774381 := by exact prefixLift 774381
  have htrace : WordTrace (prefixWord ++ tailWord_774381) baseStart_774381 baseEnd_774381 := by
    simpa [prefixWord, tailWord_774381, baseEnd_774381] using wordTrace_append hprefix tailTrace_774381
  have hstable : (prefixWord ++ tailWord_774381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774381).length < 2 ^ (prefixWord ++ tailWord_774381).sum := by decide
  have hdescent : baseEnd_774381 < baseStart_774381 := by decide
  rcases family_descends (prefixWord ++ tailWord_774381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774402 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_774402 : Nat := 118140960795 + 774402 * 2 ^ 59
def prefixEnd_774402 : Nat := 4983230072969 + 3 ^ 40 * 774402 * 2
def baseEnd_774402 : Nat := 265093630535456254875731

theorem tailTrace_774402 : CollatzResearch.WordTrace tailWord_774402 prefixEnd_774402 265093630535456254875731 := by
  unfold tailWord_774402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061190335120321544291365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18829840893654190784776973 7061190335120321544291365)
  ·
    refine ⟨1323973187835060289554631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7061190335120321544291365 1323973187835060289554631)
    ·
      refine ⟨1985959781752590434331947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323973187835060289554631 1985959781752590434331947)
      ·
        refine ⟨2978939672628885651497921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985959781752590434331947 2978939672628885651497921)
        ·
          refine ⟨2234204754471664238623441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978939672628885651497921 2234204754471664238623441)
          ·
            refine ⟨1675653565853748178967581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234204754471664238623441 1675653565853748178967581)
            ·
              refine ⟨628370087195155567112843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1675653565853748178967581 628370087195155567112843)
              ·
                refine ⟨942555130792733350669265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628370087195155567112843 942555130792733350669265)
                ·
                  refine ⟨706916348094550013001949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942555130792733350669265 706916348094550013001949)
                  ·
                    refine ⟨265093630535456254875731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706916348094550013001949 265093630535456254875731)
                    ·
                      rfl

theorem cell22_774402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_774402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774402 prefixEnd_774402 := by exact prefixLift 774402
  have htrace : WordTrace (prefixWord ++ tailWord_774402) baseStart_774402 baseEnd_774402 := by
    simpa [prefixWord, tailWord_774402, baseEnd_774402] using wordTrace_append hprefix tailTrace_774402
  have hstable : (prefixWord ++ tailWord_774402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774402).length < 2 ^ (prefixWord ++ tailWord_774402).sum := by decide
  have hdescent : baseEnd_774402 < baseStart_774402 := by decide
  rcases family_descends (prefixWord ++ tailWord_774402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774565 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_774565 : Nat := 118140960795 + 774565 * 2 ^ 59
def prefixEnd_774565 : Nat := 4983230072969 + 3 ^ 40 * 774565 * 2
def baseEnd_774565 : Nat := 265149428766578163050231

theorem tailTrace_774565 : CollatzResearch.WordTrace tailWord_774565 prefixEnd_774565 265149428766578163050231 := by
  unfold tailWord_774565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28250706438890765015349149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18833804292593843343566099 28250706438890765015349149)
  ·
    refine ⟨10594014914584036880755931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28250706438890765015349149 10594014914584036880755931)
    ·
      refine ⟨15891022371876055321133897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594014914584036880755931 15891022371876055321133897)
      ·
        refine ⟨11918266778907041490850423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15891022371876055321133897 11918266778907041490850423)
        ·
          refine ⟨17877400168360562236275635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918266778907041490850423 17877400168360562236275635)
          ·
            refine ⟨26816100252540843354413453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17877400168360562236275635 26816100252540843354413453)
            ·
              refine ⟨10056037594702816257905045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26816100252540843354413453 10056037594702816257905045)
              ·
                refine ⟨471376762251694512089299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10056037594702816257905045 471376762251694512089299)
                ·
                  refine ⟨707065143377541768133949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471376762251694512089299 707065143377541768133949)
                  ·
                    refine ⟨265149428766578163050231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707065143377541768133949 265149428766578163050231)
                    ·
                      rfl

theorem cell22_774565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_774565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774565 prefixEnd_774565 := by exact prefixLift 774565
  have htrace : WordTrace (prefixWord ++ tailWord_774565) baseStart_774565 baseEnd_774565 := by
    simpa [prefixWord, tailWord_774565, baseEnd_774565] using wordTrace_append hprefix tailTrace_774565
  have hstable : (prefixWord ++ tailWord_774565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774565).length < 2 ^ (prefixWord ++ tailWord_774565).sum := by decide
  have hdescent : baseEnd_774565 < baseStart_774565 := by decide
  rcases family_descends (prefixWord ++ tailWord_774565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774623 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 6]
def baseStart_774623 : Nat := 118140960795 + 774623 * 2 ^ 59
def prefixEnd_774623 : Nat := 4983230072969 + 3 ^ 40 * 774623 * 2
def baseEnd_774623 : Nat := 88389761117295115033351

theorem tailTrace_774623 : CollatzResearch.WordTrace tailWord_774623 prefixEnd_774623 88389761117295115033351 := by
  unfold tailWord_774623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28252821872680640920960523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18835214581787093947307015 28252821872680640920960523)
  ·
    refine ⟨42379232809020961381440785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28252821872680640920960523 42379232809020961381440785)
    ·
      refine ⟨31784424606765721036080589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42379232809020961381440785 31784424606765721036080589)
      ·
        refine ⟨11919159227537145388530221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31784424606765721036080589 11919159227537145388530221)
        ·
          refine ⟨4469684710326429520698833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11919159227537145388530221 4469684710326429520698833)
          ·
            refine ⟨3352263532744822140524125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469684710326429520698833 3352263532744822140524125)
            ·
              refine ⟨1257098824779308302696547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3352263532744822140524125 1257098824779308302696547)
              ·
                refine ⟨1885648237168962454044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257098824779308302696547 1885648237168962454044821)
                ·
                  refine ⟨88389761117295115033351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1885648237168962454044821 88389761117295115033351)
                  ·
                    rfl

theorem cell22_774623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_774623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774623 prefixEnd_774623 := by exact prefixLift 774623
  have htrace : WordTrace (prefixWord ++ tailWord_774623) baseStart_774623 baseEnd_774623 := by
    simpa [prefixWord, tailWord_774623, baseEnd_774623] using wordTrace_append hprefix tailTrace_774623
  have hstable : (prefixWord ++ tailWord_774623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774623).length < 2 ^ (prefixWord ++ tailWord_774623).sum := by decide
  have hdescent : baseEnd_774623 < baseStart_774623 := by decide
  rcases family_descends (prefixWord ++ tailWord_774623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774629 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 5]
def baseStart_774629 : Nat := 118140960795 + 774629 * 2 ^ 59
def prefixEnd_774629 : Nat := 4983230072969 + 3 ^ 40 * 774629 * 2
def baseEnd_774629 : Nat := 88390445758167776483345

theorem tailTrace_774629 : CollatzResearch.WordTrace tailWord_774629 prefixEnd_774629 88390445758167776483345 := by
  unfold tailWord_774629
  simp only [CollatzResearch.WordTrace]
  refine ⟨28253040710658903945678941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18835360473772602630452627 28253040710658903945678941)
  ·
    refine ⟨10594890266497088979629603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28253040710658903945678941 10594890266497088979629603)
    ·
      refine ⟨15892335399745633469444405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594890266497088979629603 15892335399745633469444405)
      ·
        refine ⟨1489906443726153137760413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15892335399745633469444405 1489906443726153137760413)
        ·
          refine ⟨558714916397307426660155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489906443726153137760413 558714916397307426660155)
          ·
            refine ⟨838072374595961139990233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558714916397307426660155 838072374595961139990233)
            ·
              refine ⟨628554280946970854992675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838072374595961139990233 628554280946970854992675)
              ·
                refine ⟨942831421420456282489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628554280946970854992675 942831421420456282489013)
                ·
                  refine ⟨88390445758167776483345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 942831421420456282489013 88390445758167776483345)
                  ·
                    rfl

theorem cell22_774629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_774629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774629 prefixEnd_774629 := by exact prefixLift 774629
  have htrace : WordTrace (prefixWord ++ tailWord_774629) baseStart_774629 baseEnd_774629 := by
    simpa [prefixWord, tailWord_774629, baseEnd_774629] using wordTrace_append hprefix tailTrace_774629
  have hstable : (prefixWord ++ tailWord_774629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774629).length < 2 ^ (prefixWord ++ tailWord_774629).sum := by decide
  have hdescent : baseEnd_774629 < baseStart_774629 := by decide
  rcases family_descends (prefixWord ++ tailWord_774629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774670 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_774670 : Nat := 118140960795 + 774670 * 2 ^ 59
def prefixEnd_774670 : Nat := 4983230072969 + 3 ^ 40 * 774670 * 2
def baseEnd_774670 : Nat := 265185372412392889174909

theorem tailTrace_774670 : CollatzResearch.WordTrace tailWord_774670 prefixEnd_774670 265185372412392889174909 := by
  unfold tailWord_774670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531817012938795993490183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18836357402340245298614309 3531817012938795993490183)
  ·
    refine ⟨5297725519408193990235275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531817012938795993490183 5297725519408193990235275)
    ·
      refine ⟨7946588279112290985352913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297725519408193990235275 7946588279112290985352913)
      ·
        refine ⟨5959941209334218239014685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7946588279112290985352913 5959941209334218239014685)
        ·
          refine ⟨2234977953500331839630507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5959941209334218239014685 2234977953500331839630507)
          ·
            refine ⟨3352466930250497759445761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234977953500331839630507 3352466930250497759445761)
            ·
              refine ⟨2514350197687873319584321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352466930250497759445761 2514350197687873319584321)
              ·
                refine ⟨1885762648265904989688241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514350197687873319584321 1885762648265904989688241)
                ·
                  refine ⟨1414321986199428742266181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885762648265904989688241 1414321986199428742266181)
                  ·
                    refine ⟨265185372412392889174909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414321986199428742266181 265185372412392889174909)
                    ·
                      rfl

theorem cell22_774670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_774670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774670 prefixEnd_774670 := by exact prefixLift 774670
  have htrace : WordTrace (prefixWord ++ tailWord_774670) baseStart_774670 baseEnd_774670 := by
    simpa [prefixWord, tailWord_774670, baseEnd_774670] using wordTrace_append hprefix tailTrace_774670
  have hstable : (prefixWord ++ tailWord_774670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774670).length < 2 ^ (prefixWord ++ tailWord_774670).sum := by decide
  have hdescent : baseEnd_774670 < baseStart_774670 := by decide
  rcases family_descends (prefixWord ++ tailWord_774670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774683 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 9, 3]
def baseStart_774683 : Nat := 118140960795 + 774683 * 2 ^ 59
def prefixEnd_774683 : Nat := 4983230072969 + 3 ^ 40 * 774683 * 2
def baseEnd_774683 : Nat := 265189822578065188599869

theorem tailTrace_774683 : CollatzResearch.WordTrace tailWord_774683 prefixEnd_774683 265189822578065188599869 := by
  unfold tailWord_774683
  simp only [CollatzResearch.WordTrace]
  refine ⟨28255010252463271168144703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18836673501642180778763135 28255010252463271168144703)
  ·
    refine ⟨42382515378694906752217055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28255010252463271168144703 42382515378694906752217055)
    ·
      refine ⟨63573773068042360128325583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42382515378694906752217055 63573773068042360128325583)
      ·
        refine ⟨95360659602063540192488375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63573773068042360128325583 95360659602063540192488375)
        ·
          refine ⟨143040989403095310288732563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95360659602063540192488375 143040989403095310288732563)
          ·
            refine ⟨214561484104642965433098845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143040989403095310288732563 214561484104642965433098845)
            ·
              refine ⟨80460556539241112037412067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214561484104642965433098845 80460556539241112037412067)
              ·
                refine ⟨120690834808861668056118101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80460556539241112037412067 120690834808861668056118101)
                ·
                  refine ⟨707172860208173836266317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 120690834808861668056118101 707172860208173836266317)
                  ·
                    refine ⟨265189822578065188599869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707172860208173836266317 265189822578065188599869)
                    ·
                      rfl

theorem cell22_774683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].length) (baseStart_774683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774683 prefixEnd_774683 := by exact prefixLift 774683
  have htrace : WordTrace (prefixWord ++ tailWord_774683) baseStart_774683 baseEnd_774683 := by
    simpa [prefixWord, tailWord_774683, baseEnd_774683] using wordTrace_append hprefix tailTrace_774683
  have hstable : (prefixWord ++ tailWord_774683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774683).length < 2 ^ (prefixWord ++ tailWord_774683).sum := by decide
  have hdescent : baseEnd_774683 < baseStart_774683 := by decide
  rcases family_descends (prefixWord ++ tailWord_774683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774685 : List Nat := [1, 4, 2, 2, 1, 4, 1, 7]
def baseStart_774685 : Nat := 118140960795 + 774685 * 2 ^ 59
def prefixEnd_774685 : Nat := 4983230072969 + 3 ^ 40 * 774685 * 2
def baseEnd_774685 : Nat := 29465611913215316672207

theorem tailTrace_774685 : CollatzResearch.WordTrace tailWord_774685 prefixEnd_774685 29465611913215316672207 := by
  unfold tailWord_774685
  simp only [CollatzResearch.WordTrace]
  refine ⟨28255083198456025509717509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18836722132304017006478339 28255083198456025509717509)
  ·
    refine ⟨5297828099710504783072033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28255083198456025509717509 5297828099710504783072033)
    ·
      refine ⟨3973371074782878587304025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5297828099710504783072033 3973371074782878587304025)
      ·
        refine ⟨2980028306087158940478019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3973371074782878587304025 2980028306087158940478019)
        ·
          refine ⟨4470042459130738410717029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980028306087158940478019 4470042459130738410717029)
          ·
            refine ⟨838132961087013452009443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4470042459130738410717029 838132961087013452009443)
            ·
              refine ⟨1257199441630520178014165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838132961087013452009443 1257199441630520178014165)
              ·
                refine ⟨29465611913215316672207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1257199441630520178014165 29465611913215316672207)
                ·
                  rfl

theorem cell22_774685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 7].length) (baseStart_774685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774685 prefixEnd_774685 := by exact prefixLift 774685
  have htrace : WordTrace (prefixWord ++ tailWord_774685) baseStart_774685 baseEnd_774685 := by
    simpa [prefixWord, tailWord_774685, baseEnd_774685] using wordTrace_append hprefix tailTrace_774685
  have hstable : (prefixWord ++ tailWord_774685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774685).length < 2 ^ (prefixWord ++ tailWord_774685).sum := by decide
  have hdescent : baseEnd_774685 < baseStart_774685 := by decide
  rcases family_descends (prefixWord ++ tailWord_774685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774702 : List Nat := [4, 1, 3, 1, 3, 1, 3, 6]
def baseStart_774702 : Nat := 118140960795 + 774702 * 2 ^ 59
def prefixEnd_774702 : Nat := 4983230072969 + 3 ^ 40 * 774702 * 2
def baseEnd_774702 : Nat := 29466258518483941374979

theorem tailTrace_774702 : CollatzResearch.WordTrace tailWord_774702 prefixEnd_774702 29466258518483941374979 := by
  unfold tailWord_774702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531962904924304676635795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18837135492929624942057573 3531962904924304676635795)
  ·
    refine ⟨5297944357386457014953693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531962904924304676635795 5297944357386457014953693)
    ·
      refine ⟨1986729134019921380607635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5297944357386457014953693 1986729134019921380607635)
      ·
        refine ⟨2980093701029882070911453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986729134019921380607635 2980093701029882070911453)
        ·
          refine ⟨1117535137886205776591795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2980093701029882070911453 1117535137886205776591795)
          ·
            refine ⟨1676302706829308664887693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117535137886205776591795 1676302706829308664887693)
            ·
              refine ⟨628613515060990749332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676302706829308664887693 628613515060990749332885)
              ·
                refine ⟨29466258518483941374979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 628613515060990749332885 29466258518483941374979)
                ·
                  rfl

theorem cell22_774702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_774702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774702 prefixEnd_774702 := by exact prefixLift 774702
  have htrace : WordTrace (prefixWord ++ tailWord_774702) baseStart_774702 baseEnd_774702 := by
    simpa [prefixWord, tailWord_774702, baseEnd_774702] using wordTrace_append hprefix tailTrace_774702
  have hstable : (prefixWord ++ tailWord_774702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774702).length < 2 ^ (prefixWord ++ tailWord_774702).sum := by decide
  have hdescent : baseEnd_774702 < baseStart_774702 := by decide
  rcases family_descends (prefixWord ++ tailWord_774702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774713 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 7]
def baseStart_774713 : Nat := 118140960795 + 774713 * 2 ^ 59
def prefixEnd_774713 : Nat := 4983230072969 + 3 ^ 40 * 774713 * 2
def baseEnd_774713 : Nat := 88400030730385036783259

theorem tailTrace_774713 : CollatzResearch.WordTrace tailWord_774713 prefixEnd_774713 88400030730385036783259 := by
  unfold tailWord_774713
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256104442354586291736793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18837402961569724194491195 28256104442354586291736793)
  ·
    refine ⟨21192078331765939718802595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28256104442354586291736793 21192078331765939718802595)
    ·
      refine ⟨31788117497648909578203893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21192078331765939718802595 31788117497648909578203893)
      ·
        refine ⟨2980136015404585272956615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31788117497648909578203893 2980136015404585272956615)
        ·
          refine ⟨4470204023106877909434923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980136015404585272956615 4470204023106877909434923)
          ·
            refine ⟨6705306034660316864152385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470204023106877909434923 6705306034660316864152385)
            ·
              refine ⟨5028979525995237648114289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705306034660316864152385 5028979525995237648114289)
              ·
                refine ⟨3771734644496428236085717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028979525995237648114289 3771734644496428236085717)
                ·
                  refine ⟨88400030730385036783259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3771734644496428236085717 88400030730385036783259)
                  ·
                    rfl

theorem cell22_774713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_774713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774713 prefixEnd_774713 := by exact prefixLift 774713
  have htrace : WordTrace (prefixWord ++ tailWord_774713) baseStart_774713 baseEnd_774713 := by
    simpa [prefixWord, tailWord_774713, baseEnd_774713] using wordTrace_append hprefix tailTrace_774713
  have hstable : (prefixWord ++ tailWord_774713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774713).length < 2 ^ (prefixWord ++ tailWord_774713).sum := by decide
  have hdescent : baseEnd_774713 < baseStart_774713 := by decide
  rcases family_descends (prefixWord ++ tailWord_774713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774730 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_774730 : Nat := 118140960795 + 774730 * 2 ^ 59
def prefixEnd_774730 : Nat := 4983230072969 + 3 ^ 40 * 774730 * 2
def baseEnd_774730 : Nat := 88401970546190910891575

theorem tailTrace_774730 : CollatzResearch.WordTrace tailWord_774730 prefixEnd_774730 88401970546190910891575 := by
  unfold tailWord_774730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064181120823249548776411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18837816322195332130070429 7064181120823249548776411)
  ·
    refine ⟨10596271681234874323164617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064181120823249548776411 10596271681234874323164617)
    ·
      refine ⟨7947203760926155742373463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10596271681234874323164617 7947203760926155742373463)
      ·
        refine ⟨11920805641389233613560195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947203760926155742373463 11920805641389233613560195)
        ·
          refine ⟨17881208462083850420340293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11920805641389233613560195 17881208462083850420340293)
          ·
            refine ⟨3352726586640721953813805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17881208462083850420340293 3352726586640721953813805)
            ·
              refine ⟨1257272469990270732680177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3352726586640721953813805 1257272469990270732680177)
              ·
                refine ⟨942954352492703049510133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257272469990270732680177 942954352492703049510133)
                ·
                  refine ⟨88401970546190910891575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 942954352492703049510133 88401970546190910891575)
                  ·
                    rfl

theorem cell22_774730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_774730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774730 prefixEnd_774730 := by exact prefixLift 774730
  have htrace : WordTrace (prefixWord ++ tailWord_774730) baseStart_774730 baseEnd_774730 := by
    simpa [prefixWord, tailWord_774730, baseEnd_774730] using wordTrace_append hprefix tailTrace_774730
  have hstable : (prefixWord ++ tailWord_774730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774730).length < 2 ^ (prefixWord ++ tailWord_774730).sum := by decide
  have hdescent : baseEnd_774730 < baseStart_774730 := by decide
  rcases family_descends (prefixWord ++ tailWord_774730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774807 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 2, 3]
def baseStart_774807 : Nat := 118140960795 + 774807 * 2 ^ 59
def prefixEnd_774807 : Nat := 4983230072969 + 3 ^ 40 * 774807 * 2
def baseEnd_774807 : Nat := 265232270312170198499489

theorem tailTrace_774807 : CollatzResearch.WordTrace tailWord_774807 prefixEnd_774807 265232270312170198499489 := by
  unfold tailWord_774807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28259532904014040345658675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18839688602676026897105783 28259532904014040345658675)
  ·
    refine ⟨42389299356021060518488013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28259532904014040345658675 42389299356021060518488013)
    ·
      refine ⟨15895987258507897694433005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42389299356021060518488013 15895987258507897694433005)
      ·
        refine ⟨5960995221940461635412377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15895987258507897694433005 5960995221940461635412377)
        ·
          refine ⟨4470746416455346226559283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960995221940461635412377 4470746416455346226559283)
          ·
            refine ⟨6706119624683019339838925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470746416455346226559283 6706119624683019339838925)
            ·
              refine ⟨2514794859256132252439597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6706119624683019339838925 2514794859256132252439597)
              ·
                refine ⟨943048072221049594664849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2514794859256132252439597 943048072221049594664849)
                ·
                  refine ⟨707286054165787195998637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943048072221049594664849 707286054165787195998637)
                  ·
                    refine ⟨265232270312170198499489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707286054165787195998637 265232270312170198499489)
                    ·
                      rfl

theorem cell22_774807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_774807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774807 prefixEnd_774807 := by exact prefixLift 774807
  have htrace : WordTrace (prefixWord ++ tailWord_774807) baseStart_774807 baseEnd_774807 := by
    simpa [prefixWord, tailWord_774807, baseEnd_774807] using wordTrace_append hprefix tailTrace_774807
  have hstable : (prefixWord ++ tailWord_774807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774807).length < 2 ^ (prefixWord ++ tailWord_774807).sum := by decide
  have hdescent : baseEnd_774807 < baseStart_774807 := by decide
  rcases family_descends (prefixWord ++ tailWord_774807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774865 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 5]
def baseStart_774865 : Nat := 118140960795 + 774865 * 2 ^ 59
def prefixEnd_774865 : Nat := 4983230072969 + 3 ^ 40 * 774865 * 2
def baseEnd_774865 : Nat := 88417374965825793516437

theorem tailTrace_774865 : CollatzResearch.WordTrace tailWord_774865 prefixEnd_774865 88417374965825793516437 := by
  unfold tailWord_774865
  simp only [CollatzResearch.WordTrace]
  refine ⟨28261648337803916251270049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18841098891869277500846699 28261648337803916251270049)
  ·
    refine ⟨21196236253352937188452537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28261648337803916251270049 21196236253352937188452537)
    ·
      refine ⟨15897177190014702891339403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21196236253352937188452537 15897177190014702891339403)
      ·
        refine ⟨23845765785022054337009105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15897177190014702891339403 23845765785022054337009105)
        ·
          refine ⟨17884324338766540752756829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23845765785022054337009105 17884324338766540752756829)
          ·
            refine ⟨6706621627037452782283811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17884324338766540752756829 6706621627037452782283811)
            ·
              refine ⟨10059932440556179173425717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706621627037452782283811 10059932440556179173425717)
              ·
                refine ⟨943118666302141797508661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10059932440556179173425717 943118666302141797508661)
                ·
                  refine ⟨88417374965825793516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943118666302141797508661 88417374965825793516437)
                  ·
                    rfl

theorem cell22_774865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_774865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774865 prefixEnd_774865 := by exact prefixLift 774865
  have htrace : WordTrace (prefixWord ++ tailWord_774865) baseStart_774865 baseEnd_774865 := by
    simpa [prefixWord, tailWord_774865, baseEnd_774865] using wordTrace_append hprefix tailTrace_774865
  have hstable : (prefixWord ++ tailWord_774865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774865).length < 2 ^ (prefixWord ++ tailWord_774865).sum := by decide
  have hdescent : baseEnd_774865 < baseStart_774865 := by decide
  rcases family_descends (prefixWord ++ tailWord_774865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774944 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_774944 : Nat := 118140960795 + 774944 * 2 ^ 59
def prefixEnd_774944 : Nat := 4983230072969 + 3 ^ 40 * 774944 * 2
def baseEnd_774944 : Nat := 88426389403982502608023

theorem tailTrace_774944 : CollatzResearch.WordTrace tailWord_774944 prefixEnd_774944 88426389403982502608023 := by
  unfold tailWord_774944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132264852258856371697943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18843019803011808495597257 14132264852258856371697943)
  ·
    refine ⟨21198397278388284557546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14132264852258856371697943 21198397278388284557546915)
    ·
      refine ⟨31797595917582426836320373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21198397278388284557546915 31797595917582426836320373)
      ·
        refine ⟨2981024617273352515905035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31797595917582426836320373 2981024617273352515905035)
        ·
          refine ⟨4471536925910028773857553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981024617273352515905035 4471536925910028773857553)
          ·
            refine ⟨3353652694432521580393165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471536925910028773857553 3353652694432521580393165)
            ·
              refine ⟨1257619760412195592647437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353652694432521580393165 1257619760412195592647437)
              ·
                refine ⟨471607410154573347242789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257619760412195592647437 471607410154573347242789)
                ·
                  refine ⟨88426389403982502608023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471607410154573347242789 88426389403982502608023)
                  ·
                    rfl

theorem cell22_774944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_774944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774944 prefixEnd_774944 := by exact prefixLift 774944
  have htrace : WordTrace (prefixWord ++ tailWord_774944) baseStart_774944 baseEnd_774944 := by
    simpa [prefixWord, tailWord_774944, baseEnd_774944] using wordTrace_append hprefix tailTrace_774944
  have hstable : (prefixWord ++ tailWord_774944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774944).length < 2 ^ (prefixWord ++ tailWord_774944).sum := by decide
  have hdescent : baseEnd_774944 < baseStart_774944 := by decide
  rcases family_descends (prefixWord ++ tailWord_774944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774980 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_774980 : Nat := 118140960795 + 774980 * 2 ^ 59
def prefixEnd_774980 : Nat := 4983230072969 + 3 ^ 40 * 774980 * 2
def baseEnd_774980 : Nat := 265291491747655413923959

theorem tailTrace_774980 : CollatzResearch.WordTrace tailWord_774980 prefixEnd_774980 265291491747655413923959 := by
  unfold tailWord_774980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132921366193645445853197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18843895154924860594470929 14132921366193645445853197)
  ·
    refine ⟨5299845512322617042194949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14132921366193645445853197 5299845512322617042194949)
    ·
      refine ⟨993721033560490695411553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5299845512322617042194949 993721033560490695411553)
      ·
        refine ⟨745290775170368021558665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993721033560490695411553 745290775170368021558665)
        ·
          refine ⟨558968081377776016168999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745290775170368021558665 558968081377776016168999)
          ·
            refine ⟨838452122066664024253499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558968081377776016168999 838452122066664024253499)
            ·
              refine ⟨1257678183099996036380249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838452122066664024253499 1257678183099996036380249)
              ·
                refine ⟨943258637324997027285187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257678183099996036380249 943258637324997027285187)
                ·
                  refine ⟨1414887955987495540927781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943258637324997027285187 1414887955987495540927781)
                  ·
                    refine ⟨265291491747655413923959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414887955987495540927781 265291491747655413923959)
                    ·
                      rfl

theorem cell22_774980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_774980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_774980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_774980 prefixEnd_774980 := by exact prefixLift 774980
  have htrace : WordTrace (prefixWord ++ tailWord_774980) baseStart_774980 baseEnd_774980 := by
    simpa [prefixWord, tailWord_774980, baseEnd_774980] using wordTrace_append hprefix tailTrace_774980
  have hstable : (prefixWord ++ tailWord_774980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774980).length < 2 ^ (prefixWord ++ tailWord_774980).sum := by decide
  have hdescent : baseEnd_774980 < baseStart_774980 := by decide
  rcases family_descends (prefixWord ++ tailWord_774980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775000 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_775000 : Nat := 118140960795 + 775000 * 2 ^ 59
def prefixEnd_775000 : Nat := 4983230072969 + 3 ^ 40 * 775000 * 2
def baseEnd_775000 : Nat := 88432779385460676141299

theorem tailTrace_775000 : CollatzResearch.WordTrace tailWord_775000 prefixEnd_775000 88432779385460676141299 := by
  unfold tailWord_775000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14133286096157417153717227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18844381461543222871622969 14133286096157417153717227)
  ·
    refine ⟨21199929144236125730575841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14133286096157417153717227 21199929144236125730575841)
    ·
      refine ⟨15899946858177094297931881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21199929144236125730575841 15899946858177094297931881)
      ·
        refine ⟨11924960143632820723448911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15899946858177094297931881 11924960143632820723448911)
        ·
          refine ⟨17887440215449231085173367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11924960143632820723448911 17887440215449231085173367)
          ·
            refine ⟨26831160323173846627760051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887440215449231085173367 26831160323173846627760051)
            ·
              refine ⟨40246740484760769941640077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831160323173846627760051 40246740484760769941640077)
              ·
                refine ⟨15092527681785288728115029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40246740484760769941640077 15092527681785288728115029)
                ·
                  refine ⟨88432779385460676141299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15092527681785288728115029 88432779385460676141299)
                  ·
                    rfl

theorem cell22_775000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_775000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775000 prefixEnd_775000 := by exact prefixLift 775000
  have htrace : WordTrace (prefixWord ++ tailWord_775000) baseStart_775000 baseEnd_775000 := by
    simpa [prefixWord, tailWord_775000, baseEnd_775000] using wordTrace_append hprefix tailTrace_775000
  have hstable : (prefixWord ++ tailWord_775000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775000).length < 2 ^ (prefixWord ++ tailWord_775000).sum := by decide
  have hdescent : baseEnd_775000 < baseStart_775000 := by decide
  rcases family_descends (prefixWord ++ tailWord_775000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775038 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_775038 : Nat := 118140960795 + 775038 * 2 ^ 59
def prefixEnd_775038 : Nat := 4983230072969 + 3 ^ 40 * 775038 * 2
def baseEnd_775038 : Nat := 265311346332962595973781

theorem tailTrace_775038 : CollatzResearch.WordTrace tailWord_775038 prefixEnd_775038 265311346332962595973781 := by
  unfold tailWord_775038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533494770772145849664721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18845305444118111198211845 3533494770772145849664721)
  ·
    refine ⟨2650121078079109387248541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3533494770772145849664721 2650121078079109387248541)
    ·
      refine ⟨993795404279666020218203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2650121078079109387248541 993795404279666020218203)
      ·
        refine ⟨1490693106419499030327305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993795404279666020218203 1490693106419499030327305)
        ·
          refine ⟨1118019829814624272745479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490693106419499030327305 1118019829814624272745479)
          ·
            refine ⟨1677029744721936409118219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118019829814624272745479 1677029744721936409118219)
            ·
              refine ⟨2515544617082904613677329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677029744721936409118219 2515544617082904613677329)
              ·
                refine ⟨1886658462812178460257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515544617082904613677329 1886658462812178460257997)
                ·
                  refine ⟨707496923554566922596749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1886658462812178460257997 707496923554566922596749)
                  ·
                    refine ⟨265311346332962595973781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707496923554566922596749 265311346332962595973781)
                    ·
                      rfl

theorem cell22_775038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_775038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775038 prefixEnd_775038 := by exact prefixLift 775038
  have htrace : WordTrace (prefixWord ++ tailWord_775038) baseStart_775038 baseEnd_775038 := by
    simpa [prefixWord, tailWord_775038, baseEnd_775038] using wordTrace_append hprefix tailTrace_775038
  have hstable : (prefixWord ++ tailWord_775038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775038).length < 2 ^ (prefixWord ++ tailWord_775038).sum := by decide
  have hdescent : baseEnd_775038 < baseStart_775038 := by decide
  rcases family_descends (prefixWord ++ tailWord_775038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775068 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_775068 : Nat := 118140960795 + 775068 * 2 ^ 59
def prefixEnd_775068 : Nat := 4983230072969 + 3 ^ 40 * 775068 * 2
def baseEnd_775068 : Nat := 88440538648684172574563

theorem tailTrace_775068 : CollatzResearch.WordTrace tailWord_775068 prefixEnd_775068 88440538648684172574563 := by
  unfold tailWord_775068
  simp only [CollatzResearch.WordTrace]
  refine ⟨14134526178034240960454929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18846034904045654613939905 14134526178034240960454929)
  ·
    refine ⟨10600894633525680720341197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14134526178034240960454929 10600894633525680720341197)
    ·
      refine ⟨3975335487572130270127949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10600894633525680720341197 3975335487572130270127949)
      ·
        refine ⟨1490750807839548851297981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3975335487572130270127949 1490750807839548851297981)
        ·
          refine ⟨559031552939830819236743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1490750807839548851297981 559031552939830819236743)
          ·
            refine ⟨838547329409746228855115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559031552939830819236743 838547329409746228855115)
            ·
              refine ⟨1257820994114619343282673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838547329409746228855115 1257820994114619343282673)
              ·
                refine ⟨943365745585964507462005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257820994114619343282673 943365745585964507462005)
                ·
                  refine ⟨88440538648684172574563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943365745585964507462005 88440538648684172574563)
                  ·
                    rfl

theorem cell22_775068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_775068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775068 prefixEnd_775068 := by exact prefixLift 775068
  have htrace : WordTrace (prefixWord ++ tailWord_775068) baseStart_775068 baseEnd_775068 := by
    simpa [prefixWord, tailWord_775068, baseEnd_775068] using wordTrace_append hprefix tailTrace_775068
  have hstable : (prefixWord ++ tailWord_775068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775068).length < 2 ^ (prefixWord ++ tailWord_775068).sum := by decide
  have hdescent : baseEnd_775068 < baseStart_775068 := by decide
  rcases family_descends (prefixWord ++ tailWord_775068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775124 : List Nat := [2, 4, 1, 2, 1, 4, 8]
def baseStart_775124 : Nat := 118140960795 + 775124 * 2 ^ 59
def prefixEnd_775124 : Nat := 4983230072969 + 3 ^ 40 * 775124 * 2
def baseEnd_775124 : Nat := 9827436514462482900871

theorem tailTrace_775124 : CollatzResearch.WordTrace tailWord_775124 prefixEnd_775124 9827436514462482900871 := by
  unfold tailWord_775124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135547421932801742474213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18847396562577068989965617 14135547421932801742474213)
  ·
    refine ⟨2650415141612400326713915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14135547421932801742474213 2650415141612400326713915)
    ·
      refine ⟨3975622712418600490070873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650415141612400326713915 3975622712418600490070873)
      ·
        refine ⟨2981717034313950367553155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975622712418600490070873 2981717034313950367553155)
        ·
          refine ⟨4472575551470925551329733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981717034313950367553155 4472575551470925551329733)
          ·
            refine ⟨838607915900798540874325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4472575551470925551329733 838607915900798540874325)
            ·
              refine ⟨9827436514462482900871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 838607915900798540874325 9827436514462482900871)
              ·
                rfl

theorem cell22_775124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 8].length) (baseStart_775124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775124 prefixEnd_775124 := by exact prefixLift 775124
  have htrace : WordTrace (prefixWord ++ tailWord_775124) baseStart_775124 baseEnd_775124 := by
    simpa [prefixWord, tailWord_775124, baseEnd_775124] using wordTrace_append hprefix tailTrace_775124
  have hstable : (prefixWord ++ tailWord_775124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775124).length < 2 ^ (prefixWord ++ tailWord_775124).sum := by decide
  have hdescent : baseEnd_775124 < baseStart_775124 := by decide
  rcases family_descends (prefixWord ++ tailWord_775124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775126 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_775126 : Nat := 118140960795 + 775126 * 2 ^ 59
def prefixEnd_775126 : Nat := 4983230072969 + 3 ^ 40 * 775126 * 2
def baseEnd_775126 : Nat := 265341470531359699773511

theorem tailTrace_775126 : CollatzResearch.WordTrace tailWord_775126 prefixEnd_775126 265341470531359699773511 := by
  unfold tailWord_775126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766947986866147364157577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18847445193238905217680821 1766947986866147364157577)
  ·
    refine ⟨1325210990149610523118183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1766947986866147364157577 1325210990149610523118183)
    ·
      refine ⟨1987816485224415784677275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325210990149610523118183 1987816485224415784677275)
      ·
        refine ⟨2981724727836623677015913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987816485224415784677275 2981724727836623677015913)
        ·
          refine ⟨2236293545877467757761935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981724727836623677015913 2236293545877467757761935)
          ·
            refine ⟨3354440318816201636642903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236293545877467757761935 3354440318816201636642903)
            ·
              refine ⟨5031660478224302454964355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354440318816201636642903 5031660478224302454964355)
              ·
                refine ⟨7547490717336453682446533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031660478224302454964355 7547490717336453682446533)
                ·
                  refine ⟨1415154509500585065458725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7547490717336453682446533 1415154509500585065458725)
                  ·
                    refine ⟨265341470531359699773511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415154509500585065458725 265341470531359699773511)
                    ·
                      rfl

theorem cell22_775126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_775126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775126 prefixEnd_775126 := by exact prefixLift 775126
  have htrace : WordTrace (prefixWord ++ tailWord_775126) baseStart_775126 baseEnd_775126 := by
    simpa [prefixWord, tailWord_775126, baseEnd_775126] using wordTrace_append hprefix tailTrace_775126
  have hstable : (prefixWord ++ tailWord_775126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775126).length < 2 ^ (prefixWord ++ tailWord_775126).sum := by decide
  have hdescent : baseEnd_775126 < baseStart_775126 := by decide
  rcases family_descends (prefixWord ++ tailWord_775126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775137 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_775137 : Nat := 118140960795 + 775137 * 2 ^ 59
def prefixEnd_775137 : Nat := 4983230072969 + 3 ^ 40 * 775137 * 2
def baseEnd_775137 : Nat := 265345236056159337748477

theorem tailTrace_775137 : CollatzResearch.WordTrace tailWord_775137 prefixEnd_775137 265345236056159337748477 := by
  unfold tailWord_775137
  simp only [CollatzResearch.WordTrace]
  refine ⟨28271568992818506705171665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18847712661879004470114443 28271568992818506705171665)
  ·
    refine ⟨21203676744613880028878749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28271568992818506705171665 21203676744613880028878749)
    ·
      refine ⟨7951378779230205010829531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21203676744613880028878749 7951378779230205010829531)
      ·
        refine ⟨11927068168845307516244297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951378779230205010829531 11927068168845307516244297)
        ·
          refine ⟨8945301126633980637183223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11927068168845307516244297 8945301126633980637183223)
          ·
            refine ⟨13417951689950970955774835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945301126633980637183223 13417951689950970955774835)
            ·
              refine ⟨20126927534926456433662253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417951689950970955774835 20126927534926456433662253)
              ·
                refine ⟨7547597825597421162623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20126927534926456433662253 7547597825597421162623345)
                ·
                  refine ⟨5660698369198065871967509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7547597825597421162623345 5660698369198065871967509)
                  ·
                    refine ⟨265345236056159337748477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5660698369198065871967509 265345236056159337748477)
                    ·
                      rfl

theorem cell22_775137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_775137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775137 prefixEnd_775137 := by exact prefixLift 775137
  have htrace : WordTrace (prefixWord ++ tailWord_775137) baseStart_775137 baseEnd_775137 := by
    simpa [prefixWord, tailWord_775137, baseEnd_775137] using wordTrace_append hprefix tailTrace_775137
  have hstable : (prefixWord ++ tailWord_775137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775137).length < 2 ^ (prefixWord ++ tailWord_775137).sum := by decide
  have hdescent : baseEnd_775137 < baseStart_775137 := by decide
  rcases family_descends (prefixWord ++ tailWord_775137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775141 : List Nat := [1, 3, 1, 6, 1, 1, 2, 7]
def baseStart_775141 : Nat := 118140960795 + 775141 * 2 ^ 59
def prefixEnd_775141 : Nat := 4983230072969 + 3 ^ 40 * 775141 * 2
def baseEnd_775141 : Nat := 29482956148656073405385

theorem tailTrace_775141 : CollatzResearch.WordTrace tailWord_775141 prefixEnd_775141 29482956148656073405385 := by
  unfold tailWord_775141
  simp only [CollatzResearch.WordTrace]
  refine ⟨28271714884804015388317277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18847809923202676925544851 28271714884804015388317277)
  ·
    refine ⟨10601893081801505770618979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28271714884804015388317277 10601893081801505770618979)
    ·
      refine ⟨15902839622702258655928469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10601893081801505770618979 15902839622702258655928469)
      ·
        refine ⟨745445607314168374496647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15902839622702258655928469 745445607314168374496647)
        ·
          refine ⟨1118168410971252561744971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745445607314168374496647 1118168410971252561744971)
          ·
            refine ⟨1677252616456878842617457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118168410971252561744971 1677252616456878842617457)
            ·
              refine ⟨1257939462342659131963093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677252616456878842617457 1257939462342659131963093)
              ·
                refine ⟨29482956148656073405385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1257939462342659131963093 29482956148656073405385)
                ·
                  rfl

theorem cell22_775141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 7].length) (baseStart_775141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775141 prefixEnd_775141 := by exact prefixLift 775141
  have htrace : WordTrace (prefixWord ++ tailWord_775141) baseStart_775141 baseEnd_775141 := by
    simpa [prefixWord, tailWord_775141, baseEnd_775141] using wordTrace_append hprefix tailTrace_775141
  have hstable : (prefixWord ++ tailWord_775141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775141).length < 2 ^ (prefixWord ++ tailWord_775141).sum := by decide
  have hdescent : baseEnd_775141 < baseStart_775141 := by decide
  rcases family_descends (prefixWord ++ tailWord_775141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775167 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_775167 : Nat := 118140960795 + 775167 * 2 ^ 59
def prefixEnd_775167 : Nat := 4983230072969 + 3 ^ 40 * 775167 * 2
def baseEnd_775167 : Nat := 265355505669249259498385

theorem tailTrace_775167 : CollatzResearch.WordTrace tailWord_775167 prefixEnd_775167 265355505669249259498385 := by
  unfold tailWord_775167
  simp only [CollatzResearch.WordTrace]
  refine ⟨28272663182709821828763755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18848442121806547885842503 28272663182709821828763755)
  ·
    refine ⟨42408994774064732743145633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28272663182709821828763755 42408994774064732743145633)
    ·
      refine ⟨31806746080548549557359225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42408994774064732743145633 31806746080548549557359225)
      ·
        refine ⟨23855059560411412168019419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31806746080548549557359225 23855059560411412168019419)
        ·
          refine ⟨35782589340617118252029129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23855059560411412168019419 35782589340617118252029129)
          ·
            refine ⟨26836942005462838689021847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35782589340617118252029129 26836942005462838689021847)
            ·
              refine ⟨40255413008194258033532771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26836942005462838689021847 40255413008194258033532771)
              ·
                refine ⟨60383119512291387050299157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40255413008194258033532771 60383119512291387050299157)
                ·
                  refine ⟨2830458727138658767982773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60383119512291387050299157 2830458727138658767982773)
                  ·
                    refine ⟨265355505669249259498385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2830458727138658767982773 265355505669249259498385)
                    ·
                      rfl

theorem cell22_775167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_775167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775167 prefixEnd_775167 := by exact prefixLift 775167
  have htrace : WordTrace (prefixWord ++ tailWord_775167) baseStart_775167 baseEnd_775167 := by
    simpa [prefixWord, tailWord_775167, baseEnd_775167] using wordTrace_append hprefix tailTrace_775167
  have hstable : (prefixWord ++ tailWord_775167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775167).length < 2 ^ (prefixWord ++ tailWord_775167).sum := by decide
  have hdescent : baseEnd_775167 < baseStart_775167 := by decide
  rcases family_descends (prefixWord ++ tailWord_775167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775199 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_775199 : Nat := 118140960795 + 775199 * 2 ^ 59
def prefixEnd_775199 : Nat := 4983230072969 + 3 ^ 40 * 775199 * 2
def baseEnd_775199 : Nat := 265366459923211842698287

theorem tailTrace_775199 : CollatzResearch.WordTrace tailWord_775199 prefixEnd_775199 265366459923211842698287 := by
  unfold tailWord_775199
  simp only [CollatzResearch.WordTrace]
  refine ⟨28273830318593891293928651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18849220212395927529285767 28273830318593891293928651)
  ·
    refine ⟨42410745477890836940892977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28273830318593891293928651 42410745477890836940892977)
    ·
      refine ⟨31808059108418127705669733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42410745477890836940892977 31808059108418127705669733)
      ·
        refine ⟨5964011082828398944813075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31808059108418127705669733 5964011082828398944813075)
        ·
          refine ⟨8946016624242598417219613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964011082828398944813075 8946016624242598417219613)
          ·
            refine ⟨3354756234090974406457355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8946016624242598417219613 3354756234090974406457355)
            ·
              refine ⟨5032134351136461609686033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354756234090974406457355 5032134351136461609686033)
              ·
                refine ⟨3774100763352346207264525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032134351136461609686033 3774100763352346207264525)
                ·
                  refine ⟨1415287786257129827724197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3774100763352346207264525 1415287786257129827724197)
                  ·
                    refine ⟨265366459923211842698287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415287786257129827724197 265366459923211842698287)
                    ·
                      rfl

theorem cell22_775199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_775199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775199 prefixEnd_775199 := by exact prefixLift 775199
  have htrace : WordTrace (prefixWord ++ tailWord_775199) baseStart_775199 baseEnd_775199 := by
    simpa [prefixWord, tailWord_775199, baseEnd_775199] using wordTrace_append hprefix tailTrace_775199
  have hstable : (prefixWord ++ tailWord_775199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775199).length < 2 ^ (prefixWord ++ tailWord_775199).sum := by decide
  have hdescent : baseEnd_775199 < baseStart_775199 := by decide
  rcases family_descends (prefixWord ++ tailWord_775199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775233 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_775233 : Nat := 118140960795 + 775233 * 2 ^ 59
def prefixEnd_775233 : Nat := 4983230072969 + 3 ^ 40 * 775233 * 2
def baseEnd_775233 : Nat := 265378098818047087348183

theorem tailTrace_775233 : CollatzResearch.WordTrace tailWord_775233 prefixEnd_775233 265378098818047087348183 := by
  unfold tailWord_775233
  simp only [CollatzResearch.WordTrace]
  refine ⟨28275070400470715100666353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18850046933647143400444235 28275070400470715100666353)
  ·
    refine ⟨21206302800353036325499765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28275070400470715100666353 21206302800353036325499765)
    ·
      refine ⟨1988090887533097155515603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21206302800353036325499765 1988090887533097155515603)
      ·
        refine ⟨2982136331299645733273405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988090887533097155515603 2982136331299645733273405)
        ·
          refine ⟨1118301124237367149977527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2982136331299645733273405 1118301124237367149977527)
          ·
            refine ⟨1677451686356050724966291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118301124237367149977527 1677451686356050724966291)
            ·
              refine ⟨2516177529534076087449437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677451686356050724966291 2516177529534076087449437)
              ·
                refine ⟨943566573575278532793539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2516177529534076087449437 943566573575278532793539)
                ·
                  refine ⟨1415349860362917799190309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943566573575278532793539 1415349860362917799190309)
                  ·
                    refine ⟨265378098818047087348183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415349860362917799190309 265378098818047087348183)
                    ·
                      rfl

theorem cell22_775233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_775233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775233 prefixEnd_775233 := by exact prefixLift 775233
  have htrace : WordTrace (prefixWord ++ tailWord_775233) baseStart_775233 baseEnd_775233 := by
    simpa [prefixWord, tailWord_775233, baseEnd_775233] using wordTrace_append hprefix tailTrace_775233
  have hstable : (prefixWord ++ tailWord_775233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775233).length < 2 ^ (prefixWord ++ tailWord_775233).sum := by decide
  have hdescent : baseEnd_775233 < baseStart_775233 := by decide
  rcases family_descends (prefixWord ++ tailWord_775233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775244 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_775244 : Nat := 118140960795 + 775244 * 2 ^ 59
def prefixEnd_775244 : Nat := 4983230072969 + 3 ^ 40 * 775244 * 2
def baseEnd_775244 : Nat := 265381864342846725323149

theorem tailTrace_775244 : CollatzResearch.WordTrace tailWord_775244 prefixEnd_775244 265381864342846725323149 := by
  unfold tailWord_775244
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137735801715431989658393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18850314402287242652877857 14137735801715431989658393)
  ·
    refine ⟨10603301851286573992243795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14137735801715431989658393 10603301851286573992243795)
    ·
      refine ⟨15904952776929860988365693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603301851286573992243795 15904952776929860988365693)
      ·
        refine ⟨5964357291348697870637135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15904952776929860988365693 5964357291348697870637135)
        ·
          refine ⟨8946535937023046805955703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964357291348697870637135 8946535937023046805955703)
          ·
            refine ⟨13419803905534570208933555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946535937023046805955703 13419803905534570208933555)
            ·
              refine ⟨20129705858301855313400333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13419803905534570208933555 20129705858301855313400333)
              ·
                refine ⟨7548639696863195742525125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20129705858301855313400333 7548639696863195742525125)
                ·
                  refine ⟨1415369943161849201723461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7548639696863195742525125 1415369943161849201723461)
                  ·
                    refine ⟨265381864342846725323149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415369943161849201723461 265381864342846725323149)
                    ·
                      rfl

theorem cell22_775244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_775244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775244 prefixEnd_775244 := by exact prefixLift 775244
  have htrace : WordTrace (prefixWord ++ tailWord_775244) baseStart_775244 baseEnd_775244 := by
    simpa [prefixWord, tailWord_775244, baseEnd_775244] using wordTrace_append hprefix tailTrace_775244
  have hstable : (prefixWord ++ tailWord_775244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775244).length < 2 ^ (prefixWord ++ tailWord_775244).sum := by decide
  have hdescent : baseEnd_775244 < baseStart_775244 := by decide
  rcases family_descends (prefixWord ++ tailWord_775244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775246 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_775246 : Nat := 118140960795 + 775246 * 2 ^ 59
def prefixEnd_775246 : Nat := 4983230072969 + 3 ^ 40 * 775246 * 2
def baseEnd_775246 : Nat := 265382548983719386773143

theorem tailTrace_775246 : CollatzResearch.WordTrace tailWord_775246 prefixEnd_775246 265382548983719386773143 := by
  unfold tailWord_775246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534443068677952290111199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18850363032949078880593061 3534443068677952290111199)
  ·
    refine ⟨5301664603016928435166799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3534443068677952290111199 5301664603016928435166799)
    ·
      refine ⟨7952496904525392652750199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301664603016928435166799 7952496904525392652750199)
      ·
        refine ⟨11928745356788088979125299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7952496904525392652750199 11928745356788088979125299)
        ·
          refine ⟨17893118035182133468687949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11928745356788088979125299 17893118035182133468687949)
          ·
            refine ⟨6709919263193300050757981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17893118035182133468687949 6709919263193300050757981)
            ·
              refine ⟨2516219723697487519034243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709919263193300050757981 2516219723697487519034243)
              ·
                refine ⟨3774329585546231278551365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516219723697487519034243 3774329585546231278551365)
                ·
                  refine ⟨707686797289918364728381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3774329585546231278551365 707686797289918364728381)
                  ·
                    refine ⟨265382548983719386773143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707686797289918364728381 265382548983719386773143)
                    ·
                      rfl

theorem cell22_775246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_775246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775246 prefixEnd_775246 := by exact prefixLift 775246
  have htrace : WordTrace (prefixWord ++ tailWord_775246) baseStart_775246 baseEnd_775246 := by
    simpa [prefixWord, tailWord_775246, baseEnd_775246] using wordTrace_append hprefix tailTrace_775246
  have hstable : (prefixWord ++ tailWord_775246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775246).length < 2 ^ (prefixWord ++ tailWord_775246).sum := by decide
  have hdescent : baseEnd_775246 < baseStart_775246 := by decide
  rcases family_descends (prefixWord ++ tailWord_775246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775263 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 2, 3]
def baseStart_775263 : Nat := 118140960795 + 775263 * 2 ^ 59
def prefixEnd_775263 : Nat := 4983230072969 + 3 ^ 40 * 775263 * 2
def baseEnd_775263 : Nat := 265388368431137009098091

theorem tailTrace_775263 : CollatzResearch.WordTrace tailWord_775263 prefixEnd_775263 265388368431137009098091 := by
  unfold tailWord_775263
  simp only [CollatzResearch.WordTrace]
  refine ⟨28276164590362030224258443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18850776393574686816172295 28276164590362030224258443)
  ·
    refine ⟨42414246885543045336387665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28276164590362030224258443 42414246885543045336387665)
    ·
      refine ⟨31810685164157284002290749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42414246885543045336387665 31810685164157284002290749)
      ·
        refine ⟨11929006936558981500859031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31810685164157284002290749 11929006936558981500859031)
        ·
          refine ⟨17893510404838472251288547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929006936558981500859031 17893510404838472251288547)
          ·
            refine ⟨26840265607257708376932821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893510404838472251288547 26840265607257708376932821)
            ·
              refine ⟨629068725170102540084363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26840265607257708376932821 629068725170102540084363)
              ·
                refine ⟨943603087755153810126545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629068725170102540084363 943603087755153810126545)
                ·
                  refine ⟨707702315816365357594909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943603087755153810126545 707702315816365357594909)
                  ·
                    refine ⟨265388368431137009098091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707702315816365357594909 265388368431137009098091)
                    ·
                      rfl

theorem cell22_775263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_775263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775263 prefixEnd_775263 := by exact prefixLift 775263
  have htrace : WordTrace (prefixWord ++ tailWord_775263) baseStart_775263 baseEnd_775263 := by
    simpa [prefixWord, tailWord_775263, baseEnd_775263] using wordTrace_append hprefix tailTrace_775263
  have hstable : (prefixWord ++ tailWord_775263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775263).length < 2 ^ (prefixWord ++ tailWord_775263).sum := by decide
  have hdescent : baseEnd_775263 < baseStart_775263 := by decide
  rcases family_descends (prefixWord ++ tailWord_775263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775308 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_775308 : Nat := 118140960795 + 775308 * 2 ^ 59
def prefixEnd_775308 : Nat := 4983230072969 + 3 ^ 40 * 775308 * 2
def baseEnd_775308 : Nat := 265403772850771891722953

theorem tailTrace_775308 : CollatzResearch.WordTrace tailWord_775308 prefixEnd_775308 265403772850771891722953 := by
  unfold tailWord_775308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138902937599501454823289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18851870583466001939764385 14138902937599501454823289)
  ·
    refine ⟨10604177203199626091117467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14138902937599501454823289 10604177203199626091117467)
    ·
      refine ⟨15906265804799439136676201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10604177203199626091117467 15906265804799439136676201)
      ·
        refine ⟨11929699353599579352507151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15906265804799439136676201 11929699353599579352507151)
        ·
          refine ⟨17894549030399369028760727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929699353599579352507151 17894549030399369028760727)
          ·
            refine ⟨26841823545599053543141091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17894549030399369028760727 26841823545599053543141091)
            ·
              refine ⟨40262735318398580314711637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26841823545599053543141091 40262735318398580314711637)
              ·
                refine ⟨471828929512483363063027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40262735318398580314711637 471828929512483363063027)
                ·
                  refine ⟨707743394268725044594541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471828929512483363063027 707743394268725044594541)
                  ·
                    refine ⟨265403772850771891722953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707743394268725044594541 265403772850771891722953)
                    ·
                      rfl

theorem cell22_775308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_775308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775308 prefixEnd_775308 := by exact prefixLift 775308
  have htrace : WordTrace (prefixWord ++ tailWord_775308) baseStart_775308 baseEnd_775308 := by
    simpa [prefixWord, tailWord_775308, baseEnd_775308] using wordTrace_append hprefix tailTrace_775308
  have hstable : (prefixWord ++ tailWord_775308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775308).length < 2 ^ (prefixWord ++ tailWord_775308).sum := by decide
  have hdescent : baseEnd_775308 < baseStart_775308 := by decide
  rcases family_descends (prefixWord ++ tailWord_775308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775379 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_775379 : Nat := 118140960795 + 775379 * 2 ^ 59
def prefixEnd_775379 : Nat := 4983230072969 + 3 ^ 40 * 775379 * 2
def baseEnd_775379 : Nat := 265428077601751373197735

theorem tailTrace_775379 : CollatzResearch.WordTrace tailWord_775379 prefixEnd_775379 265428077601751373197735 := by
  unfold tailWord_775379
  simp only [CollatzResearch.WordTrace]
  refine ⟨28280395457941782035481191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18853596971961188023654127 28280395457941782035481191)
  ·
    refine ⟨42420593186912673053221787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28280395457941782035481191 42420593186912673053221787)
    ·
      refine ⟨63630889780369009579832681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42420593186912673053221787 63630889780369009579832681)
      ·
        refine ⟨47723167335276757184874511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63630889780369009579832681 47723167335276757184874511)
        ·
          refine ⟨71584751002915135777311767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47723167335276757184874511 71584751002915135777311767)
          ·
            refine ⟨107377126504372703665967651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71584751002915135777311767 107377126504372703665967651)
            ·
              refine ⟨161065689756559055498951477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107377126504372703665967651 161065689756559055498951477)
              ·
                refine ⟨15099908414677411453026701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161065689756559055498951477 15099908414677411453026701)
                ·
                  refine ⟨5662465655504029294885013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15099908414677411453026701 5662465655504029294885013)
                  ·
                    refine ⟨265428077601751373197735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5662465655504029294885013 265428077601751373197735)
                    ·
                      rfl

theorem cell22_775379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_775379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775379 prefixEnd_775379 := by exact prefixLift 775379
  have htrace : WordTrace (prefixWord ++ tailWord_775379) baseStart_775379 baseEnd_775379 := by
    simpa [prefixWord, tailWord_775379, baseEnd_775379] using wordTrace_append hprefix tailTrace_775379
  have hstable : (prefixWord ++ tailWord_775379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775379).length < 2 ^ (prefixWord ++ tailWord_775379).sum := by decide
  have hdescent : baseEnd_775379 < baseStart_775379 := by decide
  rcases family_descends (prefixWord ++ tailWord_775379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775432 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_775432 : Nat := 118140960795 + 775432 * 2 ^ 59
def prefixEnd_775432 : Nat := 4983230072969 + 3 ^ 40 * 775432 * 2
def baseEnd_775432 : Nat := 265446220584876901622573

theorem tailTrace_775432 : CollatzResearch.WordTrace tailWord_775432 prefixEnd_775432 265446220584876901622573 := by
  unfold tailWord_775432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141164263374886043580275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18854885684499848058107033 14141164263374886043580275)
  ·
    refine ⟨21211746395062329065370413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14141164263374886043580275 21211746395062329065370413)
    ·
      refine ⟨7954404898148373399513905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21211746395062329065370413 7954404898148373399513905)
      ·
        refine ⟨5965803673611280049635429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7954404898148373399513905 5965803673611280049635429)
        ·
          refine ⟨1118588188802115009306643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5965803673611280049635429 1118588188802115009306643)
          ·
            refine ⟨1677882283203172513959965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118588188802115009306643 1677882283203172513959965)
            ·
              refine ⟨629205856201189692734987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1677882283203172513959965 629205856201189692734987)
              ·
                refine ⟨943808784301784539102481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629205856201189692734987 943808784301784539102481)
                ·
                  refine ⟨707856588226338404326861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943808784301784539102481 707856588226338404326861)
                  ·
                    refine ⟨265446220584876901622573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707856588226338404326861 265446220584876901622573)
                    ·
                      rfl

theorem cell22_775432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_775432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775432 prefixEnd_775432 := by exact prefixLift 775432
  have htrace : WordTrace (prefixWord ++ tailWord_775432) baseStart_775432 baseEnd_775432 := by
    simpa [prefixWord, tailWord_775432, baseEnd_775432] using wordTrace_append hprefix tailTrace_775432
  have hstable : (prefixWord ++ tailWord_775432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775432).length < 2 ^ (prefixWord ++ tailWord_775432).sum := by decide
  have hdescent : baseEnd_775432 < baseStart_775432 := by decide
  rcases family_descends (prefixWord ++ tailWord_775432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775563 : List Nat := [1, 1, 1, 1, 4, 3, 5, 6]
def baseStart_775563 : Nat := 118140960795 + 775563 * 2 ^ 59
def prefixEnd_775563 : Nat := 4983230072969 + 3 ^ 40 * 775563 * 2
def baseEnd_775563 : Nat := 29499007173559580733019

theorem tailTrace_775563 : CollatzResearch.WordTrace tailWord_775563 prefixEnd_775563 29499007173559580733019 := by
  unfold tailWord_775563
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287106489275181460179343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18858070992850120973452895 28287106489275181460179343)
  ·
    refine ⟨42430659733912772190269015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28287106489275181460179343 42430659733912772190269015)
    ·
      refine ⟨63645989600869158285403523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42430659733912772190269015 63645989600869158285403523)
      ·
        refine ⟨95468984401303737428105285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63645989600869158285403523 95468984401303737428105285)
        ·
          refine ⟨17900434575244450767769741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95468984401303737428105285 17900434575244450767769741)
          ·
            refine ⟨6712662965716669037913653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17900434575244450767769741 6712662965716669037913653)
            ·
              refine ⟨629312153035937722304405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6712662965716669037913653 629312153035937722304405)
              ·
                refine ⟨29499007173559580733019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 629312153035937722304405 29499007173559580733019)
                ·
                  rfl

theorem cell22_775563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 6].length) (baseStart_775563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775563 prefixEnd_775563 := by exact prefixLift 775563
  have htrace : WordTrace (prefixWord ++ tailWord_775563) baseStart_775563 baseEnd_775563 := by
    simpa [prefixWord, tailWord_775563, baseEnd_775563] using wordTrace_append hprefix tailTrace_775563
  have hstable : (prefixWord ++ tailWord_775563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775563).length < 2 ^ (prefixWord ++ tailWord_775563).sum := by decide
  have hdescent : baseEnd_775563 < baseStart_775563 := by decide
  rcases family_descends (prefixWord ++ tailWord_775563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775580 : List Nat := [2, 2, 3, 4, 1, 1, 9]
def baseStart_775580 : Nat := 118140960795 + 775580 * 2 ^ 59
def prefixEnd_775580 : Nat := 4983230072969 + 3 ^ 40 * 775580 * 2
def baseEnd_775580 : Nat := 9833217926276068478597

theorem tailTrace_775580 : CollatzResearch.WordTrace tailWord_775580 prefixEnd_775580 9833217926276068478597 := by
  unfold tailWord_775580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143863265106796681774097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18858484353475728909032129 14143863265106796681774097)
  ·
    refine ⟨10607897448830097511330573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14143863265106796681774097 10607897448830097511330573)
    ·
      refine ⟨3977961543311286566748965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10607897448830097511330573 3977961543311286566748965)
      ·
        refine ⟨745867789370866231265431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3977961543311286566748965 745867789370866231265431)
        ·
          refine ⟨1118801684056299346898147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745867789370866231265431 1118801684056299346898147)
          ·
            refine ⟨1678202526084449020347221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118801684056299346898147 1678202526084449020347221)
            ·
              refine ⟨9833217926276068478597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1678202526084449020347221 9833217926276068478597)
              ·
                rfl

theorem cell22_775580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 9].length) (baseStart_775580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775580 prefixEnd_775580 := by exact prefixLift 775580
  have htrace : WordTrace (prefixWord ++ tailWord_775580) baseStart_775580 baseEnd_775580 := by
    simpa [prefixWord, tailWord_775580, baseEnd_775580] using wordTrace_append hprefix tailTrace_775580
  have hstable : (prefixWord ++ tailWord_775580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775580).length < 2 ^ (prefixWord ++ tailWord_775580).sum := by decide
  have hdescent : baseEnd_775580 < baseStart_775580 := by decide
  rcases family_descends (prefixWord ++ tailWord_775580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775608 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_775608 : Nat := 118140960795 + 775608 * 2 ^ 59
def prefixEnd_775608 : Nat := 4983230072969 + 3 ^ 40 * 775608 * 2
def baseEnd_775608 : Nat := 88502156327223703074011

theorem tailTrace_775608 : CollatzResearch.WordTrace tailWord_775608 prefixEnd_775608 88502156327223703074011 := by
  unfold tailWord_775608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144373887056077072783739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18859165182741436097044985 14144373887056077072783739)
  ·
    refine ⟨21216560830584115609175609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14144373887056077072783739 21216560830584115609175609)
    ·
      refine ⟨15912420622938086706881707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21216560830584115609175609 15912420622938086706881707)
      ·
        refine ⟨23868630934407130060322561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15912420622938086706881707 23868630934407130060322561)
        ·
          refine ⟨17901473200805347545241921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23868630934407130060322561 17901473200805347545241921)
          ·
            refine ⟨13426104900604010658931441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17901473200805347545241921 13426104900604010658931441)
            ·
              refine ⟨10069578675453007994198581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13426104900604010658931441 10069578675453007994198581)
              ·
                refine ⟨944023000823719499456117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10069578675453007994198581 944023000823719499456117)
                ·
                  refine ⟨88502156327223703074011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944023000823719499456117 88502156327223703074011)
                  ·
                    rfl

theorem cell22_775608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_775608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775608 prefixEnd_775608 := by exact prefixLift 775608
  have htrace : WordTrace (prefixWord ++ tailWord_775608) baseStart_775608 baseEnd_775608 := by
    simpa [prefixWord, tailWord_775608, baseEnd_775608] using wordTrace_append hprefix tailTrace_775608
  have hstable : (prefixWord ++ tailWord_775608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775608).length < 2 ^ (prefixWord ++ tailWord_775608).sum := by decide
  have hdescent : baseEnd_775608 < baseStart_775608 := by decide
  rcases family_descends (prefixWord ++ tailWord_775608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775672 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_775672 : Nat := 118140960795 + 775672 * 2 ^ 59
def prefixEnd_775672 : Nat := 4983230072969 + 3 ^ 40 * 775672 * 2
def baseEnd_775672 : Nat := 265528377489596275621837

theorem tailTrace_775672 : CollatzResearch.WordTrace tailWord_775672 prefixEnd_775672 265528377489596275621837 := by
  unfold tailWord_775672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145541022940146537948635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18860721363920195383931513 14145541022940146537948635)
  ·
    refine ⟨21218311534410219806922953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14145541022940146537948635 21218311534410219806922953)
    ·
      refine ⟨15913733650807664855192215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21218311534410219806922953 15913733650807664855192215)
      ·
        refine ⟨23870600476211497282788323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15913733650807664855192215 23870600476211497282788323)
        ·
          refine ⟨35805900714317245924182485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23870600476211497282788323 35805900714317245924182485)
          ·
            refine ⟨839200797991810451348027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35805900714317245924182485 839200797991810451348027)
            ·
              refine ⟨1258801196987715677022041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839200797991810451348027 1258801196987715677022041)
              ·
                refine ⟨944100897740786757766531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258801196987715677022041 944100897740786757766531)
                ·
                  refine ⟨1416151346611180136649797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944100897740786757766531 1416151346611180136649797)
                  ·
                    refine ⟨265528377489596275621837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416151346611180136649797 265528377489596275621837)
                    ·
                      rfl

theorem cell22_775672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_775672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775672 prefixEnd_775672 := by exact prefixLift 775672
  have htrace : WordTrace (prefixWord ++ tailWord_775672) baseStart_775672 baseEnd_775672 := by
    simpa [prefixWord, tailWord_775672, baseEnd_775672] using wordTrace_append hprefix tailTrace_775672
  have hstable : (prefixWord ++ tailWord_775672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775672).length < 2 ^ (prefixWord ++ tailWord_775672).sum := by decide
  have hdescent : baseEnd_775672 < baseStart_775672 := by decide
  rcases family_descends (prefixWord ++ tailWord_775672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775728 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_775728 : Nat := 118140960795 + 775728 * 2 ^ 59
def prefixEnd_775728 : Nat := 4983230072969 + 3 ^ 40 * 775728 * 2
def baseEnd_775728 : Nat := 265547547434030796221665

theorem tailTrace_775728 : CollatzResearch.WordTrace tailWord_775728 prefixEnd_775728 265547547434030796221665 := by
  unfold tailWord_775728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146562266838707319967919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18862083022451609759957225 14146562266838707319967919)
  ·
    refine ⟨21219843400258060979951879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14146562266838707319967919 21219843400258060979951879)
    ·
      refine ⟨31829765100387091469927819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21219843400258060979951879 31829765100387091469927819)
      ·
        refine ⟨47744647650580637204891729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31829765100387091469927819 47744647650580637204891729)
        ·
          refine ⟨35808485737935477903668797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47744647650580637204891729 35808485737935477903668797)
          ·
            refine ⟨13428182151725804213875799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35808485737935477903668797 13428182151725804213875799)
            ·
              refine ⟨20142273227588706320813699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13428182151725804213875799 20142273227588706320813699)
              ·
                refine ⟨30213409841383059481220549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20142273227588706320813699 30213409841383059481220549)
                ·
                  refine ⟨5665014345259323652728853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30213409841383059481220549 5665014345259323652728853)
                  ·
                    refine ⟨265547547434030796221665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5665014345259323652728853 265547547434030796221665)
                    ·
                      rfl

theorem cell22_775728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_775728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775728 prefixEnd_775728 := by exact prefixLift 775728
  have htrace : WordTrace (prefixWord ++ tailWord_775728) baseStart_775728 baseEnd_775728 := by
    simpa [prefixWord, tailWord_775728, baseEnd_775728] using wordTrace_append hprefix tailTrace_775728
  have hstable : (prefixWord ++ tailWord_775728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775728).length < 2 ^ (prefixWord ++ tailWord_775728).sum := by decide
  have hdescent : baseEnd_775728 < baseStart_775728 := by decide
  rcases family_descends (prefixWord ++ tailWord_775728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775764 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_775764 : Nat := 118140960795 + 775764 * 2 ^ 59
def prefixEnd_775764 : Nat := 4983230072969 + 3 ^ 40 * 775764 * 2
def baseEnd_775764 : Nat := 265559870969738702321555

theorem tailTrace_775764 : CollatzResearch.WordTrace tailWord_775764 prefixEnd_775764 265559870969738702321555 := by
  unfold tailWord_775764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14147218780773496394123173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18862958374364661858830897 14147218780773496394123173)
  ·
    refine ⟨2652603521395030573898095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14147218780773496394123173 2652603521395030573898095)
    ·
      refine ⟨3978905282092545860847143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652603521395030573898095 3978905282092545860847143)
      ·
        refine ⟨5968357923138818791270715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978905282092545860847143 5968357923138818791270715)
        ·
          refine ⟨8952536884708228186906073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968357923138818791270715 8952536884708228186906073)
          ·
            refine ⟨6714402663531171140179555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8952536884708228186906073 6714402663531171140179555)
            ·
              refine ⟨10071603995296756710269333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714402663531171140179555 10071603995296756710269333)
              ·
                refine ⟨472106437279535470793875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10071603995296756710269333 472106437279535470793875)
                ·
                  refine ⟨708159655919303206190813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472106437279535470793875 708159655919303206190813)
                  ·
                    refine ⟨265559870969738702321555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708159655919303206190813 265559870969738702321555)
                    ·
                      rfl

theorem cell22_775764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_775764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775764 prefixEnd_775764 := by exact prefixLift 775764
  have htrace : WordTrace (prefixWord ++ tailWord_775764) baseStart_775764 baseEnd_775764 := by
    simpa [prefixWord, tailWord_775764, baseEnd_775764] using wordTrace_append hprefix tailTrace_775764
  have hstable : (prefixWord ++ tailWord_775764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775764).length < 2 ^ (prefixWord ++ tailWord_775764).sum := by decide
  have hdescent : baseEnd_775764 < baseStart_775764 := by decide
  rcases family_descends (prefixWord ++ tailWord_775764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775777 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 5]
def baseStart_775777 : Nat := 118140960795 + 775777 * 2 ^ 59
def prefixEnd_775777 : Nat := 4983230072969 + 3 ^ 40 * 775777 * 2
def baseEnd_775777 : Nat := 88521440378470333915505

theorem tailTrace_775777 : CollatzResearch.WordTrace tailWord_775777 prefixEnd_775777 88521440378470333915505 := by
  unfold tailWord_775777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294911710499896008469585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18863274473666597338979723 28294911710499896008469585)
  ·
    refine ⟨21221183782874922006352189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28294911710499896008469585 21221183782874922006352189)
    ·
      refine ⟨7957943918578095752382071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21221183782874922006352189 7957943918578095752382071)
      ·
        refine ⟨11936915877867143628573107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7957943918578095752382071 11936915877867143628573107)
        ·
          refine ⟨17905373816800715442859661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936915877867143628573107 17905373816800715442859661)
          ·
            refine ⟨6714515181300268291072373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17905373816800715442859661 6714515181300268291072373)
            ·
              refine ⟨629485798246900152288035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6714515181300268291072373 629485798246900152288035)
              ·
                refine ⟨944228697370350228432053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629485798246900152288035 944228697370350228432053)
                ·
                  refine ⟨88521440378470333915505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944228697370350228432053 88521440378470333915505)
                  ·
                    rfl

theorem cell22_775777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_775777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775777 prefixEnd_775777 := by exact prefixLift 775777
  have htrace : WordTrace (prefixWord ++ tailWord_775777) baseStart_775777 baseEnd_775777 := by
    simpa [prefixWord, tailWord_775777, baseEnd_775777] using wordTrace_append hprefix tailTrace_775777
  have hstable : (prefixWord ++ tailWord_775777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775777).length < 2 ^ (prefixWord ++ tailWord_775777).sum := by decide
  have hdescent : baseEnd_775777 < baseStart_775777 := by decide
  rcases family_descends (prefixWord ++ tailWord_775777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775798 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_775798 : Nat := 118140960795 + 775798 * 2 ^ 59
def prefixEnd_775798 : Nat := 4983230072969 + 3 ^ 40 * 775798 * 2
def baseEnd_775798 : Nat := 265571509864573946971451

theorem tailTrace_775798 : CollatzResearch.WordTrace tailWord_775798 prefixEnd_775798 265571509864573946971451 := by
  unfold tailWord_775798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768479852713988537186503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18863785095615877729989365 1768479852713988537186503)
  ·
    refine ⟨2652719779070982805779755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768479852713988537186503 2652719779070982805779755)
    ·
      refine ⟨3979079668606474208669633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652719779070982805779755 3979079668606474208669633)
      ·
        refine ⟨2984309751454855656502225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979079668606474208669633 2984309751454855656502225)
        ·
          refine ⟨2238232313591141742376669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984309751454855656502225 2238232313591141742376669)
          ·
            refine ⟨839337117596678153391251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2238232313591141742376669 839337117596678153391251)
            ·
              refine ⟨1259005676395017230086877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839337117596678153391251 1259005676395017230086877)
              ·
                refine ⟨472127128648131461282579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259005676395017230086877 472127128648131461282579)
                ·
                  refine ⟨708190692972197191923869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472127128648131461282579 708190692972197191923869)
                  ·
                    refine ⟨265571509864573946971451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708190692972197191923869 265571509864573946971451)
                    ·
                      rfl

theorem cell22_775798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_775798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775798 prefixEnd_775798 := by exact prefixLift 775798
  have htrace : WordTrace (prefixWord ++ tailWord_775798) baseStart_775798 baseEnd_775798 := by
    simpa [prefixWord, tailWord_775798, baseEnd_775798] using wordTrace_append hprefix tailTrace_775798
  have hstable : (prefixWord ++ tailWord_775798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775798).length < 2 ^ (prefixWord ++ tailWord_775798).sum := by decide
  have hdescent : baseEnd_775798 < baseStart_775798 := by decide
  rcases family_descends (prefixWord ++ tailWord_775798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775822 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_775822 : Nat := 118140960795 + 775822 * 2 ^ 59
def prefixEnd_775822 : Nat := 4983230072969 + 3 ^ 40 * 775822 * 2
def baseEnd_775822 : Nat := 88526575185015294790459

theorem tailTrace_775822 : CollatzResearch.WordTrace tailWord_775822 prefixEnd_775822 88526575185015294790459 := by
  unfold tailWord_775822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537069124417108586732215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18864368663557912462571813 3537069124417108586732215)
  ·
    refine ⟨5305603686625662880098323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537069124417108586732215 5305603686625662880098323)
    ·
      refine ⟨7958405529938494320147485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5305603686625662880098323 7958405529938494320147485)
      ·
        refine ⟨2984402073726935370055307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7958405529938494320147485 2984402073726935370055307)
        ·
          refine ⟨4476603110590403055082961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984402073726935370055307 4476603110590403055082961)
          ·
            refine ⟨3357452332942802291312221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476603110590403055082961 3357452332942802291312221)
            ·
              refine ⟨1259044624853550859242083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3357452332942802291312221 1259044624853550859242083)
              ·
                refine ⟨1888566937280326288863125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259044624853550859242083 1888566937280326288863125)
                ·
                  refine ⟨88526575185015294790459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1888566937280326288863125 88526575185015294790459)
                  ·
                    rfl

theorem cell22_775822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_775822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775822 prefixEnd_775822 := by exact prefixLift 775822
  have htrace : WordTrace (prefixWord ++ tailWord_775822) baseStart_775822 baseEnd_775822 := by
    simpa [prefixWord, tailWord_775822, baseEnd_775822] using wordTrace_append hprefix tailTrace_775822
  have hstable : (prefixWord ++ tailWord_775822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775822).length < 2 ^ (prefixWord ++ tailWord_775822).sum := by decide
  have hdescent : baseEnd_775822 < baseStart_775822 := by decide
  rcases family_descends (prefixWord ++ tailWord_775822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775828 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_775828 : Nat := 118140960795 + 775828 * 2 ^ 59
def prefixEnd_775828 : Nat := 4983230072969 + 3 ^ 40 * 775828 * 2
def baseEnd_775828 : Nat := 88527259825887956240453

theorem tailTrace_775828 : CollatzResearch.WordTrace tailWord_775828 prefixEnd_775828 88527259825887956240453 := by
  unfold tailWord_775828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148385916657565859288069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18864514555543421145717425 14148385916657565859288069)
  ·
    refine ⟨2652822359373293598616513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14148385916657565859288069 2652822359373293598616513)
    ·
      refine ⟨1989616769529970198962385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2652822359373293598616513 1989616769529970198962385)
      ·
        refine ⟨1492212577147477649221789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1989616769529970198962385 1492212577147477649221789)
        ·
          refine ⟨559579716430304118458171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1492212577147477649221789 559579716430304118458171)
          ·
            refine ⟨839369574645456177687257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559579716430304118458171 839369574645456177687257)
            ·
              refine ⟨629527180984092133265443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839369574645456177687257 629527180984092133265443)
              ·
                refine ⟨944290771476138199898165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629527180984092133265443 944290771476138199898165)
                ·
                  refine ⟨88527259825887956240453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944290771476138199898165 88527259825887956240453)
                  ·
                    rfl

theorem cell22_775828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_775828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775828 prefixEnd_775828 := by exact prefixLift 775828
  have htrace : WordTrace (prefixWord ++ tailWord_775828) baseStart_775828 baseEnd_775828 := by
    simpa [prefixWord, tailWord_775828, baseEnd_775828] using wordTrace_append hprefix tailTrace_775828
  have hstable : (prefixWord ++ tailWord_775828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775828).length < 2 ^ (prefixWord ++ tailWord_775828).sum := by decide
  have hdescent : baseEnd_775828 < baseStart_775828 := by decide
  rcases family_descends (prefixWord ++ tailWord_775828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775880 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_775880 : Nat := 118140960795 + 775880 * 2 ^ 59
def prefixEnd_775880 : Nat := 4983230072969 + 3 ^ 40 * 775880 * 2
def baseEnd_775880 : Nat := 265599580140353066421199

theorem tailTrace_775880 : CollatzResearch.WordTrace tailWord_775880 prefixEnd_775880 265599580140353066421199 := by
  unfold tailWord_775880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149334214563372299734547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18865778952751163066312729 14149334214563372299734547)
  ·
    refine ⟨21224001321845058449601821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14149334214563372299734547 21224001321845058449601821)
    ·
      refine ⟨7959000495691896918600683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21224001321845058449601821 7959000495691896918600683)
      ·
        refine ⟨11938500743537845377901025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959000495691896918600683 11938500743537845377901025)
        ·
          refine ⟨8953875557653384033425769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11938500743537845377901025 8953875557653384033425769)
          ·
            refine ⟨6715406668240038025069327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953875557653384033425769 6715406668240038025069327)
            ·
              refine ⟨10073110002360057037603991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715406668240038025069327 10073110002360057037603991)
              ·
                refine ⟨15109665003540085556405987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10073110002360057037603991 15109665003540085556405987)
                ·
                  refine ⟨22664497505310128334608981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15109665003540085556405987 22664497505310128334608981)
                  ·
                    refine ⟨265599580140353066421199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22664497505310128334608981 265599580140353066421199)
                    ·
                      rfl

theorem cell22_775880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_775880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775880 prefixEnd_775880 := by exact prefixLift 775880
  have htrace : WordTrace (prefixWord ++ tailWord_775880) baseStart_775880 baseEnd_775880 := by
    simpa [prefixWord, tailWord_775880, baseEnd_775880] using wordTrace_append hprefix tailTrace_775880
  have hstable : (prefixWord ++ tailWord_775880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775880).length < 2 ^ (prefixWord ++ tailWord_775880).sum := by decide
  have hdescent : baseEnd_775880 < baseStart_775880 := by decide
  rcases family_descends (prefixWord ++ tailWord_775880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775884 : List Nat := [2, 2, 1, 5, 2, 2, 1, 7]
def baseStart_775884 : Nat := 118140960795 + 775884 * 2 ^ 59
def prefixEnd_775884 : Nat := 4983230072969 + 3 ^ 40 * 775884 * 2
def baseEnd_775884 : Nat := 29511216602455376591243

theorem tailTrace_775884 : CollatzResearch.WordTrace tailWord_775884 prefixEnd_775884 29511216602455376591243 := by
  unfold tailWord_775884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149407160556126641307353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18865876214074835521743137 14149407160556126641307353)
  ·
    refine ⟨10612055370417094980980515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14149407160556126641307353 10612055370417094980980515)
    ·
      refine ⟨15918083055625642471470773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10612055370417094980980515 15918083055625642471470773)
      ·
        refine ⟨1492320286464903981700385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15918083055625642471470773 1492320286464903981700385)
        ·
          refine ⟨1119240214848677986275289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492320286464903981700385 1119240214848677986275289)
          ·
            refine ⟨839430161136508489706467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119240214848677986275289 839430161136508489706467)
            ·
              refine ⟨1259145241704762734559701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839430161136508489706467 1259145241704762734559701)
              ·
                refine ⟨29511216602455376591243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1259145241704762734559701 29511216602455376591243)
                ·
                  rfl

theorem cell22_775884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_775884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775884 prefixEnd_775884 := by exact prefixLift 775884
  have htrace : WordTrace (prefixWord ++ tailWord_775884) baseStart_775884 baseEnd_775884 := by
    simpa [prefixWord, tailWord_775884, baseEnd_775884] using wordTrace_append hprefix tailTrace_775884
  have hstable : (prefixWord ++ tailWord_775884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775884).length < 2 ^ (prefixWord ++ tailWord_775884).sum := by decide
  have hdescent : baseEnd_775884 < baseStart_775884 := by decide
  rcases family_descends (prefixWord ++ tailWord_775884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775901 : List Nat := [1, 4, 3, 3, 1, 1, 3, 6]
def baseStart_775901 : Nat := 118140960795 + 775901 * 2 ^ 59
def prefixEnd_775901 : Nat := 4983230072969 + 3 ^ 40 * 775901 * 2
def baseEnd_775901 : Nat := 29511863207724001294015

theorem tailTrace_775901 : CollatzResearch.WordTrace tailWord_775901 prefixEnd_775901 29511863207724001294015 := by
  unfold tailWord_775901
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299434362050665185983557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18866289574700443457322371 28299434362050665185983557)
  ·
    refine ⟨5306143942884499722371917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28299434362050665185983557 5306143942884499722371917)
    ·
      refine ⟨1989803978581687395889469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5306143942884499722371917 1989803978581687395889469)
      ·
        refine ⟨746176491968132773458551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1989803978581687395889469 746176491968132773458551)
        ·
          refine ⟨1119264737952199160187827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746176491968132773458551 1119264737952199160187827)
          ·
            refine ⟨1678897106928298740281741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119264737952199160187827 1678897106928298740281741)
            ·
              refine ⟨629586415098112027605653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678897106928298740281741 629586415098112027605653)
              ·
                refine ⟨29511863207724001294015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 629586415098112027605653 29511863207724001294015)
                ·
                  rfl

theorem cell22_775901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 6].length) (baseStart_775901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775901 prefixEnd_775901 := by exact prefixLift 775901
  have htrace : WordTrace (prefixWord ++ tailWord_775901) baseStart_775901 baseEnd_775901 := by
    simpa [prefixWord, tailWord_775901, baseEnd_775901] using wordTrace_append hprefix tailTrace_775901
  have hstable : (prefixWord ++ tailWord_775901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775901).length < 2 ^ (prefixWord ++ tailWord_775901).sum := by decide
  have hdescent : baseEnd_775901 < baseStart_775901 := by decide
  rcases family_descends (prefixWord ++ tailWord_775901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775957 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 6]
def baseStart_775957 : Nat := 118140960795 + 775957 * 2 ^ 59
def prefixEnd_775957 : Nat := 4983230072969 + 3 ^ 40 * 775957 * 2
def baseEnd_775957 : Nat := 88541979604650177415321

theorem tailTrace_775957 : CollatzResearch.WordTrace tailWord_775957 prefixEnd_775957 88541979604650177415321 := by
  unfold tailWord_775957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28301476849847786750022125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18867651233231857833348083 28301476849847786750022125)
  ·
    refine ⟨10613053818692920031258297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28301476849847786750022125 10613053818692920031258297)
    ·
      refine ⟨7959790364019690023443723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10613053818692920031258297 7959790364019690023443723)
      ·
        refine ⟨11939685546029535035165585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959790364019690023443723 11939685546029535035165585)
        ·
          refine ⟨8954764159522151276374189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11939685546029535035165585 8954764159522151276374189)
          ·
            refine ⟨3358036559820806728640321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8954764159522151276374189 3358036559820806728640321)
            ·
              refine ⟨2518527419865605046480241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358036559820806728640321 2518527419865605046480241)
              ·
                refine ⟨1888895564899203784860181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518527419865605046480241 1888895564899203784860181)
                ·
                  refine ⟨88541979604650177415321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1888895564899203784860181 88541979604650177415321)
                  ·
                    rfl

theorem cell22_775957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_775957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775957 prefixEnd_775957 := by exact prefixLift 775957
  have htrace : WordTrace (prefixWord ++ tailWord_775957) baseStart_775957 baseEnd_775957 := by
    simpa [prefixWord, tailWord_775957, baseEnd_775957] using wordTrace_append hprefix tailTrace_775957
  have hstable : (prefixWord ++ tailWord_775957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775957).length < 2 ^ (prefixWord ++ tailWord_775957).sum := by decide
  have hdescent : baseEnd_775957 < baseStart_775957 := by decide
  rcases family_descends (prefixWord ++ tailWord_775957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775959 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 1, 4]
def baseStart_775959 : Nat := 118140960795 + 775959 * 2 ^ 59
def prefixEnd_775959 : Nat := 4983230072969 + 3 ^ 40 * 775959 * 2
def baseEnd_775959 : Nat := 265626623454823193695957

theorem tailTrace_775959 : CollatzResearch.WordTrace tailWord_775959 prefixEnd_775959 265626623454823193695957 := by
  unfold tailWord_775959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28301549795840541091594931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18867699863893694061063287 28301549795840541091594931)
  ·
    refine ⟨42452324693760811637392397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28301549795840541091594931 42452324693760811637392397)
    ·
      refine ⟨15919621760160304364022149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42452324693760811637392397 15919621760160304364022149)
      ·
        refine ⟨2984929080030057068254153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15919621760160304364022149 2984929080030057068254153)
        ·
          refine ⟨2238696810022542801190615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984929080030057068254153 2238696810022542801190615)
          ·
            refine ⟨3358045215033814201785923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238696810022542801190615 3358045215033814201785923)
            ·
              refine ⟨5037067822550721302678885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358045215033814201785923 5037067822550721302678885)
              ·
                refine ⟨944450216728260244252291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5037067822550721302678885 944450216728260244252291)
                ·
                  refine ⟨1416675325092390366378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944450216728260244252291 1416675325092390366378437)
                  ·
                    refine ⟨265626623454823193695957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416675325092390366378437 265626623454823193695957)
                    ·
                      rfl

theorem cell22_775959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_775959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_775959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_775959 prefixEnd_775959 := by exact prefixLift 775959
  have htrace : WordTrace (prefixWord ++ tailWord_775959) baseStart_775959 baseEnd_775959 := by
    simpa [prefixWord, tailWord_775959, baseEnd_775959] using wordTrace_append hprefix tailTrace_775959
  have hstable : (prefixWord ++ tailWord_775959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775959).length < 2 ^ (prefixWord ++ tailWord_775959).sum := by decide
  have hdescent : baseEnd_775959 < baseStart_775959 := by decide
  rcases family_descends (prefixWord ++ tailWord_775959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776042 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_776042 : Nat := 118140960795 + 776042 * 2 ^ 59
def prefixEnd_776042 : Nat := 4983230072969 + 3 ^ 40 * 776042 * 2
def baseEnd_776042 : Nat := 88551678683679547956901

theorem tailTrace_776042 : CollatzResearch.WordTrace tailWord_776042 prefixEnd_776042 88551678683679547956901 := by
  unfold tailWord_776042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076144263634961566716595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18869718036359897511244253 7076144263634961566716595)
  ·
    refine ⟨10614216395452442350074893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076144263634961566716595 10614216395452442350074893)
    ·
      refine ⟨3980331148294665881278085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10614216395452442350074893 3980331148294665881278085)
      ·
        refine ⟨746312090305249852739641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3980331148294665881278085 746312090305249852739641)
        ·
          refine ⟨559734067728937389554731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746312090305249852739641 559734067728937389554731)
          ·
            refine ⟨839601101593406084332097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559734067728937389554731 839601101593406084332097)
            ·
              refine ⟨629700826195054563249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839601101593406084332097 629700826195054563249073)
              ·
                refine ⟨472275619646290922436805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629700826195054563249073 472275619646290922436805)
                ·
                  refine ⟨88551678683679547956901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472275619646290922436805 88551678683679547956901)
                  ·
                    rfl

theorem cell22_776042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_776042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776042 prefixEnd_776042 := by exact prefixLift 776042
  have htrace : WordTrace (prefixWord ++ tailWord_776042) baseStart_776042 baseEnd_776042 := by
    simpa [prefixWord, tailWord_776042, baseEnd_776042] using wordTrace_append hprefix tailTrace_776042
  have hstable : (prefixWord ++ tailWord_776042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776042).length < 2 ^ (prefixWord ++ tailWord_776042).sum := by decide
  have hdescent : baseEnd_776042 < baseStart_776042 := by decide
  rcases family_descends (prefixWord ++ tailWord_776042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776098 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_776098 : Nat := 118140960795 + 776098 * 2 ^ 59
def prefixEnd_776098 : Nat := 4983230072969 + 3 ^ 40 * 776098 * 2
def baseEnd_776098 : Nat := 88558068665157721490177

theorem tailTrace_776098 : CollatzResearch.WordTrace tailWord_776098 prefixEnd_776098 88558068665157721490177 := by
  unfold tailWord_776098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076654885584241957726237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18871079694891311887269965 7076654885584241957726237)
  ·
    refine ⟨2653745582094090734147339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7076654885584241957726237 2653745582094090734147339)
    ·
      refine ⟨3980618373141136101221009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653745582094090734147339 3980618373141136101221009)
      ·
        refine ⟨2985463779855852075915757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980618373141136101221009 2985463779855852075915757)
        ·
          refine ⟨1119548917445944528468409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985463779855852075915757 1119548917445944528468409)
          ·
            refine ⟨839661688084458396351307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119548917445944528468409 839661688084458396351307)
            ·
              refine ⟨1259492532126687594526961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839661688084458396351307 1259492532126687594526961)
              ·
                refine ⟨944619399095015695895221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259492532126687594526961 944619399095015695895221)
                ·
                  refine ⟨88558068665157721490177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944619399095015695895221 88558068665157721490177)
                  ·
                    rfl

theorem cell22_776098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_776098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776098 prefixEnd_776098 := by exact prefixLift 776098
  have htrace : WordTrace (prefixWord ++ tailWord_776098) baseStart_776098 baseEnd_776098 := by
    simpa [prefixWord, tailWord_776098, baseEnd_776098] using wordTrace_append hprefix tailTrace_776098
  have hstable : (prefixWord ++ tailWord_776098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776098).length < 2 ^ (prefixWord ++ tailWord_776098).sum := by decide
  have hdescent : baseEnd_776098 < baseStart_776098 := by decide
  rcases family_descends (prefixWord ++ tailWord_776098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776137 : List Nat := [1, 2, 1, 1, 2, 1, 2, 12]
def baseStart_776137 : Nat := 118140960795 + 776137 * 2 ^ 59
def prefixEnd_776137 : Nat := 4983230072969 + 3 ^ 40 * 776137 * 2
def baseEnd_776137 : Nat := 29520839610276673638379

theorem tailTrace_776137 : CollatzResearch.WordTrace tailWord_776137 prefixEnd_776137 29520839610276673638379 := by
  unfold tailWord_776137
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308041989195677491574665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18872027992797118327716443 28308041989195677491574665)
  ·
    refine ⟨21231031491896758118680999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28308041989195677491574665 21231031491896758118680999)
    ·
      refine ⟨31846547237845137178021499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21231031491896758118680999 31846547237845137178021499)
      ·
        refine ⟨47769820856767705767032249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31846547237845137178021499 47769820856767705767032249)
        ·
          refine ⟨35827365642575779325274187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47769820856767705767032249 35827365642575779325274187)
          ·
            refine ⟨53741048463863668987911281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35827365642575779325274187 53741048463863668987911281)
            ·
              refine ⟨40305786347897751740933461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53741048463863668987911281 40305786347897751740933461)
              ·
                refine ⟨29520839610276673638379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 40305786347897751740933461 29520839610276673638379)
                ·
                  rfl

theorem cell22_776137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 12].length) (baseStart_776137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776137 prefixEnd_776137 := by exact prefixLift 776137
  have htrace : WordTrace (prefixWord ++ tailWord_776137) baseStart_776137 baseEnd_776137 := by
    simpa [prefixWord, tailWord_776137, baseEnd_776137] using wordTrace_append hprefix tailTrace_776137
  have hstable : (prefixWord ++ tailWord_776137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776137).length < 2 ^ (prefixWord ++ tailWord_776137).sum := by decide
  have hdescent : baseEnd_776137 < baseStart_776137 := by decide
  rcases family_descends (prefixWord ++ tailWord_776137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776139 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_776139 : Nat := 118140960795 + 776139 * 2 ^ 59
def prefixEnd_776139 : Nat := 4983230072969 + 3 ^ 40 * 776139 * 2
def baseEnd_776139 : Nat := 265688241133362724195405

theorem tailTrace_776139 : CollatzResearch.WordTrace tailWord_776139 prefixEnd_776139 265688241133362724195405 := by
  unfold tailWord_776139
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308114935188431833147471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18872076623458954555431647 28308114935188431833147471)
  ·
    refine ⟨42462172402782647749721207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28308114935188431833147471 42462172402782647749721207)
    ·
      refine ⟨63693258604173971624581811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42462172402782647749721207 63693258604173971624581811)
      ·
        refine ⟨95539887906260957436872717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63693258604173971624581811 95539887906260957436872717)
        ·
          refine ⟨35827457964847859038827269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95539887906260957436872717 35827457964847859038827269)
          ·
            refine ⟨6717648368408973569780113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35827457964847859038827269 6717648368408973569780113)
            ·
              refine ⟨5038236276306730177335085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717648368408973569780113 5038236276306730177335085)
              ·
                refine ⟨1889338603615023816500657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5038236276306730177335085 1889338603615023816500657)
                ·
                  refine ⟨1417003952711267862375493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889338603615023816500657 1417003952711267862375493)
                  ·
                    refine ⟨265688241133362724195405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417003952711267862375493 265688241133362724195405)
                    ·
                      rfl

theorem cell22_776139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_776139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776139 prefixEnd_776139 := by exact prefixLift 776139
  have htrace : WordTrace (prefixWord ++ tailWord_776139) baseStart_776139 baseEnd_776139 := by
    simpa [prefixWord, tailWord_776139, baseEnd_776139] using wordTrace_append hprefix tailTrace_776139
  have hstable : (prefixWord ++ tailWord_776139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776139).length < 2 ^ (prefixWord ++ tailWord_776139).sum := by decide
  have hdescent : baseEnd_776139 < baseStart_776139 := by decide
  rcases family_descends (prefixWord ++ tailWord_776139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776203 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 1, 3]
def baseStart_776203 : Nat := 118140960795 + 776203 * 2 ^ 59
def prefixEnd_776203 : Nat := 4983230072969 + 3 ^ 40 * 776203 * 2
def baseEnd_776203 : Nat := 265710149641287890595209

theorem tailTrace_776203 : CollatzResearch.WordTrace tailWord_776203 prefixEnd_776203 265710149641287890595209 := by
  unfold tailWord_776203
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310449206956570763477263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873632804637713842318175 28310449206956570763477263)
  ·
    refine ⟨42465673810434856145215895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28310449206956570763477263 42465673810434856145215895)
    ·
      refine ⟨63698510715652284217823843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42465673810434856145215895 63698510715652284217823843)
      ·
        refine ⟨95547766073478426326735765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63698510715652284217823843 95547766073478426326735765)
        ·
          refine ⟨4478801534694301234065739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95547766073478426326735765 4478801534694301234065739)
          ·
            refine ⟨6718202302041451851098609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478801534694301234065739 6718202302041451851098609)
            ·
              refine ⟨5038651726531088888323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6718202302041451851098609 5038651726531088888323957)
              ·
                refine ⟨472373599362289583280371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5038651726531088888323957 472373599362289583280371)
                ·
                  refine ⟨708560399043434374920557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472373599362289583280371 708560399043434374920557)
                  ·
                    refine ⟨265710149641287890595209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708560399043434374920557 265710149641287890595209)
                    ·
                      rfl

theorem cell22_776203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 3].length) (baseStart_776203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776203 prefixEnd_776203 := by exact prefixLift 776203
  have htrace : WordTrace (prefixWord ++ tailWord_776203) baseStart_776203 baseEnd_776203 := by
    simpa [prefixWord, tailWord_776203, baseEnd_776203] using wordTrace_append hprefix tailTrace_776203
  have hstable : (prefixWord ++ tailWord_776203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776203).length < 2 ^ (prefixWord ++ tailWord_776203).sum := by decide
  have hdescent : baseEnd_776203 < baseStart_776203 := by decide
  rcases family_descends (prefixWord ++ tailWord_776203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776205 : List Nat := [1, 7, 1, 2, 2, 9]
def baseStart_776205 : Nat := 118140960795 + 776205 * 2 ^ 59
def prefixEnd_776205 : Nat := 4983230072969 + 3 ^ 40 * 776205 * 2
def baseEnd_776205 : Nat := 3280380670150130272163

theorem tailTrace_776205 : CollatzResearch.WordTrace tailWord_776205 prefixEnd_776205 3280380670150130272163 := by
  unfold tailWord_776205
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310522152949325105050069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873681435299550070033379 28310522152949325105050069)
  ·
    refine ⟨663527862959749807149611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28310522152949325105050069 663527862959749807149611)
    ·
      refine ⟨995291794439624710724417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663527862959749807149611 995291794439624710724417)
      ·
        refine ⟨746468845829718533043313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995291794439624710724417 746468845829718533043313)
        ·
          refine ⟨559851634372288899782485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746468845829718533043313 559851634372288899782485)
          ·
            refine ⟨3280380670150130272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 559851634372288899782485 3280380670150130272163)
            ·
              rfl

theorem cell22_776205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 9].length) (baseStart_776205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776205 prefixEnd_776205 := by exact prefixLift 776205
  have htrace : WordTrace (prefixWord ++ tailWord_776205) baseStart_776205 baseEnd_776205 := by
    simpa [prefixWord, tailWord_776205, baseEnd_776205] using wordTrace_append hprefix tailTrace_776205
  have hstable : (prefixWord ++ tailWord_776205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776205).length < 2 ^ (prefixWord ++ tailWord_776205).sum := by decide
  have hdescent : baseEnd_776205 < baseStart_776205 := by decide
  rcases family_descends (prefixWord ++ tailWord_776205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776216 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_776216 : Nat := 118140960795 + 776216 * 2 ^ 59
def prefixEnd_776216 : Nat := 4983230072969 + 3 ^ 40 * 776216 * 2
def baseEnd_776216 : Nat := 88571533268986730006723

theorem tailTrace_776216 : CollatzResearch.WordTrace tailWord_776216 prefixEnd_776216 88571533268986730006723 := by
  unfold tailWord_776216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155461677954736991850251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18873948903939649322467001 14155461677954736991850251)
  ·
    refine ⟨21233192516932105487775377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14155461677954736991850251 21233192516932105487775377)
    ·
      refine ⟨15924894387699079115831533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21233192516932105487775377 15924894387699079115831533)
      ·
        refine ⟨5971835395387154668436825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15924894387699079115831533 5971835395387154668436825)
        ·
          refine ⟨4478876546540366001327619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5971835395387154668436825 4478876546540366001327619)
          ·
            refine ⟨6718314819810549001991429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478876546540366001327619 6718314819810549001991429)
            ·
              refine ⟨1259684028714477937873393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6718314819810549001991429 1259684028714477937873393)
              ·
                refine ⟨944763021535858453405045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259684028714477937873393 944763021535858453405045)
                ·
                  refine ⟨88571533268986730006723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944763021535858453405045 88571533268986730006723)
                  ·
                    rfl

theorem cell22_776216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_776216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776216 prefixEnd_776216 := by exact prefixLift 776216
  have htrace : WordTrace (prefixWord ++ tailWord_776216) baseStart_776216 baseEnd_776216 := by
    simpa [prefixWord, tailWord_776216, baseEnd_776216] using wordTrace_append hprefix tailTrace_776216
  have hstable : (prefixWord ++ tailWord_776216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776216).length < 2 ^ (prefixWord ++ tailWord_776216).sum := by decide
  have hdescent : baseEnd_776216 < baseStart_776216 := by decide
  rcases family_descends (prefixWord ++ tailWord_776216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776220 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_776220 : Nat := 118140960795 + 776220 * 2 ^ 59
def prefixEnd_776220 : Nat := 4983230072969 + 3 ^ 40 * 776220 * 2
def baseEnd_776220 : Nat := 265715969088705512920157

theorem tailTrace_776220 : CollatzResearch.WordTrace tailWord_776220 prefixEnd_776220 265715969088705512920157 := by
  unfold tailWord_776220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155534623947491333423057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18874046165263321777897409 14155534623947491333423057)
  ·
    refine ⟨10616650967960618500067293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14155534623947491333423057 10616650967960618500067293)
    ·
      refine ⟨3981244112985231937525235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10616650967960618500067293 3981244112985231937525235)
      ·
        refine ⟨5971866169477847906287853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981244112985231937525235 5971866169477847906287853)
        ·
          refine ⟨2239449813554192964857945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5971866169477847906287853 2239449813554192964857945)
          ·
            refine ⟨1679587360165644723643459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239449813554192964857945 1679587360165644723643459)
            ·
              refine ⟨2519381040248467085465189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679587360165644723643459 2519381040248467085465189)
              ·
                refine ⟨472383945046587578524723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2519381040248467085465189 472383945046587578524723)
                ·
                  refine ⟨708575917569881367787085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472383945046587578524723 708575917569881367787085)
                  ·
                    refine ⟨265715969088705512920157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708575917569881367787085 265715969088705512920157)
                    ·
                      rfl

theorem cell22_776220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_776220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776220 prefixEnd_776220 := by exact prefixLift 776220
  have htrace : WordTrace (prefixWord ++ tailWord_776220) baseStart_776220 baseEnd_776220 := by
    simpa [prefixWord, tailWord_776220, baseEnd_776220] using wordTrace_append hprefix tailTrace_776220
  have hstable : (prefixWord ++ tailWord_776220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776220).length < 2 ^ (prefixWord ++ tailWord_776220).sum := by decide
  have hdescent : baseEnd_776220 < baseStart_776220 := by decide
  rcases family_descends (prefixWord ++ tailWord_776220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776259 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_776259 : Nat := 118140960795 + 776259 * 2 ^ 59
def prefixEnd_776259 : Nat := 4983230072969 + 3 ^ 40 * 776259 * 2
def baseEnd_776259 : Nat := 265729319585722411195037

theorem tailTrace_776259 : CollatzResearch.WordTrace tailWord_776259 prefixEnd_776259 265729319585722411195037 := by
  unfold tailWord_776259
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312491694753692327515831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18874994463169128218343887 28312491694753692327515831)
  ·
    refine ⟨42468737542130538491273747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28312491694753692327515831 42468737542130538491273747)
    ·
      refine ⟨63703106313195807736910621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42468737542130538491273747 63703106313195807736910621)
      ·
        refine ⟨23888664867448427901341483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63703106313195807736910621 23888664867448427901341483)
        ·
          refine ⟨35832997301172641852012225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23888664867448427901341483 35832997301172641852012225)
          ·
            refine ⟨26874747975879481389009169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35832997301172641852012225 26874747975879481389009169)
            ·
              refine ⟨20156060981909611041756877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26874747975879481389009169 20156060981909611041756877)
              ·
                refine ⟨7558522868216104140658829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20156060981909611041756877 7558522868216104140658829)
                ·
                  refine ⟨2834446075581039052747061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7558522868216104140658829 2834446075581039052747061)
                  ·
                    refine ⟨265729319585722411195037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2834446075581039052747061 265729319585722411195037)
                    ·
                      rfl

theorem cell22_776259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_776259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776259 prefixEnd_776259 := by exact prefixLift 776259
  have htrace : WordTrace (prefixWord ++ tailWord_776259) baseStart_776259 baseEnd_776259 := by
    simpa [prefixWord, tailWord_776259, baseEnd_776259] using wordTrace_append hprefix tailTrace_776259
  have hstable : (prefixWord ++ tailWord_776259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776259).length < 2 ^ (prefixWord ++ tailWord_776259).sum := by decide
  have hdescent : baseEnd_776259 < baseStart_776259 := by decide
  rcases family_descends (prefixWord ++ tailWord_776259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776289 : List Nat := [1, 2, 3, 1, 1, 2, 1, 11]
def baseStart_776289 : Nat := 118140960795 + 776289 * 2 ^ 59
def prefixEnd_776289 : Nat := 4983230072969 + 3 ^ 40 * 776289 * 2
def baseEnd_776289 : Nat := 29526621022090259216105

theorem tailTrace_776289 : CollatzResearch.WordTrace tailWord_776289 prefixEnd_776289 29526621022090259216105 := by
  unfold tailWord_776289
  simp only [CollatzResearch.WordTrace]
  refine ⟨28313585884645007451107921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18875723923096671634071947 28313585884645007451107921)
  ·
    refine ⟨21235189413483755588330941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28313585884645007451107921 21235189413483755588330941)
    ·
      refine ⟨7963196030056408345624103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21235189413483755588330941 7963196030056408345624103)
      ·
        refine ⟨11944794045084612518436155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963196030056408345624103 11944794045084612518436155)
        ·
          refine ⟨17917191067626918777654233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944794045084612518436155 17917191067626918777654233)
          ·
            refine ⟨13437893300720189083240675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17917191067626918777654233 13437893300720189083240675)
            ·
              refine ⟨20156839951080283624861013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13437893300720189083240675 20156839951080283624861013)
              ·
                refine ⟨29526621022090259216105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20156839951080283624861013 29526621022090259216105)
                ·
                  rfl

theorem cell22_776289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 11].length) (baseStart_776289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776289 prefixEnd_776289 := by exact prefixLift 776289
  have htrace : WordTrace (prefixWord ++ tailWord_776289) baseStart_776289 baseEnd_776289 := by
    simpa [prefixWord, tailWord_776289, baseEnd_776289] using wordTrace_append hprefix tailTrace_776289
  have hstable : (prefixWord ++ tailWord_776289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776289).length < 2 ^ (prefixWord ++ tailWord_776289).sum := by decide
  have hdescent : baseEnd_776289 < baseStart_776289 := by decide
  rcases family_descends (prefixWord ++ tailWord_776289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776293 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_776293 : Nat := 118140960795 + 776293 * 2 ^ 59
def prefixEnd_776293 : Nat := 4983230072969 + 3 ^ 40 * 776293 * 2
def baseEnd_776293 : Nat := 265740958480557655844933

theorem tailTrace_776293 : CollatzResearch.WordTrace tailWord_776293 prefixEnd_776293 265740958480557655844933 := by
  unfold tailWord_776293
  simp only [CollatzResearch.WordTrace]
  refine ⟨28313731776630516134253533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18875821184420344089502355 28313731776630516134253533)
  ·
    refine ⟨10617649416236443550345075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28313731776630516134253533 10617649416236443550345075)
    ·
      refine ⟨15926474124354665325517613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617649416236443550345075 15926474124354665325517613)
      ·
        refine ⟨5972427796632999497069105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15926474124354665325517613 5972427796632999497069105)
        ·
          refine ⟨4479320847474749622801829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972427796632999497069105 4479320847474749622801829)
          ·
            refine ⟨839872658901515554275343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4479320847474749622801829 839872658901515554275343)
            ·
              refine ⟨1259808988352273331413015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839872658901515554275343 1259808988352273331413015)
              ·
                refine ⟨1889713482528409997119523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259808988352273331413015 1889713482528409997119523)
                ·
                  refine ⟨2834570223792614995679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889713482528409997119523 2834570223792614995679285)
                  ·
                    refine ⟨265740958480557655844933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2834570223792614995679285 265740958480557655844933)
                    ·
                      rfl

theorem cell22_776293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_776293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776293 prefixEnd_776293 := by exact prefixLift 776293
  have htrace : WordTrace (prefixWord ++ tailWord_776293) baseStart_776293 baseEnd_776293 := by
    simpa [prefixWord, tailWord_776293, baseEnd_776293] using wordTrace_append hprefix tailTrace_776293
  have hstable : (prefixWord ++ tailWord_776293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776293).length < 2 ^ (prefixWord ++ tailWord_776293).sum := by decide
  have hdescent : baseEnd_776293 < baseStart_776293 := by decide
  rcases family_descends (prefixWord ++ tailWord_776293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776306 : List Nat := [3, 2, 1, 2, 2, 3, 1, 8]
def baseStart_776306 : Nat := 118140960795 + 776306 * 2 ^ 59
def prefixEnd_776306 : Nat := 4983230072969 + 3 ^ 40 * 776306 * 2
def baseEnd_776306 : Nat := 29527267627358883918877

theorem tailTrace_776306 : CollatzResearch.WordTrace tailWord_776306 prefixEnd_776306 29527267627358883918877 := by
  unfold tailWord_776306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078551481395854838619193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18876137283722279569651181 7078551481395854838619193)
  ·
    refine ⟨5308913611046891128964395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7078551481395854838619193 5308913611046891128964395)
    ·
      refine ⟨7963370416570336693446593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308913611046891128964395 7963370416570336693446593)
      ·
        refine ⟨5972527812427752520084945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7963370416570336693446593 5972527812427752520084945)
        ·
          refine ⟨4479395859320814390063709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972527812427752520084945 4479395859320814390063709)
          ·
            refine ⟨1679773447245305396273891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4479395859320814390063709 1679773447245305396273891)
            ·
              refine ⟨2519660170867958094410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679773447245305396273891 2519660170867958094410837)
              ·
                refine ⟨29527267627358883918877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2519660170867958094410837 29527267627358883918877)
                ·
                  rfl

theorem cell22_776306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_776306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776306 prefixEnd_776306 := by exact prefixLift 776306
  have htrace : WordTrace (prefixWord ++ tailWord_776306) baseStart_776306 baseEnd_776306 := by
    simpa [prefixWord, tailWord_776306, baseEnd_776306] using wordTrace_append hprefix tailTrace_776306
  have hstable : (prefixWord ++ tailWord_776306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776306).length < 2 ^ (prefixWord ++ tailWord_776306).sum := by decide
  have hdescent : baseEnd_776306 < baseStart_776306 := by decide
  rcases family_descends (prefixWord ++ tailWord_776306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776340 : List Nat := [2, 4, 2, 3, 1, 1, 2, 7]
def baseStart_776340 : Nat := 118140960795 + 776340 * 2 ^ 59
def prefixEnd_776340 : Nat := 4983230072969 + 3 ^ 40 * 776340 * 2
def baseEnd_776340 : Nat := 29528560837896133324421

theorem tailTrace_776340 : CollatzResearch.WordTrace tailWord_776340 prefixEnd_776340 29528560837896133324421 := by
  unfold tailWord_776340
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157723003730121580607237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18876964004973495440809649 14157723003730121580607237)
  ·
    refine ⟨2654573063199397796363857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14157723003730121580607237 2654573063199397796363857)
    ·
      refine ⟨1990929797399548347272893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2654573063199397796363857 1990929797399548347272893)
      ·
        refine ⟨746598674024830630227335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1990929797399548347272893 746598674024830630227335)
        ·
          refine ⟨1119898011037245945341003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746598674024830630227335 1119898011037245945341003)
          ·
            refine ⟨1679847016555868918011505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119898011037245945341003 1679847016555868918011505)
            ·
              refine ⟨1259885262416901688508629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679847016555868918011505 1259885262416901688508629)
              ·
                refine ⟨29528560837896133324421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1259885262416901688508629 29528560837896133324421)
                ·
                  rfl

theorem cell22_776340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_776340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776340 prefixEnd_776340 := by exact prefixLift 776340
  have htrace : WordTrace (prefixWord ++ tailWord_776340) baseStart_776340 baseEnd_776340 := by
    simpa [prefixWord, tailWord_776340, baseEnd_776340] using wordTrace_append hprefix tailTrace_776340
  have hstable : (prefixWord ++ tailWord_776340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776340).length < 2 ^ (prefixWord ++ tailWord_776340).sum := by decide
  have hdescent : baseEnd_776340 < baseStart_776340 := by decide
  rcases family_descends (prefixWord ++ tailWord_776340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776344 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_776344 : Nat := 118140960795 + 776344 * 2 ^ 59
def prefixEnd_776344 : Nat := 4983230072969 + 3 ^ 40 * 776344 * 2
def baseEnd_776344 : Nat := 265758416822810522819777

theorem tailTrace_776344 : CollatzResearch.WordTrace tailWord_776344 prefixEnd_776344 265758416822810522819777 := by
  unfold tailWord_776344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157795949722875922180043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18877061266297167896240057 14157795949722875922180043)
  ·
    refine ⟨21236693924584313883270065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14157795949722875922180043 21236693924584313883270065)
    ·
      refine ⟨15927520443438235412452549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21236693924584313883270065 15927520443438235412452549)
      ·
        refine ⟨2986410083144669139834853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15927520443438235412452549 2986410083144669139834853)
        ·
          refine ⟨559951890589625463719035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2986410083144669139834853 559951890589625463719035)
          ·
            refine ⟨839927835884438195578553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559951890589625463719035 839927835884438195578553)
            ·
              refine ⟨629945876913328646683915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839927835884438195578553 629945876913328646683915)
              ·
                refine ⟨944918815369992970025873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629945876913328646683915 944918815369992970025873)
                ·
                  refine ⟨708689111527494727519405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 944918815369992970025873 708689111527494727519405)
                  ·
                    refine ⟨265758416822810522819777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708689111527494727519405 265758416822810522819777)
                    ·
                      rfl

theorem cell22_776344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_776344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776344 prefixEnd_776344 := by exact prefixLift 776344
  have htrace : WordTrace (prefixWord ++ tailWord_776344) baseStart_776344 baseEnd_776344 := by
    simpa [prefixWord, tailWord_776344, baseEnd_776344] using wordTrace_append hprefix tailTrace_776344
  have hstable : (prefixWord ++ tailWord_776344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776344).length < 2 ^ (prefixWord ++ tailWord_776344).sum := by decide
  have hdescent : baseEnd_776344 < baseStart_776344 := by decide
  rcases family_descends (prefixWord ++ tailWord_776344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776398 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_776398 : Nat := 118140960795 + 776398 * 2 ^ 59
def prefixEnd_776398 : Nat := 4983230072969 + 3 ^ 40 * 776398 * 2
def baseEnd_776398 : Nat := 265776902126372381969611

theorem tailTrace_776398 : CollatzResearch.WordTrace tailWord_776398 prefixEnd_776398 265776902126372381969611 := by
  unfold tailWord_776398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539695180156264883353231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18878374294166746044550565 3539695180156264883353231)
  ·
    refine ⟨5309542770234397325029847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3539695180156264883353231 5309542770234397325029847)
    ·
      refine ⟨7964314155351595987544771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5309542770234397325029847 7964314155351595987544771)
      ·
        refine ⟨11946471233027393981317157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964314155351595987544771 11946471233027393981317157)
        ·
          refine ⟨2239963356192636371496967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11946471233027393981317157 2239963356192636371496967)
          ·
            refine ⟨3359945034288954557245451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239963356192636371496967 3359945034288954557245451)
            ·
              refine ⟨5039917551433431835868177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359945034288954557245451 5039917551433431835868177)
              ·
                refine ⟨3779938163575073876901133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039917551433431835868177 3779938163575073876901133)
                ·
                  refine ⟨1417476811340652703837925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3779938163575073876901133 1417476811340652703837925)
                  ·
                    refine ⟨265776902126372381969611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417476811340652703837925 265776902126372381969611)
                    ·
                      rfl

theorem cell22_776398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_776398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776398 prefixEnd_776398 := by exact prefixLift 776398
  have htrace : WordTrace (prefixWord ++ tailWord_776398) baseStart_776398 baseEnd_776398 := by
    simpa [prefixWord, tailWord_776398, baseEnd_776398] using wordTrace_append hprefix tailTrace_776398
  have hstable : (prefixWord ++ tailWord_776398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776398).length < 2 ^ (prefixWord ++ tailWord_776398).sum := by decide
  have hdescent : baseEnd_776398 < baseStart_776398 := by decide
  rcases family_descends (prefixWord ++ tailWord_776398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776411 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_776411 : Nat := 118140960795 + 776411 * 2 ^ 59
def prefixEnd_776411 : Nat := 4983230072969 + 3 ^ 40 * 776411 * 2
def baseEnd_776411 : Nat := 265781352292044681394571

theorem tailTrace_776411 : CollatzResearch.WordTrace tailWord_776411 prefixEnd_776411 265781352292044681394571 := by
  unfold tailWord_776411
  simp only [CollatzResearch.WordTrace]
  refine ⟨28318035590203022287049087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18878690393468681524699391 28318035590203022287049087)
  ·
    refine ⟨42477053385304533430573631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28318035590203022287049087 42477053385304533430573631)
    ·
      refine ⟨63715580077956800145860447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42477053385304533430573631 63715580077956800145860447)
      ·
        refine ⟨95573370116935200218790671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63715580077956800145860447 95573370116935200218790671)
        ·
          refine ⟨143360055175402800328186007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95573370116935200218790671 143360055175402800328186007)
          ·
            refine ⟨215040082763104200492279011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143360055175402800328186007 215040082763104200492279011)
            ·
              refine ⟨322560124144656300738418517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215040082763104200492279011 322560124144656300738418517)
              ·
                refine ⟨1890000727410095512139171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 322560124144656300738418517 1890000727410095512139171)
                ·
                  refine ⟨2835001091115143268208757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890000727410095512139171 2835001091115143268208757)
                  ·
                    refine ⟨265781352292044681394571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2835001091115143268208757 265781352292044681394571)
                    ·
                      rfl

theorem cell22_776411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_776411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776411 prefixEnd_776411 := by exact prefixLift 776411
  have htrace : WordTrace (prefixWord ++ tailWord_776411) baseStart_776411 baseEnd_776411 := by
    simpa [prefixWord, tailWord_776411, baseEnd_776411] using wordTrace_append hprefix tailTrace_776411
  have hstable : (prefixWord ++ tailWord_776411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776411).length < 2 ^ (prefixWord ++ tailWord_776411).sum := by decide
  have hdescent : baseEnd_776411 < baseStart_776411 := by decide
  rcases family_descends (prefixWord ++ tailWord_776411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776413 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 8]
def baseStart_776413 : Nat := 118140960795 + 776413 * 2 ^ 59
def prefixEnd_776413 : Nat := 4983230072969 + 3 ^ 40 * 776413 * 2
def baseEnd_776413 : Nat := 88594012310972447614855

theorem tailTrace_776413 : CollatzResearch.WordTrace tailWord_776413 prefixEnd_776413 88594012310972447614855 := by
  unfold tailWord_776413
  simp only [CollatzResearch.WordTrace]
  refine ⟨28318108536195776628621893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18878739024130517752414595 28318108536195776628621893)
  ·
    refine ⟨5309645350536708117866605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28318108536195776628621893 5309645350536708117866605)
    ·
      refine ⟨1991117006451265544199977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5309645350536708117866605 1991117006451265544199977)
      ·
        refine ⟨1493337754838449158149983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991117006451265544199977 1493337754838449158149983)
        ·
          refine ⟨2240006632257673737224975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493337754838449158149983 2240006632257673737224975)
          ·
            refine ⟨3360009948386510605837463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240006632257673737224975 3360009948386510605837463)
            ·
              refine ⟨5040014922579765908756195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360009948386510605837463 5040014922579765908756195)
              ·
                refine ⟨7560022383869648863134293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040014922579765908756195 7560022383869648863134293)
                ·
                  refine ⟨88594012310972447614855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7560022383869648863134293 88594012310972447614855)
                  ·
                    rfl

theorem cell22_776413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_776413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776413 prefixEnd_776413 := by exact prefixLift 776413
  have htrace : WordTrace (prefixWord ++ tailWord_776413) baseStart_776413 baseEnd_776413 := by
    simpa [prefixWord, tailWord_776413, baseEnd_776413] using wordTrace_append hprefix tailTrace_776413
  have hstable : (prefixWord ++ tailWord_776413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776413).length < 2 ^ (prefixWord ++ tailWord_776413).sum := by decide
  have hdescent : baseEnd_776413 < baseStart_776413 := by decide
  rcases family_descends (prefixWord ++ tailWord_776413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776428 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_776428 : Nat := 118140960795 + 776428 * 2 ^ 59
def prefixEnd_776428 : Nat := 4983230072969 + 3 ^ 40 * 776428 * 2
def baseEnd_776428 : Nat := 265787171739462303719519

theorem tailTrace_776428 : CollatzResearch.WordTrace tailWord_776428 prefixEnd_776428 265787171739462303719519 := by
  unfold tailWord_776428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159327815570717095208969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18879103754094289460278625 14159327815570717095208969)
  ·
    refine ⟨10619495861678037821406727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159327815570717095208969 10619495861678037821406727)
    ·
      refine ⟨15929243792517056732110091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619495861678037821406727 15929243792517056732110091)
      ·
        refine ⟨23893865688775585098165137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15929243792517056732110091 23893865688775585098165137)
        ·
          refine ⟨17920399266581688823623853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23893865688775585098165137 17920399266581688823623853)
          ·
            refine ⟨6720149724968133308858945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17920399266581688823623853 6720149724968133308858945)
            ·
              refine ⟨5040112293726099981644209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720149724968133308858945 5040112293726099981644209)
              ·
                refine ⟨3780084220294574986233157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040112293726099981644209 3780084220294574986233157)
                ·
                  refine ⟨708765791305232809918717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3780084220294574986233157 708765791305232809918717)
                  ·
                    refine ⟨265787171739462303719519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708765791305232809918717 265787171739462303719519)
                    ·
                      rfl

theorem cell22_776428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_776428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776428 prefixEnd_776428 := by exact prefixLift 776428
  have htrace : WordTrace (prefixWord ++ tailWord_776428) baseStart_776428 baseEnd_776428 := by
    simpa [prefixWord, tailWord_776428, baseEnd_776428] using wordTrace_append hprefix tailTrace_776428
  have hstable : (prefixWord ++ tailWord_776428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776428).length < 2 ^ (prefixWord ++ tailWord_776428).sum := by decide
  have hdescent : baseEnd_776428 < baseStart_776428 := by decide
  rcases family_descends (prefixWord ++ tailWord_776428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776462 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_776462 : Nat := 118140960795 + 776462 * 2 ^ 59
def prefixEnd_776462 : Nat := 4983230072969 + 3 ^ 40 * 776462 * 2
def baseEnd_776462 : Nat := 265798810634297548369415

theorem tailTrace_776462 : CollatzResearch.WordTrace tailWord_776462 prefixEnd_776462 265798810634297548369415 := by
  unfold tailWord_776462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539986964127282249644455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18879930475345505331437093 3539986964127282249644455)
  ·
    refine ⟨5309980446190923374466683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3539986964127282249644455 5309980446190923374466683)
    ·
      refine ⟨7964970669286385061700025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5309980446190923374466683 7964970669286385061700025)
      ·
        refine ⟨5973728001964788796275019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7964970669286385061700025 5973728001964788796275019)
        ·
          refine ⟨8960592002947183194412529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973728001964788796275019 8960592002947183194412529)
          ·
            refine ⟨6720444002210387395809397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8960592002947183194412529 6720444002210387395809397)
            ·
              refine ⟨630041625207223818357131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6720444002210387395809397 630041625207223818357131)
              ·
                refine ⟨945062437810835727535697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630041625207223818357131 945062437810835727535697)
                ·
                  refine ⟨708796828358126795651773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 945062437810835727535697 708796828358126795651773)
                  ·
                    refine ⟨265798810634297548369415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 708796828358126795651773 265798810634297548369415)
                    ·
                      rfl

theorem cell22_776462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_776462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776462 prefixEnd_776462 := by exact prefixLift 776462
  have htrace : WordTrace (prefixWord ++ tailWord_776462) baseStart_776462 baseEnd_776462 := by
    simpa [prefixWord, tailWord_776462, baseEnd_776462] using wordTrace_append hprefix tailTrace_776462
  have hstable : (prefixWord ++ tailWord_776462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776462).length < 2 ^ (prefixWord ++ tailWord_776462).sum := by decide
  have hdescent : baseEnd_776462 < baseStart_776462 := by decide
  rcases family_descends (prefixWord ++ tailWord_776462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776520 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_776520 : Nat := 118140960795 + 776520 * 2 ^ 59
def prefixEnd_776520 : Nat := 4983230072969 + 3 ^ 40 * 776520 * 2
def baseEnd_776520 : Nat := 88606221739868243473079

theorem tailTrace_776520 : CollatzResearch.WordTrace tailWord_776520 prefixEnd_776520 88606221739868243473079 := by
  unfold tailWord_776520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161005573404066951383507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18881340764538755935178009 14161005573404066951383507)
  ·
    refine ⟨21241508360106100427075261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14161005573404066951383507 21241508360106100427075261)
    ·
      refine ⟨7965565635039787660153223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21241508360106100427075261 7965565635039787660153223)
      ·
        refine ⟨11948348452559681490229835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965565635039787660153223 11948348452559681490229835)
        ·
          refine ⟨17922522678839522235344753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948348452559681490229835 17922522678839522235344753)
          ·
            refine ⟨13441892009129641676508565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17922522678839522235344753 13441892009129641676508565)
            ·
              refine ⟨630088687927951953586339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13441892009129641676508565 630088687927951953586339)
              ·
                refine ⟨945133031891927930379509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630088687927951953586339 945133031891927930379509)
                ·
                  refine ⟨88606221739868243473079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945133031891927930379509 88606221739868243473079)
                  ·
                    rfl

theorem cell22_776520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_776520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776520 prefixEnd_776520 := by exact prefixLift 776520
  have htrace : WordTrace (prefixWord ++ tailWord_776520) baseStart_776520 baseEnd_776520 := by
    simpa [prefixWord, tailWord_776520, baseEnd_776520] using wordTrace_append hprefix tailTrace_776520
  have hstable : (prefixWord ++ tailWord_776520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776520).length < 2 ^ (prefixWord ++ tailWord_776520).sum := by decide
  have hdescent : baseEnd_776520 < baseStart_776520 := by decide
  rcases family_descends (prefixWord ++ tailWord_776520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776580 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_776580 : Nat := 118140960795 + 776580 * 2 ^ 59
def prefixEnd_776580 : Nat := 4983230072969 + 3 ^ 40 * 776580 * 2
def baseEnd_776580 : Nat := 265839204445784573919053

theorem tailTrace_776580 : CollatzResearch.WordTrace tailWord_776580 prefixEnd_776580 265839204445784573919053 := by
  unfold tailWord_776580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14162099763295382074975597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18882799684393842766634129 14162099763295382074975597)
  ·
    refine ⟨5310787411235768278115849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14162099763295382074975597 5310787411235768278115849)
    ·
      refine ⟨3983090558426826208586887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310787411235768278115849 3983090558426826208586887)
      ·
        refine ⟨5974635837640239312880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983090558426826208586887 5974635837640239312880331)
        ·
          refine ⟨8961953756460358969320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974635837640239312880331 8961953756460358969320497)
          ·
            refine ⟨6721465317345269226990373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8961953756460358969320497 6721465317345269226990373)
            ·
              refine ⟨1260274747002237980060695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6721465317345269226990373 1260274747002237980060695)
              ·
                refine ⟨1890412120503356970091043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260274747002237980060695 1890412120503356970091043)
                ·
                  refine ⟨2835618180755035455136565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890412120503356970091043 2835618180755035455136565)
                  ·
                    refine ⟨265839204445784573919053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2835618180755035455136565 265839204445784573919053)
                    ·
                      rfl

theorem cell22_776580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_776580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776580 prefixEnd_776580 := by exact prefixLift 776580
  have htrace : WordTrace (prefixWord ++ tailWord_776580) baseStart_776580 baseEnd_776580 := by
    simpa [prefixWord, tailWord_776580, baseEnd_776580] using wordTrace_append hprefix tailTrace_776580
  have hstable : (prefixWord ++ tailWord_776580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776580).length < 2 ^ (prefixWord ++ tailWord_776580).sum := by decide
  have hdescent : baseEnd_776580 < baseStart_776580 := by decide
  rcases family_descends (prefixWord ++ tailWord_776580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776644 : List Nat := [2, 3, 3, 2, 2, 2, 2, 6]
def baseStart_776644 : Nat := 118140960795 + 776644 * 2 ^ 59
def prefixEnd_776644 : Nat := 4983230072969 + 3 ^ 40 * 776644 * 2
def baseEnd_776644 : Nat := 29540123661523304479873

theorem tailTrace_776644 : CollatzResearch.WordTrace tailWord_776644 prefixEnd_776644 29540123661523304479873 := by
  unfold tailWord_776644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163266899179451540140493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18884355865572602053520657 14163266899179451540140493)
  ·
    refine ⟨5311225087192294327552685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14163266899179451540140493 5311225087192294327552685)
    ·
      refine ⟨1991709407697110372832257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5311225087192294327552685 1991709407697110372832257)
      ·
        refine ⟨1493782055772832779624193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991709407697110372832257 1493782055772832779624193)
        ·
          refine ⟨1120336541829624584718145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493782055772832779624193 1120336541829624584718145)
          ·
            refine ⟨840252406372218438538609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120336541829624584718145 840252406372218438538609)
            ·
              refine ⟨630189304779163828903957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840252406372218438538609 630189304779163828903957)
              ·
                refine ⟨29540123661523304479873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 630189304779163828903957 29540123661523304479873)
                ·
                  rfl

theorem cell22_776644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_776644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776644 prefixEnd_776644 := by exact prefixLift 776644
  have htrace : WordTrace (prefixWord ++ tailWord_776644) baseStart_776644 baseEnd_776644 := by
    simpa [prefixWord, tailWord_776644, baseEnd_776644] using wordTrace_append hprefix tailTrace_776644
  have hstable : (prefixWord ++ tailWord_776644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776644).length < 2 ^ (prefixWord ++ tailWord_776644).sum := by decide
  have hdescent : baseEnd_776644 < baseStart_776644 := by decide
  rcases family_descends (prefixWord ++ tailWord_776644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776715 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_776715 : Nat := 118140960795 + 776715 * 2 ^ 59
def prefixEnd_776715 : Nat := 4983230072969 + 3 ^ 40 * 776715 * 2
def baseEnd_776715 : Nat := 265885417704689221793639

theorem tailTrace_776715 : CollatzResearch.WordTrace tailWord_776715 prefixEnd_776715 265885417704689221793639 := by
  unfold tailWord_776715
  simp only [CollatzResearch.WordTrace]
  refine ⟨28329123381101682206115599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18886082254067788137410399 28329123381101682206115599)
  ·
    refine ⟨42493685071652523309173399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28329123381101682206115599 42493685071652523309173399)
    ·
      refine ⟨63740527607478784963760099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42493685071652523309173399 63740527607478784963760099)
      ·
        refine ⟨95610791411218177445640149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63740527607478784963760099 95610791411218177445640149)
        ·
          refine ⟨2240877923700426033882191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95610791411218177445640149 2240877923700426033882191)
          ·
            refine ⟨3361316885550639050823287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240877923700426033882191 3361316885550639050823287)
            ·
              refine ⟨5041975328325958576234931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361316885550639050823287 5041975328325958576234931)
              ·
                refine ⟨7562962992488937864352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041975328325958576234931 7562962992488937864352397)
                ·
                  refine ⟨2836111122183351699132149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7562962992488937864352397 2836111122183351699132149)
                  ·
                    refine ⟨265885417704689221793639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2836111122183351699132149 265885417704689221793639)
                    ·
                      rfl

theorem cell22_776715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_776715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776715 prefixEnd_776715 := by exact prefixLift 776715
  have htrace : WordTrace (prefixWord ++ tailWord_776715) baseStart_776715 baseEnd_776715 := by
    simpa [prefixWord, tailWord_776715, baseEnd_776715] using wordTrace_append hprefix tailTrace_776715
  have hstable : (prefixWord ++ tailWord_776715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776715).length < 2 ^ (prefixWord ++ tailWord_776715).sum := by decide
  have hdescent : baseEnd_776715 < baseStart_776715 := by decide
  rcases family_descends (prefixWord ++ tailWord_776715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776762 : List Nat := [3, 1, 1, 1, 3, 4, 3, 6]
def baseStart_776762 : Nat := 118140960795 + 776762 * 2 ^ 59
def prefixEnd_776762 : Nat := 4983230072969 + 3 ^ 40 * 776762 * 2
def baseEnd_776762 : Nat := 29544611862799640652055

theorem tailTrace_776762 : CollatzResearch.WordTrace tailWord_776762 prefixEnd_776762 29544611862799640652055 := by
  unfold tailWord_776762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082709402982852308269135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18887225074620939488717693 7082709402982852308269135)
  ·
    refine ⟨10624064104474278462403703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7082709402982852308269135 10624064104474278462403703)
    ·
      refine ⟨15936096156711417693605555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10624064104474278462403703 15936096156711417693605555)
      ·
        refine ⟨23904144235067126540408333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936096156711417693605555 23904144235067126540408333)
        ·
          refine ⟨8964054088150172452653125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23904144235067126540408333 8964054088150172452653125)
          ·
            refine ⟨1680760141528157334872461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8964054088150172452653125 1680760141528157334872461)
            ·
              refine ⟨630285053073059000577173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1680760141528157334872461 630285053073059000577173)
              ·
                refine ⟨29544611862799640652055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 630285053073059000577173 29544611862799640652055)
                ·
                  rfl

theorem cell22_776762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_776762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776762 prefixEnd_776762 := by exact prefixLift 776762
  have htrace : WordTrace (prefixWord ++ tailWord_776762) baseStart_776762 baseEnd_776762 := by
    simpa [prefixWord, tailWord_776762, baseEnd_776762] using wordTrace_append hprefix tailTrace_776762
  have hstable : (prefixWord ++ tailWord_776762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776762).length < 2 ^ (prefixWord ++ tailWord_776762).sum := by decide
  have hdescent : baseEnd_776762 < baseStart_776762 := by decide
  rcases family_descends (prefixWord ++ tailWord_776762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776764 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_776764 : Nat := 118140960795 + 776764 * 2 ^ 59
def prefixEnd_776764 : Nat := 4983230072969 + 3 ^ 40 * 776764 * 2
def baseEnd_776764 : Nat := 265902191406069427318489

theorem tailTrace_776764 : CollatzResearch.WordTrace tailWord_776764 prefixEnd_776764 265902191406069427318489 := by
  unfold tailWord_776764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165455278962081787324673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18887273705282775716432897 14165455278962081787324673)
  ·
    refine ⟨10624091459221561340493505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14165455278962081787324673 10624091459221561340493505)
    ·
      refine ⟨7968068594416171005370129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624091459221561340493505 7968068594416171005370129)
      ·
        refine ⟨5976051445812128254027597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7968068594416171005370129 5976051445812128254027597)
        ·
          refine ⟨2241019292179548095260349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5976051445812128254027597 2241019292179548095260349)
          ·
            refine ⟨840382234567330535722631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2241019292179548095260349 840382234567330535722631)
            ·
              refine ⟨1260573351850995803583947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840382234567330535722631 1260573351850995803583947)
              ·
                refine ⟨1890860027776493705375921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260573351850995803583947 1890860027776493705375921)
                ·
                  refine ⟨1418145020832370279031941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890860027776493705375921 1418145020832370279031941)
                  ·
                    refine ⟨265902191406069427318489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418145020832370279031941 265902191406069427318489)
                    ·
                      rfl

theorem cell22_776764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_776764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776764 prefixEnd_776764 := by exact prefixLift 776764
  have htrace : WordTrace (prefixWord ++ tailWord_776764) baseStart_776764 baseEnd_776764 := by
    simpa [prefixWord, tailWord_776764, baseEnd_776764] using wordTrace_append hprefix tailTrace_776764
  have hstable : (prefixWord ++ tailWord_776764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776764).length < 2 ^ (prefixWord ++ tailWord_776764).sum := by decide
  have hdescent : baseEnd_776764 < baseStart_776764 := by decide
  rcases family_descends (prefixWord ++ tailWord_776764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776835 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 8]
def baseStart_776835 : Nat := 118140960795 + 776835 * 2 ^ 59
def prefixEnd_776835 : Nat := 4983230072969 + 3 ^ 40 * 776835 * 2
def baseEnd_776835 : Nat := 88642165385682969597757

theorem tailTrace_776835 : CollatzResearch.WordTrace tailWord_776835 prefixEnd_776835 88642165385682969597757 := by
  unfold tailWord_776835
  simp only [CollatzResearch.WordTrace]
  refine ⟨28333500140666942700483959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18889000093777961800322639 28333500140666942700483959)
  ·
    refine ⟨42500250211000414050725939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28333500140666942700483959 42500250211000414050725939)
    ·
      refine ⟨63750375316500621076088909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42500250211000414050725939 63750375316500621076088909)
      ·
        refine ⟨23906390743687732903533341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63750375316500621076088909 23906390743687732903533341)
        ·
          refine ⟨8964896528882899838825003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23906390743687732903533341 8964896528882899838825003)
          ·
            refine ⟨13447344793324349758237505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964896528882899838825003 13447344793324349758237505)
            ·
              refine ⟨10085508594993262318678129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13447344793324349758237505 10085508594993262318678129)
              ·
                refine ⟨7564131446244946739008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10085508594993262318678129 7564131446244946739008597)
                ·
                  refine ⟨88642165385682969597757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7564131446244946739008597 88642165385682969597757)
                  ·
                    rfl

theorem cell22_776835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_776835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776835 prefixEnd_776835 := by exact prefixLift 776835
  have htrace : WordTrace (prefixWord ++ tailWord_776835) baseStart_776835 baseEnd_776835 := by
    simpa [prefixWord, tailWord_776835, baseEnd_776835] using wordTrace_append hprefix tailTrace_776835
  have hstable : (prefixWord ++ tailWord_776835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776835).length < 2 ^ (prefixWord ++ tailWord_776835).sum := by decide
  have hdescent : baseEnd_776835 < baseStart_776835 := by decide
  rcases family_descends (prefixWord ++ tailWord_776835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776858 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_776858 : Nat := 118140960795 + 776858 * 2 ^ 59
def prefixEnd_776858 : Nat := 4983230072969 + 3 ^ 40 * 776858 * 2
def baseEnd_776858 : Nat := 88644789842361505156067

theorem tailTrace_776858 : CollatzResearch.WordTrace tailWord_776858 prefixEnd_776858 88644789842361505156067 := by
  unfold tailWord_776858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083584754895904407142807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18889559346389078419047485 7083584754895904407142807)
  ·
    refine ⟨10625377132343856610714211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7083584754895904407142807 10625377132343856610714211)
    ·
      refine ⟨15938065698515784916071317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10625377132343856610714211 15938065698515784916071317)
      ·
        refine ⟨747096829617927417940843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15938065698515784916071317 747096829617927417940843)
        ·
          refine ⟨1120645244426891126911265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747096829617927417940843 1120645244426891126911265)
          ·
            refine ⟨840483933320168345183449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120645244426891126911265 840483933320168345183449)
            ·
              refine ⟨630362949990126258887587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840483933320168345183449 630362949990126258887587)
              ·
                refine ⟨945544424985189388331381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630362949990126258887587 945544424985189388331381)
                ·
                  refine ⟨88644789842361505156067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945544424985189388331381 88644789842361505156067)
                  ·
                    rfl

theorem cell22_776858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_776858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776858 prefixEnd_776858 := by exact prefixLift 776858
  have htrace : WordTrace (prefixWord ++ tailWord_776858) baseStart_776858 baseEnd_776858 := by
    simpa [prefixWord, tailWord_776858, baseEnd_776858] using wordTrace_append hprefix tailTrace_776858
  have hstable : (prefixWord ++ tailWord_776858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776858).length < 2 ^ (prefixWord ++ tailWord_776858).sum := by decide
  have hdescent : baseEnd_776858 < baseStart_776858 := by decide
  rcases family_descends (prefixWord ++ tailWord_776858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776867 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 6, 3]
def baseStart_776867 : Nat := 118140960795 + 776867 * 2 ^ 59
def prefixEnd_776867 : Nat := 4983230072969 + 3 ^ 40 * 776867 * 2
def baseEnd_776867 : Nat := 265937450411011491993173

theorem tailTrace_776867 : CollatzResearch.WordTrace tailWord_776867 prefixEnd_776867 265937450411011491993173 := by
  unfold tailWord_776867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28334667276551012165648855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18889778184367341443765903 28334667276551012165648855)
  ·
    refine ⟨42502000914826518248473283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28334667276551012165648855 42502000914826518248473283)
    ·
      refine ⟨63753001372239777372709925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42502000914826518248473283 63753001372239777372709925)
      ·
        refine ⟨11953687757294958257383111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63753001372239777372709925 11953687757294958257383111)
        ·
          refine ⟨17930531635942437386074667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11953687757294958257383111 17930531635942437386074667)
          ·
            refine ⟨26895797453913656079112001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17930531635942437386074667 26895797453913656079112001)
            ·
              refine ⟨20171848090435242059334001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26895797453913656079112001 20171848090435242059334001)
              ·
                refine ⟨15128886067826431544500501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20171848090435242059334001 15128886067826431544500501)
                ·
                  refine ⟨709166534429363978648461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15128886067826431544500501 709166534429363978648461)
                  ·
                    refine ⟨265937450411011491993173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709166534429363978648461 265937450411011491993173)
                    ·
                      rfl

theorem cell22_776867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 3].length) (baseStart_776867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776867 prefixEnd_776867 := by exact prefixLift 776867
  have htrace : WordTrace (prefixWord ++ tailWord_776867) baseStart_776867 baseEnd_776867 := by
    simpa [prefixWord, tailWord_776867, baseEnd_776867] using wordTrace_append hprefix tailTrace_776867
  have hstable : (prefixWord ++ tailWord_776867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776867).length < 2 ^ (prefixWord ++ tailWord_776867).sum := by decide
  have hdescent : baseEnd_776867 < baseStart_776867 := by decide
  rcases family_descends (prefixWord ++ tailWord_776867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776871 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 3, 4]
def baseStart_776871 : Nat := 118140960795 + 776871 * 2 ^ 59
def prefixEnd_776871 : Nat := 4983230072969 + 3 ^ 40 * 776871 * 2
def baseEnd_776871 : Nat := 265938819692756814893161

theorem tailTrace_776871 : CollatzResearch.WordTrace tailWord_776871 prefixEnd_776871 265938819692756814893161 := by
  unfold tailWord_776871
  simp only [CollatzResearch.WordTrace]
  refine ⟨28334813168536520848794467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18889875445691013899196311 28334813168536520848794467)
  ·
    refine ⟨42502219752804781273191701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28334813168536520848794467 42502219752804781273191701)
    ·
      refine ⟨1992291550912724122180861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42502219752804781273191701 1992291550912724122180861)
      ·
        refine ⟨747109331592271545817823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1992291550912724122180861 747109331592271545817823)
        ·
          refine ⟨1120663997388407318726735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747109331592271545817823 1120663997388407318726735)
          ·
            refine ⟨1680995996082610978090103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120663997388407318726735 1680995996082610978090103)
            ·
              refine ⟨2521493994123916467135155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680995996082610978090103 2521493994123916467135155)
              ·
                refine ⟨3782240991185874700702733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521493994123916467135155 3782240991185874700702733)
                ·
                  refine ⟨1418340371694703012763525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3782240991185874700702733 1418340371694703012763525)
                  ·
                    refine ⟨265938819692756814893161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418340371694703012763525 265938819692756814893161)
                    ·
                      rfl

theorem cell22_776871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_776871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776871 prefixEnd_776871 := by exact prefixLift 776871
  have htrace : WordTrace (prefixWord ++ tailWord_776871) baseStart_776871 baseEnd_776871 := by
    simpa [prefixWord, tailWord_776871, baseEnd_776871] using wordTrace_append hprefix tailTrace_776871
  have hstable : (prefixWord ++ tailWord_776871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776871).length < 2 ^ (prefixWord ++ tailWord_776871).sum := by decide
  have hdescent : baseEnd_776871 < baseStart_776871 := by decide
  rcases family_descends (prefixWord ++ tailWord_776871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776929 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_776929 : Nat := 118140960795 + 776929 * 2 ^ 59
def prefixEnd_776929 : Nat := 4983230072969 + 3 ^ 40 * 776929 * 2
def baseEnd_776929 : Nat := 265958674278063996942983

theorem tailTrace_776929 : CollatzResearch.WordTrace tailWord_776929 prefixEnd_776929 265958674278063996942983 := by
  unfold tailWord_776929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28336928602326396754405841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18891285734884264502937227 28336928602326396754405841)
  ·
    refine ⟨21252696451744797565804381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28336928602326396754405841 21252696451744797565804381)
    ·
      refine ⟨7969761169404299087176643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21252696451744797565804381 7969761169404299087176643)
      ·
        refine ⟨11954641754106448630764965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969761169404299087176643 11954641754106448630764965)
        ·
          refine ⟨2241495328894959118268431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11954641754106448630764965 2241495328894959118268431)
          ·
            refine ⟨3362242993342438677402647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241495328894959118268431 3362242993342438677402647)
            ·
              refine ⟨5043364490013658016103971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362242993342438677402647 5043364490013658016103971)
              ·
                refine ⟨7565046735020487024155957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043364490013658016103971 7565046735020487024155957)
                ·
                  refine ⟨709223131408170658514621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7565046735020487024155957 709223131408170658514621)
                  ·
                    refine ⟨265958674278063996942983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709223131408170658514621 265958674278063996942983)
                    ·
                      rfl

theorem cell22_776929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_776929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776929 prefixEnd_776929 := by exact prefixLift 776929
  have htrace : WordTrace (prefixWord ++ tailWord_776929) baseStart_776929 baseEnd_776929 := by
    simpa [prefixWord, tailWord_776929, baseEnd_776929] using wordTrace_append hprefix tailTrace_776929
  have hstable : (prefixWord ++ tailWord_776929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776929).length < 2 ^ (prefixWord ++ tailWord_776929).sum := by decide
  have hdescent : baseEnd_776929 < baseStart_776929 := by decide
  rcases family_descends (prefixWord ++ tailWord_776929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776957 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_776957 : Nat := 118140960795 + 776957 * 2 ^ 59
def prefixEnd_776957 : Nat := 4983230072969 + 3 ^ 40 * 776957 * 2
def baseEnd_776957 : Nat := 265968259250281257242897

theorem tailTrace_776957 : CollatzResearch.WordTrace tailWord_776957 prefixEnd_776957 265968259250281257242897 := by
  unfold tailWord_776957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337949846224957536425125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18891966564149971690950083 28337949846224957536425125)
  ·
    refine ⟨5313365596167179538079711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28337949846224957536425125 5313365596167179538079711)
    ·
      refine ⟨7970048394250769307119567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313365596167179538079711 7970048394250769307119567)
      ·
        refine ⟨11955072591376153960679351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7970048394250769307119567 11955072591376153960679351)
        ·
          refine ⟨17932608887064230941019027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11955072591376153960679351 17932608887064230941019027)
          ·
            refine ⟨26898913330596346411528541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17932608887064230941019027 26898913330596346411528541)
            ·
              refine ⟨10087092498973629904323203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26898913330596346411528541 10087092498973629904323203)
              ·
                refine ⟨15130638748460444856484805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10087092498973629904323203 15130638748460444856484805)
                ·
                  refine ⟨2836994765336333410590901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15130638748460444856484805 2836994765336333410590901)
                  ·
                    refine ⟨265968259250281257242897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2836994765336333410590901 265968259250281257242897)
                    ·
                      rfl

theorem cell22_776957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_776957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_776957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_776957 prefixEnd_776957 := by exact prefixLift 776957
  have htrace : WordTrace (prefixWord ++ tailWord_776957) baseStart_776957 baseEnd_776957 := by
    simpa [prefixWord, tailWord_776957, baseEnd_776957] using wordTrace_append hprefix tailTrace_776957
  have hstable : (prefixWord ++ tailWord_776957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776957).length < 2 ^ (prefixWord ++ tailWord_776957).sum := by decide
  have hdescent : baseEnd_776957 < baseStart_776957 := by decide
  rcases family_descends (prefixWord ++ tailWord_776957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777070 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_777070 : Nat := 118140960795 + 777070 * 2 ^ 59
def prefixEnd_777070 : Nat := 4983230072969 + 3 ^ 40 * 777070 * 2
def baseEnd_777070 : Nat := 266006941459586629167551

theorem tailTrace_777070 : CollatzResearch.WordTrace tailWord_777070 prefixEnd_777070 266006941459586629167551 := by
  unfold tailWord_777070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542758911851947229411083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18894714196543718556859109 3542758911851947229411083)
  ·
    refine ⟨5314138367777920844116625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542758911851947229411083 5314138367777920844116625)
    ·
      refine ⟨3985603775833440633087469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5314138367777920844116625 3985603775833440633087469)
      ·
        refine ⟨1494601415937540237407801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3985603775833440633087469 1494601415937540237407801)
        ·
          refine ⟨1120951061953155178055851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494601415937540237407801 1120951061953155178055851)
          ·
            refine ⟨1681426592929732767083777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120951061953155178055851 1681426592929732767083777)
            ·
              refine ⟨1261069944697299575312833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681426592929732767083777 1261069944697299575312833)
              ·
                refine ⟨945802458522974681484625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261069944697299575312833 945802458522974681484625)
                ·
                  refine ⟨709351843892231011113469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 945802458522974681484625 709351843892231011113469)
                  ·
                    refine ⟨266006941459586629167551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709351843892231011113469 266006941459586629167551)
                    ·
                      rfl

theorem cell22_777070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_777070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777070 prefixEnd_777070 := by exact prefixLift 777070
  have htrace : WordTrace (prefixWord ++ tailWord_777070) baseStart_777070 baseEnd_777070 := by
    simpa [prefixWord, tailWord_777070, baseEnd_777070] using wordTrace_append hprefix tailTrace_777070
  have hstable : (prefixWord ++ tailWord_777070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777070).length < 2 ^ (prefixWord ++ tailWord_777070).sum := by decide
  have hdescent : baseEnd_777070 < baseStart_777070 := by decide
  rcases family_descends (prefixWord ++ tailWord_777070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777098 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_777098 : Nat := 118140960795 + 777098 * 2 ^ 59
def prefixEnd_777098 : Nat := 4983230072969 + 3 ^ 40 * 777098 * 2
def baseEnd_777098 : Nat := 266016526431803889467465

theorem tailTrace_777098 : CollatzResearch.WordTrace tailWord_777098 prefixEnd_777098 266016526431803889467465 := by
  unfold tailWord_777098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7085773134678534654326987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18895395025809425744871965 7085773134678534654326987)
  ·
    refine ⟨10628659702017801981490481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7085773134678534654326987 10628659702017801981490481)
    ·
      refine ⟨7971494776513351486117861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10628659702017801981490481 7971494776513351486117861)
      ·
        refine ⟨1494655270596253403647099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7971494776513351486117861 1494655270596253403647099)
        ·
          refine ⟨2241982905894380105470649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494655270596253403647099 2241982905894380105470649)
          ·
            refine ⟨1681487179420785079102987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241982905894380105470649 1681487179420785079102987)
            ·
              refine ⟨2522230769131177618654481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681487179420785079102987 2522230769131177618654481)
              ·
                refine ⟨1891673076848383213990861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522230769131177618654481 1891673076848383213990861)
                ·
                  refine ⟨709377403818143705246573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1891673076848383213990861 709377403818143705246573)
                  ·
                    refine ⟨266016526431803889467465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709377403818143705246573 266016526431803889467465)
                    ·
                      rfl

theorem cell22_777098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_777098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777098 prefixEnd_777098 := by exact prefixLift 777098
  have htrace : WordTrace (prefixWord ++ tailWord_777098) baseStart_777098 baseEnd_777098 := by
    simpa [prefixWord, tailWord_777098, baseEnd_777098] using wordTrace_append hprefix tailTrace_777098
  have hstable : (prefixWord ++ tailWord_777098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777098).length < 2 ^ (prefixWord ++ tailWord_777098).sum := by decide
  have hdescent : baseEnd_777098 < baseStart_777098 := by decide
  rcases family_descends (prefixWord ++ tailWord_777098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777169 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_777169 : Nat := 118140960795 + 777169 * 2 ^ 59
def prefixEnd_777169 : Nat := 4983230072969 + 3 ^ 40 * 777169 * 2
def baseEnd_777169 : Nat := 266040831182783370942247

theorem tailTrace_777169 : CollatzResearch.WordTrace tailWord_777169 prefixEnd_777169 266040831182783370942247 := by
  unfold tailWord_777169
  simp only [CollatzResearch.WordTrace]
  refine ⟨28345682121456917743142561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18897121414304611828761707 28345682121456917743142561)
  ·
    refine ⟨21259261591092688307356921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28345682121456917743142561 21259261591092688307356921)
    ·
      refine ⟨15944446193319516230517691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21259261591092688307356921 15944446193319516230517691)
      ·
        refine ⟨23916669289979274345776537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15944446193319516230517691 23916669289979274345776537)
        ·
          refine ⟨17937501967484455759332403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23916669289979274345776537 17937501967484455759332403)
          ·
            refine ⟨26906252951226683638998605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17937501967484455759332403 26906252951226683638998605)
            ·
              refine ⟨10089844856710006364624477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26906252951226683638998605 10089844856710006364624477)
              ·
                refine ⟨3783691821266252386734179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10089844856710006364624477 3783691821266252386734179)
                ·
                  refine ⟨5675537731899378580101269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783691821266252386734179 5675537731899378580101269)
                  ·
                    refine ⟨266040831182783370942247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5675537731899378580101269 266040831182783370942247)
                    ·
                      rfl

theorem cell22_777169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_777169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777169 prefixEnd_777169 := by exact prefixLift 777169
  have htrace : WordTrace (prefixWord ++ tailWord_777169) baseStart_777169 baseEnd_777169 := by
    simpa [prefixWord, tailWord_777169, baseEnd_777169] using wordTrace_append hprefix tailTrace_777169
  have hstable : (prefixWord ++ tailWord_777169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777169).length < 2 ^ (prefixWord ++ tailWord_777169).sum := by decide
  have hdescent : baseEnd_777169 < baseStart_777169 := by decide
  rcases family_descends (prefixWord ++ tailWord_777169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777201 : List Nat := [1, 2, 2, 2, 4, 2, 2, 7]
def baseStart_777201 : Nat := 118140960795 + 777201 * 2 ^ 59
def prefixEnd_777201 : Nat := 4983230072969 + 3 ^ 40 * 777201 * 2
def baseEnd_777201 : Nat := 29561309492971772682461

theorem tailTrace_777201 : CollatzResearch.WordTrace tailWord_777201 prefixEnd_777201 29561309492971772682461 := by
  unfold tailWord_777201
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346849257340987208307457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18897899504893991472204971 28346849257340987208307457)
  ·
    refine ⟨21260136943005740406230593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28346849257340987208307457 21260136943005740406230593)
    ·
      refine ⟨15945102707254305304672945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21260136943005740406230593 15945102707254305304672945)
      ·
        refine ⟨11958827030440728978504709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15945102707254305304672945 11958827030440728978504709)
        ·
          refine ⟨2242280068207636683469633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11958827030440728978504709 2242280068207636683469633)
          ·
            refine ⟨1681710051155727512602225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242280068207636683469633 1681710051155727512602225)
            ·
              refine ⟨1261282538366795634451669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681710051155727512602225 1261282538366795634451669)
              ·
                refine ⟨29561309492971772682461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1261282538366795634451669 29561309492971772682461)
                ·
                  rfl

theorem cell22_777201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 7].length) (baseStart_777201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777201 prefixEnd_777201 := by exact prefixLift 777201
  have htrace : WordTrace (prefixWord ++ tailWord_777201) baseStart_777201 baseEnd_777201 := by
    simpa [prefixWord, tailWord_777201, baseEnd_777201] using wordTrace_append hprefix tailTrace_777201
  have hstable : (prefixWord ++ tailWord_777201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777201).length < 2 ^ (prefixWord ++ tailWord_777201).sum := by decide
  have hdescent : baseEnd_777201 < baseStart_777201 := by decide
  rcases family_descends (prefixWord ++ tailWord_777201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777308 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_777308 : Nat := 118140960795 + 777308 * 2 ^ 59
def prefixEnd_777308 : Nat := 4983230072969 + 3 ^ 40 * 777308 * 2
def baseEnd_777308 : Nat := 88696137907811113905607

theorem tailTrace_777308 : CollatzResearch.WordTrace tailWord_777308 prefixEnd_777308 88696137907811113905607 := by
  unfold tailWord_777308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175375933976672241226289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18900501245302229654968385 14175375933976672241226289)
  ·
    refine ⟨10631531950482504180919717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14175375933976672241226289 10631531950482504180919717)
    ·
      refine ⟨1993412240715469533922447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10631531950482504180919717 1993412240715469533922447)
      ·
        refine ⟨2990118361073204300883671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993412240715469533922447 2990118361073204300883671)
        ·
          refine ⟨4485177541609806451325507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990118361073204300883671 4485177541609806451325507)
          ·
            refine ⟨6727766312414709676988261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485177541609806451325507 6727766312414709676988261)
            ·
              refine ⟨1261456183577758064435299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6727766312414709676988261 1261456183577758064435299)
              ·
                refine ⟨1892184275366637096652949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261456183577758064435299 1892184275366637096652949)
                ·
                  refine ⟨88696137907811113905607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1892184275366637096652949 88696137907811113905607)
                  ·
                    rfl

theorem cell22_777308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_777308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777308 prefixEnd_777308 := by exact prefixLift 777308
  have htrace : WordTrace (prefixWord ++ tailWord_777308) baseStart_777308 baseEnd_777308 := by
    simpa [prefixWord, tailWord_777308, baseEnd_777308] using wordTrace_append hprefix tailTrace_777308
  have hstable : (prefixWord ++ tailWord_777308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777308).length < 2 ^ (prefixWord ++ tailWord_777308).sum := by decide
  have hdescent : baseEnd_777308 < baseStart_777308 := by decide
  rcases family_descends (prefixWord ++ tailWord_777308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777321 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_777321 : Nat := 118140960795 + 777321 * 2 ^ 59
def prefixEnd_777321 : Nat := 4983230072969 + 3 ^ 40 * 777321 * 2
def baseEnd_777321 : Nat := 266092863889105641141781

theorem tailTrace_777321 : CollatzResearch.WordTrace tailWord_777321 prefixEnd_777321 266092863889105641141781 := by
  unfold tailWord_777321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28351226016906247702675817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18900817344604165135117211 28351226016906247702675817)
  ·
    refine ⟨21263419512679685777006863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28351226016906247702675817 21263419512679685777006863)
    ·
      refine ⟨31895129269019528665510295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21263419512679685777006863 31895129269019528665510295)
      ·
        refine ⟨47842693903529292998265443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31895129269019528665510295 47842693903529292998265443)
        ·
          refine ⟨71764040855293939497398165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47842693903529292998265443 71764040855293939497398165)
          ·
            refine ⟨3363939415091903413940539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71764040855293939497398165 3363939415091903413940539)
            ·
              refine ⟨5045909122637855120910809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363939415091903413940539 5045909122637855120910809)
              ·
                refine ⟨3784431841978391340683107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045909122637855120910809 3784431841978391340683107)
                ·
                  refine ⟨5676647762967587011024661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784431841978391340683107 5676647762967587011024661)
                  ·
                    refine ⟨266092863889105641141781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5676647762967587011024661 266092863889105641141781)
                    ·
                      rfl

theorem cell22_777321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_777321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777321 prefixEnd_777321 := by exact prefixLift 777321
  have htrace : WordTrace (prefixWord ++ tailWord_777321) baseStart_777321 baseEnd_777321 := by
    simpa [prefixWord, tailWord_777321, baseEnd_777321] using wordTrace_append hprefix tailTrace_777321
  have hstable : (prefixWord ++ tailWord_777321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777321).length < 2 ^ (prefixWord ++ tailWord_777321).sum := by decide
  have hdescent : baseEnd_777321 < baseStart_777321 := by decide
  rcases family_descends (prefixWord ++ tailWord_777321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777374 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_777374 : Nat := 118140960795 + 777374 * 2 ^ 59
def prefixEnd_777374 : Nat := 4983230072969 + 3 ^ 40 * 777374 * 2
def baseEnd_777374 : Nat := 266111006872231169566619

theorem tailTrace_777374 : CollatzResearch.WordTrace tailWord_777374 prefixEnd_777374 266111006872231169566619 := by
  unfold tailWord_777374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544144885714279719294397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18902106057142825169570117 3544144885714279719294397)
  ·
    refine ⟨1329054332142854894735399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3544144885714279719294397 1329054332142854894735399)
    ·
      refine ⟨1993581498214282342103099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329054332142854894735399 1993581498214282342103099)
      ·
        refine ⟨2990372247321423513154649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993581498214282342103099 2990372247321423513154649)
        ·
          refine ⟨2242779185491067634865987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990372247321423513154649 2242779185491067634865987)
          ·
            refine ⟨3364168778236601452298981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242779185491067634865987 3364168778236601452298981)
            ·
              refine ⟨630781645919362772306059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3364168778236601452298981 630781645919362772306059)
              ·
                refine ⟨946172468879044158459089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630781645919362772306059 946172468879044158459089)
                ·
                  refine ⟨709629351659283118844317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946172468879044158459089 709629351659283118844317)
                  ·
                    refine ⟨266111006872231169566619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709629351659283118844317 266111006872231169566619)
                    ·
                      rfl

theorem cell22_777374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_777374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777374 prefixEnd_777374 := by exact prefixLift 777374
  have htrace : WordTrace (prefixWord ++ tailWord_777374) baseStart_777374 baseEnd_777374 := by
    simpa [prefixWord, tailWord_777374, baseEnd_777374] using wordTrace_append hprefix tailTrace_777374
  have hstable : (prefixWord ++ tailWord_777374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777374).length < 2 ^ (prefixWord ++ tailWord_777374).sum := by decide
  have hdescent : baseEnd_777374 < baseStart_777374 := by decide
  rcases family_descends (prefixWord ++ tailWord_777374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777475 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 4, 3]
def baseStart_777475 : Nat := 118140960795 + 777475 * 2 ^ 59
def prefixEnd_777475 : Nat := 4983230072969 + 3 ^ 40 * 777475 * 2
def baseEnd_777475 : Nat := 266145581236300572791309

theorem tailTrace_777475 : CollatzResearch.WordTrace tailWord_777475 prefixEnd_777475 266145581236300572791309 := by
  unfold tailWord_777475
  simp only [CollatzResearch.WordTrace]
  refine ⟨28356842858348332003781879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18904561905565554669187919 28356842858348332003781879)
  ·
    refine ⟨42535264287522498005672819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28356842858348332003781879 42535264287522498005672819)
    ·
      refine ⟨63802896431283747008509229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42535264287522498005672819 63802896431283747008509229)
      ·
        refine ⟨23926086161731405128190961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63802896431283747008509229 23926086161731405128190961)
        ·
          refine ⟨17944564621298553846143221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23926086161731405128190961 17944564621298553846143221)
          ·
            refine ⟨1682302933246739423075927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17944564621298553846143221 1682302933246739423075927)
            ·
              refine ⟨2523454399870109134613891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682302933246739423075927 2523454399870109134613891)
              ·
                refine ⟨3785181599805163701920837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523454399870109134613891 3785181599805163701920837)
                ·
                  refine ⟨709721549963468194110157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3785181599805163701920837 709721549963468194110157)
                  ·
                    refine ⟨266145581236300572791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709721549963468194110157 266145581236300572791309)
                    ·
                      rfl

theorem cell22_777475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].length) (baseStart_777475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777475 prefixEnd_777475 := by exact prefixLift 777475
  have htrace : WordTrace (prefixWord ++ tailWord_777475) baseStart_777475 baseEnd_777475 := by
    simpa [prefixWord, tailWord_777475, baseEnd_777475] using wordTrace_append hprefix tailTrace_777475
  have hstable : (prefixWord ++ tailWord_777475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777475).length < 2 ^ (prefixWord ++ tailWord_777475).sum := by decide
  have hdescent : baseEnd_777475 < baseStart_777475 := by decide
  rcases family_descends (prefixWord ++ tailWord_777475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777550 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_777550 : Nat := 118140960795 + 777550 * 2 ^ 59
def prefixEnd_777550 : Nat := 4983230072969 + 3 ^ 40 * 777550 * 2
def baseEnd_777550 : Nat := 88723751756341792388693

theorem tailTrace_777550 : CollatzResearch.WordTrace tailWord_777550 prefixEnd_777550 88723751756341792388693 := by
  unfold tailWord_777550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544947291634577476595263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18906385555384413208508069 3544947291634577476595263)
  ·
    refine ⟨5317420937451866214892895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3544947291634577476595263 5317420937451866214892895)
    ·
      refine ⟨7976131406177799322339343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5317420937451866214892895 7976131406177799322339343)
      ·
        refine ⟨11964197109266698983509015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976131406177799322339343 11964197109266698983509015)
        ·
          refine ⟨17946295663900048475263523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11964197109266698983509015 17946295663900048475263523)
          ·
            refine ⟨26919443495850072712895285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17946295663900048475263523 26919443495850072712895285)
            ·
              refine ⟨2523697827735944316833933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26919443495850072712895285 2523697827735944316833933)
              ·
                refine ⟨946386685400979118812725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2523697827735944316833933 946386685400979118812725)
                ·
                  refine ⟨88723751756341792388693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 946386685400979118812725 88723751756341792388693)
                  ·
                    rfl

theorem cell22_777550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_777550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777550 prefixEnd_777550 := by exact prefixLift 777550
  have htrace : WordTrace (prefixWord ++ tailWord_777550) baseStart_777550 baseEnd_777550 := by
    simpa [prefixWord, tailWord_777550, baseEnd_777550] using wordTrace_append hprefix tailTrace_777550
  have hstable : (prefixWord ++ tailWord_777550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777550).length < 2 ^ (prefixWord ++ tailWord_777550).sum := by decide
  have hdescent : baseEnd_777550 < baseStart_777550 := by decide
  rcases family_descends (prefixWord ++ tailWord_777550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777558 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_777558 : Nat := 118140960795 + 777558 * 2 ^ 59
def prefixEnd_777558 : Nat := 4983230072969 + 3 ^ 40 * 777558 * 2
def baseEnd_777558 : Nat := 266173993832516022966055

theorem tailTrace_777558 : CollatzResearch.WordTrace tailWord_777558 prefixEnd_777558 266173993832516022966055 := by
  unfold tailWord_777558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772491882315477323690833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18906580078031758119368885 1772491882315477323690833)
  ·
    refine ⟨1329368911736607992768125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1772491882315477323690833 1329368911736607992768125)
    ·
      refine ⟨498513341901227997288047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1329368911736607992768125 498513341901227997288047)
      ·
        refine ⟨747770012851841995932071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498513341901227997288047 747770012851841995932071)
        ·
          refine ⟨1121655019277762993898107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747770012851841995932071 1121655019277762993898107)
          ·
            refine ⟨1682482528916644490847161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121655019277762993898107 1682482528916644490847161)
            ·
              refine ⟨1261861896687483368135371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682482528916644490847161 1261861896687483368135371)
              ·
                refine ⟨1892792845031225052203057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261861896687483368135371 1892792845031225052203057)
                ·
                  refine ⟨1419594633773418789152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892792845031225052203057 1419594633773418789152293)
                  ·
                    refine ⟨266173993832516022966055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1419594633773418789152293 266173993832516022966055)
                    ·
                      rfl

theorem cell22_777558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_777558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777558 prefixEnd_777558 := by exact prefixLift 777558
  have htrace : WordTrace (prefixWord ++ tailWord_777558) baseStart_777558 baseEnd_777558 := by
    simpa [prefixWord, tailWord_777558, baseEnd_777558] using wordTrace_append hprefix tailTrace_777558
  have hstable : (prefixWord ++ tailWord_777558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777558).length < 2 ^ (prefixWord ++ tailWord_777558).sum := by decide
  have hdescent : baseEnd_777558 < baseStart_777558 := by decide
  rcases family_descends (prefixWord ++ tailWord_777558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777625 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_777625 : Nat := 118140960795 + 777625 * 2 ^ 59
def prefixEnd_777625 : Nat := 4983230072969 + 3 ^ 40 * 777625 * 2
def baseEnd_777625 : Nat := 266196929301750181540849

theorem tailTrace_777625 : CollatzResearch.WordTrace tailWord_777625 prefixEnd_777625 266196929301750181540849 := by
  unfold tailWord_777625
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362313807804907621742329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18908209205203271747828219 28362313807804907621742329)
  ·
    refine ⟨21271735355853680716306747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28362313807804907621742329 21271735355853680716306747)
    ·
      refine ⟨31907603033780521074460121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21271735355853680716306747 31907603033780521074460121)
      ·
        refine ⟨23930702275335390805845091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31907603033780521074460121 23930702275335390805845091)
        ·
          refine ⟨35896053413003086208767637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23930702275335390805845091 35896053413003086208767637)
          ·
            refine ⟨1682627503734519666035983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35896053413003086208767637 1682627503734519666035983)
            ·
              refine ⟨2523941255601779499053975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682627503734519666035983 2523941255601779499053975)
              ·
                refine ⟨3785911883402669248580963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523941255601779499053975 3785911883402669248580963)
                ·
                  refine ⟨5678867825104003872871445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785911883402669248580963 5678867825104003872871445)
                  ·
                    refine ⟨266196929301750181540849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5678867825104003872871445 266196929301750181540849)
                    ·
                      rfl

theorem cell22_777625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_777625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777625 prefixEnd_777625 := by exact prefixLift 777625
  have htrace : WordTrace (prefixWord ++ tailWord_777625) baseStart_777625 baseEnd_777625 := by
    simpa [prefixWord, tailWord_777625, baseEnd_777625] using wordTrace_append hprefix tailTrace_777625
  have hstable : (prefixWord ++ tailWord_777625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777625).length < 2 ^ (prefixWord ++ tailWord_777625).sum := by decide
  have hdescent : baseEnd_777625 < baseStart_777625 := by decide
  rcases family_descends (prefixWord ++ tailWord_777625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777629 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 4]
def baseStart_777629 : Nat := 118140960795 + 777629 * 2 ^ 59
def prefixEnd_777629 : Nat := 4983230072969 + 3 ^ 40 * 777629 * 2
def baseEnd_777629 : Nat := 88732766194498501480279

theorem tailTrace_777629 : CollatzResearch.WordTrace tailWord_777629 prefixEnd_777629 88732766194498501480279 := by
  unfold tailWord_777629
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362459699790416304887941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18908306466526944203258627 28362459699790416304887941)
  ·
    refine ⟨5317961193710703057166489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28362459699790416304887941 5317961193710703057166489)
    ·
      refine ⟨3988470895283027292874867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5317961193710703057166489 3988470895283027292874867)
      ·
        refine ⟨5982706342924540939312301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988470895283027292874867 5982706342924540939312301)
        ·
          refine ⟨2243514878596702852242113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5982706342924540939312301 2243514878596702852242113)
          ·
            refine ⟨1682636158947527139181585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243514878596702852242113 1682636158947527139181585)
            ·
              refine ⟨1261977119210645354386189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682636158947527139181585 1261977119210645354386189)
              ·
                refine ⟨473241419703992007894821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261977119210645354386189 473241419703992007894821)
                ·
                  refine ⟨88732766194498501480279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473241419703992007894821 88732766194498501480279)
                  ·
                    rfl

theorem cell22_777629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_777629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777629 prefixEnd_777629 := by exact prefixLift 777629
  have htrace : WordTrace (prefixWord ++ tailWord_777629) baseStart_777629 baseEnd_777629 := by
    simpa [prefixWord, tailWord_777629, baseEnd_777629] using wordTrace_append hprefix tailTrace_777629
  have hstable : (prefixWord ++ tailWord_777629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777629).length < 2 ^ (prefixWord ++ tailWord_777629).sum := by decide
  have hdescent : baseEnd_777629 < baseStart_777629 := by decide
  rcases family_descends (prefixWord ++ tailWord_777629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777672 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_777672 : Nat := 118140960795 + 777672 * 2 ^ 59
def prefixEnd_777672 : Nat := 4983230072969 + 3 ^ 40 * 777672 * 2
def baseEnd_777672 : Nat := 266213018362257725615705

theorem tailTrace_777672 : CollatzResearch.WordTrace tailWord_777672 prefixEnd_777672 266213018362257725615705 := by
  unfold tailWord_777672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182014019317317324351635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18909352025756423099135513 14182014019317317324351635)
  ·
    refine ⟨21273021028975975986527453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182014019317317324351635 21273021028975975986527453)
    ·
      refine ⟨7977382885865990994947795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21273021028975975986527453 7977382885865990994947795)
      ·
        refine ⟨11966074328798986492421693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977382885865990994947795 11966074328798986492421693)
        ·
          refine ⟨4487277873299619934658135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11966074328798986492421693 4487277873299619934658135)
          ·
            refine ⟨6730916809949429901987203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487277873299619934658135 6730916809949429901987203)
            ·
              refine ⟨10096375214924144852980805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730916809949429901987203 10096375214924144852980805)
              ·
                refine ⟨1893070352798277159933901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10096375214924144852980805 1893070352798277159933901)
                ·
                  refine ⟨709901382299353934975213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1893070352798277159933901 709901382299353934975213)
                  ·
                    refine ⟨266213018362257725615705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709901382299353934975213 266213018362257725615705)
                    ·
                      rfl

theorem cell22_777672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_777672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777672 prefixEnd_777672 := by exact prefixLift 777672
  have htrace : WordTrace (prefixWord ++ tailWord_777672) baseStart_777672 baseEnd_777672 := by
    simpa [prefixWord, tailWord_777672, baseEnd_777672] using wordTrace_append hprefix tailTrace_777672
  have hstable : (prefixWord ++ tailWord_777672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777672).length < 2 ^ (prefixWord ++ tailWord_777672).sum := by decide
  have hdescent : baseEnd_777672 < baseStart_777672 := by decide
  rcases family_descends (prefixWord ++ tailWord_777672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777685 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 9]
def baseStart_777685 : Nat := 118140960795 + 777685 * 2 ^ 59
def prefixEnd_777685 : Nat := 4983230072969 + 3 ^ 40 * 777685 * 2
def baseEnd_777685 : Nat := 88739156175976675013555

theorem tailTrace_777685 : CollatzResearch.WordTrace tailWord_777685 prefixEnd_777685 88739156175976675013555 := by
  unfold tailWord_777685
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364502187587537868926509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18909668125058358579284339 28364502187587537868926509)
  ·
    refine ⟨10636688320345326700847441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28364502187587537868926509 10636688320345326700847441)
    ·
      refine ⟨7977516240258995025635581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10636688320345326700847441 7977516240258995025635581)
      ·
        refine ⟨2991568590097123134613343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7977516240258995025635581 2991568590097123134613343)
        ·
          refine ⟨4487352885145684701920015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991568590097123134613343 4487352885145684701920015)
          ·
            refine ⟨6731029327718527052880023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487352885145684701920015 6731029327718527052880023)
            ·
              refine ⟨10096543991577790579320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731029327718527052880023 10096543991577790579320035)
              ·
                refine ⟨15144815987366685868980053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096543991577790579320035 15144815987366685868980053)
                ·
                  refine ⟨88739156175976675013555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15144815987366685868980053 88739156175976675013555)
                  ·
                    rfl

theorem cell22_777685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_777685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777685 prefixEnd_777685 := by exact prefixLift 777685
  have htrace : WordTrace (prefixWord ++ tailWord_777685) baseStart_777685 baseEnd_777685 := by
    simpa [prefixWord, tailWord_777685, baseEnd_777685] using wordTrace_append hprefix tailTrace_777685
  have hstable : (prefixWord ++ tailWord_777685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777685).length < 2 ^ (prefixWord ++ tailWord_777685).sum := by decide
  have hdescent : baseEnd_777685 < baseStart_777685 := by decide
  rcases family_descends (prefixWord ++ tailWord_777685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777700 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_777700 : Nat := 118140960795 + 777700 * 2 ^ 59
def prefixEnd_777700 : Nat := 4983230072969 + 3 ^ 40 * 777700 * 2
def baseEnd_777700 : Nat := 266222603334474985915619

theorem tailTrace_777700 : CollatzResearch.WordTrace tailWord_777700 prefixEnd_777700 266222603334474985915619 := by
  unfold tailWord_777700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182524641266597715361277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18910032855022130287148369 14182524641266597715361277)
  ·
    refine ⟨5318446740474974143260479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14182524641266597715361277 5318446740474974143260479)
    ·
      refine ⟨7977670110712461214890719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318446740474974143260479 7977670110712461214890719)
      ·
        refine ⟨11966505166068691822336079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977670110712461214890719 11966505166068691822336079)
        ·
          refine ⟨17949757749103037733504119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966505166068691822336079 17949757749103037733504119)
          ·
            refine ⟨26924636623654556600256179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949757749103037733504119 26924636623654556600256179)
            ·
              refine ⟨40386954935481834900384269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26924636623654556600256179 40386954935481834900384269)
              ·
                refine ⟨15145108100805688087644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40386954935481834900384269 15145108100805688087644101)
                ·
                  refine ⟨2839707768901066516433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15145108100805688087644101 2839707768901066516433269)
                  ·
                    refine ⟨266222603334474985915619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2839707768901066516433269 266222603334474985915619)
                    ·
                      rfl

theorem cell22_777700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_777700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777700 prefixEnd_777700 := by exact prefixLift 777700
  have htrace : WordTrace (prefixWord ++ tailWord_777700) baseStart_777700 baseEnd_777700 := by
    simpa [prefixWord, tailWord_777700, baseEnd_777700] using wordTrace_append hprefix tailTrace_777700
  have hstable : (prefixWord ++ tailWord_777700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777700).length < 2 ^ (prefixWord ++ tailWord_777700).sum := by decide
  have hdescent : baseEnd_777700 < baseStart_777700 := by decide
  rcases family_descends (prefixWord ++ tailWord_777700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777706 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_777706 : Nat := 118140960795 + 777706 * 2 ^ 59
def prefixEnd_777706 : Nat := 4983230072969 + 3 ^ 40 * 777706 * 2
def baseEnd_777706 : Nat := 266224657257092970265601

theorem tailTrace_777706 : CollatzResearch.WordTrace tailWord_777706 prefixEnd_777706 266224657257092970265601 := by
  unfold tailWord_777706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091317030127864613860243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18910178747007638970293981 7091317030127864613860243)
  ·
    refine ⟨10636975545191796920790365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7091317030127864613860243 10636975545191796920790365)
    ·
      refine ⟨3988865829446923845296387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10636975545191796920790365 3988865829446923845296387)
      ·
        refine ⟨5983298744170385767944581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988865829446923845296387 5983298744170385767944581)
        ·
          refine ⟨1121868514531947331489609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5983298744170385767944581 1121868514531947331489609)
          ·
            refine ⟨841401385898960498617207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121868514531947331489609 841401385898960498617207)
            ·
              refine ⟨1262102078848440747925811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841401385898960498617207 1262102078848440747925811)
              ·
                refine ⟨1893153118272661121888717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262102078848440747925811 1893153118272661121888717)
                ·
                  refine ⟨709932419352247920708269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1893153118272661121888717 709932419352247920708269)
                  ·
                    refine ⟨266224657257092970265601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709932419352247920708269 266224657257092970265601)
                    ·
                      rfl

theorem cell22_777706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_777706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777706 prefixEnd_777706 := by exact prefixLift 777706
  have htrace : WordTrace (prefixWord ++ tailWord_777706) baseStart_777706 baseEnd_777706 := by
    simpa [prefixWord, tailWord_777706, baseEnd_777706] using wordTrace_append hprefix tailTrace_777706
  have hstable : (prefixWord ++ tailWord_777706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777706).length < 2 ^ (prefixWord ++ tailWord_777706).sum := by decide
  have hdescent : baseEnd_777706 < baseStart_777706 := by decide
  rcases family_descends (prefixWord ++ tailWord_777706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777779 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 2, 3]
def baseStart_777779 : Nat := 118140960795 + 777779 * 2 ^ 59
def prefixEnd_777779 : Nat := 4983230072969 + 3 ^ 40 * 777779 * 2
def baseEnd_777779 : Nat := 266249646648945113190377

theorem tailTrace_777779 : CollatzResearch.WordTrace tailWord_777779 prefixEnd_777779 266249646648945113190377 := by
  unfold tailWord_777779
  simp only [CollatzResearch.WordTrace]
  refine ⟨28367930649246991922848391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18911953766164661281898927 28367930649246991922848391)
  ·
    refine ⟨42551895973870487884272587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28367930649246991922848391 42551895973870487884272587)
    ·
      refine ⟨63827843960805731826408881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42551895973870487884272587 63827843960805731826408881)
      ·
        refine ⟨47870882970604298869806661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63827843960805731826408881 47870882970604298869806661)
        ·
          refine ⟨8975790556988306038088749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47870882970604298869806661 8975790556988306038088749)
          ·
            refine ⟨3365921458870614764283281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8975790556988306038088749 3365921458870614764283281)
            ·
              refine ⟨2524441094152961073212461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365921458870614764283281 2524441094152961073212461)
              ·
                refine ⟨946665410307360402454673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2524441094152961073212461 946665410307360402454673)
                ·
                  refine ⟨709999057730520301841005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946665410307360402454673 709999057730520301841005)
                  ·
                    refine ⟨266249646648945113190377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 709999057730520301841005 266249646648945113190377)
                    ·
                      rfl

theorem cell22_777779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 3].length) (baseStart_777779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777779 prefixEnd_777779 := by exact prefixLift 777779
  have htrace : WordTrace (prefixWord ++ tailWord_777779) baseStart_777779 baseEnd_777779 := by
    simpa [prefixWord, tailWord_777779, baseEnd_777779] using wordTrace_append hprefix tailTrace_777779
  have hstable : (prefixWord ++ tailWord_777779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777779).length < 2 ^ (prefixWord ++ tailWord_777779).sum := by decide
  have hdescent : baseEnd_777779 < baseStart_777779 := by decide
  rcases family_descends (prefixWord ++ tailWord_777779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777807 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 7, 3]
def baseStart_777807 : Nat := 118140960795 + 777807 * 2 ^ 59
def prefixEnd_777807 : Nat := 4983230072969 + 3 ^ 40 * 777807 * 2
def baseEnd_777807 : Nat := 266259231621162373490291

theorem tailTrace_777807 : CollatzResearch.WordTrace tailWord_777807 prefixEnd_777807 266259231621162373490291 := by
  unfold tailWord_777807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28368951893145552704867675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18912634595430368469911783 28368951893145552704867675)
  ·
    refine ⟨42553427839718329057301513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28368951893145552704867675 42553427839718329057301513)
    ·
      refine ⟨31915070879788746792976135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42553427839718329057301513 31915070879788746792976135)
      ·
        refine ⟨47872606319683120189464203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31915070879788746792976135 47872606319683120189464203)
        ·
          refine ⟨71808909479524680284196305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47872606319683120189464203 71808909479524680284196305)
          ·
            refine ⟨53856682109643510213147229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71808909479524680284196305 53856682109643510213147229)
            ·
              refine ⟨20196255791116316329930211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53856682109643510213147229 20196255791116316329930211)
              ·
                refine ⟨30294383686674474494895317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196255791116316329930211 30294383686674474494895317)
                ·
                  refine ⟨710024617656432995974109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30294383686674474494895317 710024617656432995974109)
                  ·
                    refine ⟨266259231621162373490291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710024617656432995974109 266259231621162373490291)
                    ·
                      rfl

theorem cell22_777807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_777807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777807 prefixEnd_777807 := by exact prefixLift 777807
  have htrace : WordTrace (prefixWord ++ tailWord_777807) baseStart_777807 baseEnd_777807 := by
    simpa [prefixWord, tailWord_777807, baseEnd_777807] using wordTrace_append hprefix tailTrace_777807
  have hstable : (prefixWord ++ tailWord_777807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777807).length < 2 ^ (prefixWord ++ tailWord_777807).sum := by decide
  have hdescent : baseEnd_777807 < baseStart_777807 := by decide
  rcases family_descends (prefixWord ++ tailWord_777807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777912 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_777912 : Nat := 118140960795 + 777912 * 2 ^ 59
def prefixEnd_777912 : Nat := 4983230072969 + 3 ^ 40 * 777912 * 2
def baseEnd_777912 : Nat := 266295175266977099614969

theorem tailTrace_777912 : CollatzResearch.WordTrace tailWord_777912 prefixEnd_777912 266295175266977099614969 := by
  unfold tailWord_777912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14186390778882577818719995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18915187705176770424959993 14186390778882577818719995)
  ·
    refine ⟨21279586168323866728079993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14186390778882577818719995 21279586168323866728079993)
    ·
      refine ⟨15959689626242900046059995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21279586168323866728079993 15959689626242900046059995)
      ·
        refine ⟨23939534439364350069089993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959689626242900046059995 23939534439364350069089993)
        ·
          refine ⟨17954650829523262551817495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23939534439364350069089993 17954650829523262551817495)
          ·
            refine ⟨26931976244284893827726243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17954650829523262551817495 26931976244284893827726243)
            ·
              refine ⟨40397964366427340741589365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26931976244284893827726243 40397964366427340741589365)
              ·
                refine ⟨3787309159352563194524003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40397964366427340741589365 3787309159352563194524003)
                ·
                  refine ⟨5680963739028844791786005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787309159352563194524003 5680963739028844791786005)
                  ·
                    refine ⟨266295175266977099614969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5680963739028844791786005 266295175266977099614969)
                    ·
                      rfl

theorem cell22_777912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_777912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777912 prefixEnd_777912 := by exact prefixLift 777912
  have htrace : WordTrace (prefixWord ++ tailWord_777912) baseStart_777912 baseEnd_777912 := by
    simpa [prefixWord, tailWord_777912, baseEnd_777912] using wordTrace_append hprefix tailTrace_777912
  have hstable : (prefixWord ++ tailWord_777912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777912).length < 2 ^ (prefixWord ++ tailWord_777912).sum := by decide
  have hdescent : baseEnd_777912 < baseStart_777912 := by decide
  rcases family_descends (prefixWord ++ tailWord_777912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777914 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_777914 : Nat := 118140960795 + 777914 * 2 ^ 59
def prefixEnd_777914 : Nat := 4983230072969 + 3 ^ 40 * 777914 * 2
def baseEnd_777914 : Nat := 266295859907849761064963

theorem tailTrace_777914 : CollatzResearch.WordTrace tailWord_777914 prefixEnd_777914 266295859907849761064963 := by
  unfold tailWord_777914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093213625939477494753199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18915236335838606652675197 7093213625939477494753199)
  ·
    refine ⟨10639820438909216242129799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093213625939477494753199 10639820438909216242129799)
    ·
      refine ⟨15959730658363824363194699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639820438909216242129799 15959730658363824363194699)
      ·
        refine ⟨23939595987545736544792049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959730658363824363194699 23939595987545736544792049)
        ·
          refine ⟨17954696990659302408594037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23939595987545736544792049 17954696990659302408594037)
          ·
            refine ⟨1683252842874309600805691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17954696990659302408594037 1683252842874309600805691)
            ·
              refine ⟨2524879264311464401208537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683252842874309600805691 2524879264311464401208537)
              ·
                refine ⟨1893659448233598300906403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524879264311464401208537 1893659448233598300906403)
                ·
                  refine ⟨2840489172350397451359605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893659448233598300906403 2840489172350397451359605)
                  ·
                    refine ⟨266295859907849761064963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2840489172350397451359605 266295859907849761064963)
                    ·
                      rfl

theorem cell22_777914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_777914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777914 prefixEnd_777914 := by exact prefixLift 777914
  have htrace : WordTrace (prefixWord ++ tailWord_777914) baseStart_777914 baseEnd_777914 := by
    simpa [prefixWord, tailWord_777914, baseEnd_777914] using wordTrace_append hprefix tailTrace_777914
  have hstable : (prefixWord ++ tailWord_777914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777914).length < 2 ^ (prefixWord ++ tailWord_777914).sum := by decide
  have hdescent : baseEnd_777914 < baseStart_777914 := by decide
  rcases family_descends (prefixWord ++ tailWord_777914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777918 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_777918 : Nat := 118140960795 + 777918 * 2 ^ 59
def prefixEnd_777918 : Nat := 4983230072969 + 3 ^ 40 * 777918 * 2
def baseEnd_777918 : Nat := 266297229189595083964951

theorem tailTrace_777918 : CollatzResearch.WordTrace tailWord_777918 prefixEnd_777918 266297229189595083964951 := by
  unfold tailWord_777918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546625049467927332769801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18915333597162279108105605 3546625049467927332769801)
  ·
    refine ⟨2659968787100945499577351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3546625049467927332769801 2659968787100945499577351)
    ·
      refine ⟨3989953180651418249366027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659968787100945499577351 3989953180651418249366027)
      ·
        refine ⟨5984929770977127374049041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989953180651418249366027 5984929770977127374049041)
        ·
          refine ⟨4488697328232845530536781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5984929770977127374049041 4488697328232845530536781)
          ·
            refine ⟨1683261498087317073951293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488697328232845530536781 1683261498087317073951293)
            ·
              refine ⟨631223061782743902731735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683261498087317073951293 631223061782743902731735)
              ·
                refine ⟨946834592674115854097603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631223061782743902731735 946834592674115854097603)
                ·
                  refine ⟨1420251889011173781146405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946834592674115854097603 1420251889011173781146405)
                  ·
                    refine ⟨266297229189595083964951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420251889011173781146405 266297229189595083964951)
                    ·
                      rfl

theorem cell22_777918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_777918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777918 prefixEnd_777918 := by exact prefixLift 777918
  have htrace : WordTrace (prefixWord ++ tailWord_777918) baseStart_777918 baseEnd_777918 := by
    simpa [prefixWord, tailWord_777918, baseEnd_777918] using wordTrace_append hprefix tailTrace_777918
  have hstable : (prefixWord ++ tailWord_777918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777918).length < 2 ^ (prefixWord ++ tailWord_777918).sum := by decide
  have hdescent : baseEnd_777918 < baseStart_777918 := by decide
  rcases family_descends (prefixWord ++ tailWord_777918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777948 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_777948 : Nat := 118140960795 + 777948 * 2 ^ 59
def prefixEnd_777948 : Nat := 4983230072969 + 3 ^ 40 * 777948 * 2
def baseEnd_777948 : Nat := 266307498802685005714859

theorem tailTrace_777948 : CollatzResearch.WordTrace tailWord_777948 prefixEnd_777948 266307498802685005714859 := by
  unfold tailWord_777948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187047292817366892875249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18916063057089822523833665 14187047292817366892875249)
  ·
    refine ⟨10640285469613025169656437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14187047292817366892875249 10640285469613025169656437)
    ·
      refine ⟨997526762776221109655291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10640285469613025169656437 997526762776221109655291)
      ·
        refine ⟨1496290144164331664482937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997526762776221109655291 1496290144164331664482937)
        ·
          refine ⟨1122217608123248748362203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496290144164331664482937 1122217608123248748362203)
          ·
            refine ⟨1683326412184873122543305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122217608123248748362203 1683326412184873122543305)
            ·
              refine ⟨1262494809138654841907479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683326412184873122543305 1262494809138654841907479)
              ·
                refine ⟨1893742213707982262861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262494809138654841907479 1893742213707982262861219)
                ·
                  refine ⟨2840613320561973394291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893742213707982262861219 2840613320561973394291829)
                  ·
                    refine ⟨266307498802685005714859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2840613320561973394291829 266307498802685005714859)
                    ·
                      rfl

theorem cell22_777948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_777948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777948 prefixEnd_777948 := by exact prefixLift 777948
  have htrace : WordTrace (prefixWord ++ tailWord_777948) baseStart_777948 baseEnd_777948 := by
    simpa [prefixWord, tailWord_777948, baseEnd_777948] using wordTrace_append hprefix tailTrace_777948
  have hstable : (prefixWord ++ tailWord_777948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777948).length < 2 ^ (prefixWord ++ tailWord_777948).sum := by decide
  have hdescent : baseEnd_777948 < baseStart_777948 := by decide
  rcases family_descends (prefixWord ++ tailWord_777948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777982 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_777982 : Nat := 118140960795 + 777982 * 2 ^ 59
def prefixEnd_777982 : Nat := 4983230072969 + 3 ^ 40 * 777982 * 2
def baseEnd_777982 : Nat := 266319137697520250364755

theorem tailTrace_777982 : CollatzResearch.WordTrace tailWord_777982 prefixEnd_777982 266319137697520250364755 := by
  unfold tailWord_777982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546916833438944699061025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18916889778341038394992133 3546916833438944699061025)
  ·
    refine ⟨2660187625079208524295769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3546916833438944699061025 2660187625079208524295769)
    ·
      refine ⟨1995140718809406393221827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2660187625079208524295769 1995140718809406393221827)
      ·
        refine ⟨2992711078214109589832741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995140718809406393221827 2992711078214109589832741)
        ·
          refine ⟨561133327165145548093639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2992711078214109589832741 561133327165145548093639)
          ·
            refine ⟨841699990747718322140459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561133327165145548093639 841699990747718322140459)
            ·
              refine ⟨1262549986121577483210689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841699990747718322140459 1262549986121577483210689)
              ·
                refine ⟨946912489591183112408017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262549986121577483210689 946912489591183112408017)
                ·
                  refine ⟨710184367193387334306013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946912489591183112408017 710184367193387334306013)
                  ·
                    refine ⟨266319137697520250364755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710184367193387334306013 266319137697520250364755)
                    ·
                      rfl

theorem cell22_777982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_777982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_777982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_777982 prefixEnd_777982 := by exact prefixLift 777982
  have htrace : WordTrace (prefixWord ++ tailWord_777982) baseStart_777982 baseEnd_777982 := by
    simpa [prefixWord, tailWord_777982, baseEnd_777982] using wordTrace_append hprefix tailTrace_777982
  have hstable : (prefixWord ++ tailWord_777982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777982).length < 2 ^ (prefixWord ++ tailWord_777982).sum := by decide
  have hdescent : baseEnd_777982 < baseStart_777982 := by decide
  rcases family_descends (prefixWord ++ tailWord_777982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778019 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_778019 : Nat := 118140960795 + 778019 * 2 ^ 59
def prefixEnd_778019 : Nat := 4983230072969 + 3 ^ 40 * 778019 * 2
def baseEnd_778019 : Nat := 266331803553664487189641

theorem tailTrace_778019 : CollatzResearch.WordTrace tailWord_778019 prefixEnd_778019 266331803553664487189641 := by
  unfold tailWord_778019
  simp only [CollatzResearch.WordTrace]
  refine ⟨28376684168377512911585111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18917789445585008607723407 28376684168377512911585111)
  ·
    refine ⟨42565026252566269367377667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28376684168377512911585111 42565026252566269367377667)
    ·
      refine ⟨63847539378849404051066501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42565026252566269367377667 63847539378849404051066501)
      ·
        refine ⟨11971413633534263259574969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63847539378849404051066501 11971413633534263259574969)
        ·
          refine ⟨8978560225150697444681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971413633534263259574969 8978560225150697444681227)
          ·
            refine ⟨13467840337726046167021841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978560225150697444681227 13467840337726046167021841)
            ·
              refine ⟨10100880253294534625266381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13467840337726046167021841 10100880253294534625266381)
              ·
                refine ⟨3787830094985450484474893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10100880253294534625266381 3787830094985450484474893)
                ·
                  refine ⟨1420436285619543931678085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3787830094985450484474893 1420436285619543931678085)
                  ·
                    refine ⟨266331803553664487189641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420436285619543931678085 266331803553664487189641)
                    ·
                      rfl

theorem cell22_778019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_778019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778019 prefixEnd_778019 := by exact prefixLift 778019
  have htrace : WordTrace (prefixWord ++ tailWord_778019) baseStart_778019 baseEnd_778019 := by
    simpa [prefixWord, tailWord_778019, baseEnd_778019] using wordTrace_append hprefix tailTrace_778019
  have hstable : (prefixWord ++ tailWord_778019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778019).length < 2 ^ (prefixWord ++ tailWord_778019).sum := by decide
  have hdescent : baseEnd_778019 < baseStart_778019 := by decide
  rcases family_descends (prefixWord ++ tailWord_778019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778051 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 6]
def baseStart_778051 : Nat := 118140960795 + 778051 * 2 ^ 59
def prefixEnd_778051 : Nat := 4983230072969 + 3 ^ 40 * 778051 * 2
def baseEnd_778051 : Nat := 88780919269209023463181

theorem tailTrace_778051 : CollatzResearch.WordTrace tailWord_778051 prefixEnd_778051 88780919269209023463181 := by
  unfold tailWord_778051
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377851304261582376750007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18918567536174388251166671 28377851304261582376750007)
  ·
    refine ⟨42566776956392373565125011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28377851304261582376750007 42566776956392373565125011)
    ·
      refine ⟨63850165434588560347687517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42566776956392373565125011 63850165434588560347687517)
      ·
        refine ⟨23943812037970710130382819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63850165434588560347687517 23943812037970710130382819)
        ·
          refine ⟨35915718056956065195574229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23943812037970710130382819 35915718056956065195574229)
          ·
            refine ⟨841774641959907778021271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35915718056956065195574229 841774641959907778021271)
            ·
              refine ⟨1262661962939861667031907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841774641959907778021271 1262661962939861667031907)
              ·
                refine ⟨1893992944409792500547861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262661962939861667031907 1893992944409792500547861)
                ·
                  refine ⟨88780919269209023463181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1893992944409792500547861 88780919269209023463181)
                  ·
                    rfl

theorem cell22_778051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].length) (baseStart_778051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778051 prefixEnd_778051 := by exact prefixLift 778051
  have htrace : WordTrace (prefixWord ++ tailWord_778051) baseStart_778051 baseEnd_778051 := by
    simpa [prefixWord, tailWord_778051, baseEnd_778051] using wordTrace_append hprefix tailTrace_778051
  have hstable : (prefixWord ++ tailWord_778051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778051).length < 2 ^ (prefixWord ++ tailWord_778051).sum := by decide
  have hdescent : baseEnd_778051 < baseStart_778051 := by decide
  rcases family_descends (prefixWord ++ tailWord_778051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778064 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_778064 : Nat := 118140960795 + 778064 * 2 ^ 59
def prefixEnd_778064 : Nat := 4983230072969 + 3 ^ 40 * 778064 * 2
def baseEnd_778064 : Nat := 266347207973299369814503

theorem tailTrace_778064 : CollatzResearch.WordTrace tailWord_778064 prefixEnd_778064 266347207973299369814503 := by
  unfold tailWord_778064
  simp only [CollatzResearch.WordTrace]
  refine ⟨14189162726607242798486623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18918883635476323731315497 14189162726607242798486623)
  ·
    refine ⟨21283744089910864197729935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14189162726607242798486623 21283744089910864197729935)
    ·
      refine ⟨31925616134866296296594903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283744089910864197729935 31925616134866296296594903)
      ·
        refine ⟨47888424202299444444892355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31925616134866296296594903 47888424202299444444892355)
        ·
          refine ⟨71832636303449166667338533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47888424202299444444892355 71832636303449166667338533)
          ·
            refine ⟨13468619306896718750125975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71832636303449166667338533 13468619306896718750125975)
            ·
              refine ⟨20202928960345078125188963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13468619306896718750125975 20202928960345078125188963)
              ·
                refine ⟨30304393440517617187783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20202928960345078125188963 30304393440517617187783445)
                ·
                  refine ⟨1420518442524263305677349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30304393440517617187783445 1420518442524263305677349)
                  ·
                    refine ⟨266347207973299369814503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420518442524263305677349 266347207973299369814503)
                    ·
                      rfl

theorem cell22_778064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_778064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778064 prefixEnd_778064 := by exact prefixLift 778064
  have htrace : WordTrace (prefixWord ++ tailWord_778064) baseStart_778064 baseEnd_778064 := by
    simpa [prefixWord, tailWord_778064, baseEnd_778064] using wordTrace_append hprefix tailTrace_778064
  have hstable : (prefixWord ++ tailWord_778064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778064).length < 2 ^ (prefixWord ++ tailWord_778064).sum := by decide
  have hdescent : baseEnd_778064 < baseStart_778064 := by decide
  rcases family_descends (prefixWord ++ tailWord_778064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778079 : List Nat := [1, 1, 2, 3, 1, 4, 2, 8]
def baseStart_778079 : Nat := 118140960795 + 778079 * 2 ^ 59
def prefixEnd_778079 : Nat := 4983230072969 + 3 ^ 40 * 778079 * 2
def baseEnd_778079 : Nat := 29594704753316036743273

theorem tailTrace_778079 : CollatzResearch.WordTrace tailWord_778079 prefixEnd_778079 29594704753316036743273 := by
  unfold tailWord_778079
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378872548160143158769291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18919248365440095439179527 28378872548160143158769291)
  ·
    refine ⟨42568308822240214738153937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28378872548160143158769291 42568308822240214738153937)
    ·
      refine ⟨31926231616680161053615453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42568308822240214738153937 31926231616680161053615453)
      ·
        refine ⟨11972336856255060395105795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31926231616680161053615453 11972336856255060395105795)
        ·
          refine ⟨17958505284382590592658693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972336856255060395105795 17958505284382590592658693)
          ·
            refine ⟨3367219740821735736123505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17958505284382590592658693 3367219740821735736123505)
            ·
              refine ⟨2525414805616301802092629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367219740821735736123505 2525414805616301802092629)
              ·
                refine ⟨29594704753316036743273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2525414805616301802092629 29594704753316036743273)
                ·
                  rfl

theorem cell22_778079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 8].length) (baseStart_778079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778079 prefixEnd_778079 := by exact prefixLift 778079
  have htrace : WordTrace (prefixWord ++ tailWord_778079) baseStart_778079 baseEnd_778079 := by
    simpa [prefixWord, tailWord_778079, baseEnd_778079] using wordTrace_append hprefix tailTrace_778079
  have hstable : (prefixWord ++ tailWord_778079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778079).length < 2 ^ (prefixWord ++ tailWord_778079).sum := by decide
  have hdescent : baseEnd_778079 < baseStart_778079 := by decide
  rcases family_descends (prefixWord ++ tailWord_778079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778081 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_778081 : Nat := 118140960795 + 778081 * 2 ^ 59
def prefixEnd_778081 : Nat := 4983230072969 + 3 ^ 40 * 778081 * 2
def baseEnd_778081 : Nat := 266353027420716992139451

theorem tailTrace_778081 : CollatzResearch.WordTrace tailWord_778081 prefixEnd_778081 266353027420716992139451 := by
  unfold tailWord_778081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378945494152897500342097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18919296996101931666894731 28378945494152897500342097)
  ·
    refine ⟨21284209120614673125256573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28378945494152897500342097 21284209120614673125256573)
    ·
      refine ⟨7981578420230502421971215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21284209120614673125256573 7981578420230502421971215)
      ·
        refine ⟨11972367630345753632956823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7981578420230502421971215 11972367630345753632956823)
        ·
          refine ⟨17958551445518630449435235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972367630345753632956823 17958551445518630449435235)
          ·
            refine ⟨26937827168277945674152853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17958551445518630449435235 26937827168277945674152853)
            ·
              refine ⟨1262710648513028703475915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26937827168277945674152853 1262710648513028703475915)
              ·
                refine ⟨1894065972769543055213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262710648513028703475915 1894065972769543055213873)
                ·
                  refine ⟨1420549479577157291410405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1894065972769543055213873 1420549479577157291410405)
                  ·
                    refine ⟨266353027420716992139451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420549479577157291410405 266353027420716992139451)
                    ·
                      rfl

theorem cell22_778081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_778081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778081 prefixEnd_778081 := by exact prefixLift 778081
  have htrace : WordTrace (prefixWord ++ tailWord_778081) baseStart_778081 baseEnd_778081 := by
    simpa [prefixWord, tailWord_778081, baseEnd_778081] using wordTrace_append hprefix tailTrace_778081
  have hstable : (prefixWord ++ tailWord_778081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778081).length < 2 ^ (prefixWord ++ tailWord_778081).sum := by decide
  have hdescent : baseEnd_778081 < baseStart_778081 := by decide
  rcases family_descends (prefixWord ++ tailWord_778081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778111 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 3, 3]
def baseStart_778111 : Nat := 118140960795 + 778111 * 2 ^ 59
def prefixEnd_778111 : Nat := 4983230072969 + 3 ^ 40 * 778111 * 2
def baseEnd_778111 : Nat := 266363297033806913889359

theorem tailTrace_778111 : CollatzResearch.WordTrace tailWord_778111 prefixEnd_778111 266363297033806913889359 := by
  unfold tailWord_778111
  simp only [CollatzResearch.WordTrace]
  refine ⟨28380039684044212623934187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18920026456029475082622791 28380039684044212623934187)
  ·
    refine ⟨42570059526066318935901281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28380039684044212623934187 42570059526066318935901281)
    ·
      refine ⟨31927544644549739201925961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42570059526066318935901281 31927544644549739201925961)
      ·
        refine ⟨23945658483412304401444471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31927544644549739201925961 23945658483412304401444471)
        ·
          refine ⟨35918487725118456602166707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23945658483412304401444471 35918487725118456602166707)
          ·
            refine ⟨53877731587677684903250061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35918487725118456602166707 53877731587677684903250061)
            ·
              refine ⟨20204149345379131838718773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53877731587677684903250061 20204149345379131838718773)
              ·
                refine ⟨1894139001129293609879885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20204149345379131838718773 1894139001129293609879885)
                ·
                  refine ⟨710302125423485103704957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1894139001129293609879885 710302125423485103704957)
                  ·
                    refine ⟨266363297033806913889359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710302125423485103704957 266363297033806913889359)
                    ·
                      rfl

theorem cell22_778111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_778111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778111 prefixEnd_778111 := by exact prefixLift 778111
  have htrace : WordTrace (prefixWord ++ tailWord_778111) baseStart_778111 baseEnd_778111 := by
    simpa [prefixWord, tailWord_778111, baseEnd_778111] using wordTrace_append hprefix tailTrace_778111
  have hstable : (prefixWord ++ tailWord_778111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778111).length < 2 ^ (prefixWord ++ tailWord_778111).sum := by decide
  have hdescent : baseEnd_778111 < baseStart_778111 := by decide
  rcases family_descends (prefixWord ++ tailWord_778111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778124 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_778124 : Nat := 118140960795 + 778124 * 2 ^ 59
def prefixEnd_778124 : Nat := 4983230072969 + 3 ^ 40 * 778124 * 2
def baseEnd_778124 : Nat := 88789249066493071104773

theorem tailTrace_778124 : CollatzResearch.WordTrace tailWord_778124 prefixEnd_778124 88789249066493071104773 := by
  unfold tailWord_778124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190256916498557922078713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18920342555331410562771617 14190256916498557922078713)
  ·
    refine ⟨10642692687373918441559035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14190256916498557922078713 10642692687373918441559035)
    ·
      refine ⟨15964039031060877662338553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642692687373918441559035 15964039031060877662338553)
      ·
        refine ⟨11973029273295658246753915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15964039031060877662338553 11973029273295658246753915)
        ·
          refine ⟨17959543909943487370130873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973029273295658246753915 17959543909943487370130873)
          ·
            refine ⟨13469657932457615527598155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17959543909943487370130873 13469657932457615527598155)
            ·
              refine ⟨20204486898686423291397233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469657932457615527598155 20204486898686423291397233)
              ·
                refine ⟨15153365174014817468547925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20204486898686423291397233 15153365174014817468547925)
                ·
                  refine ⟨88789249066493071104773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15153365174014817468547925 88789249066493071104773)
                  ·
                    rfl

theorem cell22_778124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_778124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778124 prefixEnd_778124 := by exact prefixLift 778124
  have htrace : WordTrace (prefixWord ++ tailWord_778124) baseStart_778124 baseEnd_778124 := by
    simpa [prefixWord, tailWord_778124, baseEnd_778124] using wordTrace_append hprefix tailTrace_778124
  have hstable : (prefixWord ++ tailWord_778124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778124).length < 2 ^ (prefixWord ++ tailWord_778124).sum := by decide
  have hdescent : baseEnd_778124 < baseStart_778124 := by decide
  rcases family_descends (prefixWord ++ tailWord_778124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778186 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_778186 : Nat := 118140960795 + 778186 * 2 ^ 59
def prefixEnd_778186 : Nat := 4983230072969 + 3 ^ 40 * 778186 * 2
def baseEnd_778186 : Nat := 88796323688843906088043

theorem tailTrace_778186 : CollatzResearch.WordTrace tailWord_778186 prefixEnd_778186 88796323688843906088043 := by
  unfold tailWord_778186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095693789693125108228603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18921850105848333621942941 7095693789693125108228603)
  ·
    refine ⟨10643540684539687662342905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7095693789693125108228603 10643540684539687662342905)
    ·
      refine ⟨7982655513404765746757179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10643540684539687662342905 7982655513404765746757179)
      ·
        refine ⟨11973983270107148620135769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982655513404765746757179 11973983270107148620135769)
        ·
          refine ⟨8980487452580361465101827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11973983270107148620135769 8980487452580361465101827)
          ·
            refine ⟨13470731178870542197652741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8980487452580361465101827 13470731178870542197652741)
            ·
              refine ⟨2525762096038226662059889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13470731178870542197652741 2525762096038226662059889)
              ·
                refine ⟨1894321572028669996544917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525762096038226662059889 1894321572028669996544917)
                ·
                  refine ⟨88796323688843906088043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1894321572028669996544917 88796323688843906088043)
                  ·
                    rfl

theorem cell22_778186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_778186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778186 prefixEnd_778186 := by exact prefixLift 778186
  have htrace : WordTrace (prefixWord ++ tailWord_778186) baseStart_778186 baseEnd_778186 := by
    simpa [prefixWord, tailWord_778186, baseEnd_778186] using wordTrace_append hprefix tailTrace_778186
  have hstable : (prefixWord ++ tailWord_778186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778186).length < 2 ^ (prefixWord ++ tailWord_778186).sum := by decide
  have hdescent : baseEnd_778186 < baseStart_778186 := by decide
  rcases family_descends (prefixWord ++ tailWord_778186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778188 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_778188 : Nat := 118140960795 + 778188 * 2 ^ 59
def prefixEnd_778188 : Nat := 4983230072969 + 3 ^ 40 * 778188 * 2
def baseEnd_778188 : Nat := 266389655707404379714123

theorem tailTrace_778188 : CollatzResearch.WordTrace tailWord_778188 prefixEnd_778188 266389655707404379714123 := by
  unfold tailWord_778188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191424052382627387243609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18921898736510169849658145 14191424052382627387243609)
  ·
    refine ⟨10643568039286970540432707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14191424052382627387243609 10643568039286970540432707)
    ·
      refine ⟨15965352058930455810649061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643568039286970540432707 15965352058930455810649061)
      ·
        refine ⟨2993503511049460464496699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15965352058930455810649061 2993503511049460464496699)
        ·
          refine ⟨4490255266574190696745049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993503511049460464496699 4490255266574190696745049)
          ·
            refine ⟨3367691449930643022558787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490255266574190696745049 3367691449930643022558787)
            ·
              refine ⟨5051537174895964533838181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367691449930643022558787 5051537174895964533838181)
              ·
                refine ⟨947163220292993350094659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5051537174895964533838181 947163220292993350094659)
                ·
                  refine ⟨1420744830439490025141989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947163220292993350094659 1420744830439490025141989)
                  ·
                    refine ⟨266389655707404379714123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420744830439490025141989 266389655707404379714123)
                    ·
                      rfl

theorem cell22_778188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_778188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778188 prefixEnd_778188 := by exact prefixLift 778188
  have htrace : WordTrace (prefixWord ++ tailWord_778188) baseStart_778188 baseEnd_778188 := by
    simpa [prefixWord, tailWord_778188, baseEnd_778188] using wordTrace_append hprefix tailTrace_778188
  have hstable : (prefixWord ++ tailWord_778188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778188).length < 2 ^ (prefixWord ++ tailWord_778188).sum := by decide
  have hdescent : baseEnd_778188 < baseStart_778188 := by decide
  rcases family_descends (prefixWord ++ tailWord_778188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778218 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_778218 : Nat := 118140960795 + 778218 * 2 ^ 59
def prefixEnd_778218 : Nat := 4983230072969 + 3 ^ 40 * 778218 * 2
def baseEnd_778218 : Nat := 266399925320494301464031

theorem tailTrace_778218 : CollatzResearch.WordTrace tailWord_778218 prefixEnd_778218 266399925320494301464031 := by
  unfold tailWord_778218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095985573664142474519827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18922628196437713265386205 7095985573664142474519827)
  ·
    refine ⟨10643978360496213711779741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7095985573664142474519827 10643978360496213711779741)
    ·
      refine ⟨3991491885186080141917403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10643978360496213711779741 3991491885186080141917403)
      ·
        refine ⟨5987237827779120212876105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991491885186080141917403 5987237827779120212876105)
        ·
          refine ⟨4490428370834340159657079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5987237827779120212876105 4490428370834340159657079)
          ·
            refine ⟨6735642556251510239485619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490428370834340159657079 6735642556251510239485619)
            ·
              refine ⟨10103463834377265359228429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735642556251510239485619 10103463834377265359228429)
              ·
                refine ⟨3788798937891474509710661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10103463834377265359228429 3788798937891474509710661)
                ·
                  refine ⟨710399800854651470570749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3788798937891474509710661 710399800854651470570749)
                  ·
                    refine ⟨266399925320494301464031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710399800854651470570749 266399925320494301464031)
                    ·
                      rfl

theorem cell22_778218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_778218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778218 prefixEnd_778218 := by exact prefixLift 778218
  have htrace : WordTrace (prefixWord ++ tailWord_778218) baseStart_778218 baseEnd_778218 := by
    simpa [prefixWord, tailWord_778218, baseEnd_778218] using wordTrace_append hprefix tailTrace_778218
  have hstable : (prefixWord ++ tailWord_778218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778218).length < 2 ^ (prefixWord ++ tailWord_778218).sum := by decide
  have hdescent : baseEnd_778218 < baseStart_778218 := by decide
  rcases family_descends (prefixWord ++ tailWord_778218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778235 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 2, 3]
def baseStart_778235 : Nat := 118140960795 + 778235 * 2 ^ 59
def prefixEnd_778235 : Nat := 4983230072969 + 3 ^ 40 * 778235 * 2
def baseEnd_778235 : Nat := 266405744767911923788979

theorem tailTrace_778235 : CollatzResearch.WordTrace tailWord_778235 prefixEnd_778235 266405744767911923788979 := by
  unfold tailWord_778235
  simp only [CollatzResearch.WordTrace]
  refine ⟨28384562335594981801448159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18923041557063321200965439 28384562335594981801448159)
  ·
    refine ⟨42576843503392472702172239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28384562335594981801448159 42576843503392472702172239)
    ·
      refine ⟨63865265255088709053258359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42576843503392472702172239 63865265255088709053258359)
      ·
        refine ⟨95797897882633063579887539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63865265255088709053258359 95797897882633063579887539)
        ·
          refine ⟨143696846823949595369831309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95797897882633063579887539 143696846823949595369831309)
          ·
            refine ⟨53886317558981098263686741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143696846823949595369831309 53886317558981098263686741)
            ·
              refine ⟨631480283894309745277579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 53886317558981098263686741 631480283894309745277579)
              ·
                refine ⟨947220425841464617916369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631480283894309745277579 947220425841464617916369)
                ·
                  refine ⟨710415319381098463437277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 947220425841464617916369 710415319381098463437277)
                  ·
                    refine ⟨266405744767911923788979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710415319381098463437277 266405744767911923788979)
                    ·
                      rfl

theorem cell22_778235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 3].length) (baseStart_778235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778235 prefixEnd_778235 := by exact prefixLift 778235
  have htrace : WordTrace (prefixWord ++ tailWord_778235) baseStart_778235 baseEnd_778235 := by
    simpa [prefixWord, tailWord_778235, baseEnd_778235] using wordTrace_append hprefix tailTrace_778235
  have hstable : (prefixWord ++ tailWord_778235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778235).length < 2 ^ (prefixWord ++ tailWord_778235).sum := by decide
  have hdescent : baseEnd_778235 < baseStart_778235 := by decide
  rcases family_descends (prefixWord ++ tailWord_778235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778250 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_778250 : Nat := 118140960795 + 778250 * 2 ^ 59
def prefixEnd_778250 : Nat := 4983230072969 + 3 ^ 40 * 778250 * 2
def baseEnd_778250 : Nat := 266410879574456884663933

theorem tailTrace_778250 : CollatzResearch.WordTrace tailWord_778250 prefixEnd_778250 266410879574456884663933 := by
  unfold tailWord_778250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096277357635159840811051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18923406287027092908829469 7096277357635159840811051)
  ·
    refine ⟨10644416036452739761216577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096277357635159840811051 10644416036452739761216577)
    ·
      refine ⟨7983312027339554820912433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10644416036452739761216577 7983312027339554820912433)
      ·
        refine ⟨5987484020504666115684325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7983312027339554820912433 5987484020504666115684325)
        ·
          refine ⟨1122653253844624896690811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5987484020504666115684325 1122653253844624896690811)
          ·
            refine ⟨1683979880766937345036217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122653253844624896690811 1683979880766937345036217)
            ·
              refine ⟨1262984910575203008777163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683979880766937345036217 1262984910575203008777163)
              ·
                refine ⟨1894477365862804513165745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262984910575203008777163 1894477365862804513165745)
                ·
                  refine ⟨1420858024397103384874309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1894477365862804513165745 1420858024397103384874309)
                  ·
                    refine ⟨266410879574456884663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420858024397103384874309 266410879574456884663933)
                    ·
                      rfl

theorem cell22_778250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_778250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778250 prefixEnd_778250 := by exact prefixLift 778250
  have htrace : WordTrace (prefixWord ++ tailWord_778250) baseStart_778250 baseEnd_778250 := by
    simpa [prefixWord, tailWord_778250, baseEnd_778250] using wordTrace_append hprefix tailTrace_778250
  have hstable : (prefixWord ++ tailWord_778250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778250).length < 2 ^ (prefixWord ++ tailWord_778250).sum := by decide
  have hdescent : baseEnd_778250 < baseStart_778250 := by decide
  rcases family_descends (prefixWord ++ tailWord_778250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778291 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_778291 : Nat := 118140960795 + 778291 * 2 ^ 59
def prefixEnd_778291 : Nat := 4983230072969 + 3 ^ 40 * 778291 * 2
def baseEnd_778291 : Nat := 266424914712346444388807

theorem tailTrace_778291 : CollatzResearch.WordTrace tailWord_778291 prefixEnd_778291 266424914712346444388807 := by
  unfold tailWord_778291
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386604823392103365486727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18924403215594735576991151 28386604823392103365486727)
  ·
    refine ⟨42579907235088155048230091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28386604823392103365486727 42579907235088155048230091)
    ·
      refine ⟨63869860852632232572345137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42579907235088155048230091 63869860852632232572345137)
      ·
        refine ⟨47902395639474174429258853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63869860852632232572345137 47902395639474174429258853)
        ·
          refine ⟨8981699182401407705486035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47902395639474174429258853 8981699182401407705486035)
          ·
            refine ⟨13472548773602111558229053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981699182401407705486035 13472548773602111558229053)
            ·
              refine ⟨5052205790100791834335895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13472548773602111558229053 5052205790100791834335895)
              ·
                refine ⟨7578308685151187751503843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052205790100791834335895 7578308685151187751503843)
                ·
                  refine ⟨11367463027726781627255765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7578308685151187751503843 11367463027726781627255765)
                  ·
                    refine ⟨266424914712346444388807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11367463027726781627255765 266424914712346444388807)
                    ·
                      rfl

theorem cell22_778291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_778291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778291 prefixEnd_778291 := by exact prefixLift 778291
  have htrace : WordTrace (prefixWord ++ tailWord_778291) baseStart_778291 baseEnd_778291 := by
    simpa [prefixWord, tailWord_778291, baseEnd_778291] using wordTrace_append hprefix tailTrace_778291
  have hstable : (prefixWord ++ tailWord_778291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778291).length < 2 ^ (prefixWord ++ tailWord_778291).sum := by decide
  have hdescent : baseEnd_778291 < baseStart_778291 := by decide
  rcases family_descends (prefixWord ++ tailWord_778291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778293 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 5]
def baseStart_778293 : Nat := 118140960795 + 778293 * 2 ^ 59
def prefixEnd_778293 : Nat := 4983230072969 + 3 ^ 40 * 778293 * 2
def baseEnd_778293 : Nat := 88808533117739701946267

theorem tailTrace_778293 : CollatzResearch.WordTrace tailWord_778293 prefixEnd_778293 88808533117739701946267 := by
  unfold tailWord_778293
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386677769384857707059533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18924451846256571804706355 28386677769384857707059533)
  ·
    refine ⟨10645004163519321640147325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28386677769384857707059533 10645004163519321640147325)
    ·
      refine ⟨3991876561319745615055247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10645004163519321640147325 3991876561319745615055247)
      ·
        refine ⟨5987814841979618422582871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991876561319745615055247 5987814841979618422582871)
        ·
          refine ⟨8981722262969427633874307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987814841979618422582871 8981722262969427633874307)
          ·
            refine ⟨13472583394454141450811461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981722262969427633874307 13472583394454141450811461)
            ·
              refine ⟨2526109386460151522027149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13472583394454141450811461 2526109386460151522027149)
              ·
                refine ⟨947291019922556820760181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2526109386460151522027149 947291019922556820760181)
                ·
                  refine ⟨88808533117739701946267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 947291019922556820760181 88808533117739701946267)
                  ·
                    rfl

theorem cell22_778293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_778293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778293 prefixEnd_778293 := by exact prefixLift 778293
  have htrace : WordTrace (prefixWord ++ tailWord_778293) baseStart_778293 baseEnd_778293 := by
    simpa [prefixWord, tailWord_778293, baseEnd_778293] using wordTrace_append hprefix tailTrace_778293
  have hstable : (prefixWord ++ tailWord_778293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778293).length < 2 ^ (prefixWord ++ tailWord_778293).sum := by decide
  have hdescent : baseEnd_778293 < baseStart_778293 := by decide
  rcases family_descends (prefixWord ++ tailWord_778293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778310 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_778310 : Nat := 118140960795 + 778310 * 2 ^ 59
def prefixEnd_778310 : Nat := 4983230072969 + 3 ^ 40 * 778310 * 2
def baseEnd_778310 : Nat := 88810472933545576054583

theorem tailTrace_778310 : CollatzResearch.WordTrace tailWord_778310 prefixEnd_778310 88810472933545576054583 := by
  unfold tailWord_778310
  simp only [CollatzResearch.WordTrace]
  refine ⟨887103056572602175325887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18924865206882179740285589 887103056572602175325887)
  ·
    refine ⟨1330654584858903262988831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887103056572602175325887 1330654584858903262988831)
    ·
      refine ⟨1995981877288354894483247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330654584858903262988831 1995981877288354894483247)
      ·
        refine ⟨2993972815932532341724871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995981877288354894483247 2993972815932532341724871)
        ·
          refine ⟨4490959223898798512587307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993972815932532341724871 4490959223898798512587307)
          ·
            refine ⟨6736438835848197768880961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490959223898798512587307 6736438835848197768880961)
            ·
              refine ⟨5052329126886148326660721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6736438835848197768880961 5052329126886148326660721)
              ·
                refine ⟨3789246845164611244995541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052329126886148326660721 3789246845164611244995541)
                ·
                  refine ⟨88810472933545576054583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3789246845164611244995541 88810472933545576054583)
                  ·
                    rfl

theorem cell22_778310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_778310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778310 prefixEnd_778310 := by exact prefixLift 778310
  have htrace : WordTrace (prefixWord ++ tailWord_778310) baseStart_778310 baseEnd_778310 := by
    simpa [prefixWord, tailWord_778310, baseEnd_778310] using wordTrace_append hprefix tailTrace_778310
  have hstable : (prefixWord ++ tailWord_778310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778310).length < 2 ^ (prefixWord ++ tailWord_778310).sum := by decide
  have hdescent : baseEnd_778310 < baseStart_778310 := by decide
  rcases family_descends (prefixWord ++ tailWord_778310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778321 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 10]
def baseStart_778321 : Nat := 118140960795 + 778321 * 2 ^ 59
def prefixEnd_778321 : Nat := 4983230072969 + 3 ^ 40 * 778321 * 2
def baseEnd_778321 : Nat := 88811728108478788712905

theorem tailTrace_778321 : CollatzResearch.WordTrace tailWord_778321 prefixEnd_778321 88811728108478788712905 := by
  unfold tailWord_778321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28387699013283418489078817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18925132675522278992719211 28387699013283418489078817)
  ·
    refine ⟨21290774259962563866809113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28387699013283418489078817 21290774259962563866809113)
    ·
      refine ⟨15968080694971922900106835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21290774259962563866809113 15968080694971922900106835)
      ·
        refine ⟨23952121042457884350160253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15968080694971922900106835 23952121042457884350160253)
        ·
          refine ⟨8982045390921706631310095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23952121042457884350160253 8982045390921706631310095)
          ·
            refine ⟨13473068086382559946965143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982045390921706631310095 13473068086382559946965143)
            ·
              refine ⟨20209602129573839920447715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13473068086382559946965143 20209602129573839920447715)
              ·
                refine ⟨30314403194360759880671573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20209602129573839920447715 30314403194360759880671573)
                ·
                  refine ⟨88811728108478788712905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30314403194360759880671573 88811728108478788712905)
                  ·
                    rfl

theorem cell22_778321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_778321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778321 prefixEnd_778321 := by exact prefixLift 778321
  have htrace : WordTrace (prefixWord ++ tailWord_778321) baseStart_778321 baseEnd_778321 := by
    simpa [prefixWord, tailWord_778321, baseEnd_778321] using wordTrace_append hprefix tailTrace_778321
  have hstable : (prefixWord ++ tailWord_778321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778321).length < 2 ^ (prefixWord ++ tailWord_778321).sum := by decide
  have hdescent : baseEnd_778321 < baseStart_778321 := by decide
  rcases family_descends (prefixWord ++ tailWord_778321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778368 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_778368 : Nat := 118140960795 + 778368 * 2 ^ 59
def prefixEnd_778368 : Nat := 4983230072969 + 3 ^ 40 * 778368 * 2
def baseEnd_778368 : Nat := 266451273385943910213571

theorem tailTrace_778368 : CollatzResearch.WordTrace tailWord_778368 prefixEnd_778368 266451273385943910213571 := by
  unfold tailWord_778368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194706622056572758019879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18926275496075430344026505 14194706622056572758019879)
  ·
    refine ⟨21292059933084859137029819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194706622056572758019879 21292059933084859137029819)
    ·
      refine ⟨31938089899627288705544729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21292059933084859137029819 31938089899627288705544729)
      ·
        refine ⟨23953567424720466529158547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31938089899627288705544729 23953567424720466529158547)
        ·
          refine ⟨35930351137080699793737821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23953567424720466529158547 35930351137080699793737821)
          ·
            refine ⟨13473881676405262422651683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35930351137080699793737821 13473881676405262422651683)
            ·
              refine ⟨20210822514607893633977525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13473881676405262422651683 20210822514607893633977525)
              ·
                refine ⟨1894764610744490028185393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20210822514607893633977525 1894764610744490028185393)
                ·
                  refine ⟨1421073458058367521139045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1894764610744490028185393 1421073458058367521139045)
                  ·
                    refine ⟨266451273385943910213571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421073458058367521139045 266451273385943910213571)
                    ·
                      rfl

theorem cell22_778368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_778368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778368 prefixEnd_778368 := by exact prefixLift 778368
  have htrace : WordTrace (prefixWord ++ tailWord_778368) baseStart_778368 baseEnd_778368 := by
    simpa [prefixWord, tailWord_778368, baseEnd_778368] using wordTrace_append hprefix tailTrace_778368
  have hstable : (prefixWord ++ tailWord_778368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778368).length < 2 ^ (prefixWord ++ tailWord_778368).sum := by decide
  have hdescent : baseEnd_778368 < baseStart_778368 := by decide
  rcases family_descends (prefixWord ++ tailWord_778368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778443 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_778443 : Nat := 118140960795 + 778443 * 2 ^ 59
def prefixEnd_778443 : Nat := 4983230072969 + 3 ^ 40 * 778443 * 2
def baseEnd_778443 : Nat := 266476947418668714588341

theorem tailTrace_778443 : CollatzResearch.WordTrace tailWord_778443 prefixEnd_778443 266476947418668714588341 := by
  unfold tailWord_778443
  simp only [CollatzResearch.WordTrace]
  refine ⟨28392148718841433325019983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18928099145894288883346655 28392148718841433325019983)
  ·
    refine ⟨42588223078262149987529975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28392148718841433325019983 42588223078262149987529975)
    ·
      refine ⟨63882334617393224981294963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42588223078262149987529975 63882334617393224981294963)
      ·
        refine ⟨95823501926089837471942445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63882334617393224981294963 95823501926089837471942445)
        ·
          refine ⟨35933813222283689051978417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95823501926089837471942445 35933813222283689051978417)
          ·
            refine ⟨26950359916712766788983813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35933813222283689051978417 26950359916712766788983813)
            ·
              refine ⟨5053192484383643772934465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26950359916712766788983813 5053192484383643772934465)
              ·
                refine ⟨3789894363287732829700849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053192484383643772934465 3789894363287732829700849)
                ·
                  refine ⟨2842420772465799622275637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789894363287732829700849 2842420772465799622275637)
                  ·
                    refine ⟨266476947418668714588341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2842420772465799622275637 266476947418668714588341)
                    ·
                      rfl

theorem cell22_778443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_778443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778443 prefixEnd_778443 := by exact prefixLift 778443
  have htrace : WordTrace (prefixWord ++ tailWord_778443) baseStart_778443 baseEnd_778443 := by
    simpa [prefixWord, tailWord_778443, baseEnd_778443] using wordTrace_append hprefix tailTrace_778443
  have hstable : (prefixWord ++ tailWord_778443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778443).length < 2 ^ (prefixWord ++ tailWord_778443).sum := by decide
  have hdescent : baseEnd_778443 < baseStart_778443 := by decide
  rcases family_descends (prefixWord ++ tailWord_778443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778449 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_778449 : Nat := 118140960795 + 778449 * 2 ^ 59
def prefixEnd_778449 : Nat := 4983230072969 + 3 ^ 40 * 778449 * 2
def baseEnd_778449 : Nat := 266479001341286698938323

theorem tailTrace_778449 : CollatzResearch.WordTrace tailWord_778449 prefixEnd_778449 266479001341286698938323 := by
  unfold tailWord_778449
  simp only [CollatzResearch.WordTrace]
  refine ⟨28392367556819696349738401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18928245037879797566492267 28392367556819696349738401)
  ·
    refine ⟨21294275667614772262303801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28392367556819696349738401 21294275667614772262303801)
    ·
      refine ⟨15970706750711079196727851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21294275667614772262303801 15970706750711079196727851)
      ·
        refine ⟨23956060126066618795091777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15970706750711079196727851 23956060126066618795091777)
        ·
          refine ⟨17967045094549964096318833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23956060126066618795091777 17967045094549964096318833)
          ·
            refine ⟨13475283820912473072239125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17967045094549964096318833 13475283820912473072239125)
            ·
              refine ⟨631653929105272175261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13475283820912473072239125 631653929105272175261209)
              ·
                refine ⟨473740446828954131445907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631653929105272175261209 473740446828954131445907)
                ·
                  refine ⟨710610670243431197168861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473740446828954131445907 710610670243431197168861)
                  ·
                    refine ⟨266479001341286698938323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 710610670243431197168861 266479001341286698938323)
                    ·
                      rfl

theorem cell22_778449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_778449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778449 prefixEnd_778449 := by exact prefixLift 778449
  have htrace : WordTrace (prefixWord ++ tailWord_778449) baseStart_778449 baseEnd_778449 := by
    simpa [prefixWord, tailWord_778449, baseEnd_778449] using wordTrace_append hprefix tailTrace_778449
  have hstable : (prefixWord ++ tailWord_778449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778449).length < 2 ^ (prefixWord ++ tailWord_778449).sum := by decide
  have hdescent : baseEnd_778449 < baseStart_778449 := by decide
  rcases family_descends (prefixWord ++ tailWord_778449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778473 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 6]
def baseStart_778473 : Nat := 118140960795 + 778473 * 2 ^ 59
def prefixEnd_778473 : Nat := 4983230072969 + 3 ^ 40 * 778473 * 2
def baseEnd_778473 : Nat := 88829072343919545446083

theorem tailTrace_778473 : CollatzResearch.WordTrace tailWord_778473 prefixEnd_778473 88829072343919545446083 := by
  unfold tailWord_778473
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393242908732748448612073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18928828605821832299074715 28393242908732748448612073)
  ·
    refine ⟨21294932181549561336459055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28393242908732748448612073 21294932181549561336459055)
    ·
      refine ⟨31942398272324342004688583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21294932181549561336459055 31942398272324342004688583)
      ·
        refine ⟨47913597408486513007032875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31942398272324342004688583 47913597408486513007032875)
        ·
          refine ⟨71870396112729769510549313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47913597408486513007032875 71870396112729769510549313)
          ·
            refine ⟨53902797084547327132911985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71870396112729769510549313 53902797084547327132911985)
            ·
              refine ⟨40427097813410495349683989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53902797084547327132911985 40427097813410495349683989)
              ·
                refine ⟨1895020210003616969516437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40427097813410495349683989 1895020210003616969516437)
                ·
                  refine ⟨88829072343919545446083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1895020210003616969516437 88829072343919545446083)
                  ·
                    rfl

theorem cell22_778473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_778473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778473 prefixEnd_778473 := by exact prefixLift 778473
  have htrace : WordTrace (prefixWord ++ tailWord_778473) baseStart_778473 baseEnd_778473 := by
    simpa [prefixWord, tailWord_778473, baseEnd_778473] using wordTrace_append hprefix tailTrace_778473
  have hstable : (prefixWord ++ tailWord_778473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778473).length < 2 ^ (prefixWord ++ tailWord_778473).sum := by decide
  have hdescent : baseEnd_778473 < baseStart_778473 := by decide
  rcases family_descends (prefixWord ++ tailWord_778473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778475 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 1, 4]
def baseStart_778475 : Nat := 118140960795 + 778475 * 2 ^ 59
def prefixEnd_778475 : Nat := 4983230072969 + 3 ^ 40 * 778475 * 2
def baseEnd_778475 : Nat := 266487901672631297788243

theorem tailTrace_778475 : CollatzResearch.WordTrace tailWord_778475 prefixEnd_778475 266487901672631297788243 := by
  unfold tailWord_778475
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393315854725502790184879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18928877236483668526789919 28393315854725502790184879)
  ·
    refine ⟨42589973782088254185277319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28393315854725502790184879 42589973782088254185277319)
    ·
      refine ⟨63884960673132381277915979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42589973782088254185277319 63884960673132381277915979)
      ·
        refine ⟨95827441009698571916873969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63884960673132381277915979 95827441009698571916873969)
        ·
          refine ⟨71870580757273928937655477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95827441009698571916873969 71870580757273928937655477)
          ·
            refine ⟨6737866945994430837905201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71870580757273928937655477 6737866945994430837905201)
            ·
              refine ⟨5053400209495823128428901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737866945994430837905201 5053400209495823128428901)
              ·
                refine ⟨947512539280466836580419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5053400209495823128428901 947512539280466836580419)
                ·
                  refine ⟨1421268808920700254870629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947512539280466836580419 1421268808920700254870629)
                  ·
                    refine ⟨266487901672631297788243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421268808920700254870629 266487901672631297788243)
                    ·
                      rfl

theorem cell22_778475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_778475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778475 prefixEnd_778475 := by exact prefixLift 778475
  have htrace : WordTrace (prefixWord ++ tailWord_778475) baseStart_778475 baseEnd_778475 := by
    simpa [prefixWord, tailWord_778475, baseEnd_778475] using wordTrace_append hprefix tailTrace_778475
  have hstable : (prefixWord ++ tailWord_778475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778475).length < 2 ^ (prefixWord ++ tailWord_778475).sum := by decide
  have hdescent : baseEnd_778475 < baseStart_778475 := by decide
  rcases family_descends (prefixWord ++ tailWord_778475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778492 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_778492 : Nat := 118140960795 + 778492 * 2 ^ 59
def prefixEnd_778492 : Nat := 4983230072969 + 3 ^ 40 * 778492 * 2
def baseEnd_778492 : Nat := 266493721120048920113191

theorem tailTrace_778492 : CollatzResearch.WordTrace tailWord_778492 prefixEnd_778492 266493721120048920113191 := by
  unfold tailWord_778492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196967947831957346776865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18929290597109276462369153 14196967947831957346776865)
  ·
    refine ⟨10647725960873968010082649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14196967947831957346776865 10647725960873968010082649)
    ·
      refine ⟨7985794470655476007561987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10647725960873968010082649 7985794470655476007561987)
      ·
        refine ⟨11978691705983214011342981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985794470655476007561987 11978691705983214011342981)
        ·
          refine ⟨2246004694871852627126809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11978691705983214011342981 2246004694871852627126809)
          ·
            refine ⟨1684503521153889470345107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246004694871852627126809 1684503521153889470345107)
            ·
              refine ⟨2526755281730834205517661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684503521153889470345107 2526755281730834205517661)
              ·
                refine ⟨947533230649062827069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2526755281730834205517661 947533230649062827069123)
                ·
                  refine ⟨1421299845973594240603685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947533230649062827069123 1421299845973594240603685)
                  ·
                    refine ⟨266493721120048920113191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421299845973594240603685 266493721120048920113191)
                    ·
                      rfl

theorem cell22_778492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_778492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778492 prefixEnd_778492 := by exact prefixLift 778492
  have htrace : WordTrace (prefixWord ++ tailWord_778492) baseStart_778492 baseEnd_778492 := by
    simpa [prefixWord, tailWord_778492, baseEnd_778492] using wordTrace_append hprefix tailTrace_778492
  have hstable : (prefixWord ++ tailWord_778492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778492).length < 2 ^ (prefixWord ++ tailWord_778492).sum := by decide
  have hdescent : baseEnd_778492 < baseStart_778492 := by decide
  rcases family_descends (prefixWord ++ tailWord_778492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778526 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_778526 : Nat := 118140960795 + 778526 * 2 ^ 59
def prefixEnd_778526 : Nat := 4983230072969 + 3 ^ 40 * 778526 * 2
def baseEnd_778526 : Nat := 266505360014884164763087

theorem tailTrace_778526 : CollatzResearch.WordTrace tailWord_778526 prefixEnd_778526 266505360014884164763087 := by
  unfold tailWord_778526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549396997192592312536429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18930117318360492333527621 3549396997192592312536429)
  ·
    refine ⟨1331023873947222117201161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3549396997192592312536429 1331023873947222117201161)
    ·
      refine ⟨998267905460416587900871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331023873947222117201161 998267905460416587900871)
      ·
        refine ⟨1497401858190624881851307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998267905460416587900871 1497401858190624881851307)
        ·
          refine ⟨2246102787285937322776961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497401858190624881851307 2246102787285937322776961)
          ·
            refine ⟨1684577090464452992082721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246102787285937322776961 1684577090464452992082721)
            ·
              refine ⟨1263432817848339744062041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684577090464452992082721 1263432817848339744062041)
              ·
                refine ⟨947574613386254808046531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263432817848339744062041 947574613386254808046531)
                ·
                  refine ⟨1421361920079382212069797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947574613386254808046531 1421361920079382212069797)
                  ·
                    refine ⟨266505360014884164763087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421361920079382212069797 266505360014884164763087)
                    ·
                      rfl

theorem cell22_778526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_778526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778526 prefixEnd_778526 := by exact prefixLift 778526
  have htrace : WordTrace (prefixWord ++ tailWord_778526) baseStart_778526 baseEnd_778526 := by
    simpa [prefixWord, tailWord_778526, baseEnd_778526] using wordTrace_append hprefix tailTrace_778526
  have hstable : (prefixWord ++ tailWord_778526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778526).length < 2 ^ (prefixWord ++ tailWord_778526).sum := by decide
  have hdescent : baseEnd_778526 < baseStart_778526 := by decide
  rcases family_descends (prefixWord ++ tailWord_778526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778659 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 4]
def baseStart_778659 : Nat := 118140960795 + 778659 * 2 ^ 59
def prefixEnd_778659 : Nat := 4983230072969 + 3 ^ 40 * 778659 * 2
def baseEnd_778659 : Nat := 88850296210972050395893

theorem tailTrace_778659 : CollatzResearch.WordTrace tailWord_778659 prefixEnd_778659 88850296210972050395893 := by
  unfold tailWord_778659
  simp only [CollatzResearch.WordTrace]
  refine ⟨28400026886058902214883031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18933351257372601476588687 28400026886058902214883031)
  ·
    refine ⟨42600040329088353322324547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28400026886058902214883031 42600040329088353322324547)
    ·
      refine ⟨63900060493632529983486821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42600040329088353322324547 63900060493632529983486821)
      ·
        refine ⟨11981261342556099371903779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63900060493632529983486821 11981261342556099371903779)
        ·
          refine ⟨17971892013834149057855669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11981261342556099371903779 17971892013834149057855669)
          ·
            refine ⟨1684864876296951474173969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17971892013834149057855669 1684864876296951474173969)
            ·
              refine ⟨1263648657222713605630477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684864876296951474173969 1263648657222713605630477)
              ·
                refine ⟨473868246458517602111429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1263648657222713605630477 473868246458517602111429)
                ·
                  refine ⟨88850296210972050395893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473868246458517602111429 88850296210972050395893)
                  ·
                    rfl

theorem cell22_778659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 4].length) (baseStart_778659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778659 prefixEnd_778659 := by exact prefixLift 778659
  have htrace : WordTrace (prefixWord ++ tailWord_778659) baseStart_778659 baseEnd_778659 := by
    simpa [prefixWord, tailWord_778659, baseEnd_778659] using wordTrace_append hprefix tailTrace_778659
  have hstable : (prefixWord ++ tailWord_778659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778659).length < 2 ^ (prefixWord ++ tailWord_778659).sum := by decide
  have hdescent : baseEnd_778659 < baseStart_778659 := by decide
  rcases family_descends (prefixWord ++ tailWord_778659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778732 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_778732 : Nat := 118140960795 + 778732 * 2 ^ 59
def prefixEnd_778732 : Nat := 4983230072969 + 3 ^ 40 * 778732 * 2
def baseEnd_778732 : Nat := 88858626008256098037485

theorem tailTrace_778732 : CollatzResearch.WordTrace tailWord_778732 prefixEnd_778732 88858626008256098037485 := by
  unfold tailWord_778732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201344707397217841145225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18935126276529623788193633 14201344707397217841145225)
  ·
    refine ⟨10651008530547913380858919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14201344707397217841145225 10651008530547913380858919)
    ·
      refine ⟨15976512795821870071288379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10651008530547913380858919 15976512795821870071288379)
      ·
        refine ⟨23964769193732805106932569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15976512795821870071288379 23964769193732805106932569)
        ·
          refine ⟨17973576895299603830199427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23964769193732805106932569 17973576895299603830199427)
          ·
            refine ⟨26960365342949405745299141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17973576895299603830199427 26960365342949405745299141)
            ·
              refine ⟨5055068501803013577243589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26960365342949405745299141 5055068501803013577243589)
              ·
                refine ⟨947825344088065045733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5055068501803013577243589 947825344088065045733173)
                ·
                  refine ⟨88858626008256098037485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 947825344088065045733173 88858626008256098037485)
                  ·
                    rfl

theorem cell22_778732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_778732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778732 prefixEnd_778732 := by exact prefixLift 778732
  have htrace : WordTrace (prefixWord ++ tailWord_778732) baseStart_778732 baseEnd_778732 := by
    simpa [prefixWord, tailWord_778732, baseEnd_778732] using wordTrace_append hprefix tailTrace_778732
  have hstable : (prefixWord ++ tailWord_778732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778732).length < 2 ^ (prefixWord ++ tailWord_778732).sum := by decide
  have hdescent : baseEnd_778732 < baseStart_778732 := by decide
  rcases family_descends (prefixWord ++ tailWord_778732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778807 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_778807 : Nat := 118140960795 + 778807 * 2 ^ 59
def prefixEnd_778807 : Nat := 4983230072969 + 3 ^ 40 * 778807 * 2
def baseEnd_778807 : Nat := 266601552057493098487225

theorem tailTrace_778807 : CollatzResearch.WordTrace tailWord_778807 prefixEnd_778807 266601552057493098487225 := by
  unfold tailWord_778807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405424889522723491270675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18936949926348482327513783 28405424889522723491270675)
  ·
    refine ⟨42608137334284085236906013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28405424889522723491270675 42608137334284085236906013)
    ·
      refine ⟨15978051500356531963839755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42608137334284085236906013 15978051500356531963839755)
      ·
        refine ⟨23967077250534797945759633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15978051500356531963839755 23967077250534797945759633)
        ·
          refine ⟨17975307937901098459319725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23967077250534797945759633 17975307937901098459319725)
          ·
            refine ⟨6740740476712911922244897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17975307937901098459319725 6740740476712911922244897)
            ·
              refine ⟨5055555357534683941683673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740740476712911922244897 5055555357534683941683673)
              ·
                refine ⟨3791666518151012956262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055555357534683941683673 3791666518151012956262755)
                ·
                  refine ⟨5687499777226519434394133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791666518151012956262755 5687499777226519434394133)
                  ·
                    refine ⟨266601552057493098487225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5687499777226519434394133 266601552057493098487225)
                    ·
                      rfl

theorem cell22_778807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_778807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778807 prefixEnd_778807 := by exact prefixLift 778807
  have htrace : WordTrace (prefixWord ++ tailWord_778807) baseStart_778807 baseEnd_778807 := by
    simpa [prefixWord, tailWord_778807, baseEnd_778807] using wordTrace_append hprefix tailTrace_778807
  have hstable : (prefixWord ++ tailWord_778807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778807).length < 2 ^ (prefixWord ++ tailWord_778807).sum := by decide
  have hdescent : baseEnd_778807 < baseStart_778807 := by decide
  rcases family_descends (prefixWord ++ tailWord_778807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778809 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_778809 : Nat := 118140960795 + 778809 * 2 ^ 59
def prefixEnd_778809 : Nat := 4983230072969 + 3 ^ 40 * 778809 * 2
def baseEnd_778809 : Nat := 266602236698365759937219

theorem tailTrace_778809 : CollatzResearch.WordTrace tailWord_778809 prefixEnd_778809 266602236698365759937219 := by
  unfold tailWord_778809
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405497835515477832843481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18936998557010318555228987 28405497835515477832843481)
  ·
    refine ⟨21304123376636608374632611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28405497835515477832843481 21304123376636608374632611)
    ·
      refine ⟨31956185064954912561948917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21304123376636608374632611 31956185064954912561948917)
      ·
        refine ⟨2995892349839523052682711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31956185064954912561948917 2995892349839523052682711)
        ·
          refine ⟨4493838524759284579024067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995892349839523052682711 4493838524759284579024067)
          ·
            refine ⟨6740757787138926868536101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493838524759284579024067 6740757787138926868536101)
            ·
              refine ⟨1263892085088548787850519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6740757787138926868536101 1263892085088548787850519)
              ·
                refine ⟨1895838127632823181775779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263892085088548787850519 1895838127632823181775779)
                ·
                  refine ⟨2843757191449234772663669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895838127632823181775779 2843757191449234772663669)
                  ·
                    refine ⟨266602236698365759937219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2843757191449234772663669 266602236698365759937219)
                    ·
                      rfl

theorem cell22_778809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_778809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778809 prefixEnd_778809 := by exact prefixLift 778809
  have htrace : WordTrace (prefixWord ++ tailWord_778809) baseStart_778809 baseEnd_778809 := by
    simpa [prefixWord, tailWord_778809, baseEnd_778809] using wordTrace_append hprefix tailTrace_778809
  have hstable : (prefixWord ++ tailWord_778809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778809).length < 2 ^ (prefixWord ++ tailWord_778809).sum := by decide
  have hdescent : baseEnd_778809 < baseStart_778809 := by decide
  rcases family_descends (prefixWord ++ tailWord_778809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778884 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_778884 : Nat := 118140960795 + 778884 * 2 ^ 59
def prefixEnd_778884 : Nat := 4983230072969 + 3 ^ 40 * 778884 * 2
def baseEnd_778884 : Nat := 88875970243696854770663

theorem tailTrace_778884 : CollatzResearch.WordTrace tailWord_778884 prefixEnd_778884 88875970243696854770663 := by
  unfold tailWord_778884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14204116655121882820911853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18938822206829177094549137 14204116655121882820911853)
  ·
    refine ⟨5326543745670706057841945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14204116655121882820911853 5326543745670706057841945)
    ·
      refine ⟨3994907809253029543381459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5326543745670706057841945 3994907809253029543381459)
      ·
        refine ⟨5992361713879544315072189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994907809253029543381459 5992361713879544315072189)
        ·
          refine ⟨2247135642704829118152071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5992361713879544315072189 2247135642704829118152071)
          ·
            refine ⟨3370703464057243677228107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247135642704829118152071 3370703464057243677228107)
            ·
              refine ⟨5056055196085865515842161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370703464057243677228107 5056055196085865515842161)
              ·
                refine ⟨3792041397064399136881621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056055196085865515842161 3792041397064399136881621)
                ·
                  refine ⟨88875970243696854770663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3792041397064399136881621 88875970243696854770663)
                  ·
                    rfl

theorem cell22_778884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_778884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778884 prefixEnd_778884 := by exact prefixLift 778884
  have htrace : WordTrace (prefixWord ++ tailWord_778884) baseStart_778884 baseEnd_778884 := by
    simpa [prefixWord, tailWord_778884, baseEnd_778884] using wordTrace_append hprefix tailTrace_778884
  have hstable : (prefixWord ++ tailWord_778884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778884).length < 2 ^ (prefixWord ++ tailWord_778884).sum := by decide
  have hdescent : baseEnd_778884 < baseStart_778884 := by decide
  rcases family_descends (prefixWord ++ tailWord_778884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778897 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_778897 : Nat := 118140960795 + 778897 * 2 ^ 59
def prefixEnd_778897 : Nat := 4983230072969 + 3 ^ 40 * 778897 * 2
def baseEnd_778897 : Nat := 266632360896762863736949

theorem tailTrace_778897 : CollatzResearch.WordTrace tailWord_778897 prefixEnd_778897 266632360896762863736949 := by
  unfold tailWord_778897
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408707459196668862046945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939138306131112574697963 28408707459196668862046945)
  ·
    refine ⟨21306530594397501646535209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28408707459196668862046945 21306530594397501646535209)
    ·
      refine ⟨15979897945798126234901407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21306530594397501646535209 15979897945798126234901407)
      ·
        refine ⟨23969846918697189352352111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15979897945798126234901407 23969846918697189352352111)
        ·
          refine ⟨35954770378045784028528167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23969846918697189352352111 35954770378045784028528167)
          ·
            refine ⟨53932155567068676042792251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35954770378045784028528167 53932155567068676042792251)
            ·
              refine ⟨80898233350603014064188377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53932155567068676042792251 80898233350603014064188377)
              ·
                refine ⟨60673675012952260548141283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80898233350603014064188377 60673675012952260548141283)
                ·
                  refine ⟨91010512519428390822211925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60673675012952260548141283 91010512519428390822211925)
                  ·
                    refine ⟨266632360896762863736949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 91010512519428390822211925 266632360896762863736949)
                    ·
                      rfl

theorem cell22_778897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_778897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778897 prefixEnd_778897 := by exact prefixLift 778897
  have htrace : WordTrace (prefixWord ++ tailWord_778897) baseStart_778897 baseEnd_778897 := by
    simpa [prefixWord, tailWord_778897, baseEnd_778897] using wordTrace_append hprefix tailTrace_778897
  have hstable : (prefixWord ++ tailWord_778897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778897).length < 2 ^ (prefixWord ++ tailWord_778897).sum := by decide
  have hdescent : baseEnd_778897 < baseStart_778897 := by decide
  rcases family_descends (prefixWord ++ tailWord_778897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778931 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 1, 4]
def baseStart_778931 : Nat := 118140960795 + 778931 * 2 ^ 59
def prefixEnd_778931 : Nat := 4983230072969 + 3 ^ 40 * 778931 * 2
def baseEnd_778931 : Nat := 266643999791598108386845

theorem tailTrace_778931 : CollatzResearch.WordTrace tailWord_778931 prefixEnd_778931 266643999791598108386845 := by
  unfold tailWord_778931
  simp only [CollatzResearch.WordTrace]
  refine ⟨28409947541073492668784647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939965027382328445856431 28409947541073492668784647)
  ·
    refine ⟨42614921311610239003176971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28409947541073492668784647 42614921311610239003176971)
    ·
      refine ⟨63922381967415358504765457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42614921311610239003176971 63922381967415358504765457)
      ·
        refine ⟨47941786475561518878574093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63922381967415358504765457 47941786475561518878574093)
        ·
          refine ⟨17978169928335569579465285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47941786475561518878574093 17978169928335569579465285)
          ·
            refine ⟨3370906861562919296149741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17978169928335569579465285 3370906861562919296149741)
            ·
              refine ⟨1264090073086094736056153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3370906861562919296149741 1264090073086094736056153)
              ·
                refine ⟨948067554814571052042115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264090073086094736056153 948067554814571052042115)
                ·
                  refine ⟨1422101332221856578063173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948067554814571052042115 1422101332221856578063173)
                  ·
                    refine ⟨266643999791598108386845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422101332221856578063173 266643999791598108386845)
                    ·
                      rfl

theorem cell22_778931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_778931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778931 prefixEnd_778931 := by exact prefixLift 778931
  have htrace : WordTrace (prefixWord ++ tailWord_778931) baseStart_778931 baseEnd_778931 := by
    simpa [prefixWord, tailWord_778931, baseEnd_778931] using wordTrace_append hprefix tailTrace_778931
  have hstable : (prefixWord ++ tailWord_778931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778931).length < 2 ^ (prefixWord ++ tailWord_778931).sum := by decide
  have hdescent : baseEnd_778931 < baseStart_778931 := by decide
  rcases family_descends (prefixWord ++ tailWord_778931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778944 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_778944 : Nat := 118140960795 + 778944 * 2 ^ 59
def prefixEnd_778944 : Nat := 4983230072969 + 3 ^ 40 * 778944 * 2
def baseEnd_778944 : Nat := 266648449957270407811805

theorem tailTrace_778944 : CollatzResearch.WordTrace tailWord_778944 prefixEnd_778944 266648449957270407811805 := by
  unfold tailWord_778944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14205210845013197944503943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18940281126684263926005257 14205210845013197944503943)
  ·
    refine ⟨21307816267519796916755915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14205210845013197944503943 21307816267519796916755915)
    ·
      refine ⟨31961724401279695375133873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21307816267519796916755915 31961724401279695375133873)
      ·
        refine ⟨23971293300959771531350405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31961724401279695375133873 23971293300959771531350405)
        ·
          refine ⟨4494617493929957162128201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23971293300959771531350405 4494617493929957162128201)
          ·
            refine ⟨3370963120447467871596151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494617493929957162128201 3370963120447467871596151)
            ·
              refine ⟨5056444680671201807394227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370963120447467871596151 5056444680671201807394227)
              ·
                refine ⟨7584667021006802711091341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056444680671201807394227 7584667021006802711091341)
                ·
                  refine ⟨2844250132877551016659253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7584667021006802711091341 2844250132877551016659253)
                  ·
                    refine ⟨266648449957270407811805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2844250132877551016659253 266648449957270407811805)
                    ·
                      rfl

theorem cell22_778944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_778944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778944 prefixEnd_778944 := by exact prefixLift 778944
  have htrace : WordTrace (prefixWord ++ tailWord_778944) baseStart_778944 baseEnd_778944 := by
    simpa [prefixWord, tailWord_778944, baseEnd_778944] using wordTrace_append hprefix tailTrace_778944
  have hstable : (prefixWord ++ tailWord_778944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778944).length < 2 ^ (prefixWord ++ tailWord_778944).sum := by decide
  have hdescent : baseEnd_778944 < baseStart_778944 := by decide
  rcases family_descends (prefixWord ++ tailWord_778944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778991 : List Nat := [1, 1, 2, 1, 5, 3, 3, 6]
def baseStart_778991 : Nat := 118140960795 + 778991 * 2 ^ 59
def prefixEnd_778991 : Nat := 4983230072969 + 3 ^ 40 * 778991 * 2
def baseEnd_778991 : Nat := 29629393224197550209629

theorem tailTrace_778991 : CollatzResearch.WordTrace tailWord_778991 prefixEnd_778991 29629393224197550209629 := by
  unfold tailWord_778991
  simp only [CollatzResearch.WordTrace]
  refine ⟨28412135920856122915968827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18941423947237415277312551 28412135920856122915968827)
  ·
    refine ⟨42618203881284184373953241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28412135920856122915968827 42618203881284184373953241)
    ·
      refine ⟨31963652910963138280464931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42618203881284184373953241 31963652910963138280464931)
      ·
        refine ⟨47945479366444707420697397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31963652910963138280464931 47945479366444707420697397)
        ·
          refine ⟨4494888690604191320690381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47945479366444707420697397 4494888690604191320690381)
          ·
            refine ⟨1685583258976571745258893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4494888690604191320690381 1685583258976571745258893)
            ·
              refine ⟨632093722116214404472085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1685583258976571745258893 632093722116214404472085)
              ·
                refine ⟨29629393224197550209629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 632093722116214404472085 29629393224197550209629)
                ·
                  rfl

theorem cell22_778991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 6].length) (baseStart_778991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_778991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_778991 prefixEnd_778991 := by exact prefixLift 778991
  have htrace : WordTrace (prefixWord ++ tailWord_778991) baseStart_778991 baseEnd_778991 := by
    simpa [prefixWord, tailWord_778991, baseEnd_778991] using wordTrace_append hprefix tailTrace_778991
  have hstable : (prefixWord ++ tailWord_778991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778991).length < 2 ^ (prefixWord ++ tailWord_778991).sum := by decide
  have hdescent : baseEnd_778991 < baseStart_778991 := by decide
  rcases family_descends (prefixWord ++ tailWord_778991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779023 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 1, 3]
def baseStart_779023 : Nat := 118140960795 + 779023 * 2 ^ 59
def prefixEnd_779023 : Nat := 4983230072969 + 3 ^ 40 * 779023 * 2
def baseEnd_779023 : Nat := 266675493271740535086563

theorem tailTrace_779023 : CollatzResearch.WordTrace tailWord_779023 prefixEnd_779023 266675493271740535086563 := by
  unfold tailWord_779023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413303056740192381133723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18942202037826794920755815 28413303056740192381133723)
  ·
    refine ⟨42619954585110288571700585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28413303056740192381133723 42619954585110288571700585)
    ·
      refine ⟨31964965938832716428775439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42619954585110288571700585 31964965938832716428775439)
      ·
        refine ⟨47947448908249074643163159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31964965938832716428775439 47947448908249074643163159)
        ·
          refine ⟨71921173362373611964744739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47947448908249074643163159 71921173362373611964744739)
          ·
            refine ⟨107881760043560417947117109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71921173362373611964744739 107881760043560417947117109)
            ·
              refine ⟨10113915004083789182542229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107881760043560417947117109 10113915004083789182542229)
              ·
                refine ⟨474089765816427617931667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10113915004083789182542229 474089765816427617931667)
                ·
                  refine ⟨711134648724641426897501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474089765816427617931667 711134648724641426897501)
                  ·
                    refine ⟨266675493271740535086563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711134648724641426897501 266675493271740535086563)
                    ·
                      rfl

theorem cell22_779023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_779023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779023 prefixEnd_779023 := by exact prefixLift 779023
  have htrace : WordTrace (prefixWord ++ tailWord_779023) baseStart_779023 baseEnd_779023 := by
    simpa [prefixWord, tailWord_779023, baseEnd_779023] using wordTrace_append hprefix tailTrace_779023
  have hstable : (prefixWord ++ tailWord_779023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779023).length < 2 ^ (prefixWord ++ tailWord_779023).sum := by decide
  have hdescent : baseEnd_779023 < baseStart_779023 := by decide
  rcases family_descends (prefixWord ++ tailWord_779023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779081 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 6]
def baseStart_779081 : Nat := 118140960795 + 779081 * 2 ^ 59
def prefixEnd_779081 : Nat := 4983230072969 + 3 ^ 40 * 779081 * 2
def baseEnd_779081 : Nat := 88898449285682572378795

theorem tailTrace_779081 : CollatzResearch.WordTrace tailWord_779081 prefixEnd_779081 88898449285682572378795 := by
  unfold tailWord_779081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415418490530068286745097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943612327020045524496731 28415418490530068286745097)
  ·
    refine ⟨21311563867897551215058823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28415418490530068286745097 21311563867897551215058823)
    ·
      refine ⟨31967345801846326822588235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311563867897551215058823 31967345801846326822588235)
      ·
        refine ⟨47951018702769490233882353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31967345801846326822588235 47951018702769490233882353)
        ·
          refine ⟨35963264027077117675411765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47951018702769490233882353 35963264027077117675411765)
          ·
            refine ⟨3371556002538479782069853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35963264027077117675411765 3371556002538479782069853)
            ·
              refine ⟨1264333500951929918276195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371556002538479782069853 1264333500951929918276195)
              ·
                refine ⟨1896500251427894877414293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264333500951929918276195 1896500251427894877414293)
                ·
                  refine ⟨88898449285682572378795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1896500251427894877414293 88898449285682572378795)
                  ·
                    rfl

theorem cell22_779081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_779081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779081 prefixEnd_779081 := by exact prefixLift 779081
  have htrace : WordTrace (prefixWord ++ tailWord_779081) baseStart_779081 baseEnd_779081 := by
    simpa [prefixWord, tailWord_779081, baseEnd_779081] using wordTrace_append hprefix tailTrace_779081
  have hstable : (prefixWord ++ tailWord_779081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779081).length < 2 ^ (prefixWord ++ tailWord_779081).sum := by decide
  have hdescent : baseEnd_779081 < baseStart_779081 := by decide
  rcases family_descends (prefixWord ++ tailWord_779081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779100 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_779100 : Nat := 118140960795 + 779100 * 2 ^ 59
def prefixEnd_779100 : Nat := 4983230072969 + 3 ^ 40 * 779100 * 2
def baseEnd_779100 : Nat := 266701851945338000911327

theorem tailTrace_779100 : CollatzResearch.WordTrace tailWord_779100 prefixEnd_779100 266701851945338000911327 := by
  unfold tailWord_779100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208055738730617265843377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18944074318307489687791169 14208055738730617265843377)
  ·
    refine ⟨10656041804047962949382533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14208055738730617265843377 10656041804047962949382533)
    ·
      refine ⟨1998007838258993053009225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10656041804047962949382533 1998007838258993053009225)
      ·
        refine ⟨1498505878694244789756919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998007838258993053009225 1498505878694244789756919)
        ·
          refine ⟨2247758818041367184635379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498505878694244789756919 2247758818041367184635379)
          ·
            refine ⟨3371638227062050776953069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247758818041367184635379 3371638227062050776953069)
            ·
              refine ⟨1264364335148269041357401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371638227062050776953069 1264364335148269041357401)
              ·
                refine ⟨948273251361201781018051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264364335148269041357401 948273251361201781018051)
                ·
                  refine ⟨1422409877041802671527077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948273251361201781018051 1422409877041802671527077)
                  ·
                    refine ⟨266701851945338000911327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422409877041802671527077 266701851945338000911327)
                    ·
                      rfl

theorem cell22_779100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_779100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779100 prefixEnd_779100 := by exact prefixLift 779100
  have htrace : WordTrace (prefixWord ++ tailWord_779100) baseStart_779100 baseEnd_779100 := by
    simpa [prefixWord, tailWord_779100, baseEnd_779100] using wordTrace_append hprefix tailTrace_779100
  have hstable : (prefixWord ++ tailWord_779100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779100).length < 2 ^ (prefixWord ++ tailWord_779100).sum := by decide
  have hdescent : baseEnd_779100 < baseStart_779100 := by decide
  rcases family_descends (prefixWord ++ tailWord_779100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779143 : List Nat := [1, 1, 4, 2, 3, 3, 1, 7]
def baseStart_779143 : Nat := 118140960795 + 779143 * 2 ^ 59
def prefixEnd_779143 : Nat := 4983230072969 + 3 ^ 40 * 779143 * 2
def baseEnd_779143 : Nat := 29635174636011135787355

theorem tailTrace_779143 : CollatzResearch.WordTrace tailWord_779143 prefixEnd_779143 29635174636011135787355 := by
  unfold tailWord_779143
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417679816305452875502083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18945119877536968583668055 28417679816305452875502083)
  ·
    refine ⟨42626519724458179313253125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28417679816305452875502083 42626519724458179313253125)
    ·
      refine ⟨7992472448335908621234961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42626519724458179313253125 7992472448335908621234961)
      ·
        refine ⟨5994354336251931465926221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7992472448335908621234961 5994354336251931465926221)
        ·
          refine ⟨2247882876094474299722333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5994354336251931465926221 2247882876094474299722333)
          ·
            refine ⟨842956078535427862395875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2247882876094474299722333 842956078535427862395875)
            ·
              refine ⟨1264434117803141793593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842956078535427862395875 1264434117803141793593813)
              ·
                refine ⟨29635174636011135787355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1264434117803141793593813 29635174636011135787355)
                ·
                  rfl

theorem cell22_779143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 7].length) (baseStart_779143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779143 prefixEnd_779143 := by exact prefixLift 779143
  have htrace : WordTrace (prefixWord ++ tailWord_779143) baseStart_779143 baseEnd_779143 := by
    simpa [prefixWord, tailWord_779143, baseEnd_779143] using wordTrace_append hprefix tailTrace_779143
  have hstable : (prefixWord ++ tailWord_779143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779143).length < 2 ^ (prefixWord ++ tailWord_779143).sum := by decide
  have hdescent : baseEnd_779143 < baseStart_779143 := by decide
  rcases family_descends (prefixWord ++ tailWord_779143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779162 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_779162 : Nat := 118140960795 + 779162 * 2 ^ 59
def prefixEnd_779162 : Nat := 4983230072969 + 3 ^ 40 * 779162 * 2
def baseEnd_779162 : Nat := 266723075812390505861137

theorem tailTrace_779162 : CollatzResearch.WordTrace tailWord_779162 prefixEnd_779162 266723075812390505861137 := by
  unfold tailWord_779162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104593200809154780110935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18945581868824412746962493 7104593200809154780110935)
  ·
    refine ⟨10656889801213732170166403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7104593200809154780110935 10656889801213732170166403)
    ·
      refine ⟨15985334701820598255249605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656889801213732170166403 15985334701820598255249605)
      ·
        refine ⟨2997250256591362172859301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15985334701820598255249605 2997250256591362172859301)
        ·
          refine ⟨561984423110880407411119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2997250256591362172859301 561984423110880407411119)
          ·
            refine ⟨842976634666320611116679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561984423110880407411119 842976634666320611116679)
            ·
              refine ⟨1264464951999480916675019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842976634666320611116679 1264464951999480916675019)
              ·
                refine ⟨1896697427999221375012529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264464951999480916675019 1896697427999221375012529)
                ·
                  refine ⟨1422523070999416031259397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896697427999221375012529 1422523070999416031259397)
                  ·
                    refine ⟨266723075812390505861137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422523070999416031259397 266723075812390505861137)
                    ·
                      rfl

theorem cell22_779162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_779162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779162 prefixEnd_779162 := by exact prefixLift 779162
  have htrace : WordTrace (prefixWord ++ tailWord_779162) baseStart_779162 baseEnd_779162 := by
    simpa [prefixWord, tailWord_779162, baseEnd_779162] using wordTrace_append hprefix tailTrace_779162
  have hstable : (prefixWord ++ tailWord_779162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779162).length < 2 ^ (prefixWord ++ tailWord_779162).sum := by decide
  have hdescent : baseEnd_779162 < baseStart_779162 := by decide
  rcases family_descends (prefixWord ++ tailWord_779162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779181 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_779181 : Nat := 118140960795 + 779181 * 2 ^ 59
def prefixEnd_779181 : Nat := 4983230072969 + 3 ^ 40 * 779181 * 2
def baseEnd_779181 : Nat := 266729579900680789636079

theorem tailTrace_779181 : CollatzResearch.WordTrace tailWord_779181 prefixEnd_779181 266729579900680789636079 := by
  unfold tailWord_779181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28419065790167785365385397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18946043860111856910256931 28419065790167785365385397)
  ·
    refine ⟨2664287417828229878004881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28419065790167785365385397 2664287417828229878004881)
    ·
      refine ⟨1998215563371172408503661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664287417828229878004881 1998215563371172408503661)
      ·
        refine ⟨749330836264189653188873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1998215563371172408503661 749330836264189653188873)
        ·
          refine ⟨561998127198142239891655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749330836264189653188873 561998127198142239891655)
          ·
            refine ⟨842997190797213359837483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561998127198142239891655 842997190797213359837483)
            ·
              refine ⟨1264495786195820039756225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842997190797213359837483 1264495786195820039756225)
              ·
                refine ⟨948371839646865029817169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264495786195820039756225 948371839646865029817169)
                ·
                  refine ⟨711278879735148772362877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 948371839646865029817169 711278879735148772362877)
                  ·
                    refine ⟨266729579900680789636079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711278879735148772362877 266729579900680789636079)
                    ·
                      rfl

theorem cell22_779181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_779181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779181 prefixEnd_779181 := by exact prefixLift 779181
  have htrace : WordTrace (prefixWord ++ tailWord_779181) baseStart_779181 baseEnd_779181 := by
    simpa [prefixWord, tailWord_779181, baseEnd_779181] using wordTrace_append hprefix tailTrace_779181
  have hstable : (prefixWord ++ tailWord_779181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779181).length < 2 ^ (prefixWord ++ tailWord_779181).sum := by decide
  have hdescent : baseEnd_779181 < baseStart_779181 := by decide
  rcases family_descends (prefixWord ++ tailWord_779181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779278 : List Nat := [4, 1, 1, 2, 2, 2, 2, 8]
def baseStart_779278 : Nat := 118140960795 + 779278 * 2 ^ 59
def prefixEnd_779278 : Nat := 4983230072969 + 3 ^ 40 * 779278 * 2
def baseEnd_779278 : Nat := 29640309442556096662309

theorem tailTrace_779278 : CollatzResearch.WordTrace tailWord_779278 prefixEnd_779278 29640309442556096662309 := by
  unfold tailWord_779278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552825458852046366458311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18948402447210913954444325 3552825458852046366458311)
  ·
    refine ⟨5329238188278069549687467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552825458852046366458311 5329238188278069549687467)
    ·
      refine ⟨7993857282417104324531201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329238188278069549687467 7993857282417104324531201)
      ·
        refine ⟨5995392961812828243398401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7993857282417104324531201 5995392961812828243398401)
        ·
          refine ⟨4496544721359621182548801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995392961812828243398401 4496544721359621182548801)
          ·
            refine ⟨3372408541019715886911601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496544721359621182548801 3372408541019715886911601)
            ·
              refine ⟨2529306405764786915183701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372408541019715886911601 2529306405764786915183701)
              ·
                refine ⟨29640309442556096662309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2529306405764786915183701 29640309442556096662309)
                ·
                  rfl

theorem cell22_779278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_779278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779278 prefixEnd_779278 := by exact prefixLift 779278
  have htrace : WordTrace (prefixWord ++ tailWord_779278) baseStart_779278 baseEnd_779278 := by
    simpa [prefixWord, tailWord_779278, baseEnd_779278] using wordTrace_append hprefix tailTrace_779278
  have hstable : (prefixWord ++ tailWord_779278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779278).length < 2 ^ (prefixWord ++ tailWord_779278).sum := by decide
  have hdescent : baseEnd_779278 < baseStart_779278 := by decide
  rcases family_descends (prefixWord ++ tailWord_779278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_779353 : Nat := 118140960795 + 779353 * 2 ^ 59
def prefixEnd_779353 : Nat := 4983230072969 + 3 ^ 40 * 779353 * 2
def baseEnd_779353 : Nat := 266788459015729674335551

theorem tailTrace_779353 : CollatzResearch.WordTrace tailWord_779353 prefixEnd_779353 266788459015729674335551 := by
  unfold tailWord_779353
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425339145544658740646713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950226097029772493764475 28425339145544658740646713)
  ·
    refine ⟨21319004359158494055485035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28425339145544658740646713 21319004359158494055485035)
    ·
      refine ⟨31978506538737741083227553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21319004359158494055485035 31978506538737741083227553)
      ·
        refine ⟨23983879904053305812420665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31978506538737741083227553 23983879904053305812420665)
        ·
          refine ⟨17987909928039979359315499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23983879904053305812420665 17987909928039979359315499)
          ·
            refine ⟨26981864892059969038973249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987909928039979359315499 26981864892059969038973249)
            ·
              refine ⟨20236398669044976779229937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26981864892059969038973249 20236398669044976779229937)
              ·
                refine ⟨15177299001783732584422453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20236398669044976779229937 15177299001783732584422453)
                ·
                  refine ⟨1422871781417224929789605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15177299001783732584422453 1422871781417224929789605)
                  ·
                    refine ⟨266788459015729674335551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422871781417224929789605 266788459015729674335551)
                    ·
                      rfl

theorem cell22_779353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_779353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779353 prefixEnd_779353 := by exact prefixLift 779353
  have htrace : WordTrace (prefixWord ++ tailWord_779353) baseStart_779353 baseEnd_779353 := by
    simpa [prefixWord, tailWord_779353, baseEnd_779353] using wordTrace_append hprefix tailTrace_779353
  have hstable : (prefixWord ++ tailWord_779353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779353).length < 2 ^ (prefixWord ++ tailWord_779353).sum := by decide
  have hdescent : baseEnd_779353 < baseStart_779353 := by decide
  rcases family_descends (prefixWord ++ tailWord_779353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779357 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 7]
def baseStart_779357 : Nat := 118140960795 + 779357 * 2 ^ 59
def prefixEnd_779357 : Nat := 4983230072969 + 3 ^ 40 * 779357 * 2
def baseEnd_779357 : Nat := 88929942765824999078513

theorem tailTrace_779357 : CollatzResearch.WordTrace tailWord_779357 prefixEnd_779357 88929942765824999078513 := by
  unfold tailWord_779357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425485037530167423792325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950323358353444949194883 28425485037530167423792325)
  ·
    refine ⟨5329778444536906391961061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28425485037530167423792325 5329778444536906391961061)
    ·
      refine ⟨999333458350669948492699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5329778444536906391961061 999333458350669948492699)
      ·
        refine ⟨1499000187526004922739049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999333458350669948492699 1499000187526004922739049)
        ·
          refine ⟨1124250140644503692054287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499000187526004922739049 1124250140644503692054287)
          ·
            refine ⟨1686375210966755538081431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124250140644503692054287 1686375210966755538081431)
            ·
              refine ⟨2529562816450133307122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686375210966755538081431 2529562816450133307122147)
              ·
                refine ⟨3794344224675199960683221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529562816450133307122147 3794344224675199960683221)
                ·
                  refine ⟨88929942765824999078513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3794344224675199960683221 88929942765824999078513)
                  ·
                    rfl

theorem cell22_779357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_779357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779357 prefixEnd_779357 := by exact prefixLift 779357
  have htrace : WordTrace (prefixWord ++ tailWord_779357) baseStart_779357 baseEnd_779357 := by
    simpa [prefixWord, tailWord_779357, baseEnd_779357] using wordTrace_append hprefix tailTrace_779357
  have hstable : (prefixWord ++ tailWord_779357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779357).length < 2 ^ (prefixWord ++ tailWord_779357).sum := by decide
  have hdescent : baseEnd_779357 < baseStart_779357 := by decide
  rcases family_descends (prefixWord ++ tailWord_779357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779415 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_779415 : Nat := 118140960795 + 779415 * 2 ^ 59
def prefixEnd_779415 : Nat := 4983230072969 + 3 ^ 40 * 779415 * 2
def baseEnd_779415 : Nat := 266809682882782179285361

theorem tailTrace_779415 : CollatzResearch.WordTrace tailWord_779415 prefixEnd_779415 266809682882782179285361 := by
  unfold tailWord_779415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28427600471320043329403699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18951733647546695552935799 28427600471320043329403699)
  ·
    refine ⟨42641400706980064994105549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28427600471320043329403699 42641400706980064994105549)
    ·
      refine ⟨15990525265117524372789581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42641400706980064994105549 15990525265117524372789581)
      ·
        refine ⟨5996446974419071639796093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15990525265117524372789581 5996446974419071639796093)
        ·
          refine ⟨2248667615407151864923535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5996446974419071639796093 2248667615407151864923535)
          ·
            refine ⟨3373001423110727797385303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248667615407151864923535 3373001423110727797385303)
            ·
              refine ⟨5059502134666091696077955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373001423110727797385303 5059502134666091696077955)
              ·
                refine ⟨7589253201999137544116933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059502134666091696077955 7589253201999137544116933)
                ·
                  refine ⟨1422984975374838289521925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7589253201999137544116933 1422984975374838289521925)
                  ·
                    refine ⟨266809682882782179285361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422984975374838289521925 266809682882782179285361)
                    ·
                      rfl

theorem cell22_779415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_779415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779415 prefixEnd_779415 := by exact prefixLift 779415
  have htrace : WordTrace (prefixWord ++ tailWord_779415) baseStart_779415 baseEnd_779415 := by
    simpa [prefixWord, tailWord_779415, baseEnd_779415] using wordTrace_append hprefix tailTrace_779415
  have hstable : (prefixWord ++ tailWord_779415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779415).length < 2 ^ (prefixWord ++ tailWord_779415).sum := by decide
  have hdescent : baseEnd_779415 < baseStart_779415 := by decide
  rcases family_descends (prefixWord ++ tailWord_779415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779537 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 4]
def baseStart_779537 : Nat := 118140960795 + 779537 * 2 ^ 59
def prefixEnd_779537 : Nat := 4983230072969 + 3 ^ 40 * 779537 * 2
def baseEnd_779537 : Nat := 88950481992004842578329

theorem tailTrace_779537 : CollatzResearch.WordTrace tailWord_779537 prefixEnd_779537 88950481992004842578329 := by
  unfold tailWord_779537
  simp only [CollatzResearch.WordTrace]
  refine ⟨28432050176878058165344865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18954700117918705443563243 28432050176878058165344865)
  ·
    refine ⟨21324037632658543624008649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28432050176878058165344865 21324037632658543624008649)
    ·
      refine ⟨15993028224493907718006487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21324037632658543624008649 15993028224493907718006487)
      ·
        refine ⟨23989542336740861577009731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993028224493907718006487 23989542336740861577009731)
        ·
          refine ⟨35984313505111292365514597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23989542336740861577009731 35984313505111292365514597)
          ·
            refine ⟨6747058782208367318533987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35984313505111292365514597 6747058782208367318533987)
            ·
              refine ⟨10120588173312550977800981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747058782208367318533987 10120588173312550977800981)
              ·
                refine ⟨474402570624025827084421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10120588173312550977800981 474402570624025827084421)
                ·
                  refine ⟨88950481992004842578329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474402570624025827084421 88950481992004842578329)
                  ·
                    rfl

theorem cell22_779537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_779537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779537 prefixEnd_779537 := by exact prefixLift 779537
  have htrace : WordTrace (prefixWord ++ tailWord_779537) baseStart_779537 baseEnd_779537 := by
    simpa [prefixWord, tailWord_779537, baseEnd_779537] using wordTrace_append hprefix tailTrace_779537
  have hstable : (prefixWord ++ tailWord_779537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779537).length < 2 ^ (prefixWord ++ tailWord_779537).sum := by decide
  have hdescent : baseEnd_779537 < baseStart_779537 := by decide
  rcases family_descends (prefixWord ++ tailWord_779537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779588 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_779588 : Nat := 118140960795 + 779588 * 2 ^ 59
def prefixEnd_779588 : Nat := 4983230072969 + 3 ^ 40 * 779588 * 2
def baseEnd_779588 : Nat := 88956301439422464903277

theorem tailTrace_779588 : CollatzResearch.WordTrace tailWord_779588 prefixEnd_779588 88956301439422464903277 := by
  unfold tailWord_779588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216955149846646937725709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18955940199795529250300945 14216955149846646937725709)
  ·
    refine ⟨5331358181192492601647141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14216955149846646937725709 5331358181192492601647141)
    ·
      refine ⟨999629658973592362808839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5331358181192492601647141 999629658973592362808839)
      ·
        refine ⟨1499444488460388544213259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999629658973592362808839 1499444488460388544213259)
        ·
          refine ⟨2249166732690582816319889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499444488460388544213259 2249166732690582816319889)
          ·
            refine ⟨1686875049517937112239917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2249166732690582816319889 1686875049517937112239917)
            ·
              refine ⟨632578143569226417089969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686875049517937112239917 632578143569226417089969)
              ·
                refine ⟨474433607676919812817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632578143569226417089969 474433607676919812817477)
                ·
                  refine ⟨88956301439422464903277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474433607676919812817477 88956301439422464903277)
                  ·
                    rfl

theorem cell22_779588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_779588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779588 prefixEnd_779588 := by exact prefixLift 779588
  have htrace : WordTrace (prefixWord ++ tailWord_779588) baseStart_779588 baseEnd_779588 := by
    simpa [prefixWord, tailWord_779588, baseEnd_779588] using wordTrace_append hprefix tailTrace_779588
  have hstable : (prefixWord ++ tailWord_779588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779588).length < 2 ^ (prefixWord ++ tailWord_779588).sum := by decide
  have hdescent : baseEnd_779588 < baseStart_779588 := by decide
  rcases family_descends (prefixWord ++ tailWord_779588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779625 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_779625 : Nat := 118140960795 + 779625 * 2 ^ 59
def prefixEnd_779625 : Nat := 4983230072969 + 3 ^ 40 * 779625 * 2
def baseEnd_779625 : Nat := 266881570174411631534717

theorem tailTrace_779625 : CollatzResearch.WordTrace tailWord_779625 prefixEnd_779625 266881570174411631534717 := by
  unfold tailWord_779625
  simp only [CollatzResearch.WordTrace]
  refine ⟨28435259800559249194548329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18956839867039499463032219 28435259800559249194548329)
  ·
    refine ⟨21326444850419436895911247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28435259800559249194548329 21326444850419436895911247)
    ·
      refine ⟨31989667275629155343866871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326444850419436895911247 31989667275629155343866871)
      ·
        refine ⟨47984500913443733015800307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31989667275629155343866871 47984500913443733015800307)
        ·
          refine ⟨71976751370165599523700461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47984500913443733015800307 71976751370165599523700461)
          ·
            refine ⟨26991281763812099821387673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71976751370165599523700461 26991281763812099821387673)
            ·
              refine ⟨20243461322859074866040755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26991281763812099821387673 20243461322859074866040755)
              ·
                refine ⟨30365191984288612299061133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20243461322859074866040755 30365191984288612299061133)
                ·
                  refine ⟨11386946994108229612147925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30365191984288612299061133 11386946994108229612147925)
                  ·
                    refine ⟨266881570174411631534717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11386946994108229612147925 266881570174411631534717)
                    ·
                      rfl

theorem cell22_779625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_779625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779625 prefixEnd_779625 := by exact prefixLift 779625
  have htrace : WordTrace (prefixWord ++ tailWord_779625) baseStart_779625 baseEnd_779625 := by
    simpa [prefixWord, tailWord_779625, baseEnd_779625] using wordTrace_append hprefix tailTrace_779625
  have hstable : (prefixWord ++ tailWord_779625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779625).length < 2 ^ (prefixWord ++ tailWord_779625).sum := by decide
  have hdescent : baseEnd_779625 < baseStart_779625 := by decide
  rcases family_descends (prefixWord ++ tailWord_779625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779674 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_779674 : Nat := 118140960795 + 779674 * 2 ^ 59
def prefixEnd_779674 : Nat := 4983230072969 + 3 ^ 40 * 779674 * 2
def baseEnd_779674 : Nat := 266898343875791837059567

theorem tailTrace_779674 : CollatzResearch.WordTrace tailWord_779674 prefixEnd_779674 266898343875791837059567 := by
  unfold tailWord_779674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109261744345432640770519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18958031318254487042054717 7109261744345432640770519)
  ·
    refine ⟨10663892616518148961155779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7109261744345432640770519 10663892616518148961155779)
    ·
      refine ⟨15995838924777223441733669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10663892616518148961155779 15995838924777223441733669)
      ·
        refine ⟨2999219798395729395325063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15995838924777223441733669 2999219798395729395325063)
        ·
          refine ⟨4498829697593594092987595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999219798395729395325063 4498829697593594092987595)
          ·
            refine ⟨6748244546390391139481393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498829697593594092987595 6748244546390391139481393)
            ·
              refine ⟨5061183409792793354611045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6748244546390391139481393 5061183409792793354611045)
              ·
                refine ⟨948971889336148753989571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5061183409792793354611045 948971889336148753989571)
                ·
                  refine ⟨1423457834004223130984357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948971889336148753989571 1423457834004223130984357)
                  ·
                    refine ⟨266898343875791837059567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423457834004223130984357 266898343875791837059567)
                    ·
                      rfl

theorem cell22_779674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_779674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779674 prefixEnd_779674 := by exact prefixLift 779674
  have htrace : WordTrace (prefixWord ++ tailWord_779674) baseStart_779674 baseEnd_779674 := by
    simpa [prefixWord, tailWord_779674, baseEnd_779674] using wordTrace_append hprefix tailTrace_779674
  have hstable : (prefixWord ++ tailWord_779674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779674).length < 2 ^ (prefixWord ++ tailWord_779674).sum := by decide
  have hdescent : baseEnd_779674 < baseStart_779674 := by decide
  rcases family_descends (prefixWord ++ tailWord_779674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779839 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_779839 : Nat := 118140960795 + 779839 * 2 ^ 59
def prefixEnd_779839 : Nat := 4983230072969 + 3 ^ 40 * 779839 * 2
def baseEnd_779839 : Nat := 266954826747786406684061

theorem tailTrace_779839 : CollatzResearch.WordTrace tailWord_779839 prefixEnd_779839 266954826747786406684061 := by
  unfold tailWord_779839
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443065021783963742838571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18962043347855975828559047 28443065021783963742838571)
  ·
    refine ⟨42664597532675945614257857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28443065021783963742838571 42664597532675945614257857)
    ·
      refine ⟨31998448149506959210693393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42664597532675945614257857 31998448149506959210693393)
      ·
        refine ⟨23998836112130219408020045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31998448149506959210693393 23998836112130219408020045)
        ·
          refine ⟨8999563542048832278007517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23998836112130219408020045 8999563542048832278007517)
          ·
            refine ⟨3374836328268312104252819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8999563542048832278007517 3374836328268312104252819)
            ·
              refine ⟨5062254492402468156379229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374836328268312104252819 5062254492402468156379229)
              ·
                refine ⟨1898345434650925558642211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5062254492402468156379229 1898345434650925558642211)
                ·
                  refine ⟨2847518151976388337963317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898345434650925558642211 2847518151976388337963317)
                  ·
                    refine ⟨266954826747786406684061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847518151976388337963317 266954826747786406684061)
                    ·
                      rfl

theorem cell22_779839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_779839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779839 prefixEnd_779839 := by exact prefixLift 779839
  have htrace : WordTrace (prefixWord ++ tailWord_779839) baseStart_779839 baseEnd_779839 := by
    simpa [prefixWord, tailWord_779839, baseEnd_779839] using wordTrace_append hprefix tailTrace_779839
  have hstable : (prefixWord ++ tailWord_779839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779839).length < 2 ^ (prefixWord ++ tailWord_779839).sum := by decide
  have hdescent : baseEnd_779839 < baseStart_779839 := by decide
  rcases family_descends (prefixWord ++ tailWord_779839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779858 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_779858 : Nat := 118140960795 + 779858 * 2 ^ 59
def prefixEnd_779858 : Nat := 4983230072969 + 3 ^ 40 * 779858 * 2
def baseEnd_779858 : Nat := 88987110278692230153001

theorem tailTrace_779858 : CollatzResearch.WordTrace tailWord_779858 prefixEnd_779858 88987110278692230153001 := by
  unfold tailWord_779858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110939502178782496945057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18962505339143419991853485 7110939502178782496945057)
  ·
    refine ⟨5333204626634086872708793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7110939502178782496945057 5333204626634086872708793)
    ·
      refine ⟨3999903469975565154531595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333204626634086872708793 3999903469975565154531595)
      ·
        refine ⟨5999855204963347731797393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999903469975565154531595 5999855204963347731797393)
        ·
          refine ⟨4499891403722510798848045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5999855204963347731797393 4499891403722510798848045)
          ·
            refine ⟨1687459276395941549568017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4499891403722510798848045 1687459276395941549568017)
            ·
              refine ⟨1265594457296956162176013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687459276395941549568017 1265594457296956162176013)
              ·
                refine ⟨474597921486358560816005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265594457296956162176013 474597921486358560816005)
                ·
                  refine ⟨88987110278692230153001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474597921486358560816005 88987110278692230153001)
                  ·
                    rfl

theorem cell22_779858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_779858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779858 prefixEnd_779858 := by exact prefixLift 779858
  have htrace : WordTrace (prefixWord ++ tailWord_779858) baseStart_779858 baseEnd_779858 := by
    simpa [prefixWord, tailWord_779858, baseEnd_779858] using wordTrace_append hprefix tailTrace_779858
  have hstable : (prefixWord ++ tailWord_779858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779858).length < 2 ^ (prefixWord ++ tailWord_779858).sum := by decide
  have hdescent : baseEnd_779858 < baseStart_779858 := by decide
  rcases family_descends (prefixWord ++ tailWord_779858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779890 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_779890 : Nat := 118140960795 + 779890 * 2 ^ 59
def prefixEnd_779890 : Nat := 4983230072969 + 3 ^ 40 * 779890 * 2
def baseEnd_779890 : Nat := 266972285090039273658905

theorem tailTrace_779890 : CollatzResearch.WordTrace tailWord_779890 prefixEnd_779890 266972285090039273658905 := by
  unfold tailWord_779890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111231286149799863236281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18963283429732799635296749 7111231286149799863236281)
  ·
    refine ⟨5333423464612349897427211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7111231286149799863236281 5333423464612349897427211)
    ·
      refine ⟨8000135196918524846140817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333423464612349897427211 8000135196918524846140817)
      ·
        refine ⟨6000101397688893634605613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000135196918524846140817 6000101397688893634605613)
        ·
          refine ⟨2250038024133335112977105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6000101397688893634605613 2250038024133335112977105)
          ·
            refine ⟨1687528518100001334732829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250038024133335112977105 1687528518100001334732829)
            ·
              refine ⟨632823194287500500524811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1687528518100001334732829 632823194287500500524811)
              ·
                refine ⟨949234791431250750787217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632823194287500500524811 949234791431250750787217)
                ·
                  refine ⟨711926093573438063090413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 949234791431250750787217 711926093573438063090413)
                  ·
                    refine ⟨266972285090039273658905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711926093573438063090413 266972285090039273658905)
                    ·
                      rfl

theorem cell22_779890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_779890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779890 prefixEnd_779890 := by exact prefixLift 779890
  have htrace : WordTrace (prefixWord ++ tailWord_779890) baseStart_779890 baseEnd_779890 := by
    simpa [prefixWord, tailWord_779890, baseEnd_779890] using wordTrace_append hprefix tailTrace_779890
  have hstable : (prefixWord ++ tailWord_779890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779890).length < 2 ^ (prefixWord ++ tailWord_779890).sum := by decide
  have hdescent : baseEnd_779890 < baseStart_779890 := by decide
  rcases family_descends (prefixWord ++ tailWord_779890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779929 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_779929 : Nat := 118140960795 + 779929 * 2 ^ 59
def prefixEnd_779929 : Nat := 4983230072969 + 3 ^ 40 * 779929 * 2
def baseEnd_779929 : Nat := 266985635587056171933785

theorem tailTrace_779929 : CollatzResearch.WordTrace tailWord_779929 prefixEnd_779929 266985635587056171933785 := by
  unfold tailWord_779929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28446347591457909113614841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18964231727638606075743227 28446347591457909113614841)
  ·
    refine ⟨21334760693593431835211131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28446347591457909113614841 21334760693593431835211131)
    ·
      refine ⟨32002141040390147752816697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21334760693593431835211131 32002141040390147752816697)
      ·
        refine ⟨24001605780292610814612523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32002141040390147752816697 24001605780292610814612523)
        ·
          refine ⟨36002408670438916221918785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24001605780292610814612523 36002408670438916221918785)
          ·
            refine ⟨27001806502829187166439089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36002408670438916221918785 27001806502829187166439089)
            ·
              refine ⟨20251354877121890374829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27001806502829187166439089 20251354877121890374829317)
              ·
                refine ⟨3797129039460354445280497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20251354877121890374829317 3797129039460354445280497)
                ·
                  refine ⟨2847846779595265833960373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797129039460354445280497 2847846779595265833960373)
                  ·
                    refine ⟨266985635587056171933785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847846779595265833960373 266985635587056171933785)
                    ·
                      rfl

theorem cell22_779929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_779929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779929 prefixEnd_779929 := by exact prefixLift 779929
  have htrace : WordTrace (prefixWord ++ tailWord_779929) baseStart_779929 baseEnd_779929 := by
    simpa [prefixWord, tailWord_779929, baseEnd_779929] using wordTrace_append hprefix tailTrace_779929
  have hstable : (prefixWord ++ tailWord_779929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779929).length < 2 ^ (prefixWord ++ tailWord_779929).sum := by decide
  have hdescent : baseEnd_779929 < baseStart_779929 := by decide
  rcases family_descends (prefixWord ++ tailWord_779929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779993 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 4]
def baseStart_779993 : Nat := 118140960795 + 779993 * 2 ^ 59
def prefixEnd_779993 : Nat := 4983230072969 + 3 ^ 40 * 779993 * 2
def baseEnd_779993 : Nat := 89002514698327112777863

theorem tailTrace_779993 : CollatzResearch.WordTrace tailWord_779993 prefixEnd_779993 89002514698327112777863 := by
  unfold tailWord_779993
  simp only [CollatzResearch.WordTrace]
  refine ⟨28448681863226048043944633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18965787908817365362629755 28448681863226048043944633)
  ·
    refine ⟨21336511397419536032958475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28448681863226048043944633 21336511397419536032958475)
    ·
      refine ⟨32004767096129304049437713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21336511397419536032958475 32004767096129304049437713)
      ·
        refine ⟨24003575322096978037078285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32004767096129304049437713 24003575322096978037078285)
        ·
          refine ⟨9001340745786366763904357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24003575322096978037078285 9001340745786366763904357)
          ·
            refine ⟨1687751389834943768232067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9001340745786366763904357 1687751389834943768232067)
            ·
              refine ⟨2531627084752415652348101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687751389834943768232067 2531627084752415652348101)
              ·
                refine ⟨474680078391077934815269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2531627084752415652348101 474680078391077934815269)
                ·
                  refine ⟨89002514698327112777863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474680078391077934815269 89002514698327112777863)
                  ·
                    rfl

theorem cell22_779993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_779993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_779993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_779993 prefixEnd_779993 := by exact prefixLift 779993
  have htrace : WordTrace (prefixWord ++ tailWord_779993) baseStart_779993 baseEnd_779993 := by
    simpa [prefixWord, tailWord_779993, baseEnd_779993] using wordTrace_append hprefix tailTrace_779993
  have hstable : (prefixWord ++ tailWord_779993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779993).length < 2 ^ (prefixWord ++ tailWord_779993).sum := by decide
  have hdescent : baseEnd_779993 < baseStart_779993 := by decide
  rcases family_descends (prefixWord ++ tailWord_779993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780008 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_780008 : Nat := 118140960795 + 780008 * 2 ^ 59
def prefixEnd_780008 : Nat := 4983230072969 + 3 ^ 40 * 780008 * 2
def baseEnd_780008 : Nat := 267012678901526299208543

theorem tailTrace_780008 : CollatzResearch.WordTrace tailWord_780008 prefixEnd_780008 267012678901526299208543 := by
  unfold tailWord_780008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14224614479085852802870339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18966152638781137070493785 14224614479085852802870339)
  ·
    refine ⟨21336921718628779204305509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14224614479085852802870339 21336921718628779204305509)
    ·
      refine ⟨4000672822242896100807283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21336921718628779204305509 4000672822242896100807283)
      ·
        refine ⟨6001009233364344151210925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000672822242896100807283 6001009233364344151210925)
        ·
          refine ⟨2250378462511629056704097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6001009233364344151210925 2250378462511629056704097)
          ·
            refine ⟨1687783846883721792528073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250378462511629056704097 1687783846883721792528073)
            ·
              refine ⟨1265837885162791344396055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687783846883721792528073 1265837885162791344396055)
              ·
                refine ⟨1898756827744187016594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265837885162791344396055 1898756827744187016594083)
                ·
                  refine ⟨2848135241616280524891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898756827744187016594083 2848135241616280524891125)
                  ·
                    refine ⟨267012678901526299208543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2848135241616280524891125 267012678901526299208543)
                    ·
                      rfl

theorem cell22_780008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_780008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780008 prefixEnd_780008 := by exact prefixLift 780008
  have htrace : WordTrace (prefixWord ++ tailWord_780008) baseStart_780008 baseEnd_780008 := by
    simpa [prefixWord, tailWord_780008, baseEnd_780008] using wordTrace_append hprefix tailTrace_780008
  have hstable : (prefixWord ++ tailWord_780008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780008).length < 2 ^ (prefixWord ++ tailWord_780008).sum := by decide
  have hdescent : baseEnd_780008 < baseStart_780008 := by decide
  rcases family_descends (prefixWord ++ tailWord_780008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780053 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_780053 : Nat := 118140960795 + 780053 * 2 ^ 59
def prefixEnd_780053 : Nat := 4983230072969 + 3 ^ 40 * 780053 * 2
def baseEnd_780053 : Nat := 267028083321161181833405

theorem tailTrace_780053 : CollatzResearch.WordTrace tailWord_780053 prefixEnd_780053 267028083321161181833405 := by
  unfold tailWord_780053
  simp only [CollatzResearch.WordTrace]
  refine ⟨28450870243008678291128813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18967246828672452194085875 28450870243008678291128813)
  ·
    refine ⟨10669076341128254359173305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28450870243008678291128813 10669076341128254359173305)
    ·
      refine ⟨8001807255846190769379979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10669076341128254359173305 8001807255846190769379979)
      ·
        refine ⟨12002710883769286154069969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001807255846190769379979 12002710883769286154069969)
        ·
          refine ⟨9002033162826964615552477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002710883769286154069969 9002033162826964615552477)
          ·
            refine ⟨3375762436060111730832179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9002033162826964615552477 3375762436060111730832179)
            ·
              refine ⟨5063643654090167596248269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375762436060111730832179 5063643654090167596248269)
              ·
                refine ⟨1898866370283812848593101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063643654090167596248269 1898866370283812848593101)
                ·
                  refine ⟨712074888856429818222413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1898866370283812848593101 712074888856429818222413)
                  ·
                    refine ⟨267028083321161181833405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 712074888856429818222413 267028083321161181833405)
                    ·
                      rfl

theorem cell22_780053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_780053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780053 prefixEnd_780053 := by exact prefixLift 780053
  have htrace : WordTrace (prefixWord ++ tailWord_780053) baseStart_780053 baseEnd_780053 := by
    simpa [prefixWord, tailWord_780053, baseEnd_780053] using wordTrace_append hprefix tailTrace_780053
  have hstable : (prefixWord ++ tailWord_780053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780053).length < 2 ^ (prefixWord ++ tailWord_780053).sum := by decide
  have hdescent : baseEnd_780053 < baseStart_780053 := by decide
  rcases family_descends (prefixWord ++ tailWord_780053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780096 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_780096 : Nat := 118140960795 + 780096 * 2 ^ 59
def prefixEnd_780096 : Nat := 4983230072969 + 3 ^ 40 * 780096 * 2
def baseEnd_780096 : Nat := 267042803099923403008273

theorem tailTrace_780096 : CollatzResearch.WordTrace tailWord_780096 prefixEnd_780096 267042803099923403008273 := by
  unfold tailWord_780096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226219290926448317472071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968292387901931089962761 14226219290926448317472071)
  ·
    refine ⟨21339328936389672476208107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14226219290926448317472071 21339328936389672476208107)
    ·
      refine ⟨32008993404584508714312161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21339328936389672476208107 32008993404584508714312161)
      ·
        refine ⟨24006745053438381535734121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32008993404584508714312161 24006745053438381535734121)
        ·
          refine ⟨18005058790078786151800591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24006745053438381535734121 18005058790078786151800591)
          ·
            refine ⟨27007588185118179227700887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18005058790078786151800591 27007588185118179227700887)
            ·
              refine ⟨40511382277677268841551331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27007588185118179227700887 40511382277677268841551331)
              ·
                refine ⟨60767073416515903262326997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40511382277677268841551331 60767073416515903262326997)
                ·
                  refine ⟨1424228283199591482710789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60767073416515903262326997 1424228283199591482710789)
                  ·
                    refine ⟨267042803099923403008273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424228283199591482710789 267042803099923403008273)
                    ·
                      rfl

theorem cell22_780096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_780096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780096 prefixEnd_780096 := by exact prefixLift 780096
  have htrace : WordTrace (prefixWord ++ tailWord_780096) baseStart_780096 baseEnd_780096 := by
    simpa [prefixWord, tailWord_780096, baseEnd_780096] using wordTrace_append hprefix tailTrace_780096
  have hstable : (prefixWord ++ tailWord_780096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780096).length < 2 ^ (prefixWord ++ tailWord_780096).sum := by decide
  have hdescent : baseEnd_780096 < baseStart_780096 := by decide
  rcases family_descends (prefixWord ++ tailWord_780096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780130 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_780130 : Nat := 118140960795 + 780130 * 2 ^ 59
def prefixEnd_780130 : Nat := 4983230072969 + 3 ^ 40 * 780130 * 2
def baseEnd_780130 : Nat := 267054441994758647658169

theorem tailTrace_780130 : CollatzResearch.WordTrace tailWord_780130 prefixEnd_780130 267054441994758647658169 := by
  unfold tailWord_780130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113419665932430110420461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18969119109153146961121229 7113419665932430110420461)
  ·
    refine ⟨2667532374724661291407673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7113419665932430110420461 2667532374724661291407673)
    ·
      refine ⟨2000649281043495968555755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2667532374724661291407673 2000649281043495968555755)
      ·
        refine ⟨3000973921565243952833633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000649281043495968555755 3000973921565243952833633)
        ·
          refine ⟨2250730441173932964625225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000973921565243952833633 2250730441173932964625225)
          ·
            refine ⟨1688047830880449723468919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250730441173932964625225 1688047830880449723468919)
            ·
              refine ⟨2532071746320674585203379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688047830880449723468919 2532071746320674585203379)
              ·
                refine ⟨3798107619481011877805069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532071746320674585203379 3798107619481011877805069)
                ·
                  refine ⟨1424290357305379454176901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3798107619481011877805069 1424290357305379454176901)
                  ·
                    refine ⟨267054441994758647658169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424290357305379454176901 267054441994758647658169)
                    ·
                      rfl

theorem cell22_780130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_780130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780130 prefixEnd_780130 := by exact prefixLift 780130
  have htrace : WordTrace (prefixWord ++ tailWord_780130) baseStart_780130 baseEnd_780130 := by
    simpa [prefixWord, tailWord_780130, baseEnd_780130] using wordTrace_append hprefix tailTrace_780130
  have hstable : (prefixWord ++ tailWord_780130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780130).length < 2 ^ (prefixWord ++ tailWord_780130).sum := by decide
  have hdescent : baseEnd_780130 < baseStart_780130 := by decide
  rcases family_descends (prefixWord ++ tailWord_780130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780160 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_780160 : Nat := 118140960795 + 780160 * 2 ^ 59
def prefixEnd_780160 : Nat := 4983230072969 + 3 ^ 40 * 780160 * 2
def baseEnd_780160 : Nat := 267064711607848569408077

theorem tailTrace_780160 : CollatzResearch.WordTrace tailWord_780160 prefixEnd_780160 267064711607848569408077 := by
  unfold tailWord_780160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14227386426810517782636967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18969848569080690376849289 14227386426810517782636967)
  ·
    refine ⟨21341079640215776673955451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14227386426810517782636967 21341079640215776673955451)
    ·
      refine ⟨32011619460323665010933177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341079640215776673955451 32011619460323665010933177)
      ·
        refine ⟨24008714595242748758199883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32011619460323665010933177 24008714595242748758199883)
        ·
          refine ⟨36013071892864123137299825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24008714595242748758199883 36013071892864123137299825)
          ·
            refine ⟨27009803919648092352974869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36013071892864123137299825 27009803919648092352974869)
            ·
              refine ⟨1266084558733504329045697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27009803919648092352974869 1266084558733504329045697)
              ·
                refine ⟨949563419050128246784273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266084558733504329045697 949563419050128246784273)
                ·
                  refine ⟨712172564287596185088205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 949563419050128246784273 712172564287596185088205)
                  ·
                    refine ⟨267064711607848569408077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 712172564287596185088205 267064711607848569408077)
                    ·
                      rfl

theorem cell22_780160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_780160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780160 prefixEnd_780160 := by exact prefixLift 780160
  have htrace : WordTrace (prefixWord ++ tailWord_780160) baseStart_780160 baseEnd_780160 := by
    simpa [prefixWord, tailWord_780160, baseEnd_780160] using wordTrace_append hprefix tailTrace_780160
  have hstable : (prefixWord ++ tailWord_780160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780160).length < 2 ^ (prefixWord ++ tailWord_780160).sum := by decide
  have hdescent : baseEnd_780160 < baseStart_780160 := by decide
  rcases family_descends (prefixWord ++ tailWord_780160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780171 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_780171 : Nat := 118140960795 + 780171 * 2 ^ 59
def prefixEnd_780171 : Nat := 4983230072969 + 3 ^ 40 * 780171 * 2
def baseEnd_780171 : Nat := 267068477132648207383043

theorem tailTrace_780171 : CollatzResearch.WordTrace tailWord_780171 prefixEnd_780171 267068477132648207383043 := by
  unfold tailWord_780171
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455174056581184443924367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18970116037720789629282911 28455174056581184443924367)
  ·
    refine ⟨42682761084871776665886551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28455174056581184443924367 42682761084871776665886551)
    ·
      refine ⟨64024141627307664998829827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42682761084871776665886551 64024141627307664998829827)
      ·
        refine ⟨96036212440961497498244741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64024141627307664998829827 96036212440961497498244741)
        ·
          refine ⟨18006789832680280780920889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96036212440961497498244741 18006789832680280780920889)
          ·
            refine ⟨13505092374510210585690667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18006789832680280780920889 13505092374510210585690667)
            ·
              refine ⟨20257638561765315878536001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13505092374510210585690667 20257638561765315878536001)
              ·
                refine ⟨15193228921323986908902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20257638561765315878536001 15193228921323986908902001)
                ·
                  refine ⟨11394921690992990181676501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15193228921323986908902001 11394921690992990181676501)
                  ·
                    refine ⟨267068477132648207383043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11394921690992990181676501 267068477132648207383043)
                    ·
                      rfl

theorem cell22_780171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_780171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780171 prefixEnd_780171 := by exact prefixLift 780171
  have htrace : WordTrace (prefixWord ++ tailWord_780171) baseStart_780171 baseEnd_780171 := by
    simpa [prefixWord, tailWord_780171, baseEnd_780171] using wordTrace_append hprefix tailTrace_780171
  have hstable : (prefixWord ++ tailWord_780171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780171).length < 2 ^ (prefixWord ++ tailWord_780171).sum := by decide
  have hdescent : baseEnd_780171 < baseStart_780171 := by decide
  rcases family_descends (prefixWord ++ tailWord_780171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780218 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_780218 : Nat := 118140960795 + 780218 * 2 ^ 59
def prefixEnd_780218 : Nat := 4983230072969 + 3 ^ 40 * 780218 * 2
def baseEnd_780218 : Nat := 89028188731051917152633

theorem tailTrace_780218 : CollatzResearch.WordTrace tailWord_780218 prefixEnd_780218 89028188731051917152633 := by
  unfold tailWord_780218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114222071852727867721327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18971258858273940980590205 7114222071852727867721327)
  ·
    refine ⟨10671333107779091801581991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114222071852727867721327 10671333107779091801581991)
    ·
      refine ⟨16006999661668637702372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671333107779091801581991 16006999661668637702372987)
      ·
        refine ⟨24010499492502956553559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16006999661668637702372987 24010499492502956553559481)
        ·
          refine ⟨18007874619377217415169611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24010499492502956553559481 18007874619377217415169611)
          ·
            refine ⟨27011811929065826122754417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007874619377217415169611 27011811929065826122754417)
            ·
              refine ⟨20258858946799369592065813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27011811929065826122754417 20258858946799369592065813)
              ·
                refine ⟨949634013131220449628085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20258858946799369592065813 949634013131220449628085)
                ·
                  refine ⟨89028188731051917152633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 949634013131220449628085 89028188731051917152633)
                  ·
                    rfl

theorem cell22_780218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_780218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780218 prefixEnd_780218 := by exact prefixLift 780218
  have htrace : WordTrace (prefixWord ++ tailWord_780218) baseStart_780218 baseEnd_780218 := by
    simpa [prefixWord, tailWord_780218, baseEnd_780218] using wordTrace_append hprefix tailTrace_780218
  have hstable : (prefixWord ++ tailWord_780218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780218).length < 2 ^ (prefixWord ++ tailWord_780218).sum := by decide
  have hdescent : baseEnd_780218 < baseStart_780218 := by decide
  rcases family_descends (prefixWord ++ tailWord_780218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780222 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_780222 : Nat := 118140960795 + 780222 * 2 ^ 59
def prefixEnd_780222 : Nat := 4983230072969 + 3 ^ 40 * 780222 * 2
def baseEnd_780222 : Nat := 267085935474901074357887

theorem tailTrace_780222 : CollatzResearch.WordTrace tailWord_780222 prefixEnd_780222 267085935474901074357887 := by
  unfold tailWord_780222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557129272424552519253865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18971356119597613436020613 3557129272424552519253865)
  ·
    refine ⟨2667846954318414389440399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3557129272424552519253865 2667846954318414389440399)
    ·
      refine ⟨4001770431477621584160599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667846954318414389440399 4001770431477621584160599)
      ·
        refine ⟨6002655647216432376240899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001770431477621584160599 6002655647216432376240899)
        ·
          refine ⟨9003983470824648564361349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002655647216432376240899 9003983470824648564361349)
          ·
            refine ⟨1688246900779621605817753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9003983470824648564361349 1688246900779621605817753)
            ·
              refine ⟨1266185175584716204363315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688246900779621605817753 1266185175584716204363315)
              ·
                refine ⟨1899277763377074306544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266185175584716204363315 1899277763377074306544973)
                ·
                  refine ⟨712229161266402864954365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1899277763377074306544973 712229161266402864954365)
                  ·
                    refine ⟨267085935474901074357887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 712229161266402864954365 267085935474901074357887)
                    ·
                      rfl

theorem cell22_780222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_780222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780222 prefixEnd_780222 := by exact prefixLift 780222
  have htrace : WordTrace (prefixWord ++ tailWord_780222) baseStart_780222 baseEnd_780222 := by
    simpa [prefixWord, tailWord_780222, baseEnd_780222] using wordTrace_append hprefix tailTrace_780222
  have hstable : (prefixWord ++ tailWord_780222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780222).length < 2 ^ (prefixWord ++ tailWord_780222).sum := by decide
  have hdescent : baseEnd_780222 < baseStart_780222 := by decide
  rcases family_descends (prefixWord ++ tailWord_780222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780235 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 5]
def baseStart_780235 : Nat := 118140960795 + 780235 * 2 ^ 59
def prefixEnd_780235 : Nat := 4983230072969 + 3 ^ 40 * 780235 * 2
def baseEnd_780235 : Nat := 89030128546857791260949

theorem tailTrace_780235 : CollatzResearch.WordTrace tailWord_780235 prefixEnd_780235 89030128546857791260949 := by
  unfold tailWord_780235
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457508328349323374254159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18971672218899548916169439 28457508328349323374254159)
  ·
    refine ⟨42686262492523985061381239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457508328349323374254159 42686262492523985061381239)
    ·
      refine ⟨64029393738785977592071859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686262492523985061381239 64029393738785977592071859)
      ·
        refine ⟨96044090608178966388107789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64029393738785977592071859 96044090608178966388107789)
        ·
          refine ⟨36016533978067112395540421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96044090608178966388107789 36016533978067112395540421)
          ·
            refine ⟨6753100120887583574163829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36016533978067112395540421 6753100120887583574163829)
            ·
              refine ⟨633103136333210960077859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6753100120887583574163829 633103136333210960077859)
              ·
                refine ⟨949654704499816440116789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633103136333210960077859 949654704499816440116789)
                ·
                  refine ⟨89030128546857791260949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 949654704499816440116789 89030128546857791260949)
                  ·
                    rfl

theorem cell22_780235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 5].length) (baseStart_780235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780235 prefixEnd_780235 := by exact prefixLift 780235
  have htrace : WordTrace (prefixWord ++ tailWord_780235) baseStart_780235 baseEnd_780235 := by
    simpa [prefixWord, tailWord_780235, baseEnd_780235] using wordTrace_append hprefix tailTrace_780235
  have hstable : (prefixWord ++ tailWord_780235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780235).length < 2 ^ (prefixWord ++ tailWord_780235).sum := by decide
  have hdescent : baseEnd_780235 < baseStart_780235 := by decide
  rcases family_descends (prefixWord ++ tailWord_780235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780280 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_780280 : Nat := 118140960795 + 780280 * 2 ^ 59
def prefixEnd_780280 : Nat := 4983230072969 + 3 ^ 40 * 780280 * 2
def baseEnd_780280 : Nat := 89035263353402752135903

theorem tailTrace_780280 : CollatzResearch.WordTrace tailWord_780280 prefixEnd_780280 89035263353402752135903 := by
  unfold tailWord_780280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14229574806593148029821147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18972766408790864039761529 14229574806593148029821147)
  ·
    refine ⟨21344362209889722044731721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14229574806593148029821147 21344362209889722044731721)
    ·
      refine ⟨16008271657417291533548791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21344362209889722044731721 16008271657417291533548791)
      ·
        refine ⟨24012407486125937300323187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008271657417291533548791 24012407486125937300323187)
        ·
          refine ⟨36018611229188905950484781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24012407486125937300323187 36018611229188905950484781)
          ·
            refine ⟨13506979210945839731431793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36018611229188905950484781 13506979210945839731431793)
            ·
              refine ⟨10130234408209379798573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13506979210945839731431793 10130234408209379798573845)
              ·
                refine ⟨474854737884814678058149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10130234408209379798573845 474854737884814678058149)
                ·
                  refine ⟨89035263353402752135903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474854737884814678058149 89035263353402752135903)
                  ·
                    rfl

theorem cell22_780280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_780280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780280 prefixEnd_780280 := by exact prefixLift 780280
  have htrace : WordTrace (prefixWord ++ tailWord_780280) baseStart_780280 baseEnd_780280 := by
    simpa [prefixWord, tailWord_780280, baseEnd_780280] using wordTrace_append hprefix tailTrace_780280
  have hstable : (prefixWord ++ tailWord_780280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780280).length < 2 ^ (prefixWord ++ tailWord_780280).sum := by decide
  have hdescent : baseEnd_780280 < baseStart_780280 := by decide
  rcases family_descends (prefixWord ++ tailWord_780280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780468 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_780468 : Nat := 118140960795 + 780468 * 2 ^ 59
def prefixEnd_780468 : Nat := 4983230072969 + 3 ^ 40 * 780468 * 2
def baseEnd_780468 : Nat := 267170146302238432707133

theorem tailTrace_780468 : CollatzResearch.WordTrace tailWord_780468 prefixEnd_780468 267170146302238432707133 := by
  unfold tailWord_780468
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233003268252602083743029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18977337691003469444990705 14233003268252602083743029)
  ·
    refine ⟨1334344056398681445350909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14233003268252602083743029 1334344056398681445350909)
    ·
      refine ⟨500379021149505542006591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1334344056398681445350909 500379021149505542006591)
      ·
        refine ⟨750568531724258313009887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500379021149505542006591 750568531724258313009887)
        ·
          refine ⟨1125852797586387469514831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750568531724258313009887 1125852797586387469514831)
          ·
            refine ⟨1688779196379581204272247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125852797586387469514831 1688779196379581204272247)
            ·
              refine ⟨2533168794569371806408371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688779196379581204272247 2533168794569371806408371)
              ·
                refine ⟨3799753191854057709612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533168794569371806408371 3799753191854057709612557)
                ·
                  refine ⟨1424907446945271641104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3799753191854057709612557 1424907446945271641104709)
                  ·
                    refine ⟨267170146302238432707133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424907446945271641104709 267170146302238432707133)
                    ·
                      rfl

theorem cell22_780468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_780468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780468 prefixEnd_780468 := by exact prefixLift 780468
  have htrace : WordTrace (prefixWord ++ tailWord_780468) baseStart_780468 baseEnd_780468 := by
    simpa [prefixWord, tailWord_780468, baseEnd_780468] using wordTrace_append hprefix tailTrace_780468
  have hstable : (prefixWord ++ tailWord_780468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780468).length < 2 ^ (prefixWord ++ tailWord_780468).sum := by decide
  have hdescent : baseEnd_780468 < baseStart_780468 := by decide
  rcases family_descends (prefixWord ++ tailWord_780468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780505 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 7]
def baseStart_780505 : Nat := 118140960795 + 780505 * 2 ^ 59
def prefixEnd_780505 : Nat := 4983230072969 + 3 ^ 40 * 780505 * 2
def baseEnd_780505 : Nat := 89060937386127556510673

theorem tailTrace_780505 : CollatzResearch.WordTrace tailWord_780505 prefixEnd_780505 89060937386127556510673 := by
  unfold tailWord_780505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467356037371159486582969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18978237358247439657721979 28467356037371159486582969)
  ·
    refine ⟨21350517028028369614937227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28467356037371159486582969 21350517028028369614937227)
    ·
      refine ⟨32025775542042554422405841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21350517028028369614937227 32025775542042554422405841)
      ·
        refine ⟨24019331656531915816804381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32025775542042554422405841 24019331656531915816804381)
        ·
          refine ⟨9007249371199468431301643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24019331656531915816804381 9007249371199468431301643)
          ·
            refine ⟨13510874056799202646952465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007249371199468431301643 13510874056799202646952465)
            ·
              refine ⟨10133155542599401985214349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13510874056799202646952465 10133155542599401985214349)
              ·
                refine ⟨3799933328474775744455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10133155542599401985214349 3799933328474775744455381)
                ·
                  refine ⟨89060937386127556510673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3799933328474775744455381 89060937386127556510673)
                  ·
                    rfl

theorem cell22_780505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_780505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780505 prefixEnd_780505 := by exact prefixLift 780505
  have htrace : WordTrace (prefixWord ++ tailWord_780505) baseStart_780505 baseEnd_780505 := by
    simpa [prefixWord, tailWord_780505, baseEnd_780505] using wordTrace_append hprefix tailTrace_780505
  have hstable : (prefixWord ++ tailWord_780505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780505).length < 2 ^ (prefixWord ++ tailWord_780505).sum := by decide
  have hdescent : baseEnd_780505 < baseStart_780505 := by decide
  rcases family_descends (prefixWord ++ tailWord_780505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780522 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_780522 : Nat := 118140960795 + 780522 * 2 ^ 59
def prefixEnd_780522 : Nat := 4983230072969 + 3 ^ 40 * 780522 * 2
def baseEnd_780522 : Nat := 89062877201933430618989

theorem tailTrace_780522 : CollatzResearch.WordTrace tailWord_780522 prefixEnd_780522 89062877201933430618989 := by
  unfold tailWord_780522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116994019577392847487955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18978650718873047593301213 7116994019577392847487955)
  ·
    refine ⟨10675491029366089271231933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116994019577392847487955 10675491029366089271231933)
    ·
      refine ⟨4003309136012283476711975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10675491029366089271231933 4003309136012283476711975)
      ·
        refine ⟨6004963704018425215067963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4003309136012283476711975 6004963704018425215067963)
        ·
          refine ⟨9007445556027637822601945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6004963704018425215067963 9007445556027637822601945)
          ·
            refine ⟨6755584167020728366951459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007445556027637822601945 6755584167020728366951459)
            ·
              refine ⟨10133376250531092550427189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755584167020728366951459 10133376250531092550427189)
              ·
                refine ⟨950004023487289926602549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10133376250531092550427189 950004023487289926602549)
                ·
                  refine ⟨89062877201933430618989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950004023487289926602549 89062877201933430618989)
                  ·
                    rfl

theorem cell22_780522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_780522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780522 prefixEnd_780522 := by exact prefixLift 780522
  have htrace : WordTrace (prefixWord ++ tailWord_780522) baseStart_780522 baseEnd_780522 := by
    simpa [prefixWord, tailWord_780522, baseEnd_780522] using wordTrace_append hprefix tailTrace_780522
  have hstable : (prefixWord ++ tailWord_780522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780522).length < 2 ^ (prefixWord ++ tailWord_780522).sum := by decide
  have hdescent : baseEnd_780522 < baseStart_780522 := by decide
  rcases family_descends (prefixWord ++ tailWord_780522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780567 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 6]
def baseStart_780567 : Nat := 118140960795 + 780567 * 2 ^ 59
def prefixEnd_780567 : Nat := 4983230072969 + 3 ^ 40 * 780567 * 2
def baseEnd_780567 : Nat := 89068012008478391493943

theorem tailTrace_780567 : CollatzResearch.WordTrace tailWord_780567 prefixEnd_780567 89068012008478391493943 := by
  unfold tailWord_780567
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469617363146544075339955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18979744908764362716893303 28469617363146544075339955)
  ·
    refine ⟨42704426044719816113009933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28469617363146544075339955 42704426044719816113009933)
    ·
      refine ⟨16014159766769931042378725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42704426044719816113009933 16014159766769931042378725)
      ·
        refine ⟨3002654956269362070446011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16014159766769931042378725 3002654956269362070446011)
        ·
          refine ⟨4503982434404043105669017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002654956269362070446011 4503982434404043105669017)
          ·
            refine ⟨3377986825803032329251763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503982434404043105669017 3377986825803032329251763)
            ·
              refine ⟨5066980238704548493877645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377986825803032329251763 5066980238704548493877645)
              ·
                refine ⟨1900117589514205685204117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5066980238704548493877645 1900117589514205685204117)
                ·
                  refine ⟨89068012008478391493943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1900117589514205685204117 89068012008478391493943)
                  ·
                    rfl

theorem cell22_780567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_780567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780567 prefixEnd_780567 := by exact prefixLift 780567
  have htrace : WordTrace (prefixWord ++ tailWord_780567) baseStart_780567 baseEnd_780567 := by
    simpa [prefixWord, tailWord_780567, baseEnd_780567] using wordTrace_append hprefix tailTrace_780567
  have hstable : (prefixWord ++ tailWord_780567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780567).length < 2 ^ (prefixWord ++ tailWord_780567).sum := by decide
  have hdescent : baseEnd_780567 < baseStart_780567 := by decide
  rcases family_descends (prefixWord ++ tailWord_780567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780597 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_780597 : Nat := 118140960795 + 780597 * 2 ^ 59
def prefixEnd_780597 : Nat := 4983230072969 + 3 ^ 40 * 780597 * 2
def baseEnd_780597 : Nat := 267214305638525096231737

theorem tailTrace_780597 : CollatzResearch.WordTrace tailWord_780597 prefixEnd_780597 267214305638525096231737 := by
  unfold tailWord_780597
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470711553037859198932045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18980474368691906132621363 28470711553037859198932045)
  ·
    refine ⟨10676516832389197199599517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28470711553037859198932045 10676516832389197199599517)
    ·
      refine ⟨4003693812145948949849819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10676516832389197199599517 4003693812145948949849819)
      ·
        refine ⟨6005540718218923424774729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4003693812145948949849819 6005540718218923424774729)
        ·
          refine ⟨4504155538664192568581047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005540718218923424774729 4504155538664192568581047)
          ·
            refine ⟨6756233307996288852871571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504155538664192568581047 6756233307996288852871571)
            ·
              refine ⟨10134349961994433279307357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756233307996288852871571 10134349961994433279307357)
              ·
                refine ⟨3800381235747912479740259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10134349961994433279307357 3800381235747912479740259)
                ·
                  refine ⟨5700571853621868719610389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800381235747912479740259 5700571853621868719610389)
                  ·
                    refine ⟨267214305638525096231737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5700571853621868719610389 267214305638525096231737)
                    ·
                      rfl

theorem cell22_780597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_780597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780597 prefixEnd_780597 := by exact prefixLift 780597
  have htrace : WordTrace (prefixWord ++ tailWord_780597) baseStart_780597 baseEnd_780597 := by
    simpa [prefixWord, tailWord_780597, baseEnd_780597] using wordTrace_append hprefix tailTrace_780597
  have hstable : (prefixWord ++ tailWord_780597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780597).length < 2 ^ (prefixWord ++ tailWord_780597).sum := by decide
  have hdescent : baseEnd_780597 < baseStart_780597 := by decide
  rcases family_descends (prefixWord ++ tailWord_780597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780601 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 4]
def baseStart_780601 : Nat := 118140960795 + 780601 * 2 ^ 59
def prefixEnd_780601 : Nat := 4983230072969 + 3 ^ 40 * 780601 * 2
def baseEnd_780601 : Nat := 89071891640090139710575

theorem tailTrace_780601 : CollatzResearch.WordTrace tailWord_780601 prefixEnd_780601 89071891640090139710575 := by
  unfold tailWord_780601
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470857445023367882077657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18980571630015578588051771 28470857445023367882077657)
  ·
    refine ⟨21353143083767525911558243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28470857445023367882077657 21353143083767525911558243)
    ·
      refine ⟨32029714625651288867337365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21353143083767525911558243 32029714625651288867337365)
      ·
        refine ⟨1501392873077404165656439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32029714625651288867337365 1501392873077404165656439)
        ·
          refine ⟨2252089309616106248484659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501392873077404165656439 2252089309616106248484659)
          ·
            refine ⟨3378133964424159372726989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252089309616106248484659 3378133964424159372726989)
            ·
              refine ⟨1266800236659059764772621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378133964424159372726989 1266800236659059764772621)
              ·
                refine ⟨475050088747147411789733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266800236659059764772621 475050088747147411789733)
                ·
                  refine ⟨89071891640090139710575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475050088747147411789733 89071891640090139710575)
                  ·
                    rfl

theorem cell22_780601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_780601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780601 prefixEnd_780601 := by exact prefixLift 780601
  have htrace : WordTrace (prefixWord ++ tailWord_780601) baseStart_780601 baseEnd_780601 := by
    simpa [prefixWord, tailWord_780601, baseEnd_780601] using wordTrace_append hprefix tailTrace_780601
  have hstable : (prefixWord ++ tailWord_780601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780601).length < 2 ^ (prefixWord ++ tailWord_780601).sum := by decide
  have hdescent : baseEnd_780601 < baseStart_780601 := by decide
  rcases family_descends (prefixWord ++ tailWord_780601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780629 : List Nat := [1, 3, 2, 2, 4, 1, 2, 7]
def baseStart_780629 : Nat := 118140960795 + 780629 * 2 ^ 59
def prefixEnd_780629 : Nat := 4983230072969 + 3 ^ 40 * 780629 * 2
def baseEnd_780629 : Nat := 29691695543609742159071

theorem tailTrace_780629 : CollatzResearch.WordTrace tailWord_780629 prefixEnd_780629 29691695543609742159071 := by
  unfold tailWord_780629
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471878688921928664096941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18981252459281285776064627 28471878688921928664096941)
  ·
    refine ⟨10676954508345723249036353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28471878688921928664096941 10676954508345723249036353)
    ·
      refine ⟨8007715881259292436777265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10676954508345723249036353 8007715881259292436777265)
      ·
        refine ⟨6005786910944469327582949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8007715881259292436777265 6005786910944469327582949)
        ·
          refine ⟨1126085045802087998921803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6005786910944469327582949 1126085045802087998921803)
          ·
            refine ⟨1689127568703131998382705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126085045802087998921803 1689127568703131998382705)
            ·
              refine ⟨1266845676527348998787029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689127568703131998382705 1266845676527348998787029)
              ·
                refine ⟨29691695543609742159071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1266845676527348998787029 29691695543609742159071)
                ·
                  rfl

theorem cell22_780629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 7].length) (baseStart_780629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780629 prefixEnd_780629 := by exact prefixLift 780629
  have htrace : WordTrace (prefixWord ++ tailWord_780629) baseStart_780629 baseEnd_780629 := by
    simpa [prefixWord, tailWord_780629, baseEnd_780629] using wordTrace_append hprefix tailTrace_780629
  have hstable : (prefixWord ++ tailWord_780629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780629).length < 2 ^ (prefixWord ++ tailWord_780629).sum := by decide
  have hdescent : baseEnd_780629 < baseStart_780629 := by decide
  rcases family_descends (prefixWord ++ tailWord_780629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780644 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_780644 : Nat := 118140960795 + 780644 * 2 ^ 59
def prefixEnd_780644 : Nat := 4983230072969 + 3 ^ 40 * 780644 * 2
def baseEnd_780644 : Nat := 267230394699032640306593

theorem tailTrace_780644 : CollatzResearch.WordTrace tailWord_780644 prefixEnd_780644 267230394699032640306593 := by
  unfold tailWord_780644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236212891933793112946493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18981617189245057483928657 14236212891933793112946493)
  ·
    refine ⟨5338579834475172417354935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14236212891933793112946493 5338579834475172417354935)
    ·
      refine ⟨8007869751712758626032403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338579834475172417354935 8007869751712758626032403)
      ·
        refine ⟨12011804627569137939048605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007869751712758626032403 12011804627569137939048605)
        ·
          refine ⟨4504426735338426727143227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12011804627569137939048605 4504426735338426727143227)
          ·
            refine ⟨6756640103007640090714841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504426735338426727143227 6756640103007640090714841)
            ·
              refine ⟨5067480077255730068036131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756640103007640090714841 5067480077255730068036131)
              ·
                refine ⟨7601220115883595102054197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067480077255730068036131 7601220115883595102054197)
                ·
                  refine ⟨712614385864087040817581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7601220115883595102054197 712614385864087040817581)
                  ·
                    refine ⟨267230394699032640306593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 712614385864087040817581 267230394699032640306593)
                    ·
                      rfl

theorem cell22_780644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_780644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780644 prefixEnd_780644 := by exact prefixLift 780644
  have htrace : WordTrace (prefixWord ++ tailWord_780644) baseStart_780644 baseEnd_780644 := by
    simpa [prefixWord, tailWord_780644, baseEnd_780644] using wordTrace_append hprefix tailTrace_780644
  have hstable : (prefixWord ++ tailWord_780644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780644).length < 2 ^ (prefixWord ++ tailWord_780644).sum := by decide
  have hdescent : baseEnd_780644 < baseStart_780644 := by decide
  rcases family_descends (prefixWord ++ tailWord_780644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780704 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_780704 : Nat := 118140960795 + 780704 * 2 ^ 59
def prefixEnd_780704 : Nat := 4983230072969 + 3 ^ 40 * 780704 * 2
def baseEnd_780704 : Nat := 267250933925212483806409

theorem tailTrace_780704 : CollatzResearch.WordTrace tailWord_780704 prefixEnd_780704 267250933925212483806409 := by
  unfold tailWord_780704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14237307081825108236538583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18983076109100144315384777 14237307081825108236538583)
  ·
    refine ⟨21355960622737662354807875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14237307081825108236538583 21355960622737662354807875)
    ·
      refine ⟨32033940934106493532211813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21355960622737662354807875 32033940934106493532211813)
      ·
        refine ⟨6006363925144967537289715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32033940934106493532211813 6006363925144967537289715)
        ·
          refine ⟨9009545887717451305934573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006363925144967537289715 9009545887717451305934573)
          ·
            refine ⟨3378579707894044239725465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9009545887717451305934573 3378579707894044239725465)
            ·
              refine ⟨2533934780920533179794099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378579707894044239725465 2533934780920533179794099)
              ·
                refine ⟨3800902171380799769691149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533934780920533179794099 3800902171380799769691149)
                ·
                  refine ⟨1425338314267799913634181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3800902171380799769691149 1425338314267799913634181)
                  ·
                    refine ⟨267250933925212483806409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425338314267799913634181 267250933925212483806409)
                    ·
                      rfl

theorem cell22_780704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_780704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780704 prefixEnd_780704 := by exact prefixLift 780704
  have htrace : WordTrace (prefixWord ++ tailWord_780704) baseStart_780704 baseEnd_780704 := by
    simpa [prefixWord, tailWord_780704, baseEnd_780704] using wordTrace_append hprefix tailTrace_780704
  have hstable : (prefixWord ++ tailWord_780704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780704).length < 2 ^ (prefixWord ++ tailWord_780704).sum := by decide
  have hdescent : baseEnd_780704 < baseStart_780704 := by decide
  rcases family_descends (prefixWord ++ tailWord_780704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780721 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_780721 : Nat := 118140960795 + 780721 * 2 ^ 59
def prefixEnd_780721 : Nat := 4983230072969 + 3 ^ 40 * 780721 * 2
def baseEnd_780721 : Nat := 267256753372630106131357

theorem tailTrace_780721 : CollatzResearch.WordTrace tailWord_780721 prefixEnd_780721 267256753372630106131357 := by
  unfold tailWord_780721
  simp only [CollatzResearch.WordTrace]
  refine ⟨28475234204588628376446017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18983489469725752250964011 28475234204588628376446017)
  ·
    refine ⟨21356425653441471282334513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28475234204588628376446017 21356425653441471282334513)
    ·
      refine ⟨16017319240081103461750885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21356425653441471282334513 16017319240081103461750885)
      ·
        refine ⟨3003247357515206899078291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16017319240081103461750885 3003247357515206899078291)
        ·
          refine ⟨4504871036272810348617437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003247357515206899078291 4504871036272810348617437)
          ·
            refine ⟨1689326638602303880731539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4504871036272810348617437 1689326638602303880731539)
            ·
              refine ⟨2533989957903455821097309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689326638602303880731539 2533989957903455821097309)
              ·
                refine ⟨950246234213795932911491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533989957903455821097309 950246234213795932911491)
                ·
                  refine ⟨1425369351320693899367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950246234213795932911491 1425369351320693899367237)
                  ·
                    refine ⟨267256753372630106131357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425369351320693899367237 267256753372630106131357)
                    ·
                      rfl

theorem cell22_780721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_780721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780721 prefixEnd_780721 := by exact prefixLift 780721
  have htrace : WordTrace (prefixWord ++ tailWord_780721) baseStart_780721 baseEnd_780721 := by
    simpa [prefixWord, tailWord_780721, baseEnd_780721] using wordTrace_append hprefix tailTrace_780721
  have hstable : (prefixWord ++ tailWord_780721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780721).length < 2 ^ (prefixWord ++ tailWord_780721).sum := by decide
  have hdescent : baseEnd_780721 < baseStart_780721 := by decide
  rcases family_descends (prefixWord ++ tailWord_780721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780734 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_780734 : Nat := 118140960795 + 780734 * 2 ^ 59
def prefixEnd_780734 : Nat := 4983230072969 + 3 ^ 40 * 780734 * 2
def baseEnd_780734 : Nat := 267261203538302405556317

theorem tailTrace_780734 : CollatzResearch.WordTrace tailWord_780734 prefixEnd_780734 267261203538302405556317 := by
  unfold tailWord_780734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559463544192691449583657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18983805569027687731112837 3559463544192691449583657)
  ·
    refine ⟨2669597658144518587187743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3559463544192691449583657 2669597658144518587187743)
    ·
      refine ⟨4004396487216777880781615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669597658144518587187743 4004396487216777880781615)
      ·
        refine ⟨6006594730825166821172423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004396487216777880781615 6006594730825166821172423)
        ·
          refine ⟨9009892096237750231758635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006594730825166821172423 9009892096237750231758635)
          ·
            refine ⟨13514838144356625347637953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9009892096237750231758635 13514838144356625347637953)
            ·
              refine ⟨10136128608267469010728465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13514838144356625347637953 10136128608267469010728465)
              ·
                refine ⟨7602096456200601758046349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10136128608267469010728465 7602096456200601758046349)
                ·
                  refine ⟨2850786171075225659267381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7602096456200601758046349 2850786171075225659267381)
                  ·
                    refine ⟨267261203538302405556317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2850786171075225659267381 267261203538302405556317)
                    ·
                      rfl

theorem cell22_780734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_780734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780734 prefixEnd_780734 := by exact prefixLift 780734
  have htrace : WordTrace (prefixWord ++ tailWord_780734) baseStart_780734 baseEnd_780734 := by
    simpa [prefixWord, tailWord_780734, baseEnd_780734] using wordTrace_append hprefix tailTrace_780734
  have hstable : (prefixWord ++ tailWord_780734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780734).length < 2 ^ (prefixWord ++ tailWord_780734).sum := by decide
  have hdescent : baseEnd_780734 < baseStart_780734 := by decide
  rcases family_descends (prefixWord ++ tailWord_780734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780747 : List Nat := [1, 1, 1, 1, 3, 3, 1, 11]
def baseStart_780747 : Nat := 118140960795 + 780747 * 2 ^ 59
def prefixEnd_780747 : Nat := 4983230072969 + 3 ^ 40 * 780747 * 2
def baseEnd_780747 : Nat := 29696183744886078331253

theorem tailTrace_780747 : CollatzResearch.WordTrace tailWord_780747 prefixEnd_780747 29696183744886078331253 := by
  unfold tailWord_780747
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476182502494434816892495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18984121668329623211261663 28476182502494434816892495)
  ·
    refine ⟨42714273753741652225338743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28476182502494434816892495 42714273753741652225338743)
    ·
      refine ⟨64071410630612478338008115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42714273753741652225338743 64071410630612478338008115)
      ·
        refine ⟨96107115945918717507012173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64071410630612478338008115 96107115945918717507012173)
        ·
          refine ⟨36040168479719519065129565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96107115945918717507012173 36040168479719519065129565)
          ·
            refine ⟨13515063179894819649423587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36040168479719519065129565 13515063179894819649423587)
            ·
              refine ⟨20272594769842229474135381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13515063179894819649423587 20272594769842229474135381)
              ·
                refine ⟨29696183744886078331253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20272594769842229474135381 29696183744886078331253)
                ·
                  rfl

theorem cell22_780747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_780747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780747 prefixEnd_780747 := by exact prefixLift 780747
  have htrace : WordTrace (prefixWord ++ tailWord_780747) baseStart_780747 baseEnd_780747 := by
    simpa [prefixWord, tailWord_780747, baseEnd_780747] using wordTrace_append hprefix tailTrace_780747
  have hstable : (prefixWord ++ tailWord_780747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780747).length < 2 ^ (prefixWord ++ tailWord_780747).sum := by decide
  have hdescent : baseEnd_780747 < baseStart_780747 := by decide
  rcases family_descends (prefixWord ++ tailWord_780747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780781 : List Nat := [1, 5, 1, 3, 1, 3, 8]
def baseStart_780781 : Nat := 118140960795 + 780781 * 2 ^ 59
def prefixEnd_780781 : Nat := 4983230072969 + 3 ^ 40 * 780781 * 2
def baseEnd_780781 : Nat := 9899158985141109245599

theorem tailTrace_780781 : CollatzResearch.WordTrace tailWord_780781 prefixEnd_780781 9899158985141109245599 := by
  unfold tailWord_780781
  simp only [CollatzResearch.WordTrace]
  refine ⟨28477422584371258623630197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18984948389580839082420131 28477422584371258623630197)
  ·
    refine ⟨2669758367284805495965331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28477422584371258623630197 2669758367284805495965331)
    ·
      refine ⟨4004637550927208243947997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669758367284805495965331 4004637550927208243947997)
      ·
        refine ⟨1501739081597703091480499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4004637550927208243947997 1501739081597703091480499)
        ·
          refine ⟨2252608622396554637220749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501739081597703091480499 2252608622396554637220749)
          ·
            refine ⟨844728233398707988957781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2252608622396554637220749 844728233398707988957781)
            ·
              refine ⟨9899158985141109245599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 844728233398707988957781 9899158985141109245599)
              ·
                rfl

theorem cell22_780781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 8].length) (baseStart_780781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780781 prefixEnd_780781 := by exact prefixLift 780781
  have htrace : WordTrace (prefixWord ++ tailWord_780781) baseStart_780781 baseEnd_780781 := by
    simpa [prefixWord, tailWord_780781, baseEnd_780781] using wordTrace_append hprefix tailTrace_780781
  have hstable : (prefixWord ++ tailWord_780781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780781).length < 2 ^ (prefixWord ++ tailWord_780781).sum := by decide
  have hdescent : baseEnd_780781 < baseStart_780781 := by decide
  rcases family_descends (prefixWord ++ tailWord_780781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780871 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 6]
def baseStart_780871 : Nat := 118140960795 + 780871 * 2 ^ 59
def prefixEnd_780871 : Nat := 4983230072969 + 3 ^ 40 * 780871 * 2
def baseEnd_780871 : Nat := 89102700479359904960299

theorem tailTrace_780871 : CollatzResearch.WordTrace tailWord_780871 prefixEnd_780871 89102700479359904960299 := by
  unfold tailWord_780871
  simp only [CollatzResearch.WordTrace]
  refine ⟨28480705154045203994406467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18987136769363469329604311 28480705154045203994406467)
  ·
    refine ⟨42721057731067805991609701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28480705154045203994406467 42721057731067805991609701)
    ·
      refine ⟨8010198324575213623426819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42721057731067805991609701 8010198324575213623426819)
      ·
        refine ⟨12015297486862820435140229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010198324575213623426819 12015297486862820435140229)
        ·
          refine ⟨2252868278786778831588793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12015297486862820435140229 2252868278786778831588793)
          ·
            refine ⟨1689651209090084123691595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2252868278786778831588793 1689651209090084123691595)
            ·
              refine ⟨2534476813635126185537393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689651209090084123691595 2534476813635126185537393)
              ·
                refine ⟨1900857610226344639153045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534476813635126185537393 1900857610226344639153045)
                ·
                  refine ⟨89102700479359904960299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1900857610226344639153045 89102700479359904960299)
                  ·
                    rfl

theorem cell22_780871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_780871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780871 prefixEnd_780871 := by exact prefixLift 780871
  have htrace : WordTrace (prefixWord ++ tailWord_780871) baseStart_780871 baseEnd_780871 := by
    simpa [prefixWord, tailWord_780871, baseEnd_780871] using wordTrace_append hprefix tailTrace_780871
  have hstable : (prefixWord ++ tailWord_780871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780871).length < 2 ^ (prefixWord ++ tailWord_780871).sum := by decide
  have hdescent : baseEnd_780871 < baseStart_780871 := by decide
  rcases family_descends (prefixWord ++ tailWord_780871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780894 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_780894 : Nat := 118140960795 + 780894 * 2 ^ 59
def prefixEnd_780894 : Nat := 4983230072969 + 3 ^ 40 * 780894 * 2
def baseEnd_780894 : Nat := 89105324936038440518609

theorem tailTrace_780894 : CollatzResearch.WordTrace tailWord_780894 prefixEnd_780894 89105324936038440518609 := by
  unfold tailWord_780894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560193004120234865311717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18987696021974585948329157 3560193004120234865311717)
  ·
    refine ⟨667536188272544037245947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3560193004120234865311717 667536188272544037245947)
    ·
      refine ⟨1001304282408816055868921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667536188272544037245947 1001304282408816055868921)
      ·
        refine ⟨750978211806612041901691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001304282408816055868921 750978211806612041901691)
        ·
          refine ⟨1126467317709918062852537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750978211806612041901691 1126467317709918062852537)
          ·
            refine ⟨844850488282438547139403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126467317709918062852537 844850488282438547139403)
            ·
              refine ⟨1267275732423657820709105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844850488282438547139403 1267275732423657820709105)
              ·
                refine ⟨950456799317743365531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267275732423657820709105 950456799317743365531829)
                ·
                  refine ⟨89105324936038440518609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950456799317743365531829 89105324936038440518609)
                  ·
                    rfl

theorem cell22_780894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_780894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780894 prefixEnd_780894 := by exact prefixLift 780894
  have htrace : WordTrace (prefixWord ++ tailWord_780894) baseStart_780894 baseEnd_780894 := by
    simpa [prefixWord, tailWord_780894, baseEnd_780894] using wordTrace_append hprefix tailTrace_780894
  have hstable : (prefixWord ++ tailWord_780894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780894).length < 2 ^ (prefixWord ++ tailWord_780894).sum := by decide
  have hdescent : baseEnd_780894 < baseStart_780894 := by decide
  rcases family_descends (prefixWord ++ tailWord_780894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780899 : List Nat := [1, 1, 1, 5, 1, 2, 11]
def baseStart_780899 : Nat := 118140960795 + 780899 * 2 ^ 59
def prefixEnd_780899 : Nat := 4983230072969 + 3 ^ 40 * 780899 * 2
def baseEnd_780899 : Nat := 9900655052233221302993

theorem tailTrace_780899 : CollatzResearch.WordTrace tailWord_780899 prefixEnd_780899 9900655052233221302993 := by
  unfold tailWord_780899
  simp only [CollatzResearch.WordTrace]
  refine ⟨28481726397943764776425751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18987817598629176517617167 28481726397943764776425751)
  ·
    refine ⟨42722589596915647164638627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28481726397943764776425751 42722589596915647164638627)
    ·
      refine ⟨64083884395373470746957941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42722589596915647164638627 64083884395373470746957941)
      ·
        refine ⟨6007864162066262882527307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64083884395373470746957941 6007864162066262882527307)
        ·
          refine ⟨9011796243099394323790961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007864162066262882527307 9011796243099394323790961)
          ·
            refine ⟨6758847182324545742843221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9011796243099394323790961 6758847182324545742843221)
            ·
              refine ⟨9900655052233221302993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6758847182324545742843221 9900655052233221302993)
              ·
                rfl

theorem cell22_780899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 11].length) (baseStart_780899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780899 prefixEnd_780899 := by exact prefixLift 780899
  have htrace : WordTrace (prefixWord ++ tailWord_780899) baseStart_780899 baseEnd_780899 := by
    simpa [prefixWord, tailWord_780899, baseEnd_780899] using wordTrace_append hprefix tailTrace_780899
  have hstable : (prefixWord ++ tailWord_780899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780899).length < 2 ^ (prefixWord ++ tailWord_780899).sum := by decide
  have hdescent : baseEnd_780899 < baseStart_780899 := by decide
  rcases family_descends (prefixWord ++ tailWord_780899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780933 : List Nat := [1, 3, 1, 1, 4, 4, 2, 6]
def baseStart_780933 : Nat := 118140960795 + 780933 * 2 ^ 59
def prefixEnd_780933 : Nat := 4983230072969 + 3 ^ 40 * 780933 * 2
def baseEnd_780933 : Nat := 29703258367236913314523

theorem tailTrace_780933 : CollatzResearch.WordTrace tailWord_780933 prefixEnd_780933 29703258367236913314523 := by
  unfold tailWord_780933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482966479820588583163453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988644319880392388775635 28482966479820588583163453)
  ·
    refine ⟨10681112429932720718686295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28482966479820588583163453 10681112429932720718686295)
    ·
      refine ⟨16021668644899081078029443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681112429932720718686295 16021668644899081078029443)
      ·
        refine ⟨24032502967348621617044165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16021668644899081078029443 24032502967348621617044165)
        ·
          refine ⟨4506094306377866553195781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24032502967348621617044165 4506094306377866553195781)
          ·
            refine ⟨844892682445849978724209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4506094306377866553195781 844892682445849978724209)
            ·
              refine ⟨633669511834387484043157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844892682445849978724209 633669511834387484043157)
              ·
                refine ⟨29703258367236913314523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 633669511834387484043157 29703258367236913314523)
                ·
                  rfl

theorem cell22_780933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 6].length) (baseStart_780933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_780933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_780933 prefixEnd_780933 := by exact prefixLift 780933
  have htrace : WordTrace (prefixWord ++ tailWord_780933) baseStart_780933 baseEnd_780933 := by
    simpa [prefixWord, tailWord_780933, baseEnd_780933] using wordTrace_append hprefix tailTrace_780933
  have hstable : (prefixWord ++ tailWord_780933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780933).length < 2 ^ (prefixWord ++ tailWord_780933).sum := by decide
  have hdescent : baseEnd_780933 < baseStart_780933 := by decide
  rcases family_descends (prefixWord ++ tailWord_780933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781036 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_781036 : Nat := 118140960795 + 781036 * 2 ^ 59
def prefixEnd_781036 : Nat := 4983230072969 + 3 ^ 40 * 781036 * 2
def baseEnd_781036 : Nat := 267364584310074284505391

theorem tailTrace_781036 : CollatzResearch.WordTrace tailWord_781036 prefixEnd_781036 267364584310074284505391 := by
  unfold tailWord_781036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243361599223718587081481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18991148798964958116108641 14243361599223718587081481)
  ·
    refine ⟨10682521199417788940311111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14243361599223718587081481 10682521199417788940311111)
    ·
      refine ⟨16023781799126683410466667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10682521199417788940311111 16023781799126683410466667)
      ·
        refine ⟨24035672698690025115700001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16023781799126683410466667 24035672698690025115700001)
        ·
          refine ⟨18026754524017518836775001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24035672698690025115700001 18026754524017518836775001)
          ·
            refine ⟨13520065893013139127581251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18026754524017518836775001 13520065893013139127581251)
            ·
              refine ⟨20280098839519708691371877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13520065893013139127581251 20280098839519708691371877)
              ·
                refine ⟨3802518532409945379632227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20280098839519708691371877 3802518532409945379632227)
                ·
                  refine ⟨5703777798614918069448341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802518532409945379632227 5703777798614918069448341)
                  ·
                    refine ⟨267364584310074284505391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5703777798614918069448341 267364584310074284505391)
                    ·
                      rfl

theorem cell22_781036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_781036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781036 prefixEnd_781036 := by exact prefixLift 781036
  have htrace : WordTrace (prefixWord ++ tailWord_781036) baseStart_781036 baseEnd_781036 := by
    simpa [prefixWord, tailWord_781036, baseEnd_781036] using wordTrace_append hprefix tailTrace_781036
  have hstable : (prefixWord ++ tailWord_781036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781036).length < 2 ^ (prefixWord ++ tailWord_781036).sum := by decide
  have hdescent : baseEnd_781036 < baseStart_781036 := by decide
  rcases family_descends (prefixWord ++ tailWord_781036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781038 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_781038 : Nat := 118140960795 + 781038 * 2 ^ 59
def prefixEnd_781038 : Nat := 4983230072969 + 3 ^ 40 * 781038 * 2
def baseEnd_781038 : Nat := 267365268950946945955385

theorem tailTrace_781038 : CollatzResearch.WordTrace tailWord_781038 prefixEnd_781038 267365268950946945955385 := by
  unfold tailWord_781038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560849518055023939466971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18991197429626794343823845 3560849518055023939466971)
  ·
    refine ⟨5341274277082535909200457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560849518055023939466971 5341274277082535909200457)
    ·
      refine ⟨4005955707811901931900343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5341274277082535909200457 4005955707811901931900343)
      ·
        refine ⟨6008933561717852897850515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005955707811901931900343 6008933561717852897850515)
        ·
          refine ⟨9013400342576779346775773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008933561717852897850515 9013400342576779346775773)
          ·
            refine ⟨3380025128466292255040915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9013400342576779346775773 3380025128466292255040915)
            ·
              refine ⟨5070037692699438382561373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380025128466292255040915 5070037692699438382561373)
              ·
                refine ⟨1901264134762289393460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5070037692699438382561373 1901264134762289393460515)
                ·
                  refine ⟨2851896202143434090190773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901264134762289393460515 2851896202143434090190773)
                  ·
                    refine ⟨267365268950946945955385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2851896202143434090190773 267365268950946945955385)
                    ·
                      rfl

theorem cell22_781038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_781038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781038 prefixEnd_781038 := by exact prefixLift 781038
  have htrace : WordTrace (prefixWord ++ tailWord_781038) baseStart_781038 baseEnd_781038 := by
    simpa [prefixWord, tailWord_781038, baseEnd_781038] using wordTrace_append hprefix tailTrace_781038
  have hstable : (prefixWord ++ tailWord_781038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781038).length < 2 ^ (prefixWord ++ tailWord_781038).sum := by decide
  have hdescent : baseEnd_781038 < baseStart_781038 := by decide
  rcases family_descends (prefixWord ++ tailWord_781038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781081 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_781081 : Nat := 118140960795 + 781081 * 2 ^ 59
def prefixEnd_781081 : Nat := 4983230072969 + 3 ^ 40 * 781081 * 2
def baseEnd_781081 : Nat := 267379988729709167130253

theorem tailTrace_781081 : CollatzResearch.WordTrace tailWord_781081 prefixEnd_781081 267379988729709167130253 := by
  unfold tailWord_781081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488364483284409859551097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18992242988856273239700731 28488364483284409859551097)
  ·
    refine ⟨21366273362463307394663323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28488364483284409859551097 21366273362463307394663323)
    ·
      refine ⟨32049410043694961091994985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21366273362463307394663323 32049410043694961091994985)
      ·
        refine ⟨24037057532771220818996239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32049410043694961091994985 24037057532771220818996239)
        ·
          refine ⟨36055586299156831228494359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24037057532771220818996239 36055586299156831228494359)
          ·
            refine ⟨54083379448735246842741539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36055586299156831228494359 54083379448735246842741539)
            ·
              refine ⟨81125069173102870264112309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54083379448735246842741539 81125069173102870264112309)
              ·
                refine ⟨7605475234978394087260529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81125069173102870264112309 7605475234978394087260529)
                ·
                  refine ⟨5704106426233795565445397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605475234978394087260529 5704106426233795565445397)
                  ·
                    refine ⟨267379988729709167130253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5704106426233795565445397 267379988729709167130253)
                    ·
                      rfl

theorem cell22_781081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_781081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781081 prefixEnd_781081 := by exact prefixLift 781081
  have htrace : WordTrace (prefixWord ++ tailWord_781081) baseStart_781081 baseEnd_781081 := by
    simpa [prefixWord, tailWord_781081, baseEnd_781081] using wordTrace_append hprefix tailTrace_781081
  have hstable : (prefixWord ++ tailWord_781081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781081).length < 2 ^ (prefixWord ++ tailWord_781081).sum := by decide
  have hdescent : baseEnd_781081 < baseStart_781081 := by decide
  rcases family_descends (prefixWord ++ tailWord_781081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781102 : List Nat := [4, 1, 3, 2, 1, 3, 2, 6]
def baseStart_781102 : Nat := 118140960795 + 781102 * 2 ^ 59
def prefixEnd_781102 : Nat := 4983230072969 + 3 ^ 40 * 781102 * 2
def baseEnd_781102 : Nat := 29709686384319123595021

theorem tailTrace_781102 : CollatzResearch.WordTrace tailWord_781102 prefixEnd_781102 29709686384319123595021 := by
  unfold tailWord_781102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561141302026041305758195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18992753610805553630710373 3561141302026041305758195)
  ·
    refine ⟨5341711953039061958637293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3561141302026041305758195 5341711953039061958637293)
    ·
      refine ⟨2003141982389648234488985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5341711953039061958637293 2003141982389648234488985)
      ·
        refine ⟨1502356486792236175866739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2003141982389648234488985 1502356486792236175866739)
        ·
          refine ⟨2253534730188354263800109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502356486792236175866739 2253534730188354263800109)
          ·
            refine ⟨845075523820632848925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2253534730188354263800109 845075523820632848925041)
            ·
              refine ⟨633806642865474636693781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845075523820632848925041 633806642865474636693781)
              ·
                refine ⟨29709686384319123595021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 633806642865474636693781 29709686384319123595021)
                ·
                  rfl

theorem cell22_781102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_781102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781102 prefixEnd_781102 := by exact prefixLift 781102
  have htrace : WordTrace (prefixWord ++ tailWord_781102) baseStart_781102 baseEnd_781102 := by
    simpa [prefixWord, tailWord_781102, baseEnd_781102] using wordTrace_append hprefix tailTrace_781102
  have hstable : (prefixWord ++ tailWord_781102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781102).length < 2 ^ (prefixWord ++ tailWord_781102).sum := by decide
  have hdescent : baseEnd_781102 < baseStart_781102 := by decide
  rcases family_descends (prefixWord ++ tailWord_781102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781160 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_781160 : Nat := 118140960795 + 781160 * 2 ^ 59
def prefixEnd_781160 : Nat := 4983230072969 + 3 ^ 40 * 781160 * 2
def baseEnd_781160 : Nat := 267407032044179294405011

theorem tailTrace_781160 : CollatzResearch.WordTrace tailWord_781160 prefixEnd_781160 267407032044179294405011 := by
  unfold tailWord_781160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245622924999103175838467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18994163899998804234451289 14245622924999103175838467)
  ·
    refine ⟨21368434387498654763757701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14245622924999103175838467 21368434387498654763757701)
    ·
      refine ⟨4006581447655997768204569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21368434387498654763757701 4006581447655997768204569)
      ·
        refine ⟨3004936085741998326153427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006581447655997768204569 3004936085741998326153427)
        ·
          refine ⟨4507404128612997489230141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004936085741998326153427 4507404128612997489230141)
          ·
            refine ⟨1690276548229874058461303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4507404128612997489230141 1690276548229874058461303)
            ·
              refine ⟨2535414822344811087691955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690276548229874058461303 2535414822344811087691955)
              ·
                refine ⟨3803122233517216631537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535414822344811087691955 3803122233517216631537933)
                ·
                  refine ⟨1426170837568956236826725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3803122233517216631537933 1426170837568956236826725)
                  ·
                    refine ⟨267407032044179294405011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426170837568956236826725 267407032044179294405011)
                    ·
                      rfl

theorem cell22_781160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_781160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781160 prefixEnd_781160 := by exact prefixLift 781160
  have htrace : WordTrace (prefixWord ++ tailWord_781160) baseStart_781160 baseEnd_781160 := by
    simpa [prefixWord, tailWord_781160, baseEnd_781160] using wordTrace_append hprefix tailTrace_781160
  have hstable : (prefixWord ++ tailWord_781160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781160).length < 2 ^ (prefixWord ++ tailWord_781160).sum := by decide
  have hdescent : baseEnd_781160 < baseStart_781160 := by decide
  rcases family_descends (prefixWord ++ tailWord_781160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781177 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_781177 : Nat := 118140960795 + 781177 * 2 ^ 59
def prefixEnd_781177 : Nat := 4983230072969 + 3 ^ 40 * 781177 * 2
def baseEnd_781177 : Nat := 267412851491596916729959

theorem tailTrace_781177 : CollatzResearch.WordTrace tailWord_781177 prefixEnd_781177 267412851491596916729959 := by
  unfold tailWord_781177
  simp only [CollatzResearch.WordTrace]
  refine ⟨28491865890936618255045785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18994577260624412170030523 28491865890936618255045785)
  ·
    refine ⟨21368899418202463691284339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28491865890936618255045785 21368899418202463691284339)
    ·
      refine ⟨32053349127303695536926509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21368899418202463691284339 32053349127303695536926509)
      ·
        refine ⟨12020005922738885826347441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32053349127303695536926509 12020005922738885826347441)
        ·
          refine ⟨9015004442054164369760581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12020005922738885826347441 9015004442054164369760581)
          ·
            refine ⟨1690313332885155819330109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9015004442054164369760581 1690313332885155819330109)
            ·
              refine ⟨633867499831933432248791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690313332885155819330109 633867499831933432248791)
              ·
                refine ⟨950801249747900148373187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633867499831933432248791 950801249747900148373187)
                ·
                  refine ⟨1426201874621850222559781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950801249747900148373187 1426201874621850222559781)
                  ·
                    refine ⟨267412851491596916729959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426201874621850222559781 267412851491596916729959)
                    ·
                      rfl

theorem cell22_781177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_781177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781177 prefixEnd_781177 := by exact prefixLift 781177
  have htrace : WordTrace (prefixWord ++ tailWord_781177) baseStart_781177 baseEnd_781177 := by
    simpa [prefixWord, tailWord_781177, baseEnd_781177] using wordTrace_append hprefix tailTrace_781177
  have hstable : (prefixWord ++ tailWord_781177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781177).length < 2 ^ (prefixWord ++ tailWord_781177).sum := by decide
  have hdescent : baseEnd_781177 < baseStart_781177 := by decide
  rcases family_descends (prefixWord ++ tailWord_781177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781188 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_781188 : Nat := 118140960795 + 781188 * 2 ^ 59
def prefixEnd_781188 : Nat := 4983230072969 + 3 ^ 40 * 781188 * 2
def baseEnd_781188 : Nat := 267416617016396554704925

theorem tailTrace_781188 : CollatzResearch.WordTrace tailWord_781188 prefixEnd_781188 267416617016396554704925 := by
  unfold tailWord_781188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246133546948383566848109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18994844729264511422464145 14246133546948383566848109)
  ·
    refine ⟨5342300080105643837568041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14246133546948383566848109 5342300080105643837568041)
    ·
      refine ⟨4006725060079232878176031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5342300080105643837568041 4006725060079232878176031)
      ·
        refine ⟨6010087590118849317264047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006725060079232878176031 6010087590118849317264047)
        ·
          refine ⟨9015131385178273975896071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010087590118849317264047 9015131385178273975896071)
          ·
            refine ⟨13522697077767410963844107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015131385178273975896071 13522697077767410963844107)
            ·
              refine ⟨20284045616651116445766161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522697077767410963844107 20284045616651116445766161)
              ·
                refine ⟨15213034212488337334324621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20284045616651116445766161 15213034212488337334324621)
                ·
                  refine ⟨5704887829683126500371733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15213034212488337334324621 5704887829683126500371733)
                  ·
                    refine ⟨267416617016396554704925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5704887829683126500371733 267416617016396554704925)
                    ·
                      rfl

theorem cell22_781188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_781188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781188 prefixEnd_781188 := by exact prefixLift 781188
  have htrace : WordTrace (prefixWord ++ tailWord_781188) baseStart_781188 baseEnd_781188 := by
    simpa [prefixWord, tailWord_781188, baseEnd_781188] using wordTrace_append hprefix tailTrace_781188
  have hstable : (prefixWord ++ tailWord_781188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781188).length < 2 ^ (prefixWord ++ tailWord_781188).sum := by decide
  have hdescent : baseEnd_781188 < baseStart_781188 := by decide
  rcases family_descends (prefixWord ++ tailWord_781188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781192 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_781192 : Nat := 118140960795 + 781192 * 2 ^ 59
def prefixEnd_781192 : Nat := 4983230072969 + 3 ^ 40 * 781192 * 2
def baseEnd_781192 : Nat := 89139328766047292534971

theorem tailTrace_781192 : CollatzResearch.WordTrace tailWord_781192 prefixEnd_781192 89139328766047292534971 := by
  unfold tailWord_781192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246206492941137908420915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18994941990588183877894553 14246206492941137908420915)
  ·
    refine ⟨21369309739411706862631373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14246206492941137908420915 21369309739411706862631373)
    ·
      refine ⟨8013491152279390073486765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21369309739411706862631373 8013491152279390073486765)
      ·
        refine ⟨3005059182104771277557537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8013491152279390073486765 3005059182104771277557537)
        ·
          refine ⟨2253794386578578458168153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005059182104771277557537 2253794386578578458168153)
          ·
            refine ⟨1690345789933933843626115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253794386578578458168153 1690345789933933843626115)
            ·
              refine ⟨2535518684900900765439173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690345789933933843626115 2535518684900900765439173)
              ·
                refine ⟨475409753418918893519845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2535518684900900765439173 475409753418918893519845)
                ·
                  refine ⟨89139328766047292534971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475409753418918893519845 89139328766047292534971)
                  ·
                    rfl

theorem cell22_781192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_781192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781192 prefixEnd_781192 := by exact prefixLift 781192
  have htrace : WordTrace (prefixWord ++ tailWord_781192) baseStart_781192 baseEnd_781192 := by
    simpa [prefixWord, tailWord_781192, baseEnd_781192] using wordTrace_append hprefix tailTrace_781192
  have hstable : (prefixWord ++ tailWord_781192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781192).length < 2 ^ (prefixWord ++ tailWord_781192).sum := by decide
  have hdescent : baseEnd_781192 < baseStart_781192 := by decide
  rcases family_descends (prefixWord ++ tailWord_781192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781220 : List Nat := [2, 3, 1, 2, 1, 2, 5, 6]
def baseStart_781220 : Nat := 118140960795 + 781220 * 2 ^ 59
def prefixEnd_781220 : Nat := 4983230072969 + 3 ^ 40 * 781220 * 2
def baseEnd_781220 : Nat := 29714174585595459767203

theorem tailTrace_781220 : CollatzResearch.WordTrace tailWord_781220 prefixEnd_781220 29714174585595459767203 := by
  unfold tailWord_781220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246717114890418299430557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18995622819853891065907409 14246717114890418299430557)
  ·
    refine ⟨5342518918083906862286459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14246717114890418299430557 5342518918083906862286459)
    ·
      refine ⟨8013778377125860293429689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5342518918083906862286459 8013778377125860293429689)
      ·
        refine ⟨6010333782844395220072267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8013778377125860293429689 6010333782844395220072267)
        ·
          refine ⟨9015500674266592830108401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010333782844395220072267 9015500674266592830108401)
          ·
            refine ⟨6761625505699944622581301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9015500674266592830108401 6761625505699944622581301)
            ·
              refine ⟨633902391159369808366997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6761625505699944622581301 633902391159369808366997)
              ·
                refine ⟨29714174585595459767203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 633902391159369808366997 29714174585595459767203)
                ·
                  rfl

theorem cell22_781220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_781220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781220 prefixEnd_781220 := by exact prefixLift 781220
  have htrace : WordTrace (prefixWord ++ tailWord_781220) baseStart_781220 baseEnd_781220 := by
    simpa [prefixWord, tailWord_781220, baseEnd_781220] using wordTrace_append hprefix tailTrace_781220
  have hstable : (prefixWord ++ tailWord_781220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781220).length < 2 ^ (prefixWord ++ tailWord_781220).sum := by decide
  have hdescent : baseEnd_781220 < baseStart_781220 := by decide
  rcases family_descends (prefixWord ++ tailWord_781220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
