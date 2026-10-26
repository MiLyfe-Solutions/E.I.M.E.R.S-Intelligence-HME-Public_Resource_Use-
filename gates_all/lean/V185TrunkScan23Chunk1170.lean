import V185TrunkScan23Chunk1169

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6931865 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6931865 : Nat := 118140960795 + 6931865 * 2 ^ 59
def prefixEnd_6931865 : Nat := 4983230072969 + 3 ^ 40 * 6931865 * 2
def baseEnd_6931865 : Nat := 3559378577078626780008439

theorem tailTrace_6931865 : CollatzResearch.WordTrace tailWord_6931865 prefixEnd_6931865 3559378577078626780008439 := by
  unfold tailWord_6931865
  simp only [CollatzResearch.WordTrace]
  refine ⟨252825887032044448134541049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168550591354696298756360699 252825887032044448134541049)
  ·
    refine ⟨189619415274033336100905787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252825887032044448134541049 189619415274033336100905787)
    ·
      refine ⟨284429122911050004151358681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189619415274033336100905787 284429122911050004151358681)
      ·
        refine ⟨213321842183287503113519011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284429122911050004151358681 213321842183287503113519011)
        ·
          refine ⟨319982763274931254670278517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213321842183287503113519011 319982763274931254670278517)
          ·
            refine ⟨29998384057024805125338611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 319982763274931254670278517 29998384057024805125338611)
            ·
              refine ⟨44997576085537207688007917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29998384057024805125338611 44997576085537207688007917)
              ·
                refine ⟨16874091032076452883002969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44997576085537207688007917 16874091032076452883002969)
                ·
                  refine ⟨12655568274057339662252227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16874091032076452883002969 12655568274057339662252227)
                  ·
                    refine ⟨18983352411086009493378341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12655568274057339662252227 18983352411086009493378341)
                    ·
                      refine ⟨3559378577078626780008439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18983352411086009493378341 3559378577078626780008439)
                      ·
                        rfl

theorem cell23_6931865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6931865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931865 prefixEnd_6931865 := by exact prefixLift 6931865
  have htrace : WordTrace (prefixWord ++ tailWord_6931865) baseStart_6931865 baseEnd_6931865 := by
    simpa [prefixWord, tailWord_6931865, baseEnd_6931865] using wordTrace_append hprefix tailTrace_6931865
  have hstable : (prefixWord ++ tailWord_6931865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931865).length < 2 ^ (prefixWord ++ tailWord_6931865).sum := by decide
  have hdescent : baseEnd_6931865 < baseStart_6931865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931926 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_6931926 : Nat := 118140960795 + 6931926 * 2 ^ 59
def prefixEnd_6931926 : Nat := 4983230072969 + 3 ^ 40 * 6931926 * 2
def baseEnd_6931926 : Nat := 1186469966466183680448553

theorem tailTrace_6931926 : CollatzResearch.WordTrace tailWord_6931926 prefixEnd_6931926 1186469966466183680448553 := by
  unfold tailWord_6931926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801756992801465972031977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168552074589882303701674421 15801756992801465972031977)
  ·
    refine ⟨11851317744601099479023983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15801756992801465972031977 11851317744601099479023983)
    ·
      refine ⟨17776976616901649218535975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11851317744601099479023983 17776976616901649218535975)
      ·
        refine ⟨26665464925352473827803963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17776976616901649218535975 26665464925352473827803963)
        ·
          refine ⟨39998197388028710741705945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26665464925352473827803963 39998197388028710741705945)
          ·
            refine ⟨29998648041021533056279459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39998197388028710741705945 29998648041021533056279459)
            ·
              refine ⟨44997972061532299584419189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29998648041021533056279459 44997972061532299584419189)
              ·
                refine ⟨4218559880768653086039299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44997972061532299584419189 4218559880768653086039299)
                ·
                  refine ⟨6327839821152979629058949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218559880768653086039299 6327839821152979629058949)
                  ·
                    refine ⟨1186469966466183680448553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327839821152979629058949 1186469966466183680448553)
                    ·
                      rfl

theorem cell23_6931926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_6931926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931926 prefixEnd_6931926 := by exact prefixLift 6931926
  have htrace : WordTrace (prefixWord ++ tailWord_6931926) baseStart_6931926 baseEnd_6931926 := by
    simpa [prefixWord, tailWord_6931926, baseEnd_6931926] using wordTrace_append hprefix tailTrace_6931926
  have hstable : (prefixWord ++ tailWord_6931926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931926).length < 2 ^ (prefixWord ++ tailWord_6931926).sum := by decide
  have hdescent : baseEnd_6931926 < baseStart_6931926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931955 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4]
def baseStart_6931955 : Nat := 118140960795 + 6931955 * 2 ^ 59
def prefixEnd_6931955 : Nat := 4983230072969 + 3 ^ 40 * 6931955 * 2
def baseEnd_6931955 : Nat := 3559424790337531427883025

theorem tailTrace_6931955 : CollatzResearch.WordTrace tailWord_6931955 prefixEnd_6931955 3559424790337531427883025 := by
  unfold tailWord_6931955
  simp only [CollatzResearch.WordTrace]
  refine ⟨252829169601718393505317319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168552779734478929003544879 252829169601718393505317319)
  ·
    refine ⟨379243754402577590257975979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252829169601718393505317319 379243754402577590257975979)
    ·
      refine ⟨568865631603866385386963969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379243754402577590257975979 568865631603866385386963969)
      ·
        refine ⟨426649223702899789040222977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568865631603866385386963969 426649223702899789040222977)
        ·
          refine ⟨319986917777174841780167233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426649223702899789040222977 319986917777174841780167233)
          ·
            refine ⟨239990188332881131335125425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319986917777174841780167233 239990188332881131335125425)
            ·
              refine ⟨179992641249660848501344069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239990188332881131335125425 179992641249660848501344069)
              ·
                refine ⟨33748620234311409094002013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179992641249660848501344069 33748620234311409094002013)
                ·
                  refine ⟨12655732587866778410250755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33748620234311409094002013 12655732587866778410250755)
                  ·
                    refine ⟨18983598881800167615376133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12655732587866778410250755 18983598881800167615376133)
                    ·
                      refine ⟨3559424790337531427883025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18983598881800167615376133 3559424790337531427883025)
                      ·
                        rfl

theorem cell23_6931955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_6931955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931955 prefixEnd_6931955 := by exact prefixLift 6931955
  have htrace : WordTrace (prefixWord ++ tailWord_6931955) baseStart_6931955 baseEnd_6931955 := by
    simpa [prefixWord, tailWord_6931955, baseEnd_6931955] using wordTrace_append hprefix tailTrace_6931955
  have hstable : (prefixWord ++ tailWord_6931955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931955).length < 2 ^ (prefixWord ++ tailWord_6931955).sum := by decide
  have hdescent : baseEnd_6931955 < baseStart_6931955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931969 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_6931969 : Nat := 118140960795 + 6931969 * 2 ^ 59
def prefixEnd_6931969 : Nat := 4983230072969 + 3 ^ 40 * 6931969 * 2
def baseEnd_6931969 : Nat := 1186477326355564791035987

theorem tailTrace_6931969 : CollatzResearch.WordTrace tailWord_6931969 prefixEnd_6931969 1186477326355564791035987 := by
  unfold tailWord_6931969
  simp only [CollatzResearch.WordTrace]
  refine ⟨252829680223667673896326961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168553120149111782597551307 252829680223667673896326961)
  ·
    refine ⟨189622260167750755422245221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252829680223667673896326961 189622260167750755422245221)
    ·
      refine ⟨35554173781453266641670979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189622260167750755422245221 35554173781453266641670979)
      ·
        refine ⟨53331260672179899962506469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35554173781453266641670979 53331260672179899962506469)
        ·
          refine ⟨9999611376033731242969963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53331260672179899962506469 9999611376033731242969963)
          ·
            refine ⟨14999417064050596864454945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9999611376033731242969963 14999417064050596864454945)
            ·
              refine ⟨11249562798037947648341209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14999417064050596864454945 11249562798037947648341209)
              ·
                refine ⟨8437172098528460736255907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11249562798037947648341209 8437172098528460736255907)
                ·
                  refine ⟨12655758147792691104383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437172098528460736255907 12655758147792691104383861)
                  ·
                    refine ⟨1186477326355564791035987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12655758147792691104383861 1186477326355564791035987)
                    ·
                      rfl

theorem cell23_6931969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_6931969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931969 prefixEnd_6931969 := by exact prefixLift 6931969
  have htrace : WordTrace (prefixWord ++ tailWord_6931969) baseStart_6931969 baseEnd_6931969 := by
    simpa [prefixWord, tailWord_6931969, baseEnd_6931969] using wordTrace_append hprefix tailTrace_6931969
  have hstable : (prefixWord ++ tailWord_6931969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931969).length < 2 ^ (prefixWord ++ tailWord_6931969).sum := by decide
  have hdescent : baseEnd_6931969 < baseStart_6931969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931985 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_6931985 : Nat := 118140960795 + 6931985 * 2 ^ 59
def prefixEnd_6931985 : Nat := 4983230072969 + 3 ^ 40 * 6931985 * 2
def baseEnd_6931985 : Nat := 3559440194757166310507887

theorem tailTrace_6931985 : CollatzResearch.WordTrace tailWord_6931985 prefixEnd_6931985 3559440194757166310507887 := by
  unfold tailWord_6931985
  simp only [CollatzResearch.WordTrace]
  refine ⟨252830263791609708628909409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168553509194406472419272939 252830263791609708628909409)
  ·
    refine ⟨189622697843707281471682057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252830263791609708628909409 189622697843707281471682057)
    ·
      refine ⟨142217023382780461103761543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189622697843707281471682057 142217023382780461103761543)
      ·
        refine ⟨213325535074170691655642315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142217023382780461103761543 213325535074170691655642315)
        ·
          refine ⟨319988302611256037483463473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213325535074170691655642315 319988302611256037483463473)
          ·
            refine ⟨239991226958442028112597605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319988302611256037483463473 239991226958442028112597605)
            ·
              refine ⟨44998355054707880271112051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239991226958442028112597605 44998355054707880271112051)
              ·
                refine ⟨67497532582061820406668077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44998355054707880271112051 67497532582061820406668077)
                ·
                  refine ⟨25311574718273182652500529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67497532582061820406668077 25311574718273182652500529)
                  ·
                    refine ⟨18983681038704886989375397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25311574718273182652500529 18983681038704886989375397)
                    ·
                      refine ⟨3559440194757166310507887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18983681038704886989375397 3559440194757166310507887)
                      ·
                        rfl

theorem cell23_6931985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_6931985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931985 prefixEnd_6931985 := by exact prefixLift 6931985
  have htrace : WordTrace (prefixWord ++ tailWord_6931985) baseStart_6931985 baseEnd_6931985 := by
    simpa [prefixWord, tailWord_6931985, baseEnd_6931985] using wordTrace_append hprefix tailTrace_6931985
  have hstable : (prefixWord ++ tailWord_6931985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931985).length < 2 ^ (prefixWord ++ tailWord_6931985).sum := by decide
  have hdescent : baseEnd_6931985 < baseStart_6931985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932039 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_6932039 : Nat := 118140960795 + 6932039 * 2 ^ 59
def prefixEnd_6932039 : Nat := 4983230072969 + 3 ^ 40 * 6932039 * 2
def baseEnd_6932039 : Nat := 3559467922712509099232639

theorem tailTrace_6932039 : CollatzResearch.WordTrace tailWord_6932039 prefixEnd_6932039 3559467922712509099232639 := by
  unfold tailWord_6932039
  simp only [CollatzResearch.WordTrace]
  refine ⟨252832233333414075851375171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168554822222276050567583447 252832233333414075851375171)
  ·
    refine ⟨379248350000121113777062757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252832233333414075851375171 379248350000121113777062757)
    ·
      refine ⟨71109065625022708833199267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379248350000121113777062757 71109065625022708833199267)
      ·
        refine ⟨106663598437534063249798901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71109065625022708833199267 106663598437534063249798901)
        ·
          refine ⟨9999712353518818429668647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106663598437534063249798901 9999712353518818429668647)
          ·
            refine ⟨14999568530278227644502971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9999712353518818429668647 14999568530278227644502971)
            ·
              refine ⟨22499352795417341466754457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14999568530278227644502971 22499352795417341466754457)
              ·
                refine ⟨16874514596563006100065843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22499352795417341466754457 16874514596563006100065843)
                ·
                  refine ⟨25311771894844509150098765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16874514596563006100065843 25311771894844509150098765)
                  ·
                    refine ⟨9491914460566690931287037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25311771894844509150098765 9491914460566690931287037)
                    ·
                      refine ⟨3559467922712509099232639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9491914460566690931287037 3559467922712509099232639)
                      ·
                        rfl

theorem cell23_6932039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_6932039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932039 prefixEnd_6932039 := by exact prefixLift 6932039
  have htrace : WordTrace (prefixWord ++ tailWord_6932039) baseStart_6932039 baseEnd_6932039 := by
    simpa [prefixWord, tailWord_6932039, baseEnd_6932039] using wordTrace_append hprefix tailTrace_6932039
  have hstable : (prefixWord ++ tailWord_6932039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932039).length < 2 ^ (prefixWord ++ tailWord_6932039).sum := by decide
  have hdescent : baseEnd_6932039 < baseStart_6932039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932072 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6932072 : Nat := 118140960795 + 6932072 * 2 ^ 59
def prefixEnd_6932072 : Nat := 4983230072969 + 3 ^ 40 * 6932072 * 2
def baseEnd_6932072 : Nat := 1186494955858035823373329

theorem tailTrace_6932072 : CollatzResearch.WordTrace tailWord_6932072 prefixEnd_6932072 1186494955858035823373329 := by
  unfold tailWord_6932072
  simp only [CollatzResearch.WordTrace]
  refine ⟨126416718471147261243663235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168555624628196348324884313 126416718471147261243663235)
  ·
    refine ⟨189625077706720891865494853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126416718471147261243663235 189625077706720891865494853)
    ·
      refine ⟨35554702070010167224780285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189625077706720891865494853 35554702070010167224780285)
      ·
        refine ⟨13333013276253812709292607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35554702070010167224780285 13333013276253812709292607)
        ·
          refine ⟨19999519914380719063938911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13333013276253812709292607 19999519914380719063938911)
          ·
            refine ⟨29999279871571078595908367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999519914380719063938911 29999279871571078595908367)
            ·
              refine ⟨44998919807356617893862551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29999279871571078595908367 44998919807356617893862551)
              ·
                refine ⟨67498379711034926840793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44998919807356617893862551 67498379711034926840793827)
                ·
                  refine ⟨101247569566552390261190741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67498379711034926840793827 101247569566552390261190741)
                  ·
                    refine ⟨1186494955858035823373329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101247569566552390261190741 1186494955858035823373329)
                    ·
                      rfl

theorem cell23_6932072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6932072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932072 prefixEnd_6932072 := by exact prefixLift 6932072
  have htrace : WordTrace (prefixWord ++ tailWord_6932072) baseStart_6932072 baseEnd_6932072 := by
    simpa [prefixWord, tailWord_6932072, baseEnd_6932072] using wordTrace_append hprefix tailTrace_6932072
  have hstable : (prefixWord ++ tailWord_6932072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932072).length < 2 ^ (prefixWord ++ tailWord_6932072).sum := by decide
  have hdescent : baseEnd_6932072 < baseStart_6932072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932079 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 6, 2, 2]
def baseStart_6932079 : Nat := 118140960795 + 6932079 * 2 ^ 59
def prefixEnd_6932079 : Nat := 4983230072969 + 3 ^ 40 * 6932079 * 2
def baseEnd_6932079 : Nat := 3559488461938688942732455

theorem tailTrace_6932079 : CollatzResearch.WordTrace tailWord_6932079 prefixEnd_6932079 3559488461938688942732455 := by
  unfold tailWord_6932079
  simp only [CollatzResearch.WordTrace]
  refine ⟨252833692253269162682831291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168555794835512775121887527 252833692253269162682831291)
  ·
    refine ⟨379250538379903744024246937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252833692253269162682831291 379250538379903744024246937)
    ·
      refine ⟨284437903784927808018185203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379250538379903744024246937 284437903784927808018185203)
      ·
        refine ⟨426656855677391712027277805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284437903784927808018185203 426656855677391712027277805)
        ·
          refine ⟨159996320879021892010229177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426656855677391712027277805 159996320879021892010229177)
          ·
            refine ⟨119997240659266419007671883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159996320879021892010229177 119997240659266419007671883)
            ·
              refine ⟨179995860988899628511507825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119997240659266419007671883 179995860988899628511507825)
              ·
                refine ⟨134996895741674721383630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179995860988899628511507825 134996895741674721383630869)
                ·
                  refine ⟨6327979487891002564857697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134996895741674721383630869 6327979487891002564857697)
                  ·
                    refine ⟨4745984615918251923643273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327979487891002564857697 4745984615918251923643273)
                    ·
                      refine ⟨3559488461938688942732455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745984615918251923643273 3559488461938688942732455)
                      ·
                        rfl

theorem cell23_6932079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2, 2].length) (baseStart_6932079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932079 prefixEnd_6932079 := by exact prefixLift 6932079
  have htrace : WordTrace (prefixWord ++ tailWord_6932079) baseStart_6932079 baseEnd_6932079 := by
    simpa [prefixWord, tailWord_6932079, baseEnd_6932079] using wordTrace_append hprefix tailTrace_6932079
  have hstable : (prefixWord ++ tailWord_6932079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932079).length < 2 ^ (prefixWord ++ tailWord_6932079).sum := by decide
  have hdescent : baseEnd_6932079 < baseStart_6932079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932100 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6932100 : Nat := 118140960795 + 6932100 * 2 ^ 59
def prefixEnd_6932100 : Nat := 4983230072969 + 3 ^ 40 * 6932100 * 2
def baseEnd_6932100 : Nat := 3559499245032433360569859

theorem tailTrace_6932100 : CollatzResearch.WordTrace tailWord_6932100 prefixEnd_6932100 3559499245032433360569859 := by
  unfold tailWord_6932100
  simp only [CollatzResearch.WordTrace]
  refine ⟨126417229093096541634672877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168556305457462055512897169 126417229093096541634672877)
  ·
    refine ⟨47406460909911203113002329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126417229093096541634672877 47406460909911203113002329)
    ·
      refine ⟨35554845682433402334751747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47406460909911203113002329 35554845682433402334751747)
      ·
        refine ⟨53332268523650103502127621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35554845682433402334751747 53332268523650103502127621)
        ·
          refine ⟨9999800348184394406648929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53332268523650103502127621 9999800348184394406648929)
          ·
            refine ⟨7499850261138295804986697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9999800348184394406648929 7499850261138295804986697)
            ·
              refine ⟨5624887695853721853740023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7499850261138295804986697 5624887695853721853740023)
              ·
                refine ⟨8437331543780582780610035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624887695853721853740023 8437331543780582780610035)
                ·
                  refine ⟨12655997315670874170915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437331543780582780610035 12655997315670874170915053)
                  ·
                    refine ⟨4745998993376577814093145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12655997315670874170915053 4745998993376577814093145)
                    ·
                      refine ⟨3559499245032433360569859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745998993376577814093145 3559499245032433360569859)
                      ·
                        rfl

theorem cell23_6932100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6932100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932100 prefixEnd_6932100 := by exact prefixLift 6932100
  have htrace : WordTrace (prefixWord ++ tailWord_6932100) baseStart_6932100 baseEnd_6932100 := by
    simpa [prefixWord, tailWord_6932100, baseEnd_6932100] using wordTrace_append hprefix tailTrace_6932100
  have hstable : (prefixWord ++ tailWord_6932100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932100).length < 2 ^ (prefixWord ++ tailWord_6932100).sum := by decide
  have hdescent : baseEnd_6932100 < baseStart_6932100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932115 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 7]
def baseStart_6932115 : Nat := 118140960795 + 6932115 * 2 ^ 59
def prefixEnd_6932115 : Nat := 4983230072969 + 3 ^ 40 * 6932115 * 2
def baseEnd_6932115 : Nat := 1186502315747416933960763

theorem tailTrace_6932115 : CollatzResearch.WordTrace tailWord_6932115 prefixEnd_6932115 1186502315747416933960763 := by
  unfold tailWord_6932115
  simp only [CollatzResearch.WordTrace]
  refine ⟨252835005281138740831141799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168556670187425827220761199 252835005281138740831141799)
  ·
    refine ⟨379252507921708111246712699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252835005281138740831141799 379252507921708111246712699)
    ·
      refine ⟨568878761882562166870069049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379252507921708111246712699 568878761882562166870069049)
      ·
        refine ⟨426659071411921625152551787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568878761882562166870069049 426659071411921625152551787)
        ·
          refine ⟨639988607117882437728827681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426659071411921625152551787 639988607117882437728827681)
          ·
            refine ⟨479991455338411828296620761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639988607117882437728827681 479991455338411828296620761)
            ·
              refine ⟨359993591503808871222465571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479991455338411828296620761 359993591503808871222465571)
              ·
                refine ⟨539990387255713306833698357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359993591503808871222465571 539990387255713306833698357)
                ·
                  refine ⟨50624098805223122515659221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539990387255713306833698357 50624098805223122515659221)
                  ·
                    refine ⟨1186502315747416933960763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50624098805223122515659221 1186502315747416933960763)
                    ·
                      rfl

theorem cell23_6932115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_6932115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932115 prefixEnd_6932115 := by exact prefixLift 6932115
  have htrace : WordTrace (prefixWord ++ tailWord_6932115) baseStart_6932115 baseEnd_6932115 := by
    simpa [prefixWord, tailWord_6932115, baseEnd_6932115] using wordTrace_append hprefix tailTrace_6932115
  have hstable : (prefixWord ++ tailWord_6932115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932115).length < 2 ^ (prefixWord ++ tailWord_6932115).sum := by decide
  have hdescent : baseEnd_6932115 < baseStart_6932115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932119 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 5]
def baseStart_6932119 : Nat := 118140960795 + 6932119 * 2 ^ 59
def prefixEnd_6932119 : Nat := 4983230072969 + 3 ^ 40 * 6932119 * 2
def baseEnd_6932119 : Nat := 395501000129429865136919

theorem tailTrace_6932119 : CollatzResearch.WordTrace tailWord_6932119 prefixEnd_6932119 395501000129429865136919 := by
  unfold tailWord_6932119
  simp only [CollatzResearch.WordTrace]
  refine ⟨252835151173124249514287411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168556767448749499676191607 252835151173124249514287411)
  ·
    refine ⟨379252726759686374271431117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252835151173124249514287411 379252726759686374271431117)
    ·
      refine ⟨142219772534882390351786669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379252726759686374271431117 142219772534882390351786669)
      ·
        refine ⟨53332414700580896381920001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142219772534882390351786669 53332414700580896381920001)
        ·
          refine ⟨39999311025435672286440001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53332414700580896381920001 39999311025435672286440001)
          ·
            refine ⟨29999483269076754214830001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39999311025435672286440001 29999483269076754214830001)
            ·
              refine ⟨22499612451807565661122501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29999483269076754214830001 22499612451807565661122501)
              ·
                refine ⟨4218677334713918561460469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22499612451807565661122501 4218677334713918561460469)
                ·
                  refine ⟨395501000129429865136919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4218677334713918561460469 395501000129429865136919)
                  ·
                    rfl

theorem cell23_6932119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 5].length) (baseStart_6932119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932119 prefixEnd_6932119 := by exact prefixLift 6932119
  have htrace : WordTrace (prefixWord ++ tailWord_6932119) baseStart_6932119 baseEnd_6932119 := by
    simpa [prefixWord, tailWord_6932119, baseEnd_6932119] using wordTrace_append hprefix tailTrace_6932119
  have hstable : (prefixWord ++ tailWord_6932119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932119).length < 2 ^ (prefixWord ++ tailWord_6932119).sum := by decide
  have hdescent : baseEnd_6932119 < baseStart_6932119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932129 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6932129 : Nat := 118140960795 + 6932129 * 2 ^ 59
def prefixEnd_6932129 : Nat := 4983230072969 + 3 ^ 40 * 6932129 * 2
def baseEnd_6932129 : Nat := 3559514135971413747107225

theorem tailTrace_6932129 : CollatzResearch.WordTrace tailWord_6932129 prefixEnd_6932129 3559514135971413747107225 := by
  unfold tailWord_6932129
  simp only [CollatzResearch.WordTrace]
  refine ⟨252835515903088021222151441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168557010602058680814767627 252835515903088021222151441)
  ·
    refine ⟨189626636927316015916613581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252835515903088021222151441 189626636927316015916613581)
    ·
      refine ⟨71109988847743505968730093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189626636927316015916613581 71109988847743505968730093)
      ·
        refine ⟨26666245817903814738273785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71109988847743505968730093 26666245817903814738273785)
        ·
          refine ⟨19999684363427861053705339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26666245817903814738273785 19999684363427861053705339)
          ·
            refine ⟨29999526545141791580558009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999684363427861053705339 29999526545141791580558009)
            ·
              refine ⟨22499644908856343685418507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29999526545141791580558009 22499644908856343685418507)
              ·
                refine ⟨33749467363284515528127761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22499644908856343685418507 33749467363284515528127761)
                ·
                  refine ⟨25312100522463386646095821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33749467363284515528127761 25312100522463386646095821)
                  ·
                    refine ⟨9492037695923769992285933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25312100522463386646095821 9492037695923769992285933)
                    ·
                      refine ⟨3559514135971413747107225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492037695923769992285933 3559514135971413747107225)
                      ·
                        rfl

theorem cell23_6932129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6932129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932129 prefixEnd_6932129 := by exact prefixLift 6932129
  have htrace : WordTrace (prefixWord ++ tailWord_6932129) baseStart_6932129 baseEnd_6932129 := by
    simpa [prefixWord, tailWord_6932129, baseEnd_6932129] using wordTrace_append hprefix tailTrace_6932129
  have hstable : (prefixWord ++ tailWord_6932129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932129).length < 2 ^ (prefixWord ++ tailWord_6932129).sum := by decide
  have hdescent : baseEnd_6932129 < baseStart_6932129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932130 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6932130 : Nat := 118140960795 + 6932130 * 2 ^ 59
def prefixEnd_6932130 : Nat := 4983230072969 + 3 ^ 40 * 6932130 * 2
def baseEnd_6932130 : Nat := 3559514649452068243194721

theorem tailTrace_6932130 : CollatzResearch.WordTrace tailWord_6932130 prefixEnd_6932130 3559514649452068243194721 := by
  unfold tailWord_6932130
  simp only [CollatzResearch.WordTrace]
  refine ⟨63208888094021099598234461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168557034917389598928625229 63208888094021099598234461)
  ·
    refine ⟨23703333035257912349337923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63208888094021099598234461 23703333035257912349337923)
    ·
      refine ⟨35554999552886868524006885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23703333035257912349337923 35554999552886868524006885)
      ·
        refine ⟨6666562416166287848251291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35554999552886868524006885 6666562416166287848251291)
        ·
          refine ⟨9999843624249431772376937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666562416166287848251291 9999843624249431772376937)
          ·
            refine ⟨7499882718187073829282703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9999843624249431772376937 7499882718187073829282703)
            ·
              refine ⟨11249824077280610743924055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499882718187073829282703 11249824077280610743924055)
              ·
                refine ⟨16874736115920916115886083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249824077280610743924055 16874736115920916115886083)
                ·
                  refine ⟨25312104173881374173829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16874736115920916115886083 25312104173881374173829125)
                  ·
                    refine ⟨4746019532602757657592961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25312104173881374173829125 4746019532602757657592961)
                    ·
                      refine ⟨3559514649452068243194721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746019532602757657592961 3559514649452068243194721)
                      ·
                        rfl

theorem cell23_6932130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6932130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932130 prefixEnd_6932130 := by exact prefixLift 6932130
  have htrace : WordTrace (prefixWord ++ tailWord_6932130) baseStart_6932130 baseEnd_6932130 := by
    simpa [prefixWord, tailWord_6932130, baseEnd_6932130] using wordTrace_append hprefix tailTrace_6932130
  have hstable : (prefixWord ++ tailWord_6932130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932130).length < 2 ^ (prefixWord ++ tailWord_6932130).sum := by decide
  have hdescent : baseEnd_6932130 < baseStart_6932130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932132 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6932132 : Nat := 118140960795 + 6932132 * 2 ^ 59
def prefixEnd_6932132 : Nat := 4983230072969 + 3 ^ 40 * 6932132 * 2
def baseEnd_6932132 : Nat := 1186505225471125745123237

theorem tailTrace_6932132 : CollatzResearch.WordTrace tailWord_6932132 prefixEnd_6932132 1186505225471125745123237 := by
  unfold tailWord_6932132
  simp only [CollatzResearch.WordTrace]
  refine ⟨126417812661038576367255325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168557083548051435156340433 126417812661038576367255325)
  ·
    refine ⟨47406679747889466137720747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126417812661038576367255325 47406679747889466137720747)
    ·
      refine ⟨71110019621834199206581121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47406679747889466137720747 71110019621834199206581121)
      ·
        refine ⟨53332514716375649404935841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71110019621834199206581121 53332514716375649404935841)
        ·
          refine ⟨39999386037281737053701881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53332514716375649404935841 39999386037281737053701881)
          ·
            refine ⟨29999539527961302790276411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39999386037281737053701881 29999539527961302790276411)
            ·
              refine ⟨44999309291941954185414617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29999539527961302790276411 44999309291941954185414617)
              ·
                refine ⟨33749481968956465639060963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44999309291941954185414617 33749481968956465639060963)
                ·
                  refine ⟨50624222953434698458591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33749481968956465639060963 50624222953434698458591445)
                  ·
                    refine ⟨1186505225471125745123237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50624222953434698458591445 1186505225471125745123237)
                    ·
                      rfl

theorem cell23_6932132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6932132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932132 prefixEnd_6932132 := by exact prefixLift 6932132
  have htrace : WordTrace (prefixWord ++ tailWord_6932132) baseStart_6932132 baseEnd_6932132 := by
    simpa [prefixWord, tailWord_6932132, baseEnd_6932132] using wordTrace_append hprefix tailTrace_6932132
  have hstable : (prefixWord ++ tailWord_6932132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932132).length < 2 ^ (prefixWord ++ tailWord_6932132).sum := by decide
  have hdescent : baseEnd_6932132 < baseStart_6932132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932152 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_6932152 : Nat := 118140960795 + 6932152 * 2 ^ 59
def prefixEnd_6932152 : Nat := 4983230072969 + 3 ^ 40 * 6932152 * 2
def baseEnd_6932152 : Nat := 3559525946026467157119619

theorem tailTrace_6932152 : CollatzResearch.WordTrace tailWord_6932152 prefixEnd_6932152 3559525946026467157119619 := by
  unfold tailWord_6932152
  simp only [CollatzResearch.WordTrace]
  refine ⟨126418177391002348075119355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168557569854669797433492473 126418177391002348075119355)
  ·
    refine ⟨189627266086503522112679033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126418177391002348075119355 189627266086503522112679033)
    ·
      refine ⟨142220449564877641584509275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189627266086503522112679033 142220449564877641584509275)
      ·
        refine ⟨213330674347316462376763913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142220449564877641584509275 213330674347316462376763913)
        ·
          refine ⟨159998005760487346782572935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213330674347316462376763913 159998005760487346782572935)
          ·
            refine ⟨239997008640731020173859403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159998005760487346782572935 239997008640731020173859403)
            ·
              refine ⟨359995512961096530260789105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239997008640731020173859403 359995512961096530260789105)
              ·
                refine ⟨269996634720822397695591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359995512961096530260789105 269996634720822397695591829)
                ·
                  refine ⟨12656092252538549891980867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269996634720822397695591829 12656092252538549891980867)
                  ·
                    refine ⟨18984138378807824837971301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12656092252538549891980867 18984138378807824837971301)
                    ·
                      refine ⟨3559525946026467157119619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18984138378807824837971301 3559525946026467157119619)
                      ·
                        rfl

theorem cell23_6932152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_6932152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932152 prefixEnd_6932152 := by exact prefixLift 6932152
  have htrace : WordTrace (prefixWord ++ tailWord_6932152) baseStart_6932152 baseEnd_6932152 := by
    simpa [prefixWord, tailWord_6932152, baseEnd_6932152] using wordTrace_append hprefix tailTrace_6932152
  have hstable : (prefixWord ++ tailWord_6932152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932152).length < 2 ^ (prefixWord ++ tailWord_6932152).sum := by decide
  have hdescent : baseEnd_6932152 < baseStart_6932152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932206 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_6932206 : Nat := 118140960795 + 6932206 * 2 ^ 59
def prefixEnd_6932206 : Nat := 4983230072969 + 3 ^ 40 * 6932206 * 2
def baseEnd_6932206 : Nat := 3559553673981809945844371

theorem tailTrace_6932206 : CollatzResearch.WordTrace tailWord_6932206 prefixEnd_6932206 3559553673981809945844371 := by
  unfold tailWord_6932206
  simp only [CollatzResearch.WordTrace]
  refine ⟨31604790540476132921588059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168558882882539375581802981 31604790540476132921588059)
  ·
    refine ⟨47407185810714199382382089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31604790540476132921588059 47407185810714199382382089)
    ·
      refine ⟨35555389358035649536786567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47407185810714199382382089 35555389358035649536786567)
      ·
        refine ⟨53333084037053474305179851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35555389358035649536786567 53333084037053474305179851)
        ·
          refine ⟨79999626055580211457769777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53333084037053474305179851 79999626055580211457769777)
          ·
            refine ⟨59999719541685158593327333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79999626055580211457769777 59999719541685158593327333)
            ·
              refine ⟨11249947414065967236248875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59999719541685158593327333 11249947414065967236248875)
              ·
                refine ⟨16874921121098950854373313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249947414065967236248875 16874921121098950854373313)
                ·
                  refine ⟨12656190840824213140779985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16874921121098950854373313 12656190840824213140779985)
                  ·
                    refine ⟨9492143130618159855584989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12656190840824213140779985 9492143130618159855584989)
                    ·
                      refine ⟨3559553673981809945844371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492143130618159855584989 3559553673981809945844371)
                      ·
                        rfl

theorem cell23_6932206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_6932206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932206 prefixEnd_6932206 := by exact prefixLift 6932206
  have htrace : WordTrace (prefixWord ++ tailWord_6932206) baseStart_6932206 baseEnd_6932206 := by
    simpa [prefixWord, tailWord_6932206, baseEnd_6932206] using wordTrace_append hprefix tailTrace_6932206
  have hstable : (prefixWord ++ tailWord_6932206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932206).length < 2 ^ (prefixWord ++ tailWord_6932206).sum := by decide
  have hdescent : baseEnd_6932206 < baseStart_6932206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932219 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 3]
def baseStart_6932219 : Nat := 118140960795 + 6932219 * 2 ^ 59
def prefixEnd_6932219 : Nat := 4983230072969 + 3 ^ 40 * 6932219 * 2
def baseEnd_6932219 : Nat := 3559560349230318394981811

theorem tailTrace_6932219 : CollatzResearch.WordTrace tailWord_6932219 prefixEnd_6932219 3559560349230318394981811 := by
  unfold tailWord_6932219
  simp only [CollatzResearch.WordTrace]
  refine ⟨252838798472761966592927711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168559198981841311061951807 252838798472761966592927711)
  ·
    refine ⟨379258197709142949889391567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252838798472761966592927711 379258197709142949889391567)
    ·
      refine ⟨568887296563714424834087351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379258197709142949889391567 568887296563714424834087351)
      ·
        refine ⟨853330944845571637251131027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568887296563714424834087351 853330944845571637251131027)
        ·
          refine ⟨1279996417268357455876696541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853330944845571637251131027 1279996417268357455876696541)
          ·
            refine ⟨479998656475634045953761203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1279996417268357455876696541 479998656475634045953761203)
            ·
              refine ⟨719997984713451068930641805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479998656475634045953761203 719997984713451068930641805)
              ·
                refine ⟨269999244267544150848990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719997984713451068930641805 269999244267544150848990677)
                ·
                  refine ⟨6328107287520566035523219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 269999244267544150848990677 6328107287520566035523219)
                  ·
                    refine ⟨9492160931280849053284829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328107287520566035523219 9492160931280849053284829)
                    ·
                      refine ⟨3559560349230318394981811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492160931280849053284829 3559560349230318394981811)
                      ·
                        rfl

theorem cell23_6932219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 3].length) (baseStart_6932219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932219 prefixEnd_6932219 := by exact prefixLift 6932219
  have htrace : WordTrace (prefixWord ++ tailWord_6932219) baseStart_6932219 baseEnd_6932219 := by
    simpa [prefixWord, tailWord_6932219, baseEnd_6932219] using wordTrace_append hprefix tailTrace_6932219
  have hstable : (prefixWord ++ tailWord_6932219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932219).length < 2 ^ (prefixWord ++ tailWord_6932219).sum := by decide
  have hdescent : baseEnd_6932219 < baseStart_6932219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932226 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_6932226 : Nat := 118140960795 + 6932226 * 2 ^ 59
def prefixEnd_6932226 : Nat := 4983230072969 + 3 ^ 40 * 6932226 * 2
def baseEnd_6932226 : Nat := 395507104843877763066031

theorem tailTrace_6932226 : CollatzResearch.WordTrace tailWord_6932226 prefixEnd_6932226 395507104843877763066031 := by
  unfold tailWord_6932226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63209763445934151697108133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168559369189157737858955021 63209763445934151697108133)
  ·
    refine ⟨11851830646112653443207775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63209763445934151697108133 11851830646112653443207775)
    ·
      refine ⟨17777745969168980164811663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11851830646112653443207775 17777745969168980164811663)
      ·
        refine ⟨26666618953753470247217495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17777745969168980164811663 26666618953753470247217495)
        ·
          refine ⟨39999928430630205370826243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26666618953753470247217495 39999928430630205370826243)
          ·
            refine ⟨59999892645945308056239365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39999928430630205370826243 59999892645945308056239365)
            ·
              refine ⟨11249979871114745260544881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59999892645945308056239365 11249979871114745260544881)
              ·
                refine ⟨8437484903336058945408661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11249979871114745260544881 8437484903336058945408661)
                ·
                  refine ⟨395507104843877763066031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8437484903336058945408661 395507104843877763066031)
                  ·
                    rfl

theorem cell23_6932226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_6932226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932226 prefixEnd_6932226 := by exact prefixLift 6932226
  have htrace : WordTrace (prefixWord ++ tailWord_6932226) baseStart_6932226 baseEnd_6932226 := by
    simpa [prefixWord, tailWord_6932226, baseEnd_6932226] using wordTrace_append hprefix tailTrace_6932226
  have hstable : (prefixWord ++ tailWord_6932226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932226).length < 2 ^ (prefixWord ++ tailWord_6932226).sum := by decide
  have hdescent : baseEnd_6932226 < baseStart_6932226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932229 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_6932229 : Nat := 118140960795 + 6932229 * 2 ^ 59
def prefixEnd_6932229 : Nat := 4983230072969 + 3 ^ 40 * 6932229 * 2
def baseEnd_6932229 : Nat := 3559565484036863355856765

theorem tailTrace_6932229 : CollatzResearch.WordTrace tailWord_6932229 prefixEnd_6932229 3559565484036863355856765 := by
  unfold tailWord_6932229
  simp only [CollatzResearch.WordTrace]
  refine ⟨252839163202725738300791741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168559442135150492200527827 252839163202725738300791741)
  ·
    refine ⟨94814686201022151862796903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252839163202725738300791741 94814686201022151862796903)
    ·
      refine ⟨142222029301533227794195355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94814686201022151862796903 142222029301533227794195355)
      ·
        refine ⟨213333043952299841691293033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142222029301533227794195355 213333043952299841691293033)
        ·
          refine ⟨159999782964224881268469775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213333043952299841691293033 159999782964224881268469775)
          ·
            refine ⟨239999674446337321902704663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159999782964224881268469775 239999674446337321902704663)
            ·
              refine ⟨359999511669505982854056995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239999674446337321902704663 359999511669505982854056995)
              ·
                refine ⟨539999267504258974281085493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359999511669505982854056995 539999267504258974281085493)
                ·
                  refine ⟨50624931328524278838851765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539999267504258974281085493 50624931328524278838851765)
                  ·
                    refine ⟨4746087312049151141142353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50624931328524278838851765 4746087312049151141142353)
                    ·
                      refine ⟨3559565484036863355856765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746087312049151141142353 3559565484036863355856765)
                      ·
                        rfl

theorem cell23_6932229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_6932229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932229 prefixEnd_6932229 := by exact prefixLift 6932229
  have htrace : WordTrace (prefixWord ++ tailWord_6932229) baseStart_6932229 baseEnd_6932229 := by
    simpa [prefixWord, tailWord_6932229, baseEnd_6932229] using wordTrace_append hprefix tailTrace_6932229
  have hstable : (prefixWord ++ tailWord_6932229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932229).length < 2 ^ (prefixWord ++ tailWord_6932229).sum := by decide
  have hdescent : baseEnd_6932229 < baseStart_6932229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932259 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6932259 : Nat := 118140960795 + 6932259 * 2 ^ 59
def prefixEnd_6932259 : Nat := 4983230072969 + 3 ^ 40 * 6932259 * 2
def baseEnd_6932259 : Nat := 3559580888456498238481627

theorem tailTrace_6932259 : CollatzResearch.WordTrace tailWord_6932259 prefixEnd_6932259 3559580888456498238481627 := by
  unfold tailWord_6932259
  simp only [CollatzResearch.WordTrace]
  refine ⟨252840257392617053424383831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168560171595078035616255887 252840257392617053424383831)
  ·
    refine ⟨379260386088925580136575747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252840257392617053424383831 379260386088925580136575747)
    ·
      refine ⟨568890579133388370204863621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379260386088925580136575747 568890579133388370204863621)
      ·
        refine ⟨106666983587510319413411929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 568890579133388370204863621 106666983587510319413411929)
        ·
          refine ⟨80000237690632739560058947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106666983587510319413411929 80000237690632739560058947)
          ·
            refine ⟨120000356535949109340088421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80000237690632739560058947 120000356535949109340088421)
            ·
              refine ⟨22500066850490458001266579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120000356535949109340088421 22500066850490458001266579)
              ·
                refine ⟨33750100275735687001899869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500066850490458001266579 33750100275735687001899869)
                ·
                  refine ⟨12656287603400882625712451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33750100275735687001899869 12656287603400882625712451)
                  ·
                    refine ⟨18984431405101323938568677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12656287603400882625712451 18984431405101323938568677)
                    ·
                      refine ⟨3559580888456498238481627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18984431405101323938568677 3559580888456498238481627)
                      ·
                        rfl

theorem cell23_6932259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6932259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932259 prefixEnd_6932259 := by exact prefixLift 6932259
  have htrace : WordTrace (prefixWord ++ tailWord_6932259) baseStart_6932259 baseEnd_6932259 := by
    simpa [prefixWord, tailWord_6932259, baseEnd_6932259] using wordTrace_append hprefix tailTrace_6932259
  have hstable : (prefixWord ++ tailWord_6932259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932259).length < 2 ^ (prefixWord ++ tailWord_6932259).sum := by decide
  have hdescent : baseEnd_6932259 < baseStart_6932259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932272 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_6932272 : Nat := 118140960795 + 6932272 * 2 ^ 59
def prefixEnd_6932272 : Nat := 4983230072969 + 3 ^ 40 * 6932272 * 2
def baseEnd_6932272 : Nat := 3559587563705006687619067

theorem tailTrace_6932272 : CollatzResearch.WordTrace tailWord_6932272 prefixEnd_6932272 3559587563705006687619067 := by
  unfold tailWord_6932272
  simp only [CollatzResearch.WordTrace]
  refine ⟨126420365770784978322303535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168560487694379971096404713 126420365770784978322303535)
  ·
    refine ⟨189630548656177467483455303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126420365770784978322303535 189630548656177467483455303)
    ·
      refine ⟨284445822984266201225182955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189630548656177467483455303 284445822984266201225182955)
      ·
        refine ⟨426668734476399301837774433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284445822984266201225182955 426668734476399301837774433)
        ·
          refine ⟨320001550857299476378330825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426668734476399301837774433 320001550857299476378330825)
          ·
            refine ⟨240001163142974607283748119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320001550857299476378330825 240001163142974607283748119)
            ·
              refine ⟨360001744714461910925622179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240001163142974607283748119 360001744714461910925622179)
              ·
                refine ⟨540002617071692866388433269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360001744714461910925622179 540002617071692866388433269)
                ·
                  refine ⟨50625245350471206223915619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540002617071692866388433269 50625245350471206223915619)
                  ·
                    refine ⟨75937868025706809335873429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50625245350471206223915619 75937868025706809335873429)
                    ·
                      refine ⟨3559587563705006687619067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75937868025706809335873429 3559587563705006687619067)
                      ·
                        rfl

theorem cell23_6932272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_6932272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932272 prefixEnd_6932272 := by exact prefixLift 6932272
  have htrace : WordTrace (prefixWord ++ tailWord_6932272) baseStart_6932272 baseEnd_6932272 := by
    simpa [prefixWord, tailWord_6932272, baseEnd_6932272] using wordTrace_append hprefix tailTrace_6932272
  have hstable : (prefixWord ++ tailWord_6932272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932272).length < 2 ^ (prefixWord ++ tailWord_6932272).sum := by decide
  have hdescent : baseEnd_6932272 < baseStart_6932272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932273 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_6932273 : Nat := 118140960795 + 6932273 * 2 ^ 59
def prefixEnd_6932273 : Nat := 4983230072969 + 3 ^ 40 * 6932273 * 2
def baseEnd_6932273 : Nat := 1186529359061887061235521

theorem tailTrace_6932273 : CollatzResearch.WordTrace tailWord_6932273 prefixEnd_6932273 1186529359061887061235521 := by
  unfold tailWord_6932273
  simp only [CollatzResearch.WordTrace]
  refine ⟨252840768014566333815393473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168560512009710889210262315 252840768014566333815393473)
  ·
    refine ⟨189630576010924750361545105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252840768014566333815393473 189630576010924750361545105)
    ·
      refine ⟨142222932008193562771158829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189630576010924750361545105 142222932008193562771158829)
      ·
        refine ⟨53333599503072586039184561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142222932008193562771158829 53333599503072586039184561)
        ·
          refine ⟨40000199627304439529388421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53333599503072586039184561 40000199627304439529388421)
          ·
            refine ⟨7500037430119582411760329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40000199627304439529388421 7500037430119582411760329)
            ·
              refine ⟨5625028072589686808820247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500037430119582411760329 5625028072589686808820247)
              ·
                refine ⟨8437542108884530213230371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625028072589686808820247 8437542108884530213230371)
                ·
                  refine ⟨12656313163326795319845557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437542108884530213230371 12656313163326795319845557)
                  ·
                    refine ⟨1186529359061887061235521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12656313163326795319845557 1186529359061887061235521)
                    ·
                      rfl

theorem cell23_6932273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_6932273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932273 prefixEnd_6932273 := by exact prefixLift 6932273
  have htrace : WordTrace (prefixWord ++ tailWord_6932273) baseStart_6932273 baseEnd_6932273 := by
    simpa [prefixWord, tailWord_6932273, baseEnd_6932273] using wordTrace_append hprefix tailTrace_6932273
  have hstable : (prefixWord ++ tailWord_6932273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932273).length < 2 ^ (prefixWord ++ tailWord_6932273).sum := by decide
  have hdescent : baseEnd_6932273 < baseStart_6932273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932279 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_6932279 : Nat := 118140960795 + 6932279 * 2 ^ 59
def prefixEnd_6932279 : Nat := 4983230072969 + 3 ^ 40 * 6932279 * 2
def baseEnd_6932279 : Nat := 3559591158069588160231535

theorem tailTrace_6932279 : CollatzResearch.WordTrace tailWord_6932279 prefixEnd_6932279 3559591158069588160231535 := by
  unfold tailWord_6932279
  simp only [CollatzResearch.WordTrace]
  refine ⟨252840986852544596840111891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168560657901696397893407927 252840986852544596840111891)
  ·
    refine ⟨379261480278816895260167837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252840986852544596840111891 379261480278816895260167837)
    ·
      refine ⟨142223055104556335722562939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379261480278816895260167837 142223055104556335722562939)
      ·
        refine ⟨213334582656834503583844409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142223055104556335722562939 213334582656834503583844409)
        ·
          refine ⟨160000936992625877687883307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213334582656834503583844409 160000936992625877687883307)
          ·
            refine ⟨240001405488938816531824961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160000936992625877687883307 240001405488938816531824961)
            ·
              refine ⟨180001054116704112398868721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240001405488938816531824961 180001054116704112398868721)
              ·
                refine ⟨135000790587528084299151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180001054116704112398868721 135000790587528084299151541)
                ·
                  refine ⟨12656324117580757903045457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135000790587528084299151541 12656324117580757903045457)
                  ·
                    refine ⟨9492243088185568427284093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12656324117580757903045457 9492243088185568427284093)
                    ·
                      refine ⟨3559591158069588160231535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492243088185568427284093 3559591158069588160231535)
                      ·
                        rfl

theorem cell23_6932279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_6932279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932279 prefixEnd_6932279 := by exact prefixLift 6932279
  have htrace : WordTrace (prefixWord ++ tailWord_6932279) baseStart_6932279 baseEnd_6932279 := by
    simpa [prefixWord, tailWord_6932279, baseEnd_6932279] using wordTrace_append hprefix tailTrace_6932279
  have hstable : (prefixWord ++ tailWord_6932279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932279).length < 2 ^ (prefixWord ++ tailWord_6932279).sum := by decide
  have hdescent : baseEnd_6932279 < baseStart_6932279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932293 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_6932293 : Nat := 118140960795 + 6932293 * 2 ^ 59
def prefixEnd_6932293 : Nat := 4983230072969 + 3 ^ 40 * 6932293 * 2
def baseEnd_6932293 : Nat := 3559598346798751105456471

theorem tailTrace_6932293 : CollatzResearch.WordTrace tailWord_6932293 prefixEnd_6932293 3559598346798751105456471 := by
  unfold tailWord_6932293
  simp only [CollatzResearch.WordTrace]
  refine ⟨252841497474493877231121533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168560998316329251487414355 252841497474493877231121533)
  ·
    refine ⟨94815561552935203961670575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252841497474493877231121533 94815561552935203961670575)
    ·
      refine ⟨142223342329402805942505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94815561552935203961670575 142223342329402805942505863)
      ·
        refine ⟨213335013494104208913758795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142223342329402805942505863 213335013494104208913758795)
        ·
          refine ⟨320002520241156313370638193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213335013494104208913758795 320002520241156313370638193)
          ·
            refine ⟨240001890180867235027978645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320002520241156313370638193 240001890180867235027978645)
            ·
              refine ⟨11250088602228151641936499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240001890180867235027978645 11250088602228151641936499)
              ·
                refine ⟨16875132903342227462904749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11250088602228151641936499 16875132903342227462904749)
                ·
                  refine ⟨6328174838753335298589281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16875132903342227462904749 6328174838753335298589281)
                  ·
                    refine ⟨4746131129065001473941961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6328174838753335298589281 4746131129065001473941961)
                    ·
                      refine ⟨3559598346798751105456471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746131129065001473941961 3559598346798751105456471)
                      ·
                        rfl

theorem cell23_6932293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_6932293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932293 prefixEnd_6932293 := by exact prefixLift 6932293
  have htrace : WordTrace (prefixWord ++ tailWord_6932293) baseStart_6932293 baseEnd_6932293 := by
    simpa [prefixWord, tailWord_6932293, baseEnd_6932293] using wordTrace_append hprefix tailTrace_6932293
  have hstable : (prefixWord ++ tailWord_6932293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932293).length < 2 ^ (prefixWord ++ tailWord_6932293).sum := by decide
  have hdescent : baseEnd_6932293 < baseStart_6932293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932306 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_6932306 : Nat := 118140960795 + 6932306 * 2 ^ 59
def prefixEnd_6932306 : Nat := 4983230072969 + 3 ^ 40 * 6932306 * 2
def baseEnd_6932306 : Nat := 3559605022047259554593911

theorem tailTrace_6932306 : CollatzResearch.WordTrace tailWord_6932306 prefixEnd_6932306 3559605022047259554593911 := by
  unfold tailWord_6932306
  simp only [CollatzResearch.WordTrace]
  refine ⟨63210492905861695112836193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168561314415631186967563181 63210492905861695112836193)
  ·
    refine ⟨47407869679396271334627145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63210492905861695112836193 47407869679396271334627145)
    ·
      refine ⟨35555902259547203500970359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47407869679396271334627145 35555902259547203500970359)
      ·
        refine ⟨53333853389320805251455539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35555902259547203500970359 53333853389320805251455539)
        ·
          refine ⟨80000780083981207877183309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53333853389320805251455539 80000780083981207877183309)
          ·
            refine ⟨30000292531492952953943741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80000780083981207877183309 30000292531492952953943741)
            ·
              refine ⟨11250109699309857357728903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30000292531492952953943741 11250109699309857357728903)
              ·
                refine ⟨16875164548964786036593355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11250109699309857357728903 16875164548964786036593355)
                ·
                  refine ⟨25312746823447179054890033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16875164548964786036593355 25312746823447179054890033)
                  ·
                    refine ⟨18984560117585384291167525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25312746823447179054890033 18984560117585384291167525)
                    ·
                      refine ⟨3559605022047259554593911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18984560117585384291167525 3559605022047259554593911)
                      ·
                        rfl

theorem cell23_6932306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_6932306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932306 prefixEnd_6932306 := by exact prefixLift 6932306
  have htrace : WordTrace (prefixWord ++ tailWord_6932306) baseStart_6932306 baseEnd_6932306 := by
    simpa [prefixWord, tailWord_6932306, baseEnd_6932306] using wordTrace_append hprefix tailTrace_6932306
  have hstable : (prefixWord ++ tailWord_6932306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932306).length < 2 ^ (prefixWord ++ tailWord_6932306).sum := by decide
  have hdescent : baseEnd_6932306 < baseStart_6932306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932316 : List Nat := [2, 2, 4, 2, 2, 1, 1, 9]
def baseStart_6932316 : Nat := 118140960795 + 6932316 * 2 ^ 59
def prefixEnd_6932316 : Nat := 4983230072969 + 3 ^ 40 * 6932316 * 2
def baseEnd_6932316 : Nat := 131837413216807574646995

theorem tailTrace_6932316 : CollatzResearch.WordTrace tailWord_6932316 prefixEnd_6932316 131837413216807574646995 := by
  unfold tailWord_6932316
  simp only [CollatzResearch.WordTrace]
  refine ⟨126421168176705276079604401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168561557568940368106139201 126421168176705276079604401)
  ·
    refine ⟨94815876132528957059703301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126421168176705276079604401 94815876132528957059703301)
    ·
      refine ⟨17777976774849179448694369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94815876132528957059703301 17777976774849179448694369)
      ·
        refine ⟨13333482581136884586520777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17777976774849179448694369 13333482581136884586520777)
        ·
          refine ⟨10000111935852663439890583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13333482581136884586520777 10000111935852663439890583)
          ·
            refine ⟨15000167903778995159835875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000111935852663439890583 15000167903778995159835875)
            ·
              refine ⟨22500251855668492739753813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15000167903778995159835875 22500251855668492739753813)
              ·
                refine ⟨131837413216807574646995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22500251855668492739753813 131837413216807574646995)
                ·
                  rfl

theorem cell23_6932316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 9].length) (baseStart_6932316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932316 prefixEnd_6932316 := by exact prefixLift 6932316
  have htrace : WordTrace (prefixWord ++ tailWord_6932316) baseStart_6932316 baseEnd_6932316 := by
    simpa [prefixWord, tailWord_6932316, baseEnd_6932316] using wordTrace_append hprefix tailTrace_6932316
  have hstable : (prefixWord ++ tailWord_6932316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932316).length < 2 ^ (prefixWord ++ tailWord_6932316).sum := by decide
  have hdescent : baseEnd_6932316 < baseStart_6932316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932336 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2]
def baseStart_6932336 : Nat := 118140960795 + 6932336 * 2 ^ 59
def prefixEnd_6932336 : Nat := 4983230072969 + 3 ^ 40 * 6932336 * 2
def baseEnd_6932336 : Nat := 3559620426466894437218773

theorem tailTrace_6932336 : CollatzResearch.WordTrace tailWord_6932336 prefixEnd_6932336 3559620426466894437218773 := by
  unfold tailWord_6932336
  simp only [CollatzResearch.WordTrace]
  refine ⟨126421532906669047787468431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168562043875558730383291241 126421532906669047787468431)
  ·
    refine ⟨189632299360003571681202647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126421532906669047787468431 189632299360003571681202647)
    ·
      refine ⟨284448449040005357521803971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189632299360003571681202647 284448449040005357521803971)
      ·
        refine ⟨426672673560008036282705957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284448449040005357521803971 426672673560008036282705957)
        ·
          refine ⟨80001126292501506803007367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426672673560008036282705957 80001126292501506803007367)
          ·
            refine ⟨120001689438752260204511051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80001126292501506803007367 120001689438752260204511051)
            ·
              refine ⟨180002534158128390306766577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120001689438752260204511051 180002534158128390306766577)
              ·
                refine ⟨135001900618596292730074933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180002534158128390306766577 135001900618596292730074933)
                ·
                  refine ⟨12656428182993402443444525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135001900618596292730074933 12656428182993402443444525)
                  ·
                    refine ⟨4746160568622525916291697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12656428182993402443444525 4746160568622525916291697)
                    ·
                      refine ⟨3559620426466894437218773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746160568622525916291697 3559620426466894437218773)
                      ·
                        rfl

theorem cell23_6932336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2].length) (baseStart_6932336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932336 prefixEnd_6932336 := by exact prefixLift 6932336
  have htrace : WordTrace (prefixWord ++ tailWord_6932336) baseStart_6932336 baseEnd_6932336 := by
    simpa [prefixWord, tailWord_6932336, baseEnd_6932336] using wordTrace_append hprefix tailTrace_6932336
  have hstable : (prefixWord ++ tailWord_6932336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932336).length < 2 ^ (prefixWord ++ tailWord_6932336).sum := by decide
  have hdescent : baseEnd_6932336 < baseStart_6932336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932349 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_6932349 : Nat := 118140960795 + 6932349 * 2 ^ 59
def prefixEnd_6932349 : Nat := 4983230072969 + 3 ^ 40 * 6932349 * 2
def baseEnd_6932349 : Nat := 3559627101715402886356213

theorem tailTrace_6932349 : CollatzResearch.WordTrace tailWord_6932349 prefixEnd_6932349 3559627101715402886356213 := by
  unfold tailWord_6932349
  simp only [CollatzResearch.WordTrace]
  refine ⟨252843539962290998795160101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168562359974860665863440067 252843539962290998795160101)
  ·
    refine ⟨47408163742929562274092519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252843539962290998795160101 47408163742929562274092519)
    ·
      refine ⟨71112245614394343411138779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47408163742929562274092519 71112245614394343411138779)
      ·
        refine ⟨106668368421591515116708169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71112245614394343411138779 106668368421591515116708169)
        ·
          refine ⟨80001276316193636337531127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106668368421591515116708169 80001276316193636337531127)
          ·
            refine ⟨120001914474290454506296691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80001276316193636337531127 120001914474290454506296691)
            ·
              refine ⟨180002871711435681759445037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120001914474290454506296691 180002871711435681759445037)
              ·
                refine ⟨67501076891788380659791889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180002871711435681759445037 67501076891788380659791889)
                ·
                  refine ⟨50625807668841285494843917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67501076891788380659791889 50625807668841285494843917)
                  ·
                    refine ⟨18984677875815482060566469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50625807668841285494843917 18984677875815482060566469)
                    ·
                      refine ⟨3559627101715402886356213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18984677875815482060566469 3559627101715402886356213)
                      ·
                        rfl

theorem cell23_6932349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_6932349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932349 prefixEnd_6932349 := by exact prefixLift 6932349
  have htrace : WordTrace (prefixWord ++ tailWord_6932349) baseStart_6932349 baseEnd_6932349 := by
    simpa [prefixWord, tailWord_6932349, baseEnd_6932349] using wordTrace_append hprefix tailTrace_6932349
  have hstable : (prefixWord ++ tailWord_6932349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932349).length < 2 ^ (prefixWord ++ tailWord_6932349).sum := by decide
  have hdescent : baseEnd_6932349 < baseStart_6932349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932360 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6932360 : Nat := 118140960795 + 6932360 * 2 ^ 59
def prefixEnd_6932360 : Nat := 4983230072969 + 3 ^ 40 * 6932360 * 2
def baseEnd_6932360 : Nat := 3559632750002602343318663

theorem tailTrace_6932360 : CollatzResearch.WordTrace tailWord_6932360 prefixEnd_6932360 3559632750002602343318663 := by
  unfold tailWord_6932360
  simp only [CollatzResearch.WordTrace]
  refine ⟨126421970582625573836905267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168562627443500765115873689 126421970582625573836905267)
  ·
    refine ⟨189632955873938360755357901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126421970582625573836905267 189632955873938360755357901)
    ·
      refine ⟨71112358452726885283259213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189632955873938360755357901 71112358452726885283259213)
      ·
        refine ⟨26667134419772581981222205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71112358452726885283259213 26667134419772581981222205)
        ·
          refine ⟨10000175407414718242958327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26667134419772581981222205 10000175407414718242958327)
          ·
            refine ⟨15000263111122077364437491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000175407414718242958327 15000263111122077364437491)
            ·
              refine ⟨22500394666683116046656237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15000263111122077364437491 22500394666683116046656237)
              ·
                refine ⟨8437648000006168517496089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22500394666683116046656237 8437648000006168517496089)
                ·
                  refine ⟨6328236000004626388122067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8437648000006168517496089 6328236000004626388122067)
                  ·
                    refine ⟨9492354000006939582183101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328236000004626388122067 9492354000006939582183101)
                    ·
                      refine ⟨3559632750002602343318663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492354000006939582183101 3559632750002602343318663)
                      ·
                        rfl

theorem cell23_6932360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6932360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932360 prefixEnd_6932360 := by exact prefixLift 6932360
  have htrace : WordTrace (prefixWord ++ tailWord_6932360) baseStart_6932360 baseEnd_6932360 := by
    simpa [prefixWord, tailWord_6932360, baseEnd_6932360] using wordTrace_append hprefix tailTrace_6932360
  have hstable : (prefixWord ++ tailWord_6932360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932360).length < 2 ^ (prefixWord ++ tailWord_6932360).sum := by decide
  have hdescent : baseEnd_6932360 < baseStart_6932360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932369 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_6932369 : Nat := 118140960795 + 6932369 * 2 ^ 59
def prefixEnd_6932369 : Nat := 4983230072969 + 3 ^ 40 * 6932369 * 2
def baseEnd_6932369 : Nat := 3559637371328492808106121

theorem tailTrace_6932369 : CollatzResearch.WordTrace tailWord_6932369 prefixEnd_6932369 3559637371328492808106121 := by
  unfold tailWord_6932369
  simp only [CollatzResearch.WordTrace]
  refine ⟨252844269422218542210888161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168562846281479028140592107 252844269422218542210888161)
  ·
    refine ⟨189633202066663906658166121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252844269422218542210888161 189633202066663906658166121)
    ·
      refine ⟨142224901549997929993624591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189633202066663906658166121 142224901549997929993624591)
      ·
        refine ⟨213337352324996894990436887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142224901549997929993624591 213337352324996894990436887)
        ·
          refine ⟨320006028487495342485655331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213337352324996894990436887 320006028487495342485655331)
          ·
            refine ⟨480009042731243013728482997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320006028487495342485655331 480009042731243013728482997)
            ·
              refine ⟨45000847756054032537045281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480009042731243013728482997 45000847756054032537045281)
              ·
                refine ⟨33750635817040524402783961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45000847756054032537045281 33750635817040524402783961)
                ·
                  refine ⟨25312976862780393302087971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33750635817040524402783961 25312976862780393302087971)
                  ·
                    refine ⟨37969465294170589953131957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25312976862780393302087971 37969465294170589953131957)
                    ·
                      refine ⟨3559637371328492808106121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37969465294170589953131957 3559637371328492808106121)
                      ·
                        rfl

theorem cell23_6932369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_6932369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932369 prefixEnd_6932369 := by exact prefixLift 6932369
  have htrace : WordTrace (prefixWord ++ tailWord_6932369) baseStart_6932369 baseEnd_6932369 := by
    simpa [prefixWord, tailWord_6932369, baseEnd_6932369] using wordTrace_append hprefix tailTrace_6932369
  have hstable : (prefixWord ++ tailWord_6932369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932369).length < 2 ^ (prefixWord ++ tailWord_6932369).sum := by decide
  have hdescent : baseEnd_6932369 < baseStart_6932369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932370 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6932370 : Nat := 118140960795 + 6932370 * 2 ^ 59
def prefixEnd_6932370 : Nat := 4983230072969 + 3 ^ 40 * 6932370 * 2
def baseEnd_6932370 : Nat := 3559637884809147304193617

theorem tailTrace_6932370 : CollatzResearch.WordTrace tailWord_6932370 prefixEnd_6932370 3559637884809147304193617 := by
  unfold tailWord_6932370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211076473803729845418641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168562870596809946254449709 63211076473803729845418641)
  ·
    refine ⟨47408307355352797384063981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63211076473803729845418641 47408307355352797384063981)
    ·
      refine ⟨17778115258257299019023993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47408307355352797384063981 17778115258257299019023993)
      ·
        refine ⟨13333586443692974264267995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17778115258257299019023993 13333586443692974264267995)
        ·
          refine ⟨20000379665539461396401993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13333586443692974264267995 20000379665539461396401993)
          ·
            refine ⟨15000284749154596047301495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20000379665539461396401993 15000284749154596047301495)
            ·
              refine ⟨22500427123731894070952243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15000284749154596047301495 22500427123731894070952243)
              ·
                refine ⟨33750640685597841106428365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500427123731894070952243 33750640685597841106428365)
                ·
                  refine ⟨12656490257099190414910637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33750640685597841106428365 12656490257099190414910637)
                  ·
                    refine ⟨4746183846412196405591489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12656490257099190414910637 4746183846412196405591489)
                    ·
                      refine ⟨3559637884809147304193617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746183846412196405591489 3559637884809147304193617)
                      ·
                        rfl

theorem cell23_6932370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6932370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932370 prefixEnd_6932370 := by exact prefixLift 6932370
  have htrace : WordTrace (prefixWord ++ tailWord_6932370) baseStart_6932370 baseEnd_6932370 := by
    simpa [prefixWord, tailWord_6932370, baseEnd_6932370] using wordTrace_append hprefix tailTrace_6932370
  have hstable : (prefixWord ++ tailWord_6932370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932370).length < 2 ^ (prefixWord ++ tailWord_6932370).sum := by decide
  have hdescent : baseEnd_6932370 < baseStart_6932370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932416 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_6932416 : Nat := 118140960795 + 6932416 * 2 ^ 59
def prefixEnd_6932416 : Nat := 4983230072969 + 3 ^ 40 * 6932416 * 2
def baseEnd_6932416 : Nat := 3559661504919254124218405

theorem tailTrace_6932416 : CollatzResearch.WordTrace tailWord_6932416 prefixEnd_6932416 3559661504919254124218405 := by
  unfold tailWord_6932416
  simp only [CollatzResearch.WordTrace]
  refine ⟨126422991826524134618924551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168563989102032179491899401 126422991826524134618924551)
  ·
    refine ⟨189634487739786201928386827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126422991826524134618924551 189634487739786201928386827)
    ·
      refine ⟨284451731609679302892580241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189634487739786201928386827 284451731609679302892580241)
      ·
        refine ⟨213338798707259477169435181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284451731609679302892580241 213338798707259477169435181)
        ·
          refine ⟨80002049515222303938538193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213338798707259477169435181 80002049515222303938538193)
          ·
            refine ⟨60001537136416727953903645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80002049515222303938538193 60001537136416727953903645)
            ·
              refine ⟨22500576426156272982713867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60001537136416727953903645 22500576426156272982713867)
              ·
                refine ⟨33750864639234409474070801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500576426156272982713867 33750864639234409474070801)
                ·
                  refine ⟨25313148479425807105553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33750864639234409474070801 25313148479425807105553101)
                  ·
                    refine ⟨9492430679784677664582413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25313148479425807105553101 9492430679784677664582413)
                    ·
                      refine ⟨3559661504919254124218405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492430679784677664582413 3559661504919254124218405)
                      ·
                        rfl

theorem cell23_6932416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_6932416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932416 prefixEnd_6932416 := by exact prefixLift 6932416
  have htrace : WordTrace (prefixWord ++ tailWord_6932416) baseStart_6932416 baseEnd_6932416 := by
    simpa [prefixWord, tailWord_6932416, baseEnd_6932416] using wordTrace_append hprefix tailTrace_6932416
  have hstable : (prefixWord ++ tailWord_6932416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932416).length < 2 ^ (prefixWord ++ tailWord_6932416).sum := by decide
  have hdescent : baseEnd_6932416 < baseStart_6932416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932436 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6932436 : Nat := 118140960795 + 6932436 * 2 ^ 59
def prefixEnd_6932436 : Nat := 4983230072969 + 3 ^ 40 * 6932436 * 2
def baseEnd_6932436 : Nat := 1186557258177448015322771

theorem tailTrace_6932436 : CollatzResearch.WordTrace tailWord_6932436 prefixEnd_6932436 1186557258177448015322771 := by
  unfold tailWord_6932436
  simp only [CollatzResearch.WordTrace]
  refine ⟨126423356556487906326788581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168564475408650541769051441 126423356556487906326788581)
  ·
    refine ⟨23704379354341482436272859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126423356556487906326788581 23704379354341482436272859)
    ·
      refine ⟨35556569031512223654409289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23704379354341482436272859 35556569031512223654409289)
      ·
        refine ⟨26667426773634167740806967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35556569031512223654409289 26667426773634167740806967)
        ·
          refine ⟨40001140160451251611210451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26667426773634167740806967 40001140160451251611210451)
          ·
            refine ⟨60001710240676877416815677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40001140160451251611210451 60001710240676877416815677)
            ·
              refine ⟨22500641340253829031305879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60001710240676877416815677 22500641340253829031305879)
              ·
                refine ⟨33750962010380743546958819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500641340253829031305879 33750962010380743546958819)
                ·
                  refine ⟨50626443015571115320438229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33750962010380743546958819 50626443015571115320438229)
                  ·
                    refine ⟨1186557258177448015322771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50626443015571115320438229 1186557258177448015322771)
                    ·
                      rfl

theorem cell23_6932436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6932436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932436 prefixEnd_6932436 := by exact prefixLift 6932436
  have htrace : WordTrace (prefixWord ++ tailWord_6932436) baseStart_6932436 baseEnd_6932436 := by
    simpa [prefixWord, tailWord_6932436, baseEnd_6932436] using wordTrace_append hprefix tailTrace_6932436
  have hstable : (prefixWord ++ tailWord_6932436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932436).length < 2 ^ (prefixWord ++ tailWord_6932436).sum := by decide
  have hdescent : baseEnd_6932436 < baseStart_6932436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932456 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6932456 : Nat := 118140960795 + 6932456 * 2 ^ 59
def prefixEnd_6932456 : Nat := 4983230072969 + 3 ^ 40 * 6932456 * 2
def baseEnd_6932456 : Nat := 3559682044145433967718221

theorem tailTrace_6932456 : CollatzResearch.WordTrace tailWord_6932456 prefixEnd_6932456 3559682044145433967718221 := by
  unfold tailWord_6932456
  simp only [CollatzResearch.WordTrace]
  refine ⟨126423721286451678034652611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168564961715268904046203481 126423721286451678034652611)
  ·
    refine ⟨189635581929677517051978917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126423721286451678034652611 189635581929677517051978917)
    ·
      refine ⟨35556671611814534447246047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189635581929677517051978917 35556671611814534447246047)
      ·
        refine ⟨53335007417721801670869071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35556671611814534447246047 53335007417721801670869071)
        ·
          refine ⟨80002511126582702506303607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53335007417721801670869071 80002511126582702506303607)
          ·
            refine ⟨120003766689874053759455411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80002511126582702506303607 120003766689874053759455411)
            ·
              refine ⟨180005650034811080639183117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120003766689874053759455411 180005650034811080639183117)
              ·
                refine ⟨67502118763054155239693669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180005650034811080639183117 67502118763054155239693669)
                ·
                  refine ⟨12656647268072654107442563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67502118763054155239693669 12656647268072654107442563)
                  ·
                    refine ⟨18984970902108981161163845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12656647268072654107442563 18984970902108981161163845)
                    ·
                      refine ⟨3559682044145433967718221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18984970902108981161163845 3559682044145433967718221)
                      ·
                        rfl

theorem cell23_6932456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6932456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932456 prefixEnd_6932456 := by exact prefixLift 6932456
  have htrace : WordTrace (prefixWord ++ tailWord_6932456) baseStart_6932456 baseEnd_6932456 := by
    simpa [prefixWord, tailWord_6932456, baseEnd_6932456] using wordTrace_append hprefix tailTrace_6932456
  have hstable : (prefixWord ++ tailWord_6932456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932456).length < 2 ^ (prefixWord ++ tailWord_6932456).sum := by decide
  have hdescent : baseEnd_6932456 < baseStart_6932456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932459 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_6932459 : Nat := 118140960795 + 6932459 * 2 ^ 59
def prefixEnd_6932459 : Nat := 4983230072969 + 3 ^ 40 * 6932459 * 2
def baseEnd_6932459 : Nat := 3559683584587397455980707

theorem tailTrace_6932459 : CollatzResearch.WordTrace tailWord_6932459 prefixEnd_6932459 3559683584587397455980707 := by
  unfold tailWord_6932459
  simp only [CollatzResearch.WordTrace]
  refine ⟨252847551991892487581664431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168565034661261658387776287 252847551991892487581664431)
  ·
    refine ⟨379271327987838731372496647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252847551991892487581664431 379271327987838731372496647)
    ·
      refine ⟨568906991981758097058744971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379271327987838731372496647 568906991981758097058744971)
      ·
        refine ⟨853360487972637145588117457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568906991981758097058744971 853360487972637145588117457)
        ·
          refine ⟨640020365979477859191088093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853360487972637145588117457 640020365979477859191088093)
          ·
            refine ⟨240007637242304197196658035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640020365979477859191088093 240007637242304197196658035)
            ·
              refine ⟨360011455863456295794987053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240007637242304197196658035 360011455863456295794987053)
              ·
                refine ⟨135004295948796110923120145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360011455863456295794987053 135004295948796110923120145)
                ·
                  refine ⟨101253221961597083192340109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135004295948796110923120145 101253221961597083192340109)
                  ·
                    refine ⟨37969958235598906197127541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101253221961597083192340109 37969958235598906197127541)
                    ·
                      refine ⟨3559683584587397455980707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37969958235598906197127541 3559683584587397455980707)
                      ·
                        rfl

theorem cell23_6932459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_6932459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932459 prefixEnd_6932459 := by exact prefixLift 6932459
  have htrace : WordTrace (prefixWord ++ tailWord_6932459) baseStart_6932459 baseEnd_6932459 := by
    simpa [prefixWord, tailWord_6932459, baseEnd_6932459] using wordTrace_append hprefix tailTrace_6932459
  have hstable : (prefixWord ++ tailWord_6932459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932459).length < 2 ^ (prefixWord ++ tailWord_6932459).sum := by decide
  have hdescent : baseEnd_6932459 < baseStart_6932459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932473 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 4, 2]
def baseStart_6932473 : Nat := 118140960795 + 6932473 * 2 ^ 59
def prefixEnd_6932473 : Nat := 4983230072969 + 3 ^ 40 * 6932473 * 2
def baseEnd_6932473 : Nat := 3559690773316560401205643

theorem tailTrace_6932473 : CollatzResearch.WordTrace tailWord_6932473 prefixEnd_6932473 3559690773316560401205643 := by
  unfold tailWord_6932473
  simp only [CollatzResearch.WordTrace]
  refine ⟨252848062613841767972674073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168565375075894511981782715 252848062613841767972674073)
  ·
    refine ⟨189636046960381325979505555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252848062613841767972674073 189636046960381325979505555)
    ·
      refine ⟨284454070440571988969258333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189636046960381325979505555 284454070440571988969258333)
      ·
        refine ⟨106670276415214495863471875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284454070440571988969258333 106670276415214495863471875)
        ·
          refine ⟨160005414622821743795207813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106670276415214495863471875 160005414622821743795207813)
          ·
            refine ⟨30001015241779076961601465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160005414622821743795207813 30001015241779076961601465)
            ·
              refine ⟨22500761431334307721201099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30001015241779076961601465 22500761431334307721201099)
              ·
                refine ⟨33751142147001461581801649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500761431334307721201099 33751142147001461581801649)
                ·
                  refine ⟨25313356610251096186351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33751142147001461581801649 25313356610251096186351237)
                  ·
                    refine ⟨4746254364422080534940857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25313356610251096186351237 4746254364422080534940857)
                    ·
                      refine ⟨3559690773316560401205643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746254364422080534940857 3559690773316560401205643)
                      ·
                        rfl

theorem cell23_6932473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_6932473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932473 prefixEnd_6932473 := by exact prefixLift 6932473
  have htrace : WordTrace (prefixWord ++ tailWord_6932473) baseStart_6932473 baseEnd_6932473 := by
    simpa [prefixWord, tailWord_6932473, baseEnd_6932473] using wordTrace_append hprefix tailTrace_6932473
  have hstable : (prefixWord ++ tailWord_6932473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932473).length < 2 ^ (prefixWord ++ tailWord_6932473).sum := by decide
  have hdescent : baseEnd_6932473 < baseStart_6932473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932476 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_6932476 : Nat := 118140960795 + 6932476 * 2 ^ 59
def prefixEnd_6932476 : Nat := 4983230072969 + 3 ^ 40 * 6932476 * 2
def baseEnd_6932476 : Nat := 3559692313758523889468129

theorem tailTrace_6932476 : CollatzResearch.WordTrace tailWord_6932476 prefixEnd_6932476 3559692313758523889468129 := by
  unfold tailWord_6932476
  simp only [CollatzResearch.WordTrace]
  refine ⟨126424086016415449742516641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168565448021887266323355521 126424086016415449742516641)
  ·
    refine ⟨94818064512311587306887481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126424086016415449742516641 94818064512311587306887481)
    ·
      refine ⟨71113548384233690480165611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94818064512311587306887481 71113548384233690480165611)
      ·
        refine ⟨106670322576350535720248417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71113548384233690480165611 106670322576350535720248417)
        ·
          refine ⟨80002741932262901790186313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106670322576350535720248417 80002741932262901790186313)
          ·
            refine ⟨60002056449197176342639735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80002741932262901790186313 60002056449197176342639735)
            ·
              refine ⟨90003084673795764513959603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60002056449197176342639735 90003084673795764513959603)
              ·
                refine ⟨135004627010693646770939405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90003084673795764513959603 135004627010693646770939405)
                ·
                  refine ⟨50626735129010117539102277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135004627010693646770939405 50626735129010117539102277)
                  ·
                    refine ⟨9492512836689397038581677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50626735129010117539102277 9492512836689397038581677)
                    ·
                      refine ⟨3559692313758523889468129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492512836689397038581677 3559692313758523889468129)
                      ·
                        rfl

theorem cell23_6932476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_6932476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932476 prefixEnd_6932476 := by exact prefixLift 6932476
  have htrace : WordTrace (prefixWord ++ tailWord_6932476) baseStart_6932476 baseEnd_6932476 := by
    simpa [prefixWord, tailWord_6932476, baseEnd_6932476] using wordTrace_append hprefix tailTrace_6932476
  have hstable : (prefixWord ++ tailWord_6932476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932476).length < 2 ^ (prefixWord ++ tailWord_6932476).sum := by decide
  have hdescent : baseEnd_6932476 < baseStart_6932476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932489 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_6932489 : Nat := 118140960795 + 6932489 * 2 ^ 59
def prefixEnd_6932489 : Nat := 4983230072969 + 3 ^ 40 * 6932489 * 2
def baseEnd_6932489 : Nat := 3559698989007032338605569

theorem tailTrace_6932489 : CollatzResearch.WordTrace tailWord_6932489 prefixEnd_6932489 3559698989007032338605569 := by
  unfold tailWord_6932489
  simp only [CollatzResearch.WordTrace]
  refine ⟨252848646181783802705256521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168565764121189201803504347 252848646181783802705256521)
  ·
    refine ⟨189636484636337852028942391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252848646181783802705256521 189636484636337852028942391)
    ·
      refine ⟨284454726954506778043413587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189636484636337852028942391 284454726954506778043413587)
      ·
        refine ⟨426682090431760167065120381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284454726954506778043413587 426682090431760167065120381)
        ·
          refine ⟨160005783911910062649420143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426682090431760167065120381 160005783911910062649420143)
          ·
            refine ⟨240008675867865093974130215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160005783911910062649420143 240008675867865093974130215)
            ·
              refine ⟨360013013801797640961195323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240008675867865093974130215 360013013801797640961195323)
              ·
                refine ⟨540019520702696461441792985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360013013801797640961195323 540019520702696461441792985)
                ·
                  refine ⟨405014640527022346081344739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540019520702696461441792985 405014640527022346081344739)
                  ·
                    refine ⟨607521960790533519122017109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405014640527022346081344739 607521960790533519122017109)
                    ·
                      refine ⟨3559698989007032338605569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 607521960790533519122017109 3559698989007032338605569)
                      ·
                        rfl

theorem cell23_6932489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_6932489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932489 prefixEnd_6932489 := by exact prefixLift 6932489
  have htrace : WordTrace (prefixWord ++ tailWord_6932489) baseStart_6932489 baseEnd_6932489 := by
    simpa [prefixWord, tailWord_6932489, baseEnd_6932489] using wordTrace_append hprefix tailTrace_6932489
  have hstable : (prefixWord ++ tailWord_6932489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932489).length < 2 ^ (prefixWord ++ tailWord_6932489).sum := by decide
  have hdescent : baseEnd_6932489 < baseStart_6932489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932517 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_6932517 : Nat := 118140960795 + 6932517 * 2 ^ 59
def prefixEnd_6932517 : Nat := 4983230072969 + 3 ^ 40 * 6932517 * 2
def baseEnd_6932517 : Nat := 1186571122155119409685147

theorem tailTrace_6932517 : CollatzResearch.WordTrace tailWord_6932517 prefixEnd_6932517 1186571122155119409685147 := by
  unfold tailWord_6932517
  simp only [CollatzResearch.WordTrace]
  refine ⟨252849667425682363487275805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168566444950454908991517203 252849667425682363487275805)
  ·
    refine ⟨94818625284630886307728427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252849667425682363487275805 94818625284630886307728427)
    ·
      refine ⟨142227937926946329461592641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94818625284630886307728427 142227937926946329461592641)
      ·
        refine ⟨106670953445209747096194481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142227937926946329461592641 106670953445209747096194481)
        ·
          refine ⟨80003215083907310322145861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106670953445209747096194481 80003215083907310322145861)
          ·
            refine ⟨15000602828232620685402349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80003215083907310322145861 15000602828232620685402349)
            ·
              refine ⟨5625226060587232757025881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15000602828232620685402349 5625226060587232757025881)
              ·
                refine ⟨4218919545440424567769411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5625226060587232757025881 4218919545440424567769411)
                ·
                  refine ⟨6328379318160636851654117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218919545440424567769411 6328379318160636851654117)
                  ·
                    refine ⟨1186571122155119409685147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328379318160636851654117 1186571122155119409685147)
                    ·
                      rfl

theorem cell23_6932517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_6932517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932517 prefixEnd_6932517 := by exact prefixLift 6932517
  have htrace : WordTrace (prefixWord ++ tailWord_6932517) baseStart_6932517 baseEnd_6932517 := by
    simpa [prefixWord, tailWord_6932517, baseEnd_6932517] using wordTrace_append hprefix tailTrace_6932517
  have hstable : (prefixWord ++ tailWord_6932517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932517).length < 2 ^ (prefixWord ++ tailWord_6932517).sum := by decide
  have hdescent : baseEnd_6932517 < baseStart_6932517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932523 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 3]
def baseStart_6932523 : Nat := 118140960795 + 6932523 * 2 ^ 59
def prefixEnd_6932523 : Nat := 4983230072969 + 3 ^ 40 * 6932523 * 2
def baseEnd_6932523 : Nat := 3559716447349285205580413

theorem tailTrace_6932523 : CollatzResearch.WordTrace tailWord_6932523 prefixEnd_6932523 3559716447349285205580413 := by
  unfold tailWord_6932523
  simp only [CollatzResearch.WordTrace]
  refine ⟨252849886263660626511994223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168566590842440417674662815 252849886263660626511994223)
  ·
    refine ⟨379274829395490939767991335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252849886263660626511994223 379274829395490939767991335)
    ·
      refine ⟨568912244093236409651987003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379274829395490939767991335 568912244093236409651987003)
      ·
        refine ⟨853368366139854614477980505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568912244093236409651987003 853368366139854614477980505)
        ·
          refine ⟨640026274604890960858485379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853368366139854614477980505 640026274604890960858485379)
          ·
            refine ⟨960039411907336441287728069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640026274604890960858485379 960039411907336441287728069)
            ·
              refine ⟨180007389732625582741449013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 960039411907336441287728069 180007389732625582741449013)
              ·
                refine ⟨16875692787433648382010845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180007389732625582741449013 16875692787433648382010845)
                ·
                  refine ⟨6328384795287618143254067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16875692787433648382010845 6328384795287618143254067)
                  ·
                    refine ⟨9492577192931427214881101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328384795287618143254067 9492577192931427214881101)
                    ·
                      refine ⟨3559716447349285205580413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492577192931427214881101 3559716447349285205580413)
                      ·
                        rfl

theorem cell23_6932523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 3].length) (baseStart_6932523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932523 prefixEnd_6932523 := by exact prefixLift 6932523
  have htrace : WordTrace (prefixWord ++ tailWord_6932523) baseStart_6932523 baseEnd_6932523 := by
    simpa [prefixWord, tailWord_6932523, baseEnd_6932523] using wordTrace_append hprefix tailTrace_6932523
  have hstable : (prefixWord ++ tailWord_6932523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932523).length < 2 ^ (prefixWord ++ tailWord_6932523).sum := by decide
  have hdescent : baseEnd_6932523 < baseStart_6932523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932530 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_6932530 : Nat := 118140960795 + 6932530 * 2 ^ 59
def prefixEnd_6932530 : Nat := 4983230072969 + 3 ^ 40 * 6932530 * 2
def baseEnd_6932530 : Nat := 395524449079318519799209

theorem tailTrace_6932530 : CollatzResearch.WordTrace tailWord_6932530 prefixEnd_6932530 395524449079318519799209 := by
  unfold tailWord_6932530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63212535393658816676874761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168566761049756844471666029 63212535393658816676874761)
  ·
    refine ⟨47409401545244112507656071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63212535393658816676874761 47409401545244112507656071)
    ·
      refine ⟨71114102317866168761484107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47409401545244112507656071 71114102317866168761484107)
      ·
        refine ⟨106671153476799253142226161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71114102317866168761484107 106671153476799253142226161)
        ·
          refine ⟨80003365107599439856669621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106671153476799253142226161 80003365107599439856669621)
          ·
            refine ⟨7500315478837447486562777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80003365107599439856669621 7500315478837447486562777)
            ·
              refine ⟨5625236609128085614922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500315478837447486562777 5625236609128085614922083)
              ·
                refine ⟨8437854913692128422383125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625236609128085614922083 8437854913692128422383125)
                ·
                  refine ⟨395524449079318519799209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8437854913692128422383125 395524449079318519799209)
                  ·
                    rfl

theorem cell23_6932530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_6932530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932530 prefixEnd_6932530 := by exact prefixLift 6932530
  have htrace : WordTrace (prefixWord ++ tailWord_6932530) baseStart_6932530 baseEnd_6932530 := by
    simpa [prefixWord, tailWord_6932530, baseEnd_6932530] using wordTrace_append hprefix tailTrace_6932530
  have hstable : (prefixWord ++ tailWord_6932530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932530).length < 2 ^ (prefixWord ++ tailWord_6932530).sum := by decide
  have hdescent : baseEnd_6932530 < baseStart_6932530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932533 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_6932533 : Nat := 118140960795 + 6932533 * 2 ^ 59
def prefixEnd_6932533 : Nat := 4983230072969 + 3 ^ 40 * 6932533 * 2
def baseEnd_6932533 : Nat := 3559721582155830166455367

theorem tailTrace_6932533 : CollatzResearch.WordTrace tailWord_6932533 prefixEnd_6932533 3559721582155830166455367 := by
  unfold tailWord_6932533
  simp only [CollatzResearch.WordTrace]
  refine ⟨252850250993624398219858253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168566833995749598813238835 252850250993624398219858253)
  ·
    refine ⟨94818844122609149332446845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252850250993624398219858253 94818844122609149332446845)
    ·
      refine ⟨35557066545978430999667567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94818844122609149332446845 35557066545978430999667567)
      ·
        refine ⟨53335599818967646499501351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35557066545978430999667567 53335599818967646499501351)
        ·
          refine ⟨80003399728451469749252027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53335599818967646499501351 80003399728451469749252027)
          ·
            refine ⟨120005099592677204623878041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80003399728451469749252027 120005099592677204623878041)
            ·
              refine ⟨90003824694507903467908531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120005099592677204623878041 90003824694507903467908531)
              ·
                refine ⟨135005737041761855201862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90003824694507903467908531 135005737041761855201862797)
                ·
                  refine ⟨50627151390660695700698549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135005737041761855201862797 50627151390660695700698549)
                  ·
                    refine ⟨4746295442874440221940489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50627151390660695700698549 4746295442874440221940489)
                    ·
                      refine ⟨3559721582155830166455367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746295442874440221940489 3559721582155830166455367)
                      ·
                        rfl

theorem cell23_6932533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_6932533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932533 prefixEnd_6932533 := by exact prefixLift 6932533
  have htrace : WordTrace (prefixWord ++ tailWord_6932533) baseStart_6932533 baseEnd_6932533 := by
    simpa [prefixWord, tailWord_6932533, baseEnd_6932533] using wordTrace_append hprefix tailTrace_6932533
  have hstable : (prefixWord ++ tailWord_6932533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932533).length < 2 ^ (prefixWord ++ tailWord_6932533).sum := by decide
  have hdescent : baseEnd_6932533 < baseStart_6932533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932543 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 1, 5]
def baseStart_6932543 : Nat := 118140960795 + 6932543 * 2 ^ 59
def prefixEnd_6932543 : Nat := 4983230072969 + 3 ^ 40 * 6932543 * 2
def baseEnd_6932543 : Nat := 1186575572320791709110107

theorem tailTrace_6932543 : CollatzResearch.WordTrace tailWord_6932543 prefixEnd_6932543 1186575572320791709110107 := by
  unfold tailWord_6932543
  simp only [CollatzResearch.WordTrace]
  refine ⟨252850615723588169927722283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168567077149058779951814855 252850615723588169927722283)
  ·
    refine ⟨379275923585382254891583425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252850615723588169927722283 379275923585382254891583425)
    ·
      refine ⟨284456942689036691168687569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379275923585382254891583425 284456942689036691168687569)
      ·
        refine ⟨213342707016777518376515677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284456942689036691168687569 213342707016777518376515677)
        ·
          refine ⟨80003515131291569391193379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213342707016777518376515677 80003515131291569391193379)
          ·
            refine ⟨120005272696937354086790069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80003515131291569391193379 120005272696937354086790069)
            ·
              refine ⟨11250494315337876945636569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120005272696937354086790069 11250494315337876945636569)
              ·
                refine ⟨8437870736503407709227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11250494315337876945636569 8437870736503407709227427)
                ·
                  refine ⟨12656806104755111563841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437870736503407709227427 12656806104755111563841141)
                  ·
                    refine ⟨1186575572320791709110107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12656806104755111563841141 1186575572320791709110107)
                    ·
                      rfl

theorem cell23_6932543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_6932543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932543 prefixEnd_6932543 := by exact prefixLift 6932543
  have htrace : WordTrace (prefixWord ++ tailWord_6932543) baseStart_6932543 baseEnd_6932543 := by
    simpa [prefixWord, tailWord_6932543, baseEnd_6932543] using wordTrace_append hprefix tailTrace_6932543
  have hstable : (prefixWord ++ tailWord_6932543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932543).length < 2 ^ (prefixWord ++ tailWord_6932543).sum := by decide
  have hdescent : baseEnd_6932543 < baseStart_6932543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932556 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_6932556 : Nat := 118140960795 + 6932556 * 2 ^ 59
def prefixEnd_6932556 : Nat := 4983230072969 + 3 ^ 40 * 6932556 * 2
def baseEnd_6932556 : Nat := 1186577797403627858822587

theorem tailTrace_6932556 : CollatzResearch.WordTrace tailWord_6932556 prefixEnd_6932556 1186577797403627858822587 := by
  unfold tailWord_6932556
  simp only [CollatzResearch.WordTrace]
  refine ⟨126425544936270536573972761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168567393248360715431963681 126425544936270536573972761)
  ·
    refine ⟨94819158702202902430479571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126425544936270536573972761 94819158702202902430479571)
    ·
      refine ⟨142228738053304353645719357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94819158702202902430479571 142228738053304353645719357)
      ·
        refine ⟨53335776769989132617144759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142228738053304353645719357 53335776769989132617144759)
        ·
          refine ⟨80003665154983698925717139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53335776769989132617144759 80003665154983698925717139)
          ·
            refine ⟨120005497732475548388575709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80003665154983698925717139 120005497732475548388575709)
            ·
              refine ⟨45002061649678330645715891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120005497732475548388575709 45002061649678330645715891)
              ·
                refine ⟨67503092474517495968573837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45002061649678330645715891 67503092474517495968573837)
                ·
                  refine ⟨25313659677944060988215189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67503092474517495968573837 25313659677944060988215189)
                  ·
                    refine ⟨1186577797403627858822587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25313659677944060988215189 1186577797403627858822587)
                    ·
                      rfl

theorem cell23_6932556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_6932556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932556 prefixEnd_6932556 := by exact prefixLift 6932556
  have htrace : WordTrace (prefixWord ++ tailWord_6932556) baseStart_6932556 baseEnd_6932556 := by
    simpa [prefixWord, tailWord_6932556, baseEnd_6932556] using wordTrace_append hprefix tailTrace_6932556
  have hstable : (prefixWord ++ tailWord_6932556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932556).length < 2 ^ (prefixWord ++ tailWord_6932556).sum := by decide
  have hdescent : baseEnd_6932556 < baseStart_6932556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932583 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_6932583 : Nat := 118140960795 + 6932583 * 2 ^ 59
def prefixEnd_6932583 : Nat := 4983230072969 + 3 ^ 40 * 6932583 * 2
def baseEnd_6932583 : Nat := 3559747256188554970830137

theorem tailTrace_6932583 : CollatzResearch.WordTrace tailWord_6932583 prefixEnd_6932583 3559747256188554970830137 := by
  unfold tailWord_6932583
  simp only [CollatzResearch.WordTrace]
  refine ⟨252852074643443256759178403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168568049762295504506118935 252852074643443256759178403)
  ·
    refine ⟨379278111965164885138767605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252852074643443256759178403 379278111965164885138767605)
    ·
      refine ⟨35557322996734207981759463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379278111965164885138767605 35557322996734207981759463)
      ·
        refine ⟨53335984495101311972639195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35557322996734207981759463 53335984495101311972639195)
        ·
          refine ⟨80003976742651967958958793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53335984495101311972639195 80003976742651967958958793)
          ·
            refine ⟨60002982556988975969219095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80003976742651967958958793 60002982556988975969219095)
            ·
              refine ⟨90004473835483463953828643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60002982556988975969219095 90004473835483463953828643)
              ·
                refine ⟨135006710753225195930742965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90004473835483463953828643 135006710753225195930742965)
                ·
                  refine ⟨12656879133114862118507153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135006710753225195930742965 12656879133114862118507153)
                  ·
                    refine ⟨9492659349836146588880365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12656879133114862118507153 9492659349836146588880365)
                    ·
                      refine ⟨3559747256188554970830137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492659349836146588880365 3559747256188554970830137)
                      ·
                        rfl

theorem cell23_6932583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_6932583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932583 prefixEnd_6932583 := by exact prefixLift 6932583
  have htrace : WordTrace (prefixWord ++ tailWord_6932583) baseStart_6932583 baseEnd_6932583 := by
    simpa [prefixWord, tailWord_6932583, baseEnd_6932583] using wordTrace_append hprefix tailTrace_6932583
  have hstable : (prefixWord ++ tailWord_6932583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932583).length < 2 ^ (prefixWord ++ tailWord_6932583).sum := by decide
  have hdescent : baseEnd_6932583 < baseStart_6932583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932590 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_6932590 : Nat := 118140960795 + 6932590 * 2 ^ 59
def prefixEnd_6932590 : Nat := 4983230072969 + 3 ^ 40 * 6932590 * 2
def baseEnd_6932590 : Nat := 1186583616851045481147535

theorem tailTrace_6932590 : CollatzResearch.WordTrace tailWord_6932590 prefixEnd_6932590 1186583616851045481147535 := by
  unfold tailWord_6932590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606541244302237119335403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168568219969611931303122149 31606541244302237119335403)
  ·
    refine ⟨47409811866453355679003105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31606541244302237119335403 47409811866453355679003105)
    ·
      refine ⟨35557358899840016759252329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47409811866453355679003105 35557358899840016759252329)
      ·
        refine ⟨26668019174880012569439247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35557358899840016759252329 26668019174880012569439247)
        ·
          refine ⟨40002028762320018854158871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26668019174880012569439247 40002028762320018854158871)
          ·
            refine ⟨60003043143480028281238307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40002028762320018854158871 60003043143480028281238307)
            ·
              refine ⟨90004564715220042421857461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60003043143480028281238307 90004564715220042421857461)
              ·
                refine ⟨8437927942051878977049137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90004564715220042421857461 8437927942051878977049137)
                ·
                  refine ⟨6328445956538909232786853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8437927942051878977049137 6328445956538909232786853)
                  ·
                    refine ⟨1186583616851045481147535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328445956538909232786853 1186583616851045481147535)
                    ·
                      rfl

theorem cell23_6932590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_6932590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932590 prefixEnd_6932590 := by exact prefixLift 6932590
  have htrace : WordTrace (prefixWord ++ tailWord_6932590) baseStart_6932590 baseEnd_6932590 := by
    simpa [prefixWord, tailWord_6932590, baseEnd_6932590] using wordTrace_append hprefix tailTrace_6932590
  have hstable : (prefixWord ++ tailWord_6932590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932590).length < 2 ^ (prefixWord ++ tailWord_6932590).sum := by decide
  have hdescent : baseEnd_6932590 < baseStart_6932590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932593 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_6932593 : Nat := 118140960795 + 6932593 * 2 ^ 59
def prefixEnd_6932593 : Nat := 4983230072969 + 3 ^ 40 * 6932593 * 2
def baseEnd_6932593 : Nat := 3559752390995099931705091

theorem tailTrace_6932593 : CollatzResearch.WordTrace tailWord_6932593 prefixEnd_6932593 3559752390995099931705091 := by
  unfold tailWord_6932593
  simp only [CollatzResearch.WordTrace]
  refine ⟨252852439373407028467042433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168568292915604685644694955 252852439373407028467042433)
  ·
    refine ⟨189639329530055271350281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252852439373407028467042433 189639329530055271350281825)
    ·
      refine ⟨142229497147541453512711369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189639329530055271350281825 142229497147541453512711369)
      ·
        refine ⟨106672122860656090134533527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142229497147541453512711369 106672122860656090134533527)
        ·
          refine ⟨160008184290984135201800291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106672122860656090134533527 160008184290984135201800291)
          ·
            refine ⟨240012276436476202802700437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160008184290984135201800291 240012276436476202802700437)
            ·
              refine ⟨11250575457959822006376583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240012276436476202802700437 11250575457959822006376583)
              ·
                refine ⟨16875863186939733009564875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11250575457959822006376583 16875863186939733009564875)
                ·
                  refine ⟨25313794780409599514347313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16875863186939733009564875 25313794780409599514347313)
                  ·
                    refine ⟨18985346085307199635760485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25313794780409599514347313 18985346085307199635760485)
                    ·
                      refine ⟨3559752390995099931705091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18985346085307199635760485 3559752390995099931705091)
                      ·
                        rfl

theorem cell23_6932593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_6932593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932593 prefixEnd_6932593 := by exact prefixLift 6932593
  have htrace : WordTrace (prefixWord ++ tailWord_6932593) baseStart_6932593 baseEnd_6932593 := by
    simpa [prefixWord, tailWord_6932593, baseEnd_6932593] using wordTrace_append hprefix tailTrace_6932593
  have hstable : (prefixWord ++ tailWord_6932593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932593).length < 2 ^ (prefixWord ++ tailWord_6932593).sum := by decide
  have hdescent : baseEnd_6932593 < baseStart_6932593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932654 : List Nat := [4, 1, 4, 2, 1, 2, 2, 7]
def baseStart_6932654 : Nat := 118140960795 + 6932654 * 2 ^ 59
def prefixEnd_6932654 : Nat := 4983230072969 + 3 ^ 40 * 6932654 * 2
def baseEnd_6932654 : Nat := 131843841233889784927493

theorem tailTrace_6932654 : CollatzResearch.WordTrace tailWord_6932654 prefixEnd_6932654 131843841233889784927493 := by
  unfold tailWord_6932654
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606833028273254485626627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168569776150790690590008677 31606833028273254485626627)
  ·
    refine ⟨47410249542409881728439941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31606833028273254485626627 47410249542409881728439941)
    ·
      refine ⟨8889421789201852824082489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47410249542409881728439941 8889421789201852824082489)
      ·
        refine ⟨6667066341901389618061867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889421789201852824082489 6667066341901389618061867)
        ·
          refine ⟨10000599512852084427092801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667066341901389618061867 10000599512852084427092801)
          ·
            refine ⟨7500449634639063320319601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10000599512852084427092801 7500449634639063320319601)
            ·
              refine ⟨5625337225979297490239701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500449634639063320319601 5625337225979297490239701)
              ·
                refine ⟨131843841233889784927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5625337225979297490239701 131843841233889784927493)
                ·
                  rfl

theorem cell23_6932654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_6932654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932654 prefixEnd_6932654 := by exact prefixLift 6932654
  have htrace : WordTrace (prefixWord ++ tailWord_6932654) baseStart_6932654 baseEnd_6932654 := by
    simpa [prefixWord, tailWord_6932654, baseEnd_6932654] using wordTrace_append hprefix tailTrace_6932654
  have hstable : (prefixWord ++ tailWord_6932654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932654).length < 2 ^ (prefixWord ++ tailWord_6932654).sum := by decide
  have hdescent : baseEnd_6932654 < baseStart_6932654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932687 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 2, 2, 2]
def baseStart_6932687 : Nat := 118140960795 + 6932687 * 2 ^ 59
def prefixEnd_6932687 : Nat := 4983230072969 + 3 ^ 40 * 6932687 * 2
def baseEnd_6932687 : Nat := 3559800658176622563929659

theorem tailTrace_6932687 : CollatzResearch.WordTrace tailWord_6932687 prefixEnd_6932687 3559800658176622563929659 := by
  unfold tailWord_6932687
  simp only [CollatzResearch.WordTrace]
  refine ⟨252855867835066482520964315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168570578556710988347309543 252855867835066482520964315)
  ·
    refine ⟨379283801752599723781446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252855867835066482520964315 379283801752599723781446473)
    ·
      refine ⟨284462851314449792836084855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379283801752599723781446473 284462851314449792836084855)
      ·
        refine ⟨426694276971674689254127283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284462851314449792836084855 426694276971674689254127283)
        ·
          refine ⟨640041415457512033881190925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426694276971674689254127283 640041415457512033881190925)
          ·
            refine ⟨240015530796567012705446597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640041415457512033881190925 240015530796567012705446597)
            ·
              refine ⟨45002912024356314882271237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240015530796567012705446597 45002912024356314882271237)
              ·
                refine ⟨8438046004566809040425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45002912024356314882271237 8438046004566809040425857)
                ·
                  refine ⟨6328534503425106780319393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438046004566809040425857 6328534503425106780319393)
                  ·
                    refine ⟨4746400877568830085239545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6328534503425106780319393 4746400877568830085239545)
                    ·
                      refine ⟨3559800658176622563929659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746400877568830085239545 3559800658176622563929659)
                      ·
                        rfl

theorem cell23_6932687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2, 2].length) (baseStart_6932687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932687 prefixEnd_6932687 := by exact prefixLift 6932687
  have htrace : WordTrace (prefixWord ++ tailWord_6932687) baseStart_6932687 baseEnd_6932687 := by
    simpa [prefixWord, tailWord_6932687, baseEnd_6932687] using wordTrace_append hprefix tailTrace_6932687
  have hstable : (prefixWord ++ tailWord_6932687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932687).length < 2 ^ (prefixWord ++ tailWord_6932687).sum := by decide
  have hdescent : baseEnd_6932687 < baseStart_6932687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932703 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_6932703 : Nat := 118140960795 + 6932703 * 2 ^ 59
def prefixEnd_6932703 : Nat := 4983230072969 + 3 ^ 40 * 6932703 * 2
def baseEnd_6932703 : Nat := 3559808873867094501329585

theorem tailTrace_6932703 : CollatzResearch.WordTrace tailWord_6932703 prefixEnd_6932703 3559808873867094501329585 := by
  unfold tailWord_6932703
  simp only [CollatzResearch.WordTrace]
  refine ⟨252856451403008517253546763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168570967602005678169031175 252856451403008517253546763)
  ·
    refine ⟨379284677104512775880320145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252856451403008517253546763 379284677104512775880320145)
    ·
      refine ⟨284463507828384581910240109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379284677104512775880320145 284463507828384581910240109)
      ·
        refine ⟨106673815435644218216340041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284463507828384581910240109 106673815435644218216340041)
        ·
          refine ⟨80005361576733163662255031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106673815435644218216340041 80005361576733163662255031)
          ·
            refine ⟨120008042365099745493382547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80005361576733163662255031 120008042365099745493382547)
            ·
              refine ⟨180012063547649618240073821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120008042365099745493382547 180012063547649618240073821)
              ·
                refine ⟨67504523830368606840027683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180012063547649618240073821 67504523830368606840027683)
                ·
                  refine ⟨101256785745552910260041525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67504523830368606840027683 101256785745552910260041525)
                  ·
                    refine ⟨9492823663645585336878893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101256785745552910260041525 9492823663645585336878893)
                    ·
                      refine ⟨3559808873867094501329585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9492823663645585336878893 3559808873867094501329585)
                      ·
                        rfl

theorem cell23_6932703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_6932703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932703 prefixEnd_6932703 := by exact prefixLift 6932703
  have htrace : WordTrace (prefixWord ++ tailWord_6932703) baseStart_6932703 baseEnd_6932703 := by
    simpa [prefixWord, tailWord_6932703, baseEnd_6932703] using wordTrace_append hprefix tailTrace_6932703
  have hstable : (prefixWord ++ tailWord_6932703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932703).length < 2 ^ (prefixWord ++ tailWord_6932703).sum := by decide
  have hdescent : baseEnd_6932703 < baseStart_6932703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932744 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 5]
def baseStart_6932744 : Nat := 118140960795 + 6932744 * 2 ^ 59
def prefixEnd_6932744 : Nat := 4983230072969 + 3 ^ 40 * 6932744 * 2
def baseEnd_6932744 : Nat := 395536658508214315657433

theorem tailTrace_6932744 : CollatzResearch.WordTrace tailWord_6932744 prefixEnd_6932744 395536658508214315657433 := by
  unfold tailWord_6932744
  simp only [CollatzResearch.WordTrace]
  refine ⟨126428973397929990627894643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168571964530573320837192857 126428973397929990627894643)
  ·
    refine ⟨189643460096894985941841965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126428973397929990627894643 189643460096894985941841965)
    ·
      refine ⟨71116297536335619728190737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189643460096894985941841965 71116297536335619728190737)
      ·
        refine ⟨53337223152251714796143053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71116297536335619728190737 53337223152251714796143053)
        ·
          refine ⟨20001458682094393048553645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53337223152251714796143053 20001458682094393048553645)
          ·
            refine ⟨7500547005785397393207617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20001458682094393048553645 7500547005785397393207617)
            ·
              refine ⟨5625410254339048044905713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500547005785397393207617 5625410254339048044905713)
              ·
                refine ⟨4219057690754286033679285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5625410254339048044905713 4219057690754286033679285)
                ·
                  refine ⟨395536658508214315657433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4219057690754286033679285 395536658508214315657433)
                  ·
                    rfl

theorem cell23_6932744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 5].length) (baseStart_6932744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932744 prefixEnd_6932744 := by exact prefixLift 6932744
  have htrace : WordTrace (prefixWord ++ tailWord_6932744) baseStart_6932744 baseEnd_6932744 := by
    simpa [prefixWord, tailWord_6932744, baseEnd_6932744] using wordTrace_append hprefix tailTrace_6932744
  have hstable : (prefixWord ++ tailWord_6932744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932744).length < 2 ^ (prefixWord ++ tailWord_6932744).sum := by decide
  have hdescent : baseEnd_6932744 < baseStart_6932744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932803 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_6932803 : Nat := 118140960795 + 6932803 * 2 ^ 59
def prefixEnd_6932803 : Nat := 4983230072969 + 3 ^ 40 * 6932803 * 2
def baseEnd_6932803 : Nat := 3559860221932544110079125

theorem tailTrace_6932803 : CollatzResearch.WordTrace tailWord_6932803 prefixEnd_6932803 3559860221932544110079125 := by
  unfold tailWord_6932803
  simp only [CollatzResearch.WordTrace]
  refine ⟨252860098702646234332187063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168573399135097489554791375 252860098702646234332187063)
  ·
    refine ⟨379290148053969351498280595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252860098702646234332187063 379290148053969351498280595)
    ·
      refine ⟨568935222080954027247420893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379290148053969351498280595 568935222080954027247420893)
      ·
        refine ⟨213350708280357760217782835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568935222080954027247420893 213350708280357760217782835)
        ·
          refine ⟨320026062420536640326674253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213350708280357760217782835 320026062420536640326674253)
          ·
            refine ⟨120009773407701240122502845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320026062420536640326674253 120009773407701240122502845)
            ·
              refine ⟨45003665027887965045938567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120009773407701240122502845 45003665027887965045938567)
              ·
                refine ⟨67505497541831947568907851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45003665027887965045938567 67505497541831947568907851)
                ·
                  refine ⟨101258246312747921353361777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67505497541831947568907851 101258246312747921353361777)
                  ·
                    refine ⟨75943684734560941015021333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101258246312747921353361777 75943684734560941015021333)
                    ·
                      refine ⟨3559860221932544110079125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75943684734560941015021333 3559860221932544110079125)
                      ·
                        rfl

theorem cell23_6932803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_6932803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932803 prefixEnd_6932803 := by exact prefixLift 6932803
  have htrace : WordTrace (prefixWord ++ tailWord_6932803) baseStart_6932803 baseEnd_6932803 := by
    simpa [prefixWord, tailWord_6932803, baseEnd_6932803] using wordTrace_append hprefix tailTrace_6932803
  have hstable : (prefixWord ++ tailWord_6932803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932803).length < 2 ^ (prefixWord ++ tailWord_6932803).sum := by decide
  have hdescent : baseEnd_6932803 < baseStart_6932803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932817 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 6]
def baseStart_6932817 : Nat := 118140960795 + 6932817 * 2 ^ 59
def prefixEnd_6932817 : Nat := 4983230072969 + 3 ^ 40 * 6932817 * 2
def baseEnd_6932817 : Nat := 395540823406856339478229

theorem tailTrace_6932817 : CollatzResearch.WordTrace tailWord_6932817 prefixEnd_6932817 395540823406856339478229 := by
  unfold tailWord_6932817
  simp only [CollatzResearch.WordTrace]
  refine ⟨252860609324595514723196705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168573739549730343148797803 252860609324595514723196705)
  ·
    refine ⟨189645456993446636042397529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252860609324595514723196705 189645456993446636042397529)
    ·
      refine ⟨142234092745084977031798147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189645456993446636042397529 142234092745084977031798147)
      ·
        refine ⟨213351139117627465547697221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142234092745084977031798147 213351139117627465547697221)
        ·
          refine ⟨40003338584555149790193229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213351139117627465547697221 40003338584555149790193229)
          ·
            refine ⟨15001251969208181171322461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40003338584555149790193229 15001251969208181171322461)
            ·
              refine ⟨5625469488453067939245923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15001251969208181171322461 5625469488453067939245923)
              ·
                refine ⟨8438204232679601908868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625469488453067939245923 8438204232679601908868885)
                ·
                  refine ⟨395540823406856339478229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8438204232679601908868885 395540823406856339478229)
                  ·
                    rfl

theorem cell23_6932817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_6932817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932817 prefixEnd_6932817 := by exact prefixLift 6932817
  have htrace : WordTrace (prefixWord ++ tailWord_6932817) baseStart_6932817 baseEnd_6932817 := by
    simpa [prefixWord, tailWord_6932817, baseEnd_6932817] using wordTrace_append hprefix tailTrace_6932817
  have hstable : (prefixWord ++ tailWord_6932817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932817).length < 2 ^ (prefixWord ++ tailWord_6932817).sum := by decide
  have hdescent : baseEnd_6932817 < baseStart_6932817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932837 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_6932837 : Nat := 118140960795 + 6932837 * 2 ^ 59
def prefixEnd_6932837 : Nat := 4983230072969 + 3 ^ 40 * 6932837 * 2
def baseEnd_6932837 : Nat := 3559877680274796977053969

theorem tailTrace_6932837 : CollatzResearch.WordTrace tailWord_6932837 prefixEnd_6932837 3559877680274796977053969 := by
  unfold tailWord_6932837
  simp only [CollatzResearch.WordTrace]
  refine ⟨252861338784523058138924765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168574225856348705425949843 252861338784523058138924765)
  ·
    refine ⟨94823002044196146802096787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252861338784523058138924765 94823002044196146802096787)
    ·
      refine ⟨142234503066294220203145181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94823002044196146802096787 142234503066294220203145181)
      ·
        refine ⟨53337938649860332576179443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142234503066294220203145181 53337938649860332576179443)
        ·
          refine ⟨80006907974790498864269165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53337938649860332576179443 80006907974790498864269165)
          ·
            refine ⟨30002590490546437074100937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80006907974790498864269165 30002590490546437074100937)
            ·
              refine ⟨22501942867909827805575703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30002590490546437074100937 22501942867909827805575703)
              ·
                refine ⟨33752914301864741708363555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22501942867909827805575703 33752914301864741708363555)
                ·
                  refine ⟨50629371452797112562545333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33752914301864741708363555 50629371452797112562545333)
                  ·
                    refine ⟨4746503573699729302738625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50629371452797112562545333 4746503573699729302738625)
                    ·
                      refine ⟨3559877680274796977053969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746503573699729302738625 3559877680274796977053969)
                      ·
                        rfl

theorem cell23_6932837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_6932837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932837 prefixEnd_6932837 := by exact prefixLift 6932837
  have htrace : WordTrace (prefixWord ++ tailWord_6932837) baseStart_6932837 baseEnd_6932837 := by
    simpa [prefixWord, tailWord_6932837, baseEnd_6932837] using wordTrace_append hprefix tailTrace_6932837
  have hstable : (prefixWord ++ tailWord_6932837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932837).length < 2 ^ (prefixWord ++ tailWord_6932837).sum := by decide
  have hdescent : baseEnd_6932837 < baseStart_6932837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932884 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6932884 : Nat := 118140960795 + 6932884 * 2 ^ 59
def prefixEnd_6932884 : Nat := 4983230072969 + 3 ^ 40 * 6932884 * 2
def baseEnd_6932884 : Nat := 3559901813865558293166253

theorem tailTrace_6932884 : CollatzResearch.WordTrace tailWord_6932884 prefixEnd_6932884 3559901813865558293166253 := by
  unfold tailWord_6932884
  simp only [CollatzResearch.WordTrace]
  refine ⟨126431526507676392582942853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168575368676901856777257137 126431526507676392582942853)
  ·
    refine ⟨23705911220189323609301785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126431526507676392582942853 23705911220189323609301785)
    ·
      refine ⟨17779433415141992706976339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23705911220189323609301785 17779433415141992706976339)
      ·
        refine ⟨26669150122712989060464509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17779433415141992706976339 26669150122712989060464509)
        ·
          refine ⟨10000931296017370897674191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26669150122712989060464509 10000931296017370897674191)
          ·
            refine ⟨15001396944026056346511287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000931296017370897674191 15001396944026056346511287)
            ·
              refine ⟨22502095416039084519766931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001396944026056346511287 22502095416039084519766931)
              ·
                refine ⟨33753143124058626779650397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502095416039084519766931 33753143124058626779650397)
                ·
                  refine ⟨12657428671521985042368899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33753143124058626779650397 12657428671521985042368899)
                  ·
                    refine ⟨18986143007282977563553349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12657428671521985042368899 18986143007282977563553349)
                    ·
                      refine ⟨3559901813865558293166253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18986143007282977563553349 3559901813865558293166253)
                      ·
                        rfl

theorem cell23_6932884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6932884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932884 prefixEnd_6932884 := by exact prefixLift 6932884
  have htrace : WordTrace (prefixWord ++ tailWord_6932884) baseStart_6932884 baseEnd_6932884 := by
    simpa [prefixWord, tailWord_6932884, baseEnd_6932884] using wordTrace_append hprefix tailTrace_6932884
  have hstable : (prefixWord ++ tailWord_6932884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932884).length < 2 ^ (prefixWord ++ tailWord_6932884).sum := by decide
  have hdescent : baseEnd_6932884 < baseStart_6932884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932890 : List Nat := [3, 1, 1, 4, 1, 2, 2, 9]
def baseStart_6932890 : Nat := 118140960795 + 6932890 * 2 ^ 59
def prefixEnd_6932890 : Nat := 4983230072969 + 3 ^ 40 * 6932890 * 2
def baseEnd_6932890 : Nat := 131848329435166121099675

theorem tailTrace_6932890 : CollatzResearch.WordTrace tailWord_6932890 prefixEnd_6932890 131848329435166121099675 := by
  unfold tailWord_6932890
  simp only [CollatzResearch.WordTrace]
  refine ⟨63215817963332762047651031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168575514568887365460402749 63215817963332762047651031)
  ·
    refine ⟨94823726944999143071476547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63215817963332762047651031 94823726944999143071476547)
    ·
      refine ⟨142235590417498714607214821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94823726944999143071476547 142235590417498714607214821)
      ·
        refine ⟨26669173203281008988852779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142235590417498714607214821 26669173203281008988852779)
        ·
          refine ⟨40003759804921513483279169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669173203281008988852779 40003759804921513483279169)
          ·
            refine ⟨30002819853691135112459377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40003759804921513483279169 30002819853691135112459377)
            ·
              refine ⟨22502114890268351334344533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30002819853691135112459377 22502114890268351334344533)
              ·
                refine ⟨131848329435166121099675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22502114890268351334344533 131848329435166121099675)
                ·
                  rfl

theorem cell23_6932890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_6932890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932890 prefixEnd_6932890 := by exact prefixLift 6932890
  have htrace : WordTrace (prefixWord ++ tailWord_6932890) baseStart_6932890 baseEnd_6932890 := by
    simpa [prefixWord, tailWord_6932890, baseEnd_6932890] using wordTrace_append hprefix tailTrace_6932890
  have hstable : (prefixWord ++ tailWord_6932890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932890).length < 2 ^ (prefixWord ++ tailWord_6932890).sum := by decide
  have hdescent : baseEnd_6932890 < baseStart_6932890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932894 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6932894 : Nat := 118140960795 + 6932894 * 2 ^ 59
def prefixEnd_6932894 : Nat := 4983230072969 + 3 ^ 40 * 6932894 * 2
def baseEnd_6932894 : Nat := 1186635649557367751347069

theorem tailTrace_6932894 : CollatzResearch.WordTrace tailWord_6932894 prefixEnd_6932894 1186635649557367751347069 := by
  unfold tailWord_6932894
  simp only [CollatzResearch.WordTrace]
  refine ⟨31607927218164569609218717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168575611830211037915833157 31607927218164569609218717)
  ·
    refine ⟨11852972706811713603457019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31607927218164569609218717 11852972706811713603457019)
    ·
      refine ⟨17779459060217570405185529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11852972706811713603457019 17779459060217570405185529)
      ·
        refine ⟨13334594295163177803889147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17779459060217570405185529 13334594295163177803889147)
        ·
          refine ⟨20001891442744766705833721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13334594295163177803889147 20001891442744766705833721)
          ·
            refine ⟨15001418582058575029375291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20001891442744766705833721 15001418582058575029375291)
            ·
              refine ⟨22502127873087862544062937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001418582058575029375291 22502127873087862544062937)
              ·
                refine ⟨16876595904815896908047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22502127873087862544062937 16876595904815896908047203)
                ·
                  refine ⟨25314893857223845362070805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16876595904815896908047203 25314893857223845362070805)
                  ·
                    refine ⟨1186635649557367751347069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25314893857223845362070805 1186635649557367751347069)
                    ·
                      rfl

theorem cell23_6932894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6932894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932894 prefixEnd_6932894 := by exact prefixLift 6932894
  have htrace : WordTrace (prefixWord ++ tailWord_6932894) baseStart_6932894 baseEnd_6932894 := by
    simpa [prefixWord, tailWord_6932894, baseEnd_6932894] using wordTrace_append hprefix tailTrace_6932894
  have hstable : (prefixWord ++ tailWord_6932894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932894).length < 2 ^ (prefixWord ++ tailWord_6932894).sum := by decide
  have hdescent : baseEnd_6932894 < baseStart_6932894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932901 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_6932901 : Nat := 118140960795 + 6932901 * 2 ^ 59
def prefixEnd_6932901 : Nat := 4983230072969 + 3 ^ 40 * 6932901 * 2
def baseEnd_6932901 : Nat := 3559910543036684726653675

theorem tailTrace_6932901 : CollatzResearch.WordTrace tailWord_6932901 prefixEnd_6932901 3559910543036684726653675 := by
  unfold tailWord_6932901
  simp only [CollatzResearch.WordTrace]
  refine ⟨252863673056291197069254557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168575782037527464712836371 252863673056291197069254557)
  ·
    refine ⟨94823877396109198900970459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252863673056291197069254557 94823877396109198900970459)
    ·
      refine ⟨142235816094163798351455689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94823877396109198900970459 142235816094163798351455689)
      ·
        refine ⟨106676862070622848763591767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142235816094163798351455689 106676862070622848763591767)
        ·
          refine ⟨160015293105934273145387651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106676862070622848763591767 160015293105934273145387651)
          ·
            refine ⟨240022939658901409718081477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160015293105934273145387651 240022939658901409718081477)
            ·
              refine ⟨45004301186044014322140277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240022939658901409718081477 45004301186044014322140277)
              ·
                refine ⟨4219153236191626342700651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45004301186044014322140277 4219153236191626342700651)
                ·
                  refine ⟨6328729854287439514050977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219153236191626342700651 6328729854287439514050977)
                  ·
                    refine ⟨4746547390715579635538233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6328729854287439514050977 4746547390715579635538233)
                    ·
                      refine ⟨3559910543036684726653675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746547390715579635538233 3559910543036684726653675)
                      ·
                        rfl

theorem cell23_6932901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_6932901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932901 prefixEnd_6932901 := by exact prefixLift 6932901
  have htrace : WordTrace (prefixWord ++ tailWord_6932901) baseStart_6932901 baseEnd_6932901 := by
    simpa [prefixWord, tailWord_6932901, baseEnd_6932901] using wordTrace_append hprefix tailTrace_6932901
  have hstable : (prefixWord ++ tailWord_6932901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932901).length < 2 ^ (prefixWord ++ tailWord_6932901).sum := by decide
  have hdescent : baseEnd_6932901 < baseStart_6932901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932904 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6932904 : Nat := 118140960795 + 6932904 * 2 ^ 59
def prefixEnd_6932904 : Nat := 4983230072969 + 3 ^ 40 * 6932904 * 2
def baseEnd_6932904 : Nat := 3559912083478648214916161

theorem tailTrace_6932904 : CollatzResearch.WordTrace tailWord_6932904 prefixEnd_6932904 3559912083478648214916161 := by
  unfold tailWord_6932904
  simp only [CollatzResearch.WordTrace]
  refine ⟨126431891237640164290806883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168575854983520219054409177 126431891237640164290806883)
  ·
    refine ⟨189647836856460246436210325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126431891237640164290806883 189647836856460246436210325)
    ·
      refine ⟨8889742352646574051697359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189647836856460246436210325 8889742352646574051697359)
      ·
        refine ⟨13334613528969861077546039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889742352646574051697359 13334613528969861077546039)
        ·
          refine ⟨20001920293454791616319059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13334613528969861077546039 20001920293454791616319059)
          ·
            refine ⟨30002880440182187424478589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20001920293454791616319059 30002880440182187424478589)
            ·
              refine ⟨11251080165068320284179471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30002880440182187424478589 11251080165068320284179471)
              ·
                refine ⟨16876620247602480426269207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11251080165068320284179471 16876620247602480426269207)
                ·
                  refine ⟨25314930371403720639403811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16876620247602480426269207 25314930371403720639403811)
                  ·
                    refine ⟨37972395557105580959105717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25314930371403720639403811 37972395557105580959105717)
                    ·
                      refine ⟨3559912083478648214916161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37972395557105580959105717 3559912083478648214916161)
                      ·
                        rfl

theorem cell23_6932904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6932904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932904 prefixEnd_6932904 := by exact prefixLift 6932904
  have htrace : WordTrace (prefixWord ++ tailWord_6932904) baseStart_6932904 baseEnd_6932904 := by
    simpa [prefixWord, tailWord_6932904, baseEnd_6932904] using wordTrace_append hprefix tailTrace_6932904
  have hstable : (prefixWord ++ tailWord_6932904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932904).length < 2 ^ (prefixWord ++ tailWord_6932904).sum := by decide
  have hdescent : baseEnd_6932904 < baseStart_6932904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6932960 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_6932960 : Nat := 118140960795 + 6932960 * 2 ^ 59
def prefixEnd_6932960 : Nat := 4983230072969 + 3 ^ 40 * 6932960 * 2
def baseEnd_6932960 : Nat := 3559940838395299995815903

theorem tailTrace_6932960 : CollatzResearch.WordTrace tailWord_6932960 prefixEnd_6932960 3559940838395299995815903 := by
  unfold tailWord_6932960
  simp only [CollatzResearch.WordTrace]
  refine ⟨126432912481538725072826167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168577216642051633430434889 126432912481538725072826167)
  ·
    refine ⟨189649368722308087609239251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126432912481538725072826167 189649368722308087609239251)
    ·
      refine ⟨284474053083462131413858877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189649368722308087609239251 284474053083462131413858877)
      ·
        refine ⟨106677769906298299280197079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284474053083462131413858877 106677769906298299280197079)
        ·
          refine ⟨160016654859447448920295619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106677769906298299280197079 160016654859447448920295619)
          ·
            refine ⟨240024982289171173380443429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160016654859447448920295619 240024982289171173380443429)
            ·
              refine ⟨45004684179219595008833143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240024982289171173380443429 45004684179219595008833143)
              ·
                refine ⟨67507026268829392513249715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45004684179219595008833143 67507026268829392513249715)
                ·
                  refine ⟨101260539403244088769874573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67507026268829392513249715 101260539403244088769874573)
                  ·
                    refine ⟨37972702276216533288702965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101260539403244088769874573 37972702276216533288702965)
                    ·
                      refine ⟨3559940838395299995815903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37972702276216533288702965 3559940838395299995815903)
                      ·
                        rfl

theorem cell23_6932960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_6932960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6932960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6932960 prefixEnd_6932960 := by exact prefixLift 6932960
  have htrace : WordTrace (prefixWord ++ tailWord_6932960) baseStart_6932960 baseEnd_6932960 := by
    simpa [prefixWord, tailWord_6932960, baseEnd_6932960] using wordTrace_append hprefix tailTrace_6932960
  have hstable : (prefixWord ++ tailWord_6932960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6932960).length < 2 ^ (prefixWord ++ tailWord_6932960).sum := by decide
  have hdescent : baseEnd_6932960 < baseStart_6932960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6932960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933027 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 4, 5]
def baseStart_6933027 : Nat := 118140960795 + 6933027 * 2 ^ 59
def prefixEnd_6933027 : Nat := 4983230072969 + 3 ^ 40 * 6933027 * 2
def baseEnd_6933027 : Nat := 1186658413866383744559365

theorem tailTrace_6933027 : CollatzResearch.WordTrace tailWord_6933027 prefixEnd_6933027 1186658413866383744559365 := by
  unfold tailWord_6933027
  simp only [CollatzResearch.WordTrace]
  refine ⟨252868268653834720588341335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168578845769223147058894223 252868268653834720588341335)
  ·
    refine ⟨379302402980752080882512003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252868268653834720588341335 379302402980752080882512003)
    ·
      refine ⟨568953604471128121323768005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379302402980752080882512003 568953604471128121323768005)
      ·
        refine ⟨106678800838336522748206501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 568953604471128121323768005 106678800838336522748206501)
        ·
          refine ⟨20002275157188098015288719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106678800838336522748206501 20002275157188098015288719)
          ·
            refine ⟨30003412735782147022933079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20002275157188098015288719 30003412735782147022933079)
            ·
              refine ⟨45005119103673220534399619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30003412735782147022933079 45005119103673220534399619)
              ·
                refine ⟨67507678655509830801599429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45005119103673220534399619 67507678655509830801599429)
                ·
                  refine ⟨12657689747908093275299893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67507678655509830801599429 12657689747908093275299893)
                  ·
                    refine ⟨1186658413866383744559365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12657689747908093275299893 1186658413866383744559365)
                    ·
                      rfl

theorem cell23_6933027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].length) (baseStart_6933027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933027 prefixEnd_6933027 := by exact prefixLift 6933027
  have htrace : WordTrace (prefixWord ++ tailWord_6933027) baseStart_6933027 baseEnd_6933027 := by
    simpa [prefixWord, tailWord_6933027, baseEnd_6933027] using wordTrace_append hprefix tailTrace_6933027
  have hstable : (prefixWord ++ tailWord_6933027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933027).length < 2 ^ (prefixWord ++ tailWord_6933027).sum := by decide
  have hdescent : baseEnd_6933027 < baseStart_6933027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933047 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_6933047 : Nat := 118140960795 + 6933047 * 2 ^ 59
def prefixEnd_6933047 : Nat := 4983230072969 + 3 ^ 40 * 6933047 * 2
def baseEnd_6933047 : Nat := 3559985511212241155428003

theorem tailTrace_6933047 : CollatzResearch.WordTrace tailWord_6933047 prefixEnd_6933047 3559985511212241155428003 := by
  unfold tailWord_6933047
  simp only [CollatzResearch.WordTrace]
  refine ⟨252868998113762264004069395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168579332075841509336046263 252868998113762264004069395)
  ·
    refine ⟨379303497170643396006104093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252868998113762264004069395 379303497170643396006104093)
    ·
      refine ⟨142238811438991273502289035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379303497170643396006104093 142238811438991273502289035)
      ·
        refine ⟨213358217158486910253433553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142238811438991273502289035 213358217158486910253433553)
        ·
          refine ⟨160018662868865182690075165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213358217158486910253433553 160018662868865182690075165)
          ·
            refine ⟨60006998575824443508778187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160018662868865182690075165 60006998575824443508778187)
            ·
              refine ⟨90010497863736665263167281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60006998575824443508778187 90010497863736665263167281)
              ·
                refine ⟨67507873397802498947375461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90010497863736665263167281 67507873397802498947375461)
                ·
                  refine ⟨12657726262087968552632899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67507873397802498947375461 12657726262087968552632899)
                  ·
                    refine ⟨18986589393131952828949349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12657726262087968552632899 18986589393131952828949349)
                    ·
                      refine ⟨3559985511212241155428003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18986589393131952828949349 3559985511212241155428003)
                      ·
                        rfl

theorem cell23_6933047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_6933047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933047 prefixEnd_6933047 := by exact prefixLift 6933047
  have htrace : WordTrace (prefixWord ++ tailWord_6933047) baseStart_6933047 baseEnd_6933047 := by
    simpa [prefixWord, tailWord_6933047, baseEnd_6933047] using wordTrace_append hprefix tailTrace_6933047
  have hstable : (prefixWord ++ tailWord_6933047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933047).length < 2 ^ (prefixWord ++ tailWord_6933047).sum := by decide
  have hdescent : baseEnd_6933047 < baseStart_6933047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933067 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3]
def baseStart_6933067 : Nat := 118140960795 + 6933067 * 2 ^ 59
def prefixEnd_6933067 : Nat := 4983230072969 + 3 ^ 40 * 6933067 * 2
def baseEnd_6933067 : Nat := 3559995780825331077177911

theorem tailTrace_6933067 : CollatzResearch.WordTrace tailWord_6933067 prefixEnd_6933067 3559995780825331077177911 := by
  unfold tailWord_6933067
  simp only [CollatzResearch.WordTrace]
  refine ⟨252869727573689807419797455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168579818382459871613198303 252869727573689807419797455)
  ·
    refine ⟨379304591360534711129696183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252869727573689807419797455 379304591360534711129696183)
    ·
      refine ⟨568956887040802066694544275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379304591360534711129696183 568956887040802066694544275)
      ·
        refine ⟨853435330561203100041816413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568956887040802066694544275 853435330561203100041816413)
        ·
          refine ⟨320038248960451162515681155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853435330561203100041816413 320038248960451162515681155)
          ·
            refine ⟨480057373440676743773521733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320038248960451162515681155 480057373440676743773521733)
            ·
              refine ⟨90010757520126889457535325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480057373440676743773521733 90010757520126889457535325)
              ·
                refine ⟨33754034070047583546575747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90010757520126889457535325 33754034070047583546575747)
                ·
                  refine ⟨50631051105071375319863621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33754034070047583546575747 50631051105071375319863621)
                  ·
                    refine ⟨9493322082200882872474429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50631051105071375319863621 9493322082200882872474429)
                    ·
                      refine ⟨3559995780825331077177911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493322082200882872474429 3559995780825331077177911)
                      ·
                        rfl

theorem cell23_6933067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].length) (baseStart_6933067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933067 prefixEnd_6933067 := by exact prefixLift 6933067
  have htrace : WordTrace (prefixWord ++ tailWord_6933067) baseStart_6933067 baseEnd_6933067 := by
    simpa [prefixWord, tailWord_6933067, baseEnd_6933067] using wordTrace_append hprefix tailTrace_6933067
  have hstable : (prefixWord ++ tailWord_6933067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933067).length < 2 ^ (prefixWord ++ tailWord_6933067).sum := by decide
  have hdescent : baseEnd_6933067 < baseStart_6933067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933091 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 1, 4]
def baseStart_6933091 : Nat := 118140960795 + 6933091 * 2 ^ 59
def prefixEnd_6933091 : Nat := 4983230072969 + 3 ^ 40 * 6933091 * 2
def baseEnd_6933091 : Nat := 1186669368120346327759267

theorem tailTrace_6933091 : CollatzResearch.WordTrace tailWord_6933091 prefixEnd_6933091 1186669368120346327759267 := by
  unfold tailWord_6933091
  simp only [CollatzResearch.WordTrace]
  refine ⟨252870602925602859518671127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168580401950401906345780751 252870602925602859518671127)
  ·
    refine ⟨379305904388404289278006691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252870602925602859518671127 379305904388404289278006691)
    ·
      refine ⟨568958856582606433917010037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379305904388404289278006691 568958856582606433917010037)
      ·
        refine ⟨53339892804619353179719691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 568958856582606433917010037 53339892804619353179719691)
        ·
          refine ⟨80009839206929029769579537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53339892804619353179719691 80009839206929029769579537)
          ·
            refine ⟨60007379405196772327184653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80009839206929029769579537 60007379405196772327184653)
            ·
              refine ⟨22502767276948789622694245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60007379405196772327184653 22502767276948789622694245)
              ·
                refine ⟨4219268864427898054255171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22502767276948789622694245 4219268864427898054255171)
                ·
                  refine ⟨6328903296641847081382757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219268864427898054255171 6328903296641847081382757)
                  ·
                    refine ⟨1186669368120346327759267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6328903296641847081382757 1186669368120346327759267)
                    ·
                      rfl

theorem cell23_6933091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 4].length) (baseStart_6933091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933091 prefixEnd_6933091 := by exact prefixLift 6933091
  have htrace : WordTrace (prefixWord ++ tailWord_6933091) baseStart_6933091 baseEnd_6933091 := by
    simpa [prefixWord, tailWord_6933091, baseEnd_6933091] using wordTrace_append hprefix tailTrace_6933091
  have hstable : (prefixWord ++ tailWord_6933091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933091).length < 2 ^ (prefixWord ++ tailWord_6933091).sum := by decide
  have hdescent : baseEnd_6933091 < baseStart_6933091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933097 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_6933097 : Nat := 118140960795 + 6933097 * 2 ^ 59
def prefixEnd_6933097 : Nat := 4983230072969 + 3 ^ 40 * 6933097 * 2
def baseEnd_6933097 : Nat := 3560011185244965959802773

theorem tailTrace_6933097 : CollatzResearch.WordTrace tailWord_6933097 prefixEnd_6933097 3560011185244965959802773 := by
  unfold tailWord_6933097
  simp only [CollatzResearch.WordTrace]
  refine ⟨252870821763581122543389545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168580547842387415028926363 252870821763581122543389545)
  ·
    refine ⟨189653116322685841907542159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252870821763581122543389545 189653116322685841907542159)
    ·
      refine ⟨284479674484028762861313239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189653116322685841907542159 284479674484028762861313239)
      ·
        refine ⟨426719511726043144291969859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284479674484028762861313239 426719511726043144291969859)
        ·
          refine ⟨640079267589064716437954789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426719511726043144291969859 640079267589064716437954789)
          ·
            refine ⟨120014862672949634332116523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 640079267589064716437954789 120014862672949634332116523)
            ·
              refine ⟨180022294009424451498174785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120014862672949634332116523 180022294009424451498174785)
              ·
                refine ⟨135016720507068338623631089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180022294009424451498174785 135016720507068338623631089)
                ·
                  refine ⟨101262540380301253967723317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135016720507068338623631089 101262540380301253967723317)
                  ·
                    refine ⟨9493363160653242559474061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101262540380301253967723317 9493363160653242559474061)
                    ·
                      refine ⟨3560011185244965959802773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493363160653242559474061 3560011185244965959802773)
                      ·
                        rfl

theorem cell23_6933097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_6933097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933097 prefixEnd_6933097 := by exact prefixLift 6933097
  have htrace : WordTrace (prefixWord ++ tailWord_6933097) baseStart_6933097 baseEnd_6933097 := by
    simpa [prefixWord, tailWord_6933097, baseEnd_6933097] using wordTrace_append hprefix tailTrace_6933097
  have hstable : (prefixWord ++ tailWord_6933097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933097).length < 2 ^ (prefixWord ++ tailWord_6933097).sum := by decide
  have hdescent : baseEnd_6933097 < baseStart_6933097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933148 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6933148 : Nat := 118140960795 + 6933148 * 2 ^ 59
def prefixEnd_6933148 : Nat := 4983230072969 + 3 ^ 40 * 6933148 * 2
def baseEnd_6933148 : Nat := 3560037372758345260265039

theorem tailTrace_6933148 : CollatzResearch.WordTrace tailWord_6933148 prefixEnd_6933148 3560037372758345260265039 := by
  unfold tailWord_6933148
  simp only [CollatzResearch.WordTrace]
  refine ⟨126436340943198179126748049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168581787924264238835664065 126436340943198179126748049)
  ·
    refine ⟨94827255707398634345061037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126436340943198179126748049 94827255707398634345061037)
    ·
      refine ⟨35560220890274487879397889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94827255707398634345061037 35560220890274487879397889)
      ·
        refine ⟨26670165667705865909548417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35560220890274487879397889 26670165667705865909548417)
        ·
          refine ⟨20002624250779399432161313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26670165667705865909548417 20002624250779399432161313)
          ·
            refine ⟨15001968188084549574120985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20002624250779399432161313 15001968188084549574120985)
            ·
              refine ⟨11251476141063412180590739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15001968188084549574120985 11251476141063412180590739)
              ·
                refine ⟨16877214211595118270886109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11251476141063412180590739 16877214211595118270886109)
                ·
                  refine ⟨6328955329348169351582291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16877214211595118270886109 6328955329348169351582291)
                  ·
                    refine ⟨9493432994022254027373437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328955329348169351582291 9493432994022254027373437)
                    ·
                      refine ⟨3560037372758345260265039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493432994022254027373437 3560037372758345260265039)
                      ·
                        rfl

theorem cell23_6933148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6933148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933148 prefixEnd_6933148 := by exact prefixLift 6933148
  have htrace : WordTrace (prefixWord ++ tailWord_6933148) baseStart_6933148 baseEnd_6933148 := by
    simpa [prefixWord, tailWord_6933148, baseEnd_6933148] using wordTrace_append hprefix tailTrace_6933148
  have hstable : (prefixWord ++ tailWord_6933148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933148).length < 2 ^ (prefixWord ++ tailWord_6933148).sum := by decide
  have hdescent : baseEnd_6933148 < baseStart_6933148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933171 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 4]
def baseStart_6933171 : Nat := 118140960795 + 6933171 * 2 ^ 59
def prefixEnd_6933171 : Nat := 4983230072969 + 3 ^ 40 * 6933171 * 2
def baseEnd_6933171 : Nat := 3560049182813398670277433

theorem tailTrace_6933171 : CollatzResearch.WordTrace tailWord_6933171 prefixEnd_6933171 3560049182813398670277433 := by
  unfold tailWord_6933171
  simp only [CollatzResearch.WordTrace]
  refine ⟨252873520765313033181583367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168582347176875355454388911 252873520765313033181583367)
  ·
    refine ⟨379310281147969549772375051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252873520765313033181583367 379310281147969549772375051)
    ·
      refine ⟨568965421721954324658562577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379310281147969549772375051 568965421721954324658562577)
      ·
        refine ⟨426724066291465743493921933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568965421721954324658562577 426724066291465743493921933)
        ·
          refine ⟨160021524859299653810220725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426724066291465743493921933 160021524859299653810220725)
          ·
            refine ⟨15002017955559342544708193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160021524859299653810220725 15002017955559342544708193)
            ·
              refine ⟨11251513466669506908531145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002017955559342544708193 11251513466669506908531145)
              ·
                refine ⟨8438635100002130181398359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11251513466669506908531145 8438635100002130181398359)
                ·
                  refine ⟨12657952650003195272097539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8438635100002130181398359 12657952650003195272097539)
                  ·
                    refine ⟨18986928975004792908146309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12657952650003195272097539 18986928975004792908146309)
                    ·
                      refine ⟨3560049182813398670277433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18986928975004792908146309 3560049182813398670277433)
                      ·
                        rfl

theorem cell23_6933171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_6933171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933171 prefixEnd_6933171 := by exact prefixLift 6933171
  have htrace : WordTrace (prefixWord ++ tailWord_6933171) baseStart_6933171 baseEnd_6933171 := by
    simpa [prefixWord, tailWord_6933171, baseEnd_6933171] using wordTrace_append hprefix tailTrace_6933171
  have hstable : (prefixWord ++ tailWord_6933171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933171).length < 2 ^ (prefixWord ++ tailWord_6933171).sum := by decide
  have hdescent : baseEnd_6933171 < baseStart_6933171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933194 : List Nat := [3, 1, 2, 1, 4, 3, 9]
def baseStart_6933194 : Nat := 118140960795 + 6933194 * 2 ^ 59
def prefixEnd_6933194 : Nat := 4983230072969 + 3 ^ 40 * 6933194 * 2
def baseEnd_6933194 : Nat := 43951370282326568892467

theorem tailTrace_6933194 : CollatzResearch.WordTrace tailWord_6933194 prefixEnd_6933194 43951370282326568892467 := by
  unfold tailWord_6933194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63218589911057427027417659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168582906429486472073113757 63218589911057427027417659)
  ·
    refine ⟨94827884866586140541126489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63218589911057427027417659 94827884866586140541126489)
    ·
      refine ⟨71120913649939605405844867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94827884866586140541126489 71120913649939605405844867)
      ·
        refine ⟨106681370474909408108767301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71120913649939605405844867 106681370474909408108767301)
        ·
          refine ⟨20002756964045514020393869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106681370474909408108767301 20002756964045514020393869)
          ·
            refine ⟨7501033861517067757647701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20002756964045514020393869 7501033861517067757647701)
            ·
              refine ⟨43951370282326568892467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7501033861517067757647701 43951370282326568892467)
              ·
                rfl

theorem cell23_6933194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 9].length) (baseStart_6933194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933194 prefixEnd_6933194 := by exact prefixLift 6933194
  have htrace : WordTrace (prefixWord ++ tailWord_6933194) baseStart_6933194 baseEnd_6933194 := by
    simpa [prefixWord, tailWord_6933194, baseEnd_6933194] using wordTrace_append hprefix tailTrace_6933194
  have hstable : (prefixWord ++ tailWord_6933194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933194).length < 2 ^ (prefixWord ++ tailWord_6933194).sum := by decide
  have hdescent : baseEnd_6933194 < baseStart_6933194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933227 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_6933227 : Nat := 118140960795 + 6933227 * 2 ^ 59
def prefixEnd_6933227 : Nat := 4983230072969 + 3 ^ 40 * 6933227 * 2
def baseEnd_6933227 : Nat := 3560077937730050451177175

theorem tailTrace_6933227 : CollatzResearch.WordTrace tailWord_6933227 prefixEnd_6933227 3560077937730050451177175 := by
  unfold tailWord_6933227
  simp only [CollatzResearch.WordTrace]
  refine ⟨252875563253110154745621935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168583708835406769830414623 252875563253110154745621935)
  ·
    refine ⟨379313344879665232118432903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252875563253110154745621935 379313344879665232118432903)
    ·
      refine ⟨568970017319497848177649355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379313344879665232118432903 568970017319497848177649355)
      ·
        refine ⟨853455025979246772266474033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568970017319497848177649355 853455025979246772266474033)
        ·
          refine ⟨640091269484435079199855525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853455025979246772266474033 640091269484435079199855525)
          ·
            refine ⟨120017113028331577349972911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 640091269484435079199855525 120017113028331577349972911)
            ·
              refine ⟨180025669542497366024959367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120017113028331577349972911 180025669542497366024959367)
              ·
                refine ⟨270038504313746049037439051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180025669542497366024959367 270038504313746049037439051)
                ·
                  refine ⟨405057756470619073556158577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270038504313746049037439051 405057756470619073556158577)
                  ·
                    refine ⟨303793317352964305167118933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405057756470619073556158577 303793317352964305167118933)
                    ·
                      refine ⟨3560077937730050451177175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 303793317352964305167118933 3560077937730050451177175)
                      ·
                        rfl

theorem cell23_6933227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_6933227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933227 prefixEnd_6933227 := by exact prefixLift 6933227
  have htrace : WordTrace (prefixWord ++ tailWord_6933227) baseStart_6933227 baseEnd_6933227 := by
    simpa [prefixWord, tailWord_6933227, baseEnd_6933227] using wordTrace_append hprefix tailTrace_6933227
  have hstable : (prefixWord ++ tailWord_6933227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933227).length < 2 ^ (prefixWord ++ tailWord_6933227).sum := by decide
  have hdescent : baseEnd_6933227 < baseStart_6933227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933255 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6933255 : Nat := 118140960795 + 6933255 * 2 ^ 59
def prefixEnd_6933255 : Nat := 4983230072969 + 3 ^ 40 * 6933255 * 2
def baseEnd_6933255 : Nat := 3560092315188376341627047

theorem tailTrace_6933255 : CollatzResearch.WordTrace tailWord_6933255 prefixEnd_6933255 3560092315188376341627047 := by
  unfold tailWord_6933255
  simp only [CollatzResearch.WordTrace]
  refine ⟨252876584497008715527641219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168584389664672477018427479 252876584497008715527641219)
  ·
    refine ⟨379314876745513073291461829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252876584497008715527641219 379314876745513073291461829)
    ·
      refine ⟨71121539389783701242149093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379314876745513073291461829 71121539389783701242149093)
      ·
        refine ⟨13335288635584443982902955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71121539389783701242149093 13335288635584443982902955)
        ·
          refine ⟨20002932953376665974354433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335288635584443982902955 20002932953376665974354433)
          ·
            refine ⟨15002199715032499480765825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20002932953376665974354433 15002199715032499480765825)
            ·
              refine ⟨11251649786274374610574369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002199715032499480765825 11251649786274374610574369)
              ·
                refine ⟨8438737339705780957930777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11251649786274374610574369 8438737339705780957930777)
                ·
                  refine ⟨6329053004779335718448083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438737339705780957930777 6329053004779335718448083)
                  ·
                    refine ⟨9493579507169003577672125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329053004779335718448083 9493579507169003577672125)
                    ·
                      refine ⟨3560092315188376341627047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493579507169003577672125 3560092315188376341627047)
                      ·
                        rfl

theorem cell23_6933255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6933255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933255 prefixEnd_6933255 := by exact prefixLift 6933255
  have htrace : WordTrace (prefixWord ++ tailWord_6933255) baseStart_6933255 baseEnd_6933255 := by
    simpa [prefixWord, tailWord_6933255, baseEnd_6933255] using wordTrace_append hprefix tailTrace_6933255
  have hstable : (prefixWord ++ tailWord_6933255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933255).length < 2 ^ (prefixWord ++ tailWord_6933255).sum := by decide
  have hdescent : baseEnd_6933255 < baseStart_6933255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933271 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 6]
def baseStart_6933271 : Nat := 118140960795 + 6933271 * 2 ^ 59
def prefixEnd_6933271 : Nat := 4983230072969 + 3 ^ 40 * 6933271 * 2
def baseEnd_6933271 : Nat := 1186700176959616093008991

theorem tailTrace_6933271 : CollatzResearch.WordTrace tailWord_6933271 prefixEnd_6933271 1186700176959616093008991 := by
  unfold tailWord_6933271
  simp only [CollatzResearch.WordTrace]
  refine ⟨252877168064950750260223667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168584778709967166840149111 252877168064950750260223667)
  ·
    refine ⟨379315752097426125390335501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252877168064950750260223667 379315752097426125390335501)
    ·
      refine ⟨142243407036534797021375813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379315752097426125390335501 142243407036534797021375813)
      ·
        refine ⟨26670638819350274441507965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142243407036534797021375813 26670638819350274441507965)
        ·
          refine ⟨10001489557256352915565487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26670638819350274441507965 10001489557256352915565487)
          ·
            refine ⟨15002234335884529373348231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001489557256352915565487 15002234335884529373348231)
            ·
              refine ⟨22503351503826794060022347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15002234335884529373348231 22503351503826794060022347)
              ·
                refine ⟨33755027255740191090033521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22503351503826794060022347 33755027255740191090033521)
                ·
                  refine ⟨25316270441805143317525141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33755027255740191090033521 25316270441805143317525141)
                  ·
                    refine ⟨1186700176959616093008991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25316270441805143317525141 1186700176959616093008991)
                    ·
                      rfl

theorem cell23_6933271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_6933271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933271 prefixEnd_6933271 := by exact prefixLift 6933271
  have htrace : WordTrace (prefixWord ++ tailWord_6933271) baseStart_6933271 baseEnd_6933271 := by
    simpa [prefixWord, tailWord_6933271, baseEnd_6933271] using wordTrace_append hprefix tailTrace_6933271
  have hstable : (prefixWord ++ tailWord_6933271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933271).length < 2 ^ (prefixWord ++ tailWord_6933271).sum := by decide
  have hdescent : baseEnd_6933271 < baseStart_6933271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933311 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_6933311 : Nat := 118140960795 + 6933311 * 2 ^ 59
def prefixEnd_6933311 : Nat := 4983230072969 + 3 ^ 40 * 6933311 * 2
def baseEnd_6933311 : Nat := 3560121070105028122526789

theorem tailTrace_6933311 : CollatzResearch.WordTrace tailWord_6933311 prefixEnd_6933311 3560121070105028122526789 := by
  unfold tailWord_6933311
  simp only [CollatzResearch.WordTrace]
  refine ⟨252878626984805837091679787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168585751323203891394453191 252878626984805837091679787)
  ·
    refine ⟨379317940477208755637519681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252878626984805837091679787 379317940477208755637519681)
    ·
      refine ⟨284488455357906566728139761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379317940477208755637519681 284488455357906566728139761)
      ·
        refine ⟨213366341518429925046104821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284488455357906566728139761 213366341518429925046104821)
        ·
          refine ⟨20003094517352805473072327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213366341518429925046104821 20003094517352805473072327)
          ·
            refine ⟨30004641776029208209608491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20003094517352805473072327 30004641776029208209608491)
            ·
              refine ⟨45006962664043812314412737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30004641776029208209608491 45006962664043812314412737)
              ·
                refine ⟨33755221998032859235809553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45006962664043812314412737 33755221998032859235809553)
                ·
                  refine ⟨25316416498524644426857165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33755221998032859235809553 25316416498524644426857165)
                  ·
                    refine ⟨9493656186946741660071437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25316416498524644426857165 9493656186946741660071437)
                    ·
                      refine ⟨3560121070105028122526789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493656186946741660071437 3560121070105028122526789)
                      ·
                        rfl

theorem cell23_6933311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_6933311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933311 prefixEnd_6933311 := by exact prefixLift 6933311
  have htrace : WordTrace (prefixWord ++ tailWord_6933311) baseStart_6933311 baseEnd_6933311 := by
    simpa [prefixWord, tailWord_6933311, baseEnd_6933311] using wordTrace_append hprefix tailTrace_6933311
  have hstable : (prefixWord ++ tailWord_6933311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933311).length < 2 ^ (prefixWord ++ tailWord_6933311).sum := by decide
  have hdescent : baseEnd_6933311 < baseStart_6933311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933344 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_6933344 : Nat := 118140960795 + 6933344 * 2 ^ 59
def prefixEnd_6933344 : Nat := 4983230072969 + 3 ^ 40 * 6933344 * 2
def baseEnd_6933344 : Nat := 1186712671655542164471379

theorem tailTrace_6933344 : CollatzResearch.WordTrace tailWord_6933344 prefixEnd_6933344 1186712671655542164471379 := by
  unfold tailWord_6933344
  simp only [CollatzResearch.WordTrace]
  refine ⟨126439915296843141863815543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168586553729124189151754057 126439915296843141863815543)
  ·
    refine ⟨189659872945264712795723315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126439915296843141863815543 189659872945264712795723315)
    ·
      refine ⟨284489809417897069193584973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189659872945264712795723315 284489809417897069193584973)
      ·
        refine ⟨106683678531711400947594365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284489809417897069193584973 106683678531711400947594365)
        ·
          refine ⟨40006379449391775355347887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106683678531711400947594365 40006379449391775355347887)
          ·
            refine ⟨60009569174087663033021831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40006379449391775355347887 60009569174087663033021831)
            ·
              refine ⟨90014353761131494549532747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60009569174087663033021831 90014353761131494549532747)
              ·
                refine ⟨135021530641697241824299121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90014353761131494549532747 135021530641697241824299121)
                ·
                  refine ⟨101266147981272931368224341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135021530641697241824299121 101266147981272931368224341)
                  ·
                    refine ⟨1186712671655542164471379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101266147981272931368224341 1186712671655542164471379)
                    ·
                      rfl

theorem cell23_6933344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_6933344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933344 prefixEnd_6933344 := by exact prefixLift 6933344
  have htrace : WordTrace (prefixWord ++ tailWord_6933344) baseStart_6933344 baseEnd_6933344 := by
    simpa [prefixWord, tailWord_6933344, baseEnd_6933344] using wordTrace_append hprefix tailTrace_6933344
  have hstable : (prefixWord ++ tailWord_6933344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933344).length < 2 ^ (prefixWord ++ tailWord_6933344).sum := by decide
  have hdescent : baseEnd_6933344 < baseStart_6933344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933351 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6933351 : Nat := 118140960795 + 6933351 * 2 ^ 59
def prefixEnd_6933351 : Nat := 4983230072969 + 3 ^ 40 * 6933351 * 2
def baseEnd_6933351 : Nat := 3560141609331207966026605

theorem tailTrace_6933351 : CollatzResearch.WordTrace tailWord_6933351 prefixEnd_6933351 3560141609331207966026605 := by
  unfold tailWord_6933351
  simp only [CollatzResearch.WordTrace]
  refine ⟨252880085904660923923135907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168586723936440615948757271 252880085904660923923135907)
  ·
    refine ⟨379320128856991385884703861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252880085904660923923135907 379320128856991385884703861)
    ·
      refine ⟨35561262080342942426690987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379320128856991385884703861 35561262080342942426690987)
      ·
        refine ⟨53341893120514413640036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35561262080342942426690987 53341893120514413640036481)
        ·
          refine ⟨40006419840385810230027361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53341893120514413640036481 40006419840385810230027361)
          ·
            refine ⟨30004814880289357672520521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40006419840385810230027361 30004814880289357672520521)
            ·
              refine ⟨22503611160217018254390391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30004814880289357672520521 22503611160217018254390391)
              ·
                refine ⟨33755416740325527381585587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22503611160217018254390391 33755416740325527381585587)
                ·
                  refine ⟨50633125110488291072378381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33755416740325527381585587 50633125110488291072378381)
                  ·
                    refine ⟨18987421916433109152141893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50633125110488291072378381 18987421916433109152141893)
                    ·
                      refine ⟨3560141609331207966026605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18987421916433109152141893 3560141609331207966026605)
                      ·
                        rfl

theorem cell23_6933351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6933351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933351 prefixEnd_6933351 := by exact prefixLift 6933351
  have htrace : WordTrace (prefixWord ++ tailWord_6933351) baseStart_6933351 baseEnd_6933351 := by
    simpa [prefixWord, tailWord_6933351, baseEnd_6933351] using wordTrace_append hprefix tailTrace_6933351
  have hstable : (prefixWord ++ tailWord_6933351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933351).length < 2 ^ (prefixWord ++ tailWord_6933351).sum := by decide
  have hdescent : baseEnd_6933351 < baseStart_6933351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933371 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3]
def baseStart_6933371 : Nat := 118140960795 + 6933371 * 2 ^ 59
def prefixEnd_6933371 : Nat := 4983230072969 + 3 ^ 40 * 6933371 * 2
def baseEnd_6933371 : Nat := 3560151878944297887776513

theorem tailTrace_6933371 : CollatzResearch.WordTrace tailWord_6933371 prefixEnd_6933371 3560151878944297887776513 := by
  unfold tailWord_6933371
  simp only [CollatzResearch.WordTrace]
  refine ⟨252880815364588467338863967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168587210243058978225909311 252880815364588467338863967)
  ·
    refine ⟨379321223046882701008295951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252880815364588467338863967 379321223046882701008295951)
    ·
      refine ⟨568981834570324051512443927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379321223046882701008295951 568981834570324051512443927)
      ·
        refine ⟨853472751855486077268665891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568981834570324051512443927 853472751855486077268665891)
        ·
          refine ⟨1280209127783229115902998837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853472751855486077268665891 1280209127783229115902998837)
          ·
            refine ⟨120019605729677729615906141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1280209127783229115902998837 120019605729677729615906141)
            ·
              refine ⟨45007352148629148605964803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120019605729677729615906141 45007352148629148605964803)
              ·
                refine ⟨67511028222943722908947205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45007352148629148605964803 67511028222943722908947205)
                ·
                  refine ⟨12658317791801948045427601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67511028222943722908947205 12658317791801948045427601)
                  ·
                    refine ⟨9493738343851461034070701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12658317791801948045427601 9493738343851461034070701)
                    ·
                      refine ⟨3560151878944297887776513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493738343851461034070701 3560151878944297887776513)
                      ·
                        rfl

theorem cell23_6933371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].length) (baseStart_6933371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933371 prefixEnd_6933371 := by exact prefixLift 6933371
  have htrace : WordTrace (prefixWord ++ tailWord_6933371) baseStart_6933371 baseEnd_6933371 := by
    simpa [prefixWord, tailWord_6933371, baseEnd_6933371] using wordTrace_append hprefix tailTrace_6933371
  have hstable : (prefixWord ++ tailWord_6933371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933371).length < 2 ^ (prefixWord ++ tailWord_6933371).sum := by decide
  have hdescent : baseEnd_6933371 < baseStart_6933371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933446 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6933446 : Nat := 118140960795 + 6933446 * 2 ^ 59
def prefixEnd_6933446 : Nat := 4983230072969 + 3 ^ 40 * 6933446 * 2
def baseEnd_6933446 : Nat := 1186730129997795031446223

theorem tailTrace_6933446 : CollatzResearch.WordTrace tailWord_6933446 prefixEnd_6933446 1186730129997795031446223 := by
  unfold tailWord_6933446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902610963728648598370131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168589033892877836765229461 7902610963728648598370131)
  ·
    refine ⟨11853916445592972897555197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7902610963728648598370131 11853916445592972897555197)
    ·
      refine ⟨4445218667097364836583199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11853916445592972897555197 4445218667097364836583199)
      ·
        refine ⟨6667828000646047254874799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445218667097364836583199 6667828000646047254874799)
        ·
          refine ⟨10001742000969070882312199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667828000646047254874799 10001742000969070882312199)
          ·
            refine ⟨15002613001453606323468299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001742000969070882312199 15002613001453606323468299)
            ·
              refine ⟨22503919502180409485202449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15002613001453606323468299 22503919502180409485202449)
              ·
                refine ⟨16877939626635307113901837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22503919502180409485202449 16877939626635307113901837)
                ·
                  refine ⟨6329227359988240167713189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16877939626635307113901837 6329227359988240167713189)
                  ·
                    refine ⟨1186730129997795031446223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329227359988240167713189 1186730129997795031446223)
                    ·
                      rfl

theorem cell23_6933446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6933446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933446 prefixEnd_6933446 := by exact prefixLift 6933446
  have htrace : WordTrace (prefixWord ++ tailWord_6933446) baseStart_6933446 baseEnd_6933446 := by
    simpa [prefixWord, tailWord_6933446, baseEnd_6933446] using wordTrace_append hprefix tailTrace_6933446
  have hstable : (prefixWord ++ tailWord_6933446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933446).length < 2 ^ (prefixWord ++ tailWord_6933446).sum := by decide
  have hdescent : baseEnd_6933446 < baseStart_6933446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933451 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 6]
def baseStart_6933451 : Nat := 118140960795 + 6933451 * 2 ^ 59
def prefixEnd_6933451 : Nat := 4983230072969 + 3 ^ 40 * 6933451 * 2
def baseEnd_6933451 : Nat := 1186730985798885858258715

theorem tailTrace_6933451 : CollatzResearch.WordTrace tailWord_6933451 prefixEnd_6933451 1186730985798885858258715 := by
  unfold tailWord_6933451
  simp only [CollatzResearch.WordTrace]
  refine ⟨252883733204298641001776207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168589155469532427334517471 252883733204298641001776207)
  ·
    refine ⟨379325599806447961502664311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252883733204298641001776207 379325599806447961502664311)
    ·
      refine ⟨568988399709671942253996467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379325599806447961502664311 568988399709671942253996467)
      ·
        refine ⟨853482599564507913380994701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568988399709671942253996467 853482599564507913380994701)
        ·
          refine ⟨320055974836690467517873013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853482599564507913380994701 320055974836690467517873013)
          ·
            refine ⟨30005247640939731329800595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320055974836690467517873013 30005247640939731329800595)
            ·
              refine ⟨45007871461409596994700893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30005247640939731329800595 45007871461409596994700893)
              ·
                refine ⟨16877951798028598873012835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45007871461409596994700893 16877951798028598873012835)
                ·
                  refine ⟨25316927697042898309519253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16877951798028598873012835 25316927697042898309519253)
                  ·
                    refine ⟨1186730985798885858258715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25316927697042898309519253 1186730985798885858258715)
                    ·
                      rfl

theorem cell23_6933451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_6933451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933451 prefixEnd_6933451 := by exact prefixLift 6933451
  have htrace : WordTrace (prefixWord ++ tailWord_6933451) baseStart_6933451 baseEnd_6933451 := by
    simpa [prefixWord, tailWord_6933451, baseEnd_6933451] using wordTrace_append hprefix tailTrace_6933451
  have hstable : (prefixWord ++ tailWord_6933451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933451).length < 2 ^ (prefixWord ++ tailWord_6933451).sum := by decide
  have hdescent : baseEnd_6933451 < baseStart_6933451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933462 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6933462 : Nat := 118140960795 + 6933462 * 2 ^ 59
def prefixEnd_6933462 : Nat := 4983230072969 + 3 ^ 40 * 6933462 * 2
def baseEnd_6933462 : Nat := 3560198605683857031738595

theorem tailTrace_6933462 : CollatzResearch.WordTrace tailWord_6933462 prefixEnd_6933462 3560198605683857031738595 := by
  unfold tailWord_6933462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805258400453674367526665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168589422938172526586951093 15805258400453674367526665)
  ·
    refine ⟨11853943800340255775644999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805258400453674367526665 11853943800340255775644999)
    ·
      refine ⟨17780915700510383663467499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11853943800340255775644999 17780915700510383663467499)
      ·
        refine ⟨26671373550765575495201249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17780915700510383663467499 26671373550765575495201249)
        ·
          refine ⟨20003530163074181621400937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26671373550765575495201249 20003530163074181621400937)
          ·
            refine ⟨15002647622305636216050703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20003530163074181621400937 15002647622305636216050703)
            ·
              refine ⟨22503971433458454324076055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15002647622305636216050703 22503971433458454324076055)
              ·
                refine ⟨33755957150187681486114083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22503971433458454324076055 33755957150187681486114083)
                ·
                  refine ⟨50633935725281522229171125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33755957150187681486114083 50633935725281522229171125)
                  ·
                    refine ⟨4746931474245142708984793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50633935725281522229171125 4746931474245142708984793)
                    ·
                      refine ⟨3560198605683857031738595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746931474245142708984793 3560198605683857031738595)
                      ·
                        rfl

theorem cell23_6933462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6933462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933462 prefixEnd_6933462 := by exact prefixLift 6933462
  have htrace : WordTrace (prefixWord ++ tailWord_6933462) baseStart_6933462 baseEnd_6933462 := by
    simpa [prefixWord, tailWord_6933462, baseEnd_6933462] using wordTrace_append hprefix tailTrace_6933462
  have hstable : (prefixWord ++ tailWord_6933462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933462).length < 2 ^ (prefixWord ++ tailWord_6933462).sum := by decide
  have hdescent : baseEnd_6933462 < baseStart_6933462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933469 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6933469 : Nat := 118140960795 + 6933469 * 2 ^ 59
def prefixEnd_6933469 : Nat := 4983230072969 + 3 ^ 40 * 6933469 * 2
def baseEnd_6933469 : Nat := 3560202200048438504351063

theorem tailTrace_6933469 : CollatzResearch.WordTrace tailWord_6933469 prefixEnd_6933469 3560202200048438504351063 := by
  unfold tailWord_6933469
  simp only [CollatzResearch.WordTrace]
  refine ⟨252884389718233430075931461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168589593145488953383954307 252884389718233430075931461)
  ·
    refine ⟨47415823072168768139237149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252884389718233430075931461 47415823072168768139237149)
    ·
      refine ⟨17780933652063288052213931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47415823072168768139237149 17780933652063288052213931)
      ·
        refine ⟨26671400478094932078320897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17780933652063288052213931 26671400478094932078320897)
        ·
          refine ⟨20003550358571199058740673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26671400478094932078320897 20003550358571199058740673)
          ·
            refine ⟨15002662768928399294055505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20003550358571199058740673 15002662768928399294055505)
            ·
              refine ⟨11251997076696299470541629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002662768928399294055505 11251997076696299470541629)
              ·
                refine ⟨4219498903761112301453111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11251997076696299470541629 4219498903761112301453111)
                ·
                  refine ⟨6329248355641668452179667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219498903761112301453111 6329248355641668452179667)
                  ·
                    refine ⟨9493872533462502678269501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329248355641668452179667 9493872533462502678269501)
                    ·
                      refine ⟨3560202200048438504351063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493872533462502678269501 3560202200048438504351063)
                      ·
                        rfl

theorem cell23_6933469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6933469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933469 prefixEnd_6933469 := by exact prefixLift 6933469
  have htrace : WordTrace (prefixWord ++ tailWord_6933469) baseStart_6933469 baseEnd_6933469 := by
    simpa [prefixWord, tailWord_6933469, baseEnd_6933469] using wordTrace_append hprefix tailTrace_6933469
  have hstable : (prefixWord ++ tailWord_6933469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933469).length < 2 ^ (prefixWord ++ tailWord_6933469).sum := by decide
  have hdescent : baseEnd_6933469 < baseStart_6933469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933475 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6933475 : Nat := 118140960795 + 6933475 * 2 ^ 59
def prefixEnd_6933475 : Nat := 4983230072969 + 3 ^ 40 * 6933475 * 2
def baseEnd_6933475 : Nat := 3560205280932365480876035

theorem tailTrace_6933475 : CollatzResearch.WordTrace tailWord_6933475 prefixEnd_6933475 3560205280932365480876035 := by
  unfold tailWord_6933475
  simp only [CollatzResearch.WordTrace]
  refine ⟨252884608556211693100649879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168589739037474462067099919 252884608556211693100649879)
  ·
    refine ⟨379326912834317539650974819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252884608556211693100649879 379326912834317539650974819)
    ·
      refine ⟨568990369251476309476462229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379326912834317539650974819 568990369251476309476462229)
      ·
        refine ⟨26671423558662952006709167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 568990369251476309476462229 26671423558662952006709167)
        ·
          refine ⟨40007135337994428010063751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26671423558662952006709167 40007135337994428010063751)
          ·
            refine ⟨60010703006991642015095627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40007135337994428010063751 60010703006991642015095627)
            ·
              refine ⟨90016054510487463022643441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60010703006991642015095627 90016054510487463022643441)
              ·
                refine ⟨67512040882865597266982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90016054510487463022643441 67512040882865597266982581)
                ·
                  refine ⟨6329253832768649743779617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67512040882865597266982581 6329253832768649743779617)
                  ·
                    refine ⟨4746940374576487307834713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329253832768649743779617 4746940374576487307834713)
                    ·
                      refine ⟨3560205280932365480876035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746940374576487307834713 3560205280932365480876035)
                      ·
                        rfl

theorem cell23_6933475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6933475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933475 prefixEnd_6933475 := by exact prefixLift 6933475
  have htrace : WordTrace (prefixWord ++ tailWord_6933475) baseStart_6933475 baseEnd_6933475 := by
    simpa [prefixWord, tailWord_6933475, baseEnd_6933475] using wordTrace_append hprefix tailTrace_6933475
  have hstable : (prefixWord ++ tailWord_6933475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933475).length < 2 ^ (prefixWord ++ tailWord_6933475).sum := by decide
  have hdescent : baseEnd_6933475 < baseStart_6933475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933491 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3]
def baseStart_6933491 : Nat := 118140960795 + 6933491 * 2 ^ 59
def prefixEnd_6933491 : Nat := 4983230072969 + 3 ^ 40 * 6933491 * 2
def baseEnd_6933491 : Nat := 3560213496622837418275961

theorem tailTrace_6933491 : CollatzResearch.WordTrace tailWord_6933491 prefixEnd_6933491 3560213496622837418275961 := by
  unfold tailWord_6933491
  simp only [CollatzResearch.WordTrace]
  refine ⟨252885192124153727833232327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168590128082769151888821551 252885192124153727833232327)
  ·
    refine ⟨379327788186230591749848491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252885192124153727833232327 379327788186230591749848491)
    ·
      refine ⟨568991682279345887624772737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379327788186230591749848491 568991682279345887624772737)
      ·
        refine ⟨426743761709509415718579553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568991682279345887624772737 426743761709509415718579553)
        ·
          refine ⟨320057821282132061788934665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426743761709509415718579553 320057821282132061788934665)
          ·
            refine ⟨240043365961599046341700999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320057821282132061788934665 240043365961599046341700999)
            ·
              refine ⟨360065048942398569512551499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240043365961599046341700999 360065048942398569512551499)
              ·
                refine ⟨540097573413597854268827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360065048942398569512551499 540097573413597854268827249)
                ·
                  refine ⟨405073180060198390701620437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540097573413597854268827249 405073180060198390701620437)
                  ·
                    refine ⟨9493902657660899782069229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 405073180060198390701620437 9493902657660899782069229)
                    ·
                      refine ⟨3560213496622837418275961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493902657660899782069229 3560213496622837418275961)
                      ·
                        rfl

theorem cell23_6933491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_6933491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933491 prefixEnd_6933491 := by exact prefixLift 6933491
  have htrace : WordTrace (prefixWord ++ tailWord_6933491) baseStart_6933491 baseEnd_6933491 := by
    simpa [prefixWord, tailWord_6933491, baseEnd_6933491] using wordTrace_append hprefix tailTrace_6933491
  have hstable : (prefixWord ++ tailWord_6933491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933491).length < 2 ^ (prefixWord ++ tailWord_6933491).sum := by decide
  have hdescent : baseEnd_6933491 < baseStart_6933491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933502 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6933502 : Nat := 118140960795 + 6933502 * 2 ^ 59
def prefixEnd_6933502 : Nat := 4983230072969 + 3 ^ 40 * 6933502 * 2
def baseEnd_6933502 : Nat := 1186739714970012291746137

theorem tailTrace_6933502 : CollatzResearch.WordTrace tailWord_6933502 prefixEnd_6933502 1186739714970012291746137 := by
  unfold tailWord_6933502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31610699165889234588985345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168590395551409251141255173 31610699165889234588985345)
  ·
    refine ⟨23708024374416925941739009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31610699165889234588985345 23708024374416925941739009)
    ·
      refine ⟨17781018280812694456304257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23708024374416925941739009 17781018280812694456304257)
      ·
        refine ⟨13335763710609520842228193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17781018280812694456304257 13335763710609520842228193)
        ·
          refine ⟨10001822782957140631671145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13335763710609520842228193 10001822782957140631671145)
          ·
            refine ⟨7501367087217855473753359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001822782957140631671145 7501367087217855473753359)
            ·
              refine ⟨11252050630826783210630039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501367087217855473753359 11252050630826783210630039)
              ·
                refine ⟨16878075946240174815945059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252050630826783210630039 16878075946240174815945059)
                ·
                  refine ⟨25317113919360262223917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16878075946240174815945059 25317113919360262223917589)
                  ·
                    refine ⟨1186739714970012291746137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25317113919360262223917589 1186739714970012291746137)
                    ·
                      rfl

theorem cell23_6933502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6933502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933502 prefixEnd_6933502 := by exact prefixLift 6933502
  have htrace : WordTrace (prefixWord ++ tailWord_6933502) baseStart_6933502 baseEnd_6933502 := by
    simpa [prefixWord, tailWord_6933502, baseEnd_6933502] using wordTrace_append hprefix tailTrace_6933502
  have hstable : (prefixWord ++ tailWord_6933502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933502).length < 2 ^ (prefixWord ++ tailWord_6933502).sum := by decide
  have hdescent : baseEnd_6933502 < baseStart_6933502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933505 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_6933505 : Nat := 118140960795 + 6933505 * 2 ^ 59
def prefixEnd_6933505 : Nat := 4983230072969 + 3 ^ 40 * 6933505 * 2
def baseEnd_6933505 : Nat := 3560220685352000363500897

theorem tailTrace_6933505 : CollatzResearch.WordTrace tailWord_6933505 prefixEnd_6933505 3560220685352000363500897 := by
  unfold tailWord_6933505
  simp only [CollatzResearch.WordTrace]
  refine ⟨252885702746103008224241969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168590468497402005482827979 252885702746103008224241969)
  ·
    refine ⟨189664277059577256168181477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252885702746103008224241969 189664277059577256168181477)
    ·
      refine ⟨35562051948670735531534027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189664277059577256168181477 35562051948670735531534027)
      ·
        refine ⟨53343077923006103297301041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35562051948670735531534027 53343077923006103297301041)
        ·
          refine ⟨40007308442254577472975781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53343077923006103297301041 40007308442254577472975781)
          ·
            refine ⟨7501370332922733276182959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40007308442254577472975781 7501370332922733276182959)
            ·
              refine ⟨11252055499384099914274439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501370332922733276182959 11252055499384099914274439)
              ·
                refine ⟨16878083249076149871411659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252055499384099914274439 16878083249076149871411659)
                ·
                  refine ⟨25317124873614224807117489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16878083249076149871411659 25317124873614224807117489)
                  ·
                    refine ⟨18987843655210668605338117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25317124873614224807117489 18987843655210668605338117)
                    ·
                      refine ⟨3560220685352000363500897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18987843655210668605338117 3560220685352000363500897)
                      ·
                        rfl

theorem cell23_6933505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_6933505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933505 prefixEnd_6933505 := by exact prefixLift 6933505
  have htrace : WordTrace (prefixWord ++ tailWord_6933505) baseStart_6933505 baseEnd_6933505 := by
    simpa [prefixWord, tailWord_6933505, baseEnd_6933505] using wordTrace_append hprefix tailTrace_6933505
  have hstable : (prefixWord ++ tailWord_6933505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933505).length < 2 ^ (prefixWord ++ tailWord_6933505).sum := by decide
  have hdescent : baseEnd_6933505 < baseStart_6933505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933525 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_6933525 : Nat := 118140960795 + 6933525 * 2 ^ 59
def prefixEnd_6933525 : Nat := 4983230072969 + 3 ^ 40 * 6933525 * 2
def baseEnd_6933525 : Nat := 3560230954965090285250805

theorem tailTrace_6933525 : CollatzResearch.WordTrace tailWord_6933525 prefixEnd_6933525 3560230954965090285250805 := by
  unfold tailWord_6933525
  simp only [CollatzResearch.WordTrace]
  refine ⟨252886432206030551639970029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168590954804020367759980019 252886432206030551639970029)
  ·
    refine ⟨94832412077261456864988761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252886432206030551639970029 94832412077261456864988761)
    ·
      refine ⟨71124309057946092648741571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94832412077261456864988761 71124309057946092648741571)
      ·
        refine ⟨106686463586919138973112357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71124309057946092648741571 106686463586919138973112357)
        ·
          refine ⟨20003711922547338557458567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106686463586919138973112357 20003711922547338557458567)
          ·
            refine ⟨30005567883821007836187851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20003711922547338557458567 30005567883821007836187851)
            ·
              refine ⟨45008351825731511754281777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30005567883821007836187851 45008351825731511754281777)
              ·
                refine ⟨33756263869298633815711333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45008351825731511754281777 33756263869298633815711333)
                ·
                  refine ⟨6329299475493493840445875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33756263869298633815711333 6329299475493493840445875)
                  ·
                    refine ⟨9493949213240240760668813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329299475493493840445875 9493949213240240760668813)
                    ·
                      refine ⟨3560230954965090285250805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9493949213240240760668813 3560230954965090285250805)
                      ·
                        rfl

theorem cell23_6933525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_6933525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933525 prefixEnd_6933525 := by exact prefixLift 6933525
  have htrace : WordTrace (prefixWord ++ tailWord_6933525) baseStart_6933525 baseEnd_6933525 := by
    simpa [prefixWord, tailWord_6933525, baseEnd_6933525] using wordTrace_append hprefix tailTrace_6933525
  have hstable : (prefixWord ++ tailWord_6933525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933525).length < 2 ^ (prefixWord ++ tailWord_6933525).sum := by decide
  have hdescent : baseEnd_6933525 < baseStart_6933525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933543 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6933543 : Nat := 118140960795 + 6933543 * 2 ^ 59
def prefixEnd_6933543 : Nat := 4983230072969 + 3 ^ 40 * 6933543 * 2
def baseEnd_6933543 : Nat := 3560240197616871214825723

theorem tailTrace_6933543 : CollatzResearch.WordTrace tailWord_6933543 prefixEnd_6933543 3560240197616871214825723 := by
  unfold tailWord_6933543
  simp only [CollatzResearch.WordTrace]
  refine ⟨252887088719965340714125283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168591392479976893809416855 252887088719965340714125283)
  ·
    refine ⟨379330633079948011071187925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252887088719965340714125283 379330633079948011071187925)
    ·
      refine ⟨8890561712811281509480967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 379330633079948011071187925 8890561712811281509480967)
      ·
        refine ⟨13335842569216922264221451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890561712811281509480967 13335842569216922264221451)
        ·
          refine ⟨20003763853825383396332177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335842569216922264221451 20003763853825383396332177)
          ·
            refine ⟨15002822890369037547249133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20003763853825383396332177 15002822890369037547249133)
            ·
              refine ⟨5626058583888389080218425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15002822890369037547249133 5626058583888389080218425)
              ·
                refine ⟨4219543937916291810163819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626058583888389080218425 4219543937916291810163819)
                ·
                  refine ⟨6329315906874437715245729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219543937916291810163819 6329315906874437715245729)
                  ·
                    refine ⟨4746986930155828286434297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329315906874437715245729 4746986930155828286434297)
                    ·
                      refine ⟨3560240197616871214825723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4746986930155828286434297 3560240197616871214825723)
                      ·
                        rfl

theorem cell23_6933543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6933543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933543 prefixEnd_6933543 := by exact prefixLift 6933543
  have htrace : WordTrace (prefixWord ++ tailWord_6933543) baseStart_6933543 baseEnd_6933543 := by
    simpa [prefixWord, tailWord_6933543, baseEnd_6933543] using wordTrace_append hprefix tailTrace_6933543
  have hstable : (prefixWord ++ tailWord_6933543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933543).length < 2 ^ (prefixWord ++ tailWord_6933543).sum := by decide
  have hdescent : baseEnd_6933543 < baseStart_6933543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933571 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 9]
def baseStart_6933571 : Nat := 118140960795 + 6933571 * 2 ^ 59
def prefixEnd_6933571 : Nat := 4983230072969 + 3 ^ 40 * 6933571 * 2
def baseEnd_6933571 : Nat := 395583841675021900586177

theorem tailTrace_6933571 : CollatzResearch.WordTrace tailWord_6933571 prefixEnd_6933571 395583841675021900586177 := by
  unfold tailWord_6933571
  simp only [CollatzResearch.WordTrace]
  refine ⟨252888109963863901496144567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168592073309242600997429711 252888109963863901496144567)
  ·
    refine ⟨379332164945795852244216851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252888109963863901496144567 379332164945795852244216851)
    ·
      refine ⟨568998247418693778366325277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379332164945795852244216851 568998247418693778366325277)
      ·
        refine ⟨213374342782010166887371979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568998247418693778366325277 213374342782010166887371979)
        ·
          refine ⟨320061514173015250331057969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213374342782010166887371979 320061514173015250331057969)
          ·
            refine ⟨240046135629761437748293477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320061514173015250331057969 240046135629761437748293477)
            ·
              refine ⟨45008650430580269577805027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240046135629761437748293477 45008650430580269577805027)
              ·
                refine ⟨67512975645870404366707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45008650430580269577805027 67512975645870404366707541)
                ·
                  refine ⟨395583841675021900586177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67512975645870404366707541 395583841675021900586177)
                  ·
                    rfl

theorem cell23_6933571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 9].length) (baseStart_6933571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933571 prefixEnd_6933571 := by exact prefixLift 6933571
  have htrace : WordTrace (prefixWord ++ tailWord_6933571) baseStart_6933571 baseEnd_6933571 := by
    simpa [prefixWord, tailWord_6933571, baseEnd_6933571] using wordTrace_append hprefix tailTrace_6933571
  have hstable : (prefixWord ++ tailWord_6933571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933571).length < 2 ^ (prefixWord ++ tailWord_6933571).sum := by decide
  have hdescent : baseEnd_6933571 < baseStart_6933571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933605 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 5]
def baseStart_6933605 : Nat := 118140960795 + 6933605 * 2 ^ 59
def prefixEnd_6933605 : Nat := 4983230072969 + 3 ^ 40 * 6933605 * 2
def baseEnd_6933605 : Nat := 395585781490827774694493

theorem tailTrace_6933605 : CollatzResearch.WordTrace tailWord_6933605 prefixEnd_6933605 395585781490827774694493 := by
  unfold tailWord_6933605
  simp only [CollatzResearch.WordTrace]
  refine ⟨252889350045740725302882269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168592900030493816868588179 252889350045740725302882269)
  ·
    refine ⟨94833506267152771988580851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252889350045740725302882269 94833506267152771988580851)
    ·
      refine ⟨142250259400729157982871277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94833506267152771988580851 142250259400729157982871277)
      ·
        refine ⟨53343847275273434243576729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142250259400729157982871277 53343847275273434243576729)
        ·
          refine ⟨40007885456455075682682547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53343847275273434243576729 40007885456455075682682547)
          ·
            refine ⟨60011828184682613524023821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40007885456455075682682547 60011828184682613524023821)
            ·
              refine ⟨22504435569255980071508933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60011828184682613524023821 22504435569255980071508933)
              ·
                refine ⟨4219581669235496263407925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22504435569255980071508933 4219581669235496263407925)
                ·
                  refine ⟨395585781490827774694493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4219581669235496263407925 395585781490827774694493)
                  ·
                    rfl

theorem cell23_6933605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_6933605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933605 prefixEnd_6933605 := by exact prefixLift 6933605
  have htrace : WordTrace (prefixWord ++ tailWord_6933605) baseStart_6933605 baseEnd_6933605 := by
    simpa [prefixWord, tailWord_6933605, baseEnd_6933605] using wordTrace_append hprefix tailTrace_6933605
  have hstable : (prefixWord ++ tailWord_6933605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933605).length < 2 ^ (prefixWord ++ tailWord_6933605).sum := by decide
  have hdescent : baseEnd_6933605 < baseStart_6933605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933618 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_6933618 : Nat := 118140960795 + 6933618 * 2 ^ 59
def prefixEnd_6933618 : Nat := 4983230072969 + 3 ^ 40 * 6933618 * 2
def baseEnd_6933618 : Nat := 1186759569555319473795959

theorem tailTrace_6933618 : CollatzResearch.WordTrace tailWord_6933618 prefixEnd_6933618 1186759569555319473795959 := by
  unfold tailWord_6933618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63222456048673407130776377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168593216129795752348737005 63222456048673407130776377)
  ·
    refine ⟨47416842036505055348082283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63222456048673407130776377 47416842036505055348082283)
    ·
      refine ⟨71125263054757583022123425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47416842036505055348082283 71125263054757583022123425)
      ·
        refine ⟨53343947291068187266592569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71125263054757583022123425 53343947291068187266592569)
        ·
          refine ⟨40007960468301140449944427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53343947291068187266592569 40007960468301140449944427)
          ·
            refine ⟨60011940702451710674916641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40007960468301140449944427 60011940702451710674916641)
            ·
              refine ⟨45008955526838783006187481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60011940702451710674916641 45008955526838783006187481)
              ·
                refine ⟨33756716645129087254640611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45008955526838783006187481 33756716645129087254640611)
                ·
                  refine ⟨50635074967693630881960917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33756716645129087254640611 50635074967693630881960917)
                  ·
                    refine ⟨1186759569555319473795959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50635074967693630881960917 1186759569555319473795959)
                    ·
                      rfl

theorem cell23_6933618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_6933618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933618 prefixEnd_6933618 := by exact prefixLift 6933618
  have htrace : WordTrace (prefixWord ++ tailWord_6933618) baseStart_6933618 baseEnd_6933618 := by
    simpa [prefixWord, tailWord_6933618, baseEnd_6933618] using wordTrace_append hprefix tailTrace_6933618
  have hstable : (prefixWord ++ tailWord_6933618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933618).length < 2 ^ (prefixWord ++ tailWord_6933618).sum := by decide
  have hdescent : baseEnd_6933618 < baseStart_6933618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933716 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_6933716 : Nat := 118140960795 + 6933716 * 2 ^ 59
def prefixEnd_6933716 : Nat := 4983230072969 + 3 ^ 40 * 6933716 * 2
def baseEnd_6933716 : Nat := 1186776343256699679320809

theorem tailTrace_6933716 : CollatzResearch.WordTrace tailWord_6933716 prefixEnd_6933716 1186776343256699679320809 := by
  unfold tailWord_6933716
  simp only [CollatzResearch.WordTrace]
  refine ⟨126446699274169295630086501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168595599032225727506782001 126446699274169295630086501)
  ·
    refine ⟨23708756113906742930641219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126446699274169295630086501 23708756113906742930641219)
    ·
      refine ⟨35563134170860114395961829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23708756113906742930641219 35563134170860114395961829)
      ·
        refine ⟨6668087657036271449242843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35563134170860114395961829 6668087657036271449242843)
        ·
          refine ⟨10002131485554407173864265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668087657036271449242843 10002131485554407173864265)
          ·
            refine ⟨7501598614165805380398199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10002131485554407173864265 7501598614165805380398199)
            ·
              refine ⟨11252397921248708070597299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501598614165805380398199 11252397921248708070597299)
              ·
                refine ⟨16878596881873062105895949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252397921248708070597299 16878596881873062105895949)
                ·
                  refine ⟨6329473830702398289710981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16878596881873062105895949 6329473830702398289710981)
                  ·
                    refine ⟨1186776343256699679320809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329473830702398289710981 1186776343256699679320809)
                    ·
                      rfl

theorem cell23_6933716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_6933716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933716 prefixEnd_6933716 := by exact prefixLift 6933716
  have htrace : WordTrace (prefixWord ++ tailWord_6933716) baseStart_6933716 baseEnd_6933716 := by
    simpa [prefixWord, tailWord_6933716, baseEnd_6933716] using wordTrace_append hprefix tailTrace_6933716
  have hstable : (prefixWord ++ tailWord_6933716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933716).length < 2 ^ (prefixWord ++ tailWord_6933716).sum := by decide
  have hdescent : baseEnd_6933716 < baseStart_6933716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933742 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_6933742 : Nat := 118140960795 + 6933742 * 2 ^ 59
def prefixEnd_6933742 : Nat := 4983230072969 + 3 ^ 40 * 6933742 * 2
def baseEnd_6933742 : Nat := 1186780793422371978745769

theorem tailTrace_6933742 : CollatzResearch.WordTrace tailWord_6933742 prefixEnd_6933742 1186780793422371978745769 := by
  unfold tailWord_6933742
  simp only [CollatzResearch.WordTrace]
  refine ⟨31611793355780549712577435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168596231230829598467079653 31611793355780549712577435)
  ·
    refine ⟨47417690033670824568866153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31611793355780549712577435 47417690033670824568866153)
    ·
      refine ⟨35563267525253118426649615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47417690033670824568866153 35563267525253118426649615)
      ·
        refine ⟨53344901287879677639974423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35563267525253118426649615 53344901287879677639974423)
        ·
          refine ⟨80017351931819516459961635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53344901287879677639974423 80017351931819516459961635)
          ·
            refine ⟨120026027897729274689942453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80017351931819516459961635 120026027897729274689942453)
            ·
              refine ⟨11252440115412119502182105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120026027897729274689942453 11252440115412119502182105)
              ·
                refine ⟨8439330086559089626636579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11252440115412119502182105 8439330086559089626636579)
                ·
                  refine ⟨12658995129838634439954869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439330086559089626636579 12658995129838634439954869)
                  ·
                    refine ⟨1186780793422371978745769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12658995129838634439954869 1186780793422371978745769)
                    ·
                      rfl

theorem cell23_6933742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_6933742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933742 prefixEnd_6933742 := by exact prefixLift 6933742
  have htrace : WordTrace (prefixWord ++ tailWord_6933742) baseStart_6933742 baseEnd_6933742 := by
    simpa [prefixWord, tailWord_6933742, baseEnd_6933742] using wordTrace_append hprefix tailTrace_6933742
  have hstable : (prefixWord ++ tailWord_6933742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933742).length < 2 ^ (prefixWord ++ tailWord_6933742).sum := by decide
  have hdescent : baseEnd_6933742 < baseStart_6933742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933768 : List Nat := [2, 1, 3, 2, 15]
def baseStart_6933768 : Nat := 118140960795 + 6933768 * 2 ^ 59
def prefixEnd_6933768 : Nat := 4983230072969 + 3 ^ 40 * 6933768 * 2
def baseEnd_6933768 : Nat := 4883889891308824190003

theorem tailTrace_6933768 : CollatzResearch.WordTrace tailWord_6933768 prefixEnd_6933768 4883889891308824190003 := by
  unfold tailWord_6933768
  simp only [CollatzResearch.WordTrace]
  refine ⟨126447647572075102070532979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168596863429433469427377305 126447647572075102070532979)
  ·
    refine ⟨189671471358112653105799469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126447647572075102070532979 189671471358112653105799469)
    ·
      refine ⟨71126801759292244914674801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189671471358112653105799469 71126801759292244914674801)
      ·
        refine ⟨53345101319469183686006101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71126801759292244914674801 53345101319469183686006101)
        ·
          refine ⟨4883889891308824190003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 53345101319469183686006101 4883889891308824190003)
          ·
            rfl

theorem cell23_6933768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 15].length) (baseStart_6933768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933768 prefixEnd_6933768 := by exact prefixLift 6933768
  have htrace : WordTrace (prefixWord ++ tailWord_6933768) baseStart_6933768 baseEnd_6933768 := by
    simpa [prefixWord, tailWord_6933768, baseEnd_6933768] using wordTrace_append hprefix tailTrace_6933768
  have hstable : (prefixWord ++ tailWord_6933768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933768).length < 2 ^ (prefixWord ++ tailWord_6933768).sum := by decide
  have hdescent : baseEnd_6933768 < baseStart_6933768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933772 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_6933772 : Nat := 118140960795 + 6933772 * 2 ^ 59
def prefixEnd_6933772 : Nat := 4983230072969 + 3 ^ 40 * 6933772 * 2
def baseEnd_6933772 : Nat := 1186785928228916939620723

theorem tailTrace_6933772 : CollatzResearch.WordTrace tailWord_6933772 prefixEnd_6933772 1186785928228916939620723 := by
  unfold tailWord_6933772
  simp only [CollatzResearch.WordTrace]
  refine ⟨126447720518067856412105785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168596960690757141882807713 126447720518067856412105785)
  ·
    refine ⟨94835790388550892309079339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126447720518067856412105785 94835790388550892309079339)
    ·
      refine ⟨142253685582826338463619009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94835790388550892309079339 142253685582826338463619009)
      ·
        refine ⟨106690264187119753847714257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142253685582826338463619009 106690264187119753847714257)
        ·
          refine ⟨80017698140339815385785693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106690264187119753847714257 80017698140339815385785693)
          ·
            refine ⟨30006636802627430769669635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80017698140339815385785693 30006636802627430769669635)
            ·
              refine ⟨45009955203941146154504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30006636802627430769669635 45009955203941146154504453)
              ·
                refine ⟨8439366600738964903969585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45009955203941146154504453 8439366600738964903969585)
                ·
                  refine ⟨6329524950554223677977189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8439366600738964903969585 6329524950554223677977189)
                  ·
                    refine ⟨1186785928228916939620723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329524950554223677977189 1186785928228916939620723)
                    ·
                      rfl

theorem cell23_6933772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_6933772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933772 prefixEnd_6933772 := by exact prefixLift 6933772
  have htrace : WordTrace (prefixWord ++ tailWord_6933772) baseStart_6933772 baseEnd_6933772 := by
    simpa [prefixWord, tailWord_6933772, baseEnd_6933772] using wordTrace_append hprefix tailTrace_6933772
  have hstable : (prefixWord ++ tailWord_6933772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933772).length < 2 ^ (prefixWord ++ tailWord_6933772).sum := by decide
  have hdescent : baseEnd_6933772 < baseStart_6933772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933789 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6933789 : Nat := 118140960795 + 6933789 * 2 ^ 59
def prefixEnd_6933789 : Nat := 4983230072969 + 3 ^ 40 * 6933789 * 2
def baseEnd_6933789 : Nat := 1186788837952625750783197

theorem tailTrace_6933789 : CollatzResearch.WordTrace tailWord_6933789 prefixEnd_6933789 1186788837952625750783197 := by
  unfold tailWord_6933789
  simp only [CollatzResearch.WordTrace]
  refine ⟨252896061077074124727580421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168597374051382749818386947 252896061077074124727580421)
  ·
    refine ⟨47418011451951398386421329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252896061077074124727580421 47418011451951398386421329)
    ·
      refine ⟨35563508588963548789815997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47418011451951398386421329 35563508588963548789815997)
      ·
        refine ⟨13336315720861330796180999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35563508588963548789815997 13336315720861330796180999)
        ·
          refine ⟨20004473581291996194271499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13336315720861330796180999 20004473581291996194271499)
          ·
            refine ⟨30006710371937994291407249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20004473581291996194271499 30006710371937994291407249)
            ·
              refine ⟨22505032778953495718555437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30006710371937994291407249 22505032778953495718555437)
              ·
                refine ⟨8439387292107560894458289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22505032778953495718555437 8439387292107560894458289)
                ·
                  refine ⟨6329540469080670670843717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8439387292107560894458289 6329540469080670670843717)
                  ·
                    refine ⟨1186788837952625750783197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329540469080670670843717 1186788837952625750783197)
                    ·
                      rfl

theorem cell23_6933789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6933789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933789 prefixEnd_6933789 := by exact prefixLift 6933789
  have htrace : WordTrace (prefixWord ++ tailWord_6933789) baseStart_6933789 baseEnd_6933789 := by
    simpa [prefixWord, tailWord_6933789, baseEnd_6933789] using wordTrace_append hprefix tailTrace_6933789
  have hstable : (prefixWord ++ tailWord_6933789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933789).length < 2 ^ (prefixWord ++ tailWord_6933789).sum := by decide
  have hdescent : baseEnd_6933789 < baseStart_6933789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933813 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_6933813 : Nat := 118140960795 + 6933813 * 2 ^ 59
def prefixEnd_6933813 : Nat := 4983230072969 + 3 ^ 40 * 6933813 * 2
def baseEnd_6933813 : Nat := 3560378837393585158449481

theorem tailTrace_6933813 : CollatzResearch.WordTrace tailWord_6933813 prefixEnd_6933813 3560378837393585158449481 := by
  unfold tailWord_6933813
  simp only [CollatzResearch.WordTrace]
  refine ⟨252896936428987176826454093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168597957619324784550969395 252896936428987176826454093)
  ·
    refine ⟨94836351160870191309920285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252896936428987176826454093 94836351160870191309920285)
    ·
      refine ⟨35563631685326321741220107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94836351160870191309920285 35563631685326321741220107)
      ·
        refine ⟨53345447527989482611830161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35563631685326321741220107 53345447527989482611830161)
        ·
          refine ⟨40009085645992111958872621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53345447527989482611830161 40009085645992111958872621)
          ·
            refine ⟨15003407117247041984577233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40009085645992111958872621 15003407117247041984577233)
            ·
              refine ⟨11252555337935281488432925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15003407117247041984577233 11252555337935281488432925)
              ·
                refine ⟨4219708251725730558162347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11252555337935281488432925 4219708251725730558162347)
                ·
                  refine ⟨6329562377588595837243521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219708251725730558162347 6329562377588595837243521)
                  ·
                    refine ⟨4747171783191446877932641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329562377588595837243521 4747171783191446877932641)
                    ·
                      refine ⟨3560378837393585158449481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747171783191446877932641 3560378837393585158449481)
                      ·
                        rfl

theorem cell23_6933813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_6933813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933813 prefixEnd_6933813 := by exact prefixLift 6933813
  have htrace : WordTrace (prefixWord ++ tailWord_6933813) baseStart_6933813 baseEnd_6933813 := by
    simpa [prefixWord, tailWord_6933813, baseEnd_6933813] using wordTrace_append hprefix tailTrace_6933813
  have hstable : (prefixWord ++ tailWord_6933813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933813).length < 2 ^ (prefixWord ++ tailWord_6933813).sum := by decide
  have hdescent : baseEnd_6933813 < baseStart_6933813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933853 : List Nat := [1, 4, 5, 1, 1, 2, 2, 7]
def baseStart_6933853 : Nat := 118140960795 + 6933853 * 2 ^ 59
def prefixEnd_6933853 : Nat := 4983230072969 + 3 ^ 40 * 6933853 * 2
def baseEnd_6933853 : Nat := 131866643578509814887011

theorem tailTrace_6933853 : CollatzResearch.WordTrace tailWord_6933853 prefixEnd_6933853 131866643578509814887011 := by
  unfold tailWord_6933853
  simp only [CollatzResearch.WordTrace]
  refine ⟨252898395348842263657910213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168598930232561509105273475 252898395348842263657910213)
  ·
    refine ⟨47418449127907924435858165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252898395348842263657910213 47418449127907924435858165)
    ·
      refine ⟨4445479605741367915861703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47418449127907924435858165 4445479605741367915861703)
      ·
        refine ⟨6668219408612051873792555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445479605741367915861703 6668219408612051873792555)
        ·
          refine ⟨10002329112918077810688833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668219408612051873792555 10002329112918077810688833)
          ·
            refine ⟨7501746834688558358016625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10002329112918077810688833 7501746834688558358016625)
            ·
              refine ⟨5626310126016418768512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501746834688558358016625 5626310126016418768512469)
              ·
                refine ⟨131866643578509814887011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5626310126016418768512469 131866643578509814887011)
                ·
                  rfl

theorem cell23_6933853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 7].length) (baseStart_6933853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933853 prefixEnd_6933853 := by exact prefixLift 6933853
  have htrace : WordTrace (prefixWord ++ tailWord_6933853) baseStart_6933853 baseEnd_6933853 := by
    simpa [prefixWord, tailWord_6933853, baseEnd_6933853] using wordTrace_append hprefix tailTrace_6933853
  have hstable : (prefixWord ++ tailWord_6933853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933853).length < 2 ^ (prefixWord ++ tailWord_6933853).sum := by decide
  have hdescent : baseEnd_6933853 < baseStart_6933853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933855 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_6933855 : Nat := 118140960795 + 6933855 * 2 ^ 59
def prefixEnd_6933855 : Nat := 4983230072969 + 3 ^ 40 * 6933855 * 2
def baseEnd_6933855 : Nat := 3560400403581073994124287

theorem tailTrace_6933855 : CollatzResearch.WordTrace tailWord_6933855 prefixEnd_6933855 3560400403581073994124287 := by
  unfold tailWord_6933855
  simp only [CollatzResearch.WordTrace]
  refine ⟨252898468294835017999483019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168598978863223345332988679 252898468294835017999483019)
  ·
    refine ⟨379347702442252526999224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252898468294835017999483019 379347702442252526999224529)
    ·
      refine ⟨284510776831689395249418397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379347702442252526999224529 284510776831689395249418397)
      ·
        refine ⟨106691541311883523218531899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284510776831689395249418397 106691541311883523218531899)
        ·
          refine ⟨160037311967825284827797849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106691541311883523218531899 160037311967825284827797849)
          ·
            refine ⟨120027983975868963620848387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160037311967825284827797849 120027983975868963620848387)
            ·
              refine ⟨180041975963803445431272581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120027983975868963620848387 180041975963803445431272581)
              ·
                refine ⟨33757870493213146018363609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180041975963803445431272581 33757870493213146018363609)
                ·
                  refine ⟨25318402869909859513772707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33757870493213146018363609 25318402869909859513772707)
                  ·
                    refine ⟨37977604304864789270659061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25318402869909859513772707 37977604304864789270659061)
                    ·
                      refine ⟨3560400403581073994124287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37977604304864789270659061 3560400403581073994124287)
                      ·
                        rfl

theorem cell23_6933855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_6933855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933855 prefixEnd_6933855 := by exact prefixLift 6933855
  have htrace : WordTrace (prefixWord ++ tailWord_6933855) baseStart_6933855 baseEnd_6933855 := by
    simpa [prefixWord, tailWord_6933855, baseEnd_6933855] using wordTrace_append hprefix tailTrace_6933855
  have hstable : (prefixWord ++ tailWord_6933855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933855).length < 2 ^ (prefixWord ++ tailWord_6933855).sum := by decide
  have hdescent : baseEnd_6933855 < baseStart_6933855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933856 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2]
def baseStart_6933856 : Nat := 118140960795 + 6933856 * 2 ^ 59
def prefixEnd_6933856 : Nat := 4983230072969 + 3 ^ 40 * 6933856 * 2
def baseEnd_6933856 : Nat := 3560400917061728490211783

theorem tailTrace_6933856 : CollatzResearch.WordTrace tailWord_6933856 prefixEnd_6933856 3560400917061728490211783 := by
  unfold tailWord_6933856
  simp only [CollatzResearch.WordTrace]
  refine ⟨126449252383915697585134711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168599003178554263446846281 126449252383915697585134711)
  ·
    refine ⟨189673878575873546377702067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126449252383915697585134711 189673878575873546377702067)
    ·
      refine ⟨284510817863810319566553101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189673878575873546377702067 284510817863810319566553101)
      ·
        refine ⟨106691556698928869837457413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284510817863810319566553101 106691556698928869837457413)
        ·
          refine ⟨20004666881049163094523265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106691556698928869837457413 20004666881049163094523265)
          ·
            refine ⟨15003500160786872320892449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20004666881049163094523265 15003500160786872320892449)
            ·
              refine ⟨11252625120590154240669337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15003500160786872320892449 11252625120590154240669337)
              ·
                refine ⟨8439468840442615680502003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11252625120590154240669337 8439468840442615680502003)
                ·
                  refine ⟨12659203260663923520753005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439468840442615680502003 12659203260663923520753005)
                  ·
                    refine ⟨4747201222748971320282377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12659203260663923520753005 4747201222748971320282377)
                    ·
                      refine ⟨3560400917061728490211783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747201222748971320282377 3560400917061728490211783)
                      ·
                        rfl

theorem cell23_6933856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_6933856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933856 prefixEnd_6933856 := by exact prefixLift 6933856
  have htrace : WordTrace (prefixWord ++ tailWord_6933856) baseStart_6933856 baseEnd_6933856 := by
    simpa [prefixWord, tailWord_6933856, baseEnd_6933856] using wordTrace_append hprefix tailTrace_6933856
  have hstable : (prefixWord ++ tailWord_6933856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933856).length < 2 ^ (prefixWord ++ tailWord_6933856).sum := by decide
  have hdescent : baseEnd_6933856 < baseStart_6933856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933865 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_6933865 : Nat := 118140960795 + 6933865 * 2 ^ 59
def prefixEnd_6933865 : Nat := 4983230072969 + 3 ^ 40 * 6933865 * 2
def baseEnd_6933865 : Nat := 3560405538387618954999241

theorem tailTrace_6933865 : CollatzResearch.WordTrace tailWord_6933865 prefixEnd_6933865 3560405538387618954999241 := by
  unfold tailWord_6933865
  simp only [CollatzResearch.WordTrace]
  refine ⟨252898833024798789707347049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168599222016532526471564699 252898833024798789707347049)
  ·
    refine ⟨189674124768599092280510287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252898833024798789707347049 189674124768599092280510287)
    ·
      refine ⟨284511187152898638420765431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189674124768599092280510287 284511187152898638420765431)
      ·
        refine ⟨426766780729347957631148147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284511187152898638420765431 426766780729347957631148147)
        ·
          refine ⟨640150171094021936446722221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426766780729347957631148147 640150171094021936446722221)
          ·
            refine ⟨240056314160258226167520833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640150171094021936446722221 240056314160258226167520833)
            ·
              refine ⟨180042235620193669625640625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240056314160258226167520833 180042235620193669625640625)
              ·
                refine ⟨135031676715145252219230469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180042235620193669625640625 135031676715145252219230469)
                ·
                  refine ⟨25318439384089734791105713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135031676715145252219230469 25318439384089734791105713)
                  ·
                    refine ⟨18988829538067301093329285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25318439384089734791105713 18988829538067301093329285)
                    ·
                      refine ⟨3560405538387618954999241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18988829538067301093329285 3560405538387618954999241)
                      ·
                        rfl

theorem cell23_6933865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_6933865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933865 prefixEnd_6933865 := by exact prefixLift 6933865
  have htrace : WordTrace (prefixWord ++ tailWord_6933865) baseStart_6933865 baseEnd_6933865 := by
    simpa [prefixWord, tailWord_6933865, baseEnd_6933865] using wordTrace_append hprefix tailTrace_6933865
  have hstable : (prefixWord ++ tailWord_6933865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933865).length < 2 ^ (prefixWord ++ tailWord_6933865).sum := by decide
  have hdescent : baseEnd_6933865 < baseStart_6933865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933885 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_6933885 : Nat := 118140960795 + 6933885 * 2 ^ 59
def prefixEnd_6933885 : Nat := 4983230072969 + 3 ^ 40 * 6933885 * 2
def baseEnd_6933885 : Nat := 3560415808000708876749149

theorem tailTrace_6933885 : CollatzResearch.WordTrace tailWord_6933885 prefixEnd_6933885 3560415808000708876749149 := by
  unfold tailWord_6933885
  simp only [CollatzResearch.WordTrace]
  refine ⟨252899562484726333123075109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168599708323150888748716739 252899562484726333123075109)
  ·
    refine ⟨47418667965886187460576583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252899562484726333123075109 47418667965886187460576583)
    ·
      refine ⟨71128001948829281190864875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47418667965886187460576583 71128001948829281190864875)
      ·
        refine ⟨106692002923243921786297313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71128001948829281190864875 106692002923243921786297313)
        ·
          refine ⟨80019002192432941339722985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106692002923243921786297313 80019002192432941339722985)
          ·
            refine ⟨60014251644324706004792239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80019002192432941339722985 60014251644324706004792239)
            ·
              refine ⟨90021377466487059007188359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60014251644324706004792239 90021377466487059007188359)
              ·
                refine ⟨135032066199730588510782539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90021377466487059007188359 135032066199730588510782539)
                ·
                  refine ⟨202548099299595882766173809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135032066199730588510782539 202548099299595882766173809)
                  ·
                    refine ⟨151911074474696912074630357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202548099299595882766173809 151911074474696912074630357)
                    ·
                      refine ⟨3560415808000708876749149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151911074474696912074630357 3560415808000708876749149)
                      ·
                        rfl

theorem cell23_6933885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_6933885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933885 prefixEnd_6933885 := by exact prefixLift 6933885
  have htrace : WordTrace (prefixWord ++ tailWord_6933885) baseStart_6933885 baseEnd_6933885 := by
    simpa [prefixWord, tailWord_6933885, baseEnd_6933885] using wordTrace_append hprefix tailTrace_6933885
  have hstable : (prefixWord ++ tailWord_6933885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933885).length < 2 ^ (prefixWord ++ tailWord_6933885).sum := by decide
  have hdescent : baseEnd_6933885 < baseStart_6933885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933892 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 7]
def baseStart_6933892 : Nat := 118140960795 + 6933892 * 2 ^ 59
def prefixEnd_6933892 : Nat := 4983230072969 + 3 ^ 40 * 6933892 * 2
def baseEnd_6933892 : Nat := 395602155818365594373513

theorem tailTrace_6933892 : CollatzResearch.WordTrace tailWord_6933892 prefixEnd_6933892 395602155818365594373513 := by
  unfold tailWord_6933892
  simp only [CollatzResearch.WordTrace]
  refine ⟨126449908897850486659289965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168599878530467315545719953 126449908897850486659289965)
  ·
    refine ⟨47418715836693932497233737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126449908897850486659289965 47418715836693932497233737)
    ·
      refine ⟨35564036877520449372925303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47418715836693932497233737 35564036877520449372925303)
      ·
        refine ⟨53346055316280674059387955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35564036877520449372925303 53346055316280674059387955)
        ·
          refine ⟨80019082974421011089081933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53346055316280674059387955 80019082974421011089081933)
          ·
            refine ⟨30007156115407879158405725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80019082974421011089081933 30007156115407879158405725)
            ·
              refine ⟨11252683543277954684402147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30007156115407879158405725 11252683543277954684402147)
              ·
                refine ⟨16879025314916932026603221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252683543277954684402147 16879025314916932026603221)
                ·
                  refine ⟨395602155818365594373513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16879025314916932026603221 395602155818365594373513)
                  ·
                    rfl

theorem cell23_6933892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_6933892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933892 prefixEnd_6933892 := by exact prefixLift 6933892
  have htrace : WordTrace (prefixWord ++ tailWord_6933892) baseStart_6933892 baseEnd_6933892 := by
    simpa [prefixWord, tailWord_6933892, baseEnd_6933892] using wordTrace_append hprefix tailTrace_6933892
  have hstable : (prefixWord ++ tailWord_6933892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933892).length < 2 ^ (prefixWord ++ tailWord_6933892).sum := by decide
  have hdescent : baseEnd_6933892 < baseStart_6933892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6933959 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_6933959 : Nat := 118140960795 + 6933959 * 2 ^ 59
def prefixEnd_6933959 : Nat := 4983230072969 + 3 ^ 40 * 6933959 * 2
def baseEnd_6933959 : Nat := 3560453805569141587223809

theorem tailTrace_6933959 : CollatzResearch.WordTrace tailWord_6933959 prefixEnd_6933959 3560453805569141587223809 := by
  unfold tailWord_6933959
  simp only [CollatzResearch.WordTrace]
  refine ⟨252902261486458243761268931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168601507657638829174179287 252902261486458243761268931)
  ·
    refine ⟨379353392229687365641903397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252902261486458243761268931 379353392229687365641903397)
    ·
      refine ⟨71128761043066381057856887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379353392229687365641903397 71128761043066381057856887)
      ·
        refine ⟨106693141564599571586785331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71128761043066381057856887 106693141564599571586785331)
        ·
          refine ⟨160039712346899357380177997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106693141564599571586785331 160039712346899357380177997)
          ·
            refine ⟨60014892130087259017566749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160039712346899357380177997 60014892130087259017566749)
            ·
              refine ⟨22505584548782722131587531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60014892130087259017566749 22505584548782722131587531)
              ·
                refine ⟨33758376823174083197381297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22505584548782722131587531 33758376823174083197381297)
                ·
                  refine ⟨25318782617380562398035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33758376823174083197381297 25318782617380562398035973)
                  ·
                    refine ⟨4747271740758855449631745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25318782617380562398035973 4747271740758855449631745)
                    ·
                      refine ⟨3560453805569141587223809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747271740758855449631745 3560453805569141587223809)
                      ·
                        rfl

theorem cell23_6933959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_6933959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6933959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6933959 prefixEnd_6933959 := by exact prefixLift 6933959
  have htrace : WordTrace (prefixWord ++ tailWord_6933959) baseStart_6933959 baseEnd_6933959 := by
    simpa [prefixWord, tailWord_6933959, baseEnd_6933959] using wordTrace_append hprefix tailTrace_6933959
  have hstable : (prefixWord ++ tailWord_6933959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6933959).length < 2 ^ (prefixWord ++ tailWord_6933959).sum := by decide
  have hdescent : baseEnd_6933959 < baseStart_6933959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6933959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934012 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_6934012 : Nat := 118140960795 + 6934012 * 2 ^ 59
def prefixEnd_6934012 : Nat := 4983230072969 + 3 ^ 40 * 6934012 * 2
def baseEnd_6934012 : Nat := 1186827006681276626620355

theorem tailTrace_6934012 : CollatzResearch.WordTrace tailWord_6934012 prefixEnd_6934012 1186827006681276626620355 := by
  unfold tailWord_6934012
  simp only [CollatzResearch.WordTrace]
  refine ⟨126452097277633116906474145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168602796370177489208632193 126452097277633116906474145)
  ·
    refine ⟨94839072958224837679855609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126452097277633116906474145 94839072958224837679855609)
    ·
      refine ⟨71129304718668628259891707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94839072958224837679855609 71129304718668628259891707)
      ·
        refine ⟨106693957078002942389837561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71129304718668628259891707 106693957078002942389837561)
        ·
          refine ⟨80020467808502206792378171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106693957078002942389837561 80020467808502206792378171)
          ·
            refine ⟨120030701712753310188567257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80020467808502206792378171 120030701712753310188567257)
            ·
              refine ⟨90023026284564982641425443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120030701712753310188567257 90023026284564982641425443)
              ·
                refine ⟨135034539426847473962138165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90023026284564982641425443 135034539426847473962138165)
                ·
                  refine ⟨12659488071266950683950453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135034539426847473962138165 12659488071266950683950453)
                  ·
                    refine ⟨1186827006681276626620355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12659488071266950683950453 1186827006681276626620355)
                    ·
                      rfl

theorem cell23_6934012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_6934012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934012 prefixEnd_6934012 := by exact prefixLift 6934012
  have htrace : WordTrace (prefixWord ++ tailWord_6934012) baseStart_6934012 baseEnd_6934012 := by
    simpa [prefixWord, tailWord_6934012, baseEnd_6934012] using wordTrace_append hprefix tailTrace_6934012
  have hstable : (prefixWord ++ tailWord_6934012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934012).length < 2 ^ (prefixWord ++ tailWord_6934012).sum := by decide
  have hdescent : baseEnd_6934012 < baseStart_6934012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934019 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 6, 3, 2]
def baseStart_6934019 : Nat := 118140960795 + 6934019 * 2 ^ 59
def prefixEnd_6934019 : Nat := 4983230072969 + 3 ^ 40 * 6934019 * 2
def baseEnd_6934019 : Nat := 3560484614408411352473533

theorem tailTrace_6934019 : CollatzResearch.WordTrace tailWord_6934019 prefixEnd_6934019 3560484614408411352473533 := by
  unfold tailWord_6934019
  simp only [CollatzResearch.WordTrace]
  refine ⟨252904449866240874008453111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168602966577493916005635407 252904449866240874008453111)
  ·
    refine ⟨379356674799361311012679667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252904449866240874008453111 379356674799361311012679667)
    ·
      refine ⟨569035012199041966519019501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379356674799361311012679667 569035012199041966519019501)
      ·
        refine ⟨213388129574640737444632313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569035012199041966519019501 213388129574640737444632313)
        ·
          refine ⟨160041097180980553083474235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213388129574640737444632313 160041097180980553083474235)
          ·
            refine ⟨240061645771470829625211353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160041097180980553083474235 240061645771470829625211353)
            ·
              refine ⟨180046234328603122218908515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240061645771470829625211353 180046234328603122218908515)
              ·
                refine ⟨270069351492904683328362773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180046234328603122218908515 270069351492904683328362773)
                ·
                  refine ⟨12659500851229907031017005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270069351492904683328362773 12659500851229907031017005)
                  ·
                    refine ⟨4747312819211215136631377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12659500851229907031017005 4747312819211215136631377)
                    ·
                      refine ⟨3560484614408411352473533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747312819211215136631377 3560484614408411352473533)
                      ·
                        rfl

theorem cell23_6934019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_6934019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934019 prefixEnd_6934019 := by exact prefixLift 6934019
  have htrace : WordTrace (prefixWord ++ tailWord_6934019) baseStart_6934019 baseEnd_6934019 := by
    simpa [prefixWord, tailWord_6934019, baseEnd_6934019] using wordTrace_append hprefix tailTrace_6934019
  have hstable : (prefixWord ++ tailWord_6934019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934019).length < 2 ^ (prefixWord ++ tailWord_6934019).sum := by decide
  have hdescent : baseEnd_6934019 < baseStart_6934019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934026 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6934026 : Nat := 118140960795 + 6934026 * 2 ^ 59
def prefixEnd_6934026 : Nat := 4983230072969 + 3 ^ 40 * 6934026 * 2
def baseEnd_6934026 : Nat := 3560488208772992825086001

theorem tailTrace_6934026 : CollatzResearch.WordTrace tailWord_6934026 prefixEnd_6934026 3560488208772992825086001 := by
  unfold tailWord_6934026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226176294303878550989483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168603136784810342802638621 63226176294303878550989483)
  ·
    refine ⟨94839264441455817826484225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63226176294303878550989483 94839264441455817826484225)
    ·
      refine ⟨71129448331091863369863169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94839264441455817826484225 71129448331091863369863169)
      ·
        refine ⟨53347086248318897527397377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71129448331091863369863169 53347086248318897527397377)
        ·
          refine ⟨40010314686239173145548033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53347086248318897527397377 40010314686239173145548033)
          ·
            refine ⟨30007736014679379859161025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40010314686239173145548033 30007736014679379859161025)
            ·
              refine ⟨22505802011009534894370769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30007736014679379859161025 22505802011009534894370769)
              ·
                refine ⟨16879351508257151170778077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22505802011009534894370769 16879351508257151170778077)
                ·
                  refine ⟨6329756815596431689041779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16879351508257151170778077 6329756815596431689041779)
                  ·
                    refine ⟨9494635223394647533562669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329756815596431689041779 9494635223394647533562669)
                    ·
                      refine ⟨3560488208772992825086001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9494635223394647533562669 3560488208772992825086001)
                      ·
                        rfl

theorem cell23_6934026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6934026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934026 prefixEnd_6934026 := by exact prefixLift 6934026
  have htrace : WordTrace (prefixWord ++ tailWord_6934026) baseStart_6934026 baseEnd_6934026 := by
    simpa [prefixWord, tailWord_6934026, baseEnd_6934026] using wordTrace_append hprefix tailTrace_6934026
  have hstable : (prefixWord ++ tailWord_6934026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934026).length < 2 ^ (prefixWord ++ tailWord_6934026).sum := by decide
  have hdescent : baseEnd_6934026 < baseStart_6934026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934042 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_6934042 : Nat := 118140960795 + 6934042 * 2 ^ 59
def prefixEnd_6934042 : Nat := 4983230072969 + 3 ^ 40 * 6934042 * 2
def baseEnd_6934042 : Nat := 1186832141487821587495309

theorem tailTrace_6934042 : CollatzResearch.WordTrace tailWord_6934042 prefixEnd_6934042 1186832141487821587495309 := by
  unfold tailWord_6934042
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226322186289387234135095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168603525830105032624360253 63226322186289387234135095)
  ·
    refine ⟨94839483279434080851202643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63226322186289387234135095 94839483279434080851202643)
    ·
      refine ⟨142259224919151121276803965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94839483279434080851202643 142259224919151121276803965)
      ·
        refine ⟨53347209344681670478801487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142259224919151121276803965 53347209344681670478801487)
        ·
          refine ⟨80020814017022505718202231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53347209344681670478801487 80020814017022505718202231)
          ·
            refine ⟨120031221025533758577303347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80020814017022505718202231 120031221025533758577303347)
            ·
              refine ⟨180046831538300637865955021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120031221025533758577303347 180046831538300637865955021)
              ·
                refine ⟨67517561826862739199733133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180046831538300637865955021 67517561826862739199733133)
                ·
                  refine ⟨25319085685073527199899925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67517561826862739199733133 25319085685073527199899925)
                  ·
                    refine ⟨1186832141487821587495309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25319085685073527199899925 1186832141487821587495309)
                    ·
                      rfl

theorem cell23_6934042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_6934042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934042 prefixEnd_6934042 := by exact prefixLift 6934042
  have htrace : WordTrace (prefixWord ++ tailWord_6934042) baseStart_6934042 baseEnd_6934042 := by
    simpa [prefixWord, tailWord_6934042, baseEnd_6934042] using wordTrace_append hprefix tailTrace_6934042
  have hstable : (prefixWord ++ tailWord_6934042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934042).length < 2 ^ (prefixWord ++ tailWord_6934042).sum := by decide
  have hdescent : baseEnd_6934042 < baseStart_6934042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934069 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6934069 : Nat := 118140960795 + 6934069 * 2 ^ 59
def prefixEnd_6934069 : Nat := 4983230072969 + 3 ^ 40 * 6934069 * 2
def baseEnd_6934069 : Nat := 3560510288441136156848303

theorem tailTrace_6934069 : CollatzResearch.WordTrace tailWord_6934069 prefixEnd_6934069 3560510288441136156848303 := by
  unfold tailWord_6934069
  simp only [CollatzResearch.WordTrace]
  refine ⟨252906273516059732547773261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168604182344039821698515507 252906273516059732547773261)
  ·
    refine ⟨94839852568522399705414973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252906273516059732547773261 94839852568522399705414973)
    ·
      refine ⟨35564944713195899889530615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94839852568522399705414973 35564944713195899889530615)
      ·
        refine ⟨53347417069793849834295923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35564944713195899889530615 53347417069793849834295923)
        ·
          refine ⟨80021125604690774751443885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53347417069793849834295923 80021125604690774751443885)
          ·
            refine ⟨30007922101759040531791457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80021125604690774751443885 30007922101759040531791457)
            ·
              refine ⟨22505941576319280398843593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30007922101759040531791457 22505941576319280398843593)
              ·
                refine ⟨16879456182239460299132695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22505941576319280398843593 16879456182239460299132695)
                ·
                  refine ⟨25319184273359190448699043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16879456182239460299132695 25319184273359190448699043)
                  ·
                    refine ⟨37978776410038785673048565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25319184273359190448699043 37978776410038785673048565)
                    ·
                      refine ⟨3560510288441136156848303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37978776410038785673048565 3560510288441136156848303)
                      ·
                        rfl

theorem cell23_6934069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6934069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934069 prefixEnd_6934069 := by exact prefixLift 6934069
  have htrace : WordTrace (prefixWord ++ tailWord_6934069) baseStart_6934069 baseEnd_6934069 := by
    simpa [prefixWord, tailWord_6934069, baseEnd_6934069] using wordTrace_append hprefix tailTrace_6934069
  have hstable : (prefixWord ++ tailWord_6934069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934069).length < 2 ^ (prefixWord ++ tailWord_6934069).sum := by decide
  have hdescent : baseEnd_6934069 < baseStart_6934069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934072 : List Nat := [2, 1, 2, 1, 4, 2, 1, 10]
def baseStart_6934072 : Nat := 118140960795 + 6934072 * 2 ^ 59
def prefixEnd_6934072 : Nat := 4983230072969 + 3 ^ 40 * 6934072 * 2
def baseEnd_6934072 : Nat := 131870808477151838707807

theorem tailTrace_6934072 : CollatzResearch.WordTrace tailWord_6934072 prefixEnd_6934072 131870808477151838707807 := by
  unfold tailWord_6934072
  simp only [CollatzResearch.WordTrace]
  refine ⟨126453191467524432030066235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168604255290032576040088313 126453191467524432030066235)
  ·
    refine ⟨189679787201286648045099353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126453191467524432030066235 189679787201286648045099353)
    ·
      refine ⟨142259840400964986033824515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189679787201286648045099353 142259840400964986033824515)
      ·
        refine ⟨213389760601447479050736773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142259840400964986033824515 213389760601447479050736773)
        ·
          refine ⟨40010580112771402322013145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213389760601447479050736773 40010580112771402322013145)
          ·
            refine ⟨30007935084578551741509859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40010580112771402322013145 30007935084578551741509859)
            ·
              refine ⟨45011902626867827612264789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30007935084578551741509859 45011902626867827612264789)
              ·
                refine ⟨131870808477151838707807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45011902626867827612264789 131870808477151838707807)
                ·
                  rfl

theorem cell23_6934072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 10].length) (baseStart_6934072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934072 prefixEnd_6934072 := by exact prefixLift 6934072
  have htrace : WordTrace (prefixWord ++ tailWord_6934072) baseStart_6934072 baseEnd_6934072 := by
    simpa [prefixWord, tailWord_6934072, baseEnd_6934072] using wordTrace_append hprefix tailTrace_6934072
  have hstable : (prefixWord ++ tailWord_6934072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934072).length < 2 ^ (prefixWord ++ tailWord_6934072).sum := by decide
  have hdescent : baseEnd_6934072 < baseStart_6934072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934100 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_6934100 : Nat := 118140960795 + 6934100 * 2 ^ 59
def prefixEnd_6934100 : Nat := 4983230072969 + 3 ^ 40 * 6934100 * 2
def baseEnd_6934100 : Nat := 3560526206341425535560661

theorem tailTrace_6934100 : CollatzResearch.WordTrace tailWord_6934100 prefixEnd_6934100 3560526206341425535560661 := by
  unfold tailWord_6934100
  simp only [CollatzResearch.WordTrace]
  refine ⟨126453702089473712421075877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168604936119298283228101169 126453702089473712421075877)
  ·
    refine ⟨23710069141776321078951727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126453702089473712421075877 23710069141776321078951727)
    ·
      refine ⟨35565103712664481618427591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23710069141776321078951727 35565103712664481618427591)
      ·
        refine ⟨53347655568996722427641387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35565103712664481618427591 53347655568996722427641387)
        ·
          refine ⟨80021483353495083641462081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53347655568996722427641387 80021483353495083641462081)
          ·
            refine ⟨60016112515121312731096561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80021483353495083641462081 60016112515121312731096561)
            ·
              refine ⟨45012084386340984548322421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60016112515121312731096561 45012084386340984548322421)
              ·
                refine ⟨4219882911219467301405227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45012084386340984548322421 4219882911219467301405227)
                ·
                  refine ⟨6329824366829200952107841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219882911219467301405227 6329824366829200952107841)
                  ·
                    refine ⟨4747368275121900714080881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329824366829200952107841 4747368275121900714080881)
                    ·
                      refine ⟨3560526206341425535560661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747368275121900714080881 3560526206341425535560661)
                      ·
                        rfl

theorem cell23_6934100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_6934100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934100 prefixEnd_6934100 := by exact prefixLift 6934100
  have htrace : WordTrace (prefixWord ++ tailWord_6934100) baseStart_6934100 baseEnd_6934100 := by
    simpa [prefixWord, tailWord_6934100, baseEnd_6934100] using wordTrace_append hprefix tailTrace_6934100
  have hstable : (prefixWord ++ tailWord_6934100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934100).length < 2 ^ (prefixWord ++ tailWord_6934100).sum := by decide
  have hdescent : baseEnd_6934100 < baseStart_6934100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934103 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_6934103 : Nat := 118140960795 + 6934103 * 2 ^ 59
def prefixEnd_6934103 : Nat := 4983230072969 + 3 ^ 40 * 6934103 * 2
def baseEnd_6934103 : Nat := 3560527746783389023823147

theorem tailTrace_6934103 : CollatzResearch.WordTrace tailWord_6934103 prefixEnd_6934103 3560527746783389023823147 := by
  unfold tailWord_6934103
  simp only [CollatzResearch.WordTrace]
  refine ⟨252907513597936556354510963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168605009065291037569673975 252907513597936556354510963)
  ·
    refine ⟨379361270396904834531766445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252907513597936556354510963 379361270396904834531766445)
    ·
      refine ⟨142260476398839312949412417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379361270396904834531766445 142260476398839312949412417)
      ·
        refine ⟨106695357299129484712059313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142260476398839312949412417 106695357299129484712059313)
        ·
          refine ⟨80021517974347113534044485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106695357299129484712059313 80021517974347113534044485)
          ·
            refine ⟨15004034620190083787633341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80021517974347113534044485 15004034620190083787633341)
            ·
              refine ⟨5626512982571281420362503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15004034620190083787633341 5626512982571281420362503)
              ·
                refine ⟨8439769473856922130543755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626512982571281420362503 8439769473856922130543755)
                ·
                  refine ⟨12659654210785383195815633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439769473856922130543755 12659654210785383195815633)
                  ·
                    refine ⟨9494740658089037396861725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12659654210785383195815633 9494740658089037396861725)
                    ·
                      refine ⟨3560527746783389023823147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9494740658089037396861725 3560527746783389023823147)
                      ·
                        rfl

theorem cell23_6934103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_6934103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934103 prefixEnd_6934103 := by exact prefixLift 6934103
  have htrace : WordTrace (prefixWord ++ tailWord_6934103) baseStart_6934103 baseEnd_6934103 := by
    simpa [prefixWord, tailWord_6934103, baseEnd_6934103] using wordTrace_append hprefix tailTrace_6934103
  have hstable : (prefixWord ++ tailWord_6934103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934103).length < 2 ^ (prefixWord ++ tailWord_6934103).sum := by decide
  have hdescent : baseEnd_6934103 < baseStart_6934103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934117 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_6934117 : Nat := 118140960795 + 6934117 * 2 ^ 59
def prefixEnd_6934117 : Nat := 4983230072969 + 3 ^ 40 * 6934117 * 2
def baseEnd_6934117 : Nat := 3560534935512551969048083

theorem tailTrace_6934117 : CollatzResearch.WordTrace tailWord_6934117 prefixEnd_6934117 3560534935512551969048083 := by
  unfold tailWord_6934117
  simp only [CollatzResearch.WordTrace]
  refine ⟨252908024219885836745520605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168605349479923891163680403 252908024219885836745520605)
  ·
    refine ⟨94840509082457188779570227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252908024219885836745520605 94840509082457188779570227)
    ·
      refine ⟨142260763623685783169355341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94840509082457188779570227 142260763623685783169355341)
      ·
        refine ⟨53347786358882168688508253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142260763623685783169355341 53347786358882168688508253)
        ·
          refine ⟨20005419884580813258190595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53347786358882168688508253 20005419884580813258190595)
          ·
            refine ⟨30008129826871219887285893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20005419884580813258190595 30008129826871219887285893)
            ·
              refine ⟨5626524342538353728866105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30008129826871219887285893 5626524342538353728866105)
              ·
                refine ⟨4219893256903765296649579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626524342538353728866105 4219893256903765296649579)
                ·
                  refine ⟨6329839885355647944974369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219893256903765296649579 6329839885355647944974369)
                  ·
                    refine ⟨4747379914016735958730777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329839885355647944974369 4747379914016735958730777)
                    ·
                      refine ⟨3560534935512551969048083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747379914016735958730777 3560534935512551969048083)
                      ·
                        rfl

theorem cell23_6934117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_6934117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934117 prefixEnd_6934117 := by exact prefixLift 6934117
  have htrace : WordTrace (prefixWord ++ tailWord_6934117) baseStart_6934117 baseEnd_6934117 := by
    simpa [prefixWord, tailWord_6934117, baseEnd_6934117] using wordTrace_append hprefix tailTrace_6934117
  have hstable : (prefixWord ++ tailWord_6934117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934117).length < 2 ^ (prefixWord ++ tailWord_6934117).sum := by decide
  have hdescent : baseEnd_6934117 < baseStart_6934117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934133 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6934133 : Nat := 118140960795 + 6934133 * 2 ^ 59
def prefixEnd_6934133 : Nat := 4983230072969 + 3 ^ 40 * 6934133 * 2
def baseEnd_6934133 : Nat := 3560543151203023906448009

theorem tailTrace_6934133 : CollatzResearch.WordTrace tailWord_6934133 prefixEnd_6934133 3560543151203023906448009 := by
  unfold tailWord_6934133
  simp only [CollatzResearch.WordTrace]
  refine ⟨252908607787827871478103053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168605738525218580985402035 252908607787827871478103053)
  ·
    refine ⟨94840727920435451804288645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252908607787827871478103053 94840727920435451804288645)
    ·
      refine ⟨17782636485081647213304121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94840727920435451804288645 17782636485081647213304121)
      ·
        refine ⟨13336977363811235409978091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17782636485081647213304121 13336977363811235409978091)
        ·
          refine ⟨20005466045716853114967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13336977363811235409978091 20005466045716853114967137)
          ·
            refine ⟨15004099534287639836225353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20005466045716853114967137 15004099534287639836225353)
            ·
              refine ⟨11253074650715729877169015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15004099534287639836225353 11253074650715729877169015)
              ·
                refine ⟨16879611976073594815753523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253074650715729877169015 16879611976073594815753523)
                ·
                  refine ⟨25319417964110392223630285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16879611976073594815753523 25319417964110392223630285)
                  ·
                    refine ⟨9494781736541397083861357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25319417964110392223630285 9494781736541397083861357)
                    ·
                      refine ⟨3560543151203023906448009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9494781736541397083861357 3560543151203023906448009)
                      ·
                        rfl

theorem cell23_6934133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6934133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934133 prefixEnd_6934133 := by exact prefixLift 6934133
  have htrace : WordTrace (prefixWord ++ tailWord_6934133) baseStart_6934133 baseEnd_6934133 := by
    simpa [prefixWord, tailWord_6934133, baseEnd_6934133] using wordTrace_append hprefix tailTrace_6934133
  have hstable : (prefixWord ++ tailWord_6934133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934133).length < 2 ^ (prefixWord ++ tailWord_6934133).sum := by decide
  have hdescent : baseEnd_6934133 < baseStart_6934133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934156 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_6934156 : Nat := 118140960795 + 6934156 * 2 ^ 59
def prefixEnd_6934156 : Nat := 4983230072969 + 3 ^ 40 * 6934156 * 2
def baseEnd_6934156 : Nat := 3560554961258077316460403

theorem tailTrace_6934156 : CollatzResearch.WordTrace tailWord_6934156 prefixEnd_6934156 3560554961258077316460403 := by
  unfold tailWord_6934156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126454723333372273203095161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168606297777829697604126881 126454723333372273203095161)
  ·
    refine ⟨94841042500029204902321371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126454723333372273203095161 94841042500029204902321371)
    ·
      refine ⟨142261563750043807353482057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94841042500029204902321371 142261563750043807353482057)
      ·
        refine ⟨106696172812532855515111543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142261563750043807353482057 106696172812532855515111543)
        ·
          refine ⟨160044259218799283272667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106696172812532855515111543 160044259218799283272667315)
          ·
            refine ⟨240066388828198924909000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160044259218799283272667315 240066388828198924909000973)
            ·
              refine ⟨90024895810574596840875365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240066388828198924909000973 90024895810574596840875365)
              ·
                refine ⟨16879667964482736907664131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90024895810574596840875365 16879667964482736907664131)
                ·
                  refine ⟨25319501946724105361496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16879667964482736907664131 25319501946724105361496197)
                  ·
                    refine ⟨4747406615010769755280537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25319501946724105361496197 4747406615010769755280537)
                    ·
                      refine ⟨3560554961258077316460403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747406615010769755280537 3560554961258077316460403)
                      ·
                        rfl

theorem cell23_6934156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_6934156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934156 prefixEnd_6934156 := by exact prefixLift 6934156
  have htrace : WordTrace (prefixWord ++ tailWord_6934156) baseStart_6934156 baseEnd_6934156 := by
    simpa [prefixWord, tailWord_6934156, baseEnd_6934156] using wordTrace_append hprefix tailTrace_6934156
  have hstable : (prefixWord ++ tailWord_6934156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934156).length < 2 ^ (prefixWord ++ tailWord_6934156).sum := by decide
  have hdescent : baseEnd_6934156 < baseStart_6934156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934179 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 7]
def baseStart_6934179 : Nat := 118140960795 + 6934179 * 2 ^ 59
def prefixEnd_6934179 : Nat := 4983230072969 + 3 ^ 40 * 6934179 * 2
def baseEnd_6934179 : Nat := 395618530145903414052533

theorem tailTrace_6934179 : CollatzResearch.WordTrace tailWord_6934179 prefixEnd_6934179 395618530145903414052533 := by
  unfold tailWord_6934179
  simp only [CollatzResearch.WordTrace]
  refine ⟨252910285545661221334277591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168606857030440814222851727 252910285545661221334277591)
  ·
    refine ⟨379365428318491832001416387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252910285545661221334277591 379365428318491832001416387)
    ·
      refine ⟨569048142477737748002124581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379365428318491832001416387 569048142477737748002124581)
      ·
        refine ⟨106696526714575827750398359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 569048142477737748002124581 106696526714575827750398359)
        ·
          refine ⟨160044790071863741625597539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106696526714575827750398359 160044790071863741625597539)
          ·
            refine ⟨240067185107795612438396309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160044790071863741625597539 240067185107795612438396309)
            ·
              refine ⟨11253149301927919333049827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240067185107795612438396309 11253149301927919333049827)
              ·
                refine ⟨16879723952891878999574741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253149301927919333049827 16879723952891878999574741)
                ·
                  refine ⟨395618530145903414052533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16879723952891878999574741 395618530145903414052533)
                  ·
                    rfl

theorem cell23_6934179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 7].length) (baseStart_6934179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934179 prefixEnd_6934179 := by exact prefixLift 6934179
  have htrace : WordTrace (prefixWord ++ tailWord_6934179) baseStart_6934179 baseEnd_6934179 := by
    simpa [prefixWord, tailWord_6934179, baseEnd_6934179] using wordTrace_append hprefix tailTrace_6934179
  have hstable : (prefixWord ++ tailWord_6934179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934179).length < 2 ^ (prefixWord ++ tailWord_6934179).sum := by decide
  have hdescent : baseEnd_6934179 < baseStart_6934179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934184 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6934184 : Nat := 118140960795 + 6934184 * 2 ^ 59
def prefixEnd_6934184 : Nat := 4983230072969 + 3 ^ 40 * 6934184 * 2
def baseEnd_6934184 : Nat := 3560569338716403206910275

theorem tailTrace_6934184 : CollatzResearch.WordTrace tailWord_6934184 prefixEnd_6934184 3560569338716403206910275 := by
  unfold tailWord_6934184
  simp only [CollatzResearch.WordTrace]
  refine ⟨126455233955321553594104803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168606978607095404792139737 126455233955321553594104803)
  ·
    refine ⟨189682850932982330391157205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126455233955321553594104803 189682850932982330391157205)
    ·
      refine ⟨4445691818741773368542747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 189682850932982330391157205 4445691818741773368542747)
      ·
        refine ⟨6668537728112660052814121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445691818741773368542747 6668537728112660052814121)
        ·
          refine ⟨5001403296084495039610591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6668537728112660052814121 5001403296084495039610591)
          ·
            refine ⟨7502104944126742559415887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001403296084495039610591 7502104944126742559415887)
            ·
              refine ⟨11253157416190113839123831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502104944126742559415887 11253157416190113839123831)
              ·
                refine ⟨16879736124285170758685747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253157416190113839123831 16879736124285170758685747)
                ·
                  refine ⟨25319604186427756138028621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16879736124285170758685747 25319604186427756138028621)
                  ·
                    refine ⟨9494851569910408551760733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25319604186427756138028621 9494851569910408551760733)
                    ·
                      refine ⟨3560569338716403206910275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9494851569910408551760733 3560569338716403206910275)
                      ·
                        rfl

theorem cell23_6934184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6934184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934184 prefixEnd_6934184 := by exact prefixLift 6934184
  have htrace : WordTrace (prefixWord ++ tailWord_6934184) baseStart_6934184 baseEnd_6934184 := by
    simpa [prefixWord, tailWord_6934184, baseEnd_6934184] using wordTrace_append hprefix tailTrace_6934184
  have hstable : (prefixWord ++ tailWord_6934184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934184).length < 2 ^ (prefixWord ++ tailWord_6934184).sum := by decide
  have hdescent : baseEnd_6934184 < baseStart_6934184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934226 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_6934226 : Nat := 118140960795 + 6934226 * 2 ^ 59
def prefixEnd_6934226 : Nat := 4983230072969 + 3 ^ 40 * 6934226 * 2
def baseEnd_6934226 : Nat := 1186863634967964014195027

theorem tailTrace_6934226 : CollatzResearch.WordTrace tailWord_6934226 prefixEnd_6934226 1186863634967964014195027 := by
  unfold tailWord_6934226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63227999944122737090309633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168607999850993965574159021 63227999944122737090309633)
  ·
    refine ⟨47420999958092052817732225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63227999944122737090309633 47420999958092052817732225)
    ·
      refine ⟨35565749968569039613299169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47420999958092052817732225 35565749968569039613299169)
      ·
        refine ⟨26674312476426779709974377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35565749968569039613299169 26674312476426779709974377)
        ·
          refine ⟨20005734357320084782480783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26674312476426779709974377 20005734357320084782480783)
          ·
            refine ⟨30008601535980127173721175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20005734357320084782480783 30008601535980127173721175)
            ·
              refine ⟨45012902303970190760581763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30008601535980127173721175 45012902303970190760581763)
              ·
                refine ⟨67519353455955286140872645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45012902303970190760581763 67519353455955286140872645)
                ·
                  refine ⟨12659878772991616151413621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67519353455955286140872645 12659878772991616151413621)
                  ·
                    refine ⟨1186863634967964014195027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12659878772991616151413621 1186863634967964014195027)
                    ·
                      rfl

theorem cell23_6934226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_6934226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934226 prefixEnd_6934226 := by exact prefixLift 6934226
  have htrace : WordTrace (prefixWord ++ tailWord_6934226) baseStart_6934226 baseEnd_6934226 := by
    simpa [prefixWord, tailWord_6934226, baseEnd_6934226] using wordTrace_append hprefix tailTrace_6934226
  have hstable : (prefixWord ++ tailWord_6934226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934226).length < 2 ^ (prefixWord ++ tailWord_6934226).sum := by decide
  have hdescent : baseEnd_6934226 < baseStart_6934226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934259 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_6934259 : Nat := 118140960795 + 6934259 * 2 ^ 59
def prefixEnd_6934259 : Nat := 4983230072969 + 3 ^ 40 * 6934259 * 2
def baseEnd_6934259 : Nat := 3560607849765490413472429

theorem tailTrace_6934259 : CollatzResearch.WordTrace tailWord_6934259 prefixEnd_6934259 3560607849765490413472429 := by
  unfold tailWord_6934259
  simp only [CollatzResearch.WordTrace]
  refine ⟨252913203385371394997189831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168608802256914263331459887 252913203385371394997189831)
  ·
    refine ⟨379369805078057092495784747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252913203385371394997189831 379369805078057092495784747)
    ·
      refine ⟨569054707617085638743677121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379369805078057092495784747 569054707617085638743677121)
      ·
        refine ⟨426791030712814229057757841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569054707617085638743677121 426791030712814229057757841)
        ·
          refine ⟨320093273034610671793318381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426791030712814229057757841 320093273034610671793318381)
          ·
            refine ⟨120034977387979001922494393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320093273034610671793318381 120034977387979001922494393)
            ·
              refine ⟨90026233040984251441870795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120034977387979001922494393 90026233040984251441870795)
              ·
                refine ⟨135039349561476377162806193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90026233040984251441870795 135039349561476377162806193)
                ·
                  refine ⟨101279512171107282872104645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135039349561476377162806193 101279512171107282872104645)
                  ·
                    refine ⟨18989908532082615538519621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101279512171107282872104645 18989908532082615538519621)
                    ·
                      refine ⟨3560607849765490413472429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18989908532082615538519621 3560607849765490413472429)
                      ·
                        rfl

theorem cell23_6934259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_6934259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934259 prefixEnd_6934259 := by exact prefixLift 6934259
  have htrace : WordTrace (prefixWord ++ tailWord_6934259) baseStart_6934259 baseEnd_6934259 := by
    simpa [prefixWord, tailWord_6934259, baseEnd_6934259] using wordTrace_append hprefix tailTrace_6934259
  have hstable : (prefixWord ++ tailWord_6934259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934259).length < 2 ^ (prefixWord ++ tailWord_6934259).sum := by decide
  have hdescent : baseEnd_6934259 < baseStart_6934259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934260 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6934260 : Nat := 118140960795 + 6934260 * 2 ^ 59
def prefixEnd_6934260 : Nat := 4983230072969 + 3 ^ 40 * 6934260 * 2
def baseEnd_6934260 : Nat := 1186869454415381636519975

theorem tailTrace_6934260 : CollatzResearch.WordTrace tailWord_6934260 prefixEnd_6934260 1186869454415381636519975 := by
  unfold tailWord_6934260
  simp only [CollatzResearch.WordTrace]
  refine ⟨126456619929183886083988117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168608826572245181445317489 126456619929183886083988117)
  ·
    refine ⟨5927654059180494660186943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126456619929183886083988117 5927654059180494660186943)
    ·
      refine ⟨8891481088770741990280415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927654059180494660186943 8891481088770741990280415)
      ·
        refine ⟨13337221633156112985420623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891481088770741990280415 13337221633156112985420623)
        ·
          refine ⟨20005832449734169478130935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337221633156112985420623 20005832449734169478130935)
          ·
            refine ⟨30008748674601254217196403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20005832449734169478130935 30008748674601254217196403)
            ·
              refine ⟨45013123011901881325794605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30008748674601254217196403 45013123011901881325794605)
              ·
                refine ⟨16879921129463205497172977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45013123011901881325794605 16879921129463205497172977)
                ·
                  refine ⟨12659940847097404122879733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16879921129463205497172977 12659940847097404122879733)
                  ·
                    refine ⟨1186869454415381636519975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12659940847097404122879733 1186869454415381636519975)
                    ·
                      rfl

theorem cell23_6934260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6934260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934260 prefixEnd_6934260 := by exact prefixLift 6934260
  have htrace : WordTrace (prefixWord ++ tailWord_6934260) baseStart_6934260 baseEnd_6934260 := by
    simpa [prefixWord, tailWord_6934260, baseEnd_6934260] using wordTrace_append hprefix tailTrace_6934260
  have hstable : (prefixWord ++ tailWord_6934260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934260).length < 2 ^ (prefixWord ++ tailWord_6934260).sum := by decide
  have hdescent : baseEnd_6934260 < baseStart_6934260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934269 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 8]
def baseStart_6934269 : Nat := 118140960795 + 6934269 * 2 ^ 59
def prefixEnd_6934269 : Nat := 4983230072969 + 3 ^ 40 * 6934269 * 2
def baseEnd_6934269 : Nat := 395623664952448374927487

theorem tailTrace_6934269 : CollatzResearch.WordTrace tailWord_6934269 prefixEnd_6934269 395623664952448374927487 := by
  unfold tailWord_6934269
  simp only [CollatzResearch.WordTrace]
  refine ⟨252913568115335166705053861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168609045410223444470035907 252913568115335166705053861)
  ·
    refine ⟨47421294021625343757197599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252913568115335166705053861 47421294021625343757197599)
    ·
      refine ⟨71131941032438015635796399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47421294021625343757197599 71131941032438015635796399)
      ·
        refine ⟨106697911548657023453694599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71131941032438015635796399 106697911548657023453694599)
        ·
          refine ⟨160046867322985535180541899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106697911548657023453694599 160046867322985535180541899)
          ·
            refine ⟨240070300984478302770812849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160046867322985535180541899 240070300984478302770812849)
            ·
              refine ⟨180052725738358727078109637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240070300984478302770812849 180052725738358727078109637)
              ·
                refine ⟨33759886075942261327145557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180052725738358727078109637 33759886075942261327145557)
                ·
                  refine ⟨395623664952448374927487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33759886075942261327145557 395623664952448374927487)
                  ·
                    rfl

theorem cell23_6934269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_6934269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934269 prefixEnd_6934269 := by exact prefixLift 6934269
  have htrace : WordTrace (prefixWord ++ tailWord_6934269) baseStart_6934269 baseEnd_6934269 := by
    simpa [prefixWord, tailWord_6934269, baseEnd_6934269] using wordTrace_append hprefix tailTrace_6934269
  have hstable : (prefixWord ++ tailWord_6934269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934269).length < 2 ^ (prefixWord ++ tailWord_6934269).sum := by decide
  have hdescent : baseEnd_6934269 < baseStart_6934269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934286 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_6934286 : Nat := 118140960795 + 6934286 * 2 ^ 59
def prefixEnd_6934286 : Nat := 4983230072969 + 3 ^ 40 * 6934286 * 2
def baseEnd_6934286 : Nat := 395624634860351311981645

theorem tailTrace_6934286 : CollatzResearch.WordTrace tailWord_6934286 prefixEnd_6934286 395624634860351311981645 := by
  unfold tailWord_6934286
  simp only [CollatzResearch.WordTrace]
  refine ⟨31614273519534197326052839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168609458770849052405615141 31614273519534197326052839)
  ·
    refine ⟨47421410279301295989079259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31614273519534197326052839 47421410279301295989079259)
    ·
      refine ⟨71132115418951943983618889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47421410279301295989079259 71132115418951943983618889)
      ·
        refine ⟨53349086564213957987714167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71132115418951943983618889 53349086564213957987714167)
        ·
          refine ⟨80023629846320936981571251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53349086564213957987714167 80023629846320936981571251)
          ·
            refine ⟨120035444769481405472356877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80023629846320936981571251 120035444769481405472356877)
            ·
              refine ⟨45013291788555527052133829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120035444769481405472356877 45013291788555527052133829)
              ·
                refine ⟨8439992210354161322275093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45013291788555527052133829 8439992210354161322275093)
                ·
                  refine ⟨395624634860351311981645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8439992210354161322275093 395624634860351311981645)
                  ·
                    rfl

theorem cell23_6934286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_6934286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934286 prefixEnd_6934286 := by exact prefixLift 6934286
  have htrace : WordTrace (prefixWord ++ tailWord_6934286) baseStart_6934286 baseEnd_6934286 := by
    simpa [prefixWord, tailWord_6934286, baseEnd_6934286] using wordTrace_append hprefix tailTrace_6934286
  have hstable : (prefixWord ++ tailWord_6934286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934286).length < 2 ^ (prefixWord ++ tailWord_6934286).sum := by decide
  have hdescent : baseEnd_6934286 < baseStart_6934286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934289 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_6934289 : Nat := 118140960795 + 6934289 * 2 ^ 59
def prefixEnd_6934289 : Nat := 4983230072969 + 3 ^ 40 * 6934289 * 2
def baseEnd_6934289 : Nat := 3560623254185125296097291

theorem tailTrace_6934289 : CollatzResearch.WordTrace tailWord_6934289 prefixEnd_6934289 3560623254185125296097291 := by
  unfold tailWord_6934289
  simp only [CollatzResearch.WordTrace]
  refine ⟨252914297575262710120781921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168609531716841806747187947 252914297575262710120781921)
  ·
    refine ⟨189685723181447032590586441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252914297575262710120781921 189685723181447032590586441)
    ·
      refine ⟨142264292386085274442939831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189685723181447032590586441 142264292386085274442939831)
      ·
        refine ⟨213396438579127911664409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142264292386085274442939831 213396438579127911664409747)
        ·
          refine ⟨320094657868691867496614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213396438579127911664409747 320094657868691867496614621)
          ·
            refine ⟨120035496700759450311230483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320094657868691867496614621 120035496700759450311230483)
            ·
              refine ⟨180053245051139175466845725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120035496700759450311230483 180053245051139175466845725)
              ·
                refine ⟨67519966894177190800067147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180053245051139175466845725 67519966894177190800067147)
                ·
                  refine ⟨101279950341265786200100721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67519966894177190800067147 101279950341265786200100721)
                  ·
                    refine ⟨75959962755949339650075541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101279950341265786200100721 75959962755949339650075541)
                    ·
                      refine ⟨3560623254185125296097291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75959962755949339650075541 3560623254185125296097291)
                      ·
                        rfl

theorem cell23_6934289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_6934289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934289 prefixEnd_6934289 := by exact prefixLift 6934289
  have htrace : WordTrace (prefixWord ++ tailWord_6934289) baseStart_6934289 baseEnd_6934289 := by
    simpa [prefixWord, tailWord_6934289, baseEnd_6934289] using wordTrace_append hprefix tailTrace_6934289
  have hstable : (prefixWord ++ tailWord_6934289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934289).length < 2 ^ (prefixWord ++ tailWord_6934289).sum := by decide
  have hdescent : baseEnd_6934289 < baseStart_6934289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934316 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_6934316 : Nat := 118140960795 + 6934316 * 2 ^ 59
def prefixEnd_6934316 : Nat := 4983230072969 + 3 ^ 40 * 6934316 * 2
def baseEnd_6934316 : Nat := 1186879039387598896819889

theorem tailTrace_6934316 : CollatzResearch.WordTrace tailWord_6934316 prefixEnd_6934316 1186879039387598896819889 := by
  unfold tailWord_6934316
  simp only [CollatzResearch.WordTrace]
  refine ⟨126457641173082446866007401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168610188230776595821343201 126457641173082446866007401)
  ·
    refine ⟨94843230879811835149505551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126457641173082446866007401 94843230879811835149505551)
    ·
      refine ⟨142264846319717752724258327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94843230879811835149505551 142264846319717752724258327)
      ·
        refine ⟨213397269479576629086387491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142264846319717752724258327 213397269479576629086387491)
        ·
          refine ⟨320095904219364943629581237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213397269479576629086387491 320095904219364943629581237)
          ·
            refine ⟨30008991020565463465273241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320095904219364943629581237 30008991020565463465273241)
            ·
              refine ⟨22506743265424097598954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30008991020565463465273241 22506743265424097598954931)
              ·
                refine ⟨33760114898136146398432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22506743265424097598954931 33760114898136146398432397)
                ·
                  refine ⟨12660043086801054899412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33760114898136146398432397 12660043086801054899412149)
                  ·
                    refine ⟨1186879039387598896819889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12660043086801054899412149 1186879039387598896819889)
                    ·
                      rfl

theorem cell23_6934316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_6934316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934316 prefixEnd_6934316 := by exact prefixLift 6934316
  have htrace : WordTrace (prefixWord ++ tailWord_6934316) baseStart_6934316 baseEnd_6934316 := by
    simpa [prefixWord, tailWord_6934316, baseEnd_6934316] using wordTrace_append hprefix tailTrace_6934316
  have hstable : (prefixWord ++ tailWord_6934316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934316).length < 2 ^ (prefixWord ++ tailWord_6934316).sum := by decide
  have hdescent : baseEnd_6934316 < baseStart_6934316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934370 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6934370 : Nat := 118140960795 + 6934370 * 2 ^ 59
def prefixEnd_6934370 : Nat := 4983230072969 + 3 ^ 40 * 6934370 * 2
def baseEnd_6934370 : Nat := 3560664846118139479184419

theorem tailTrace_6934370 : CollatzResearch.WordTrace tailWord_6934370 prefixEnd_6934370 3560664846118139479184419 := by
  unfold tailWord_6934370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63229312971992315238620141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168611501258646173969653709 63229312971992315238620141)
  ·
    refine ⟨23710992364497118214482553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63229312971992315238620141 23710992364497118214482553)
    ·
      refine ⟨17783244273372838660861915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23710992364497118214482553 17783244273372838660861915)
      ·
        refine ⟨26674866410059257991292873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17783244273372838660861915 26674866410059257991292873)
        ·
          refine ⟨20006149807544443493469655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26674866410059257991292873 20006149807544443493469655)
          ·
            refine ⟨30009224711316665240204483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20006149807544443493469655 30009224711316665240204483)
            ·
              refine ⟨45013837066974997860306725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30009224711316665240204483 45013837066974997860306725)
              ·
                refine ⟨8440094450057812098807511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45013837066974997860306725 8440094450057812098807511)
                ·
                  refine ⟨12660141675086718148211267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440094450057812098807511 12660141675086718148211267)
                  ·
                    refine ⟨18990212512630077222316901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12660141675086718148211267 18990212512630077222316901)
                    ·
                      refine ⟨3560664846118139479184419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18990212512630077222316901 3560664846118139479184419)
                      ·
                        rfl

theorem cell23_6934370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6934370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934370 prefixEnd_6934370 := by exact prefixLift 6934370
  have htrace : WordTrace (prefixWord ++ tailWord_6934370) baseStart_6934370 baseEnd_6934370 := by
    simpa [prefixWord, tailWord_6934370, baseEnd_6934370] using wordTrace_append hprefix tailTrace_6934370
  have hstable : (prefixWord ++ tailWord_6934370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934370).length < 2 ^ (prefixWord ++ tailWord_6934370).sum := by decide
  have hdescent : baseEnd_6934370 < baseStart_6934370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934376 : List Nat := [2, 1, 4, 2, 1, 1, 3, 9]
def baseStart_6934376 : Nat := 118140960795 + 6934376 * 2 ^ 59
def prefixEnd_6934376 : Nat := 4983230072969 + 3 ^ 40 * 6934376 * 2
def baseEnd_6934376 : Nat := 131876589888965424285533

theorem tailTrace_6934376 : CollatzResearch.WordTrace tailWord_6934376 prefixEnd_6934376 131876589888965424285533 := by
  unfold tailWord_6934376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126458735362973761989599491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168611647150631682652799321 126458735362973761989599491)
  ·
    refine ⟨189688103044460642984399237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126458735362973761989599491 189688103044460642984399237)
    ·
      refine ⟨35566519320836370559574857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189688103044460642984399237 35566519320836370559574857)
      ·
        refine ⟨26674889490627277919681143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35566519320836370559574857 26674889490627277919681143)
        ·
          refine ⟨40012334235940916879521715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26674889490627277919681143 40012334235940916879521715)
          ·
            refine ⟨60018501353911375319282573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40012334235940916879521715 60018501353911375319282573)
            ·
              refine ⟨22506938007716765744730965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60018501353911375319282573 22506938007716765744730965)
              ·
                refine ⟨131876589888965424285533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22506938007716765744730965 131876589888965424285533)
                ·
                  rfl

theorem cell23_6934376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 9].length) (baseStart_6934376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934376 prefixEnd_6934376 := by exact prefixLift 6934376
  have htrace : WordTrace (prefixWord ++ tailWord_6934376) baseStart_6934376 baseEnd_6934376 := by
    simpa [prefixWord, tailWord_6934376, baseEnd_6934376] using wordTrace_append hprefix tailTrace_6934376
  have hstable : (prefixWord ++ tailWord_6934376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934376).length < 2 ^ (prefixWord ++ tailWord_6934376).sum := by decide
  have hdescent : baseEnd_6934376 < baseStart_6934376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934424 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6934424 : Nat := 118140960795 + 6934424 * 2 ^ 59
def prefixEnd_6934424 : Nat := 4983230072969 + 3 ^ 40 * 6934424 * 2
def baseEnd_6934424 : Nat := 3560692574073482267909171

theorem tailTrace_6934424 : CollatzResearch.WordTrace tailWord_6934424 prefixEnd_6934424 3560692574073482267909171 := by
  unfold tailWord_6934424
  simp only [CollatzResearch.WordTrace]
  refine ⟨126459610714886814088473163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168612814286515752117964217 126459610714886814088473163)
  ·
    refine ⟨189689416072330221132709745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126459610714886814088473163 189689416072330221132709745)
    ·
      refine ⟨142267062054247665849532309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189689416072330221132709745 142267062054247665849532309)
      ·
        refine ⟨6668768533792859336696827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142267062054247665849532309 6668768533792859336696827)
        ·
          refine ⟨10003152800689289005045241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668768533792859336696827 10003152800689289005045241)
          ·
            refine ⟨7502364600516966753783931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10003152800689289005045241 7502364600516966753783931)
            ·
              refine ⟨11253546900775450130675897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502364600516966753783931 11253546900775450130675897)
              ·
                refine ⟨8440160175581587598006923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11253546900775450130675897 8440160175581587598006923)
                ·
                  refine ⟨12660240263372381397010385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440160175581587598006923 12660240263372381397010385)
                  ·
                    refine ⟨9495180197529286047757789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12660240263372381397010385 9495180197529286047757789)
                    ·
                      refine ⟨3560692574073482267909171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495180197529286047757789 3560692574073482267909171)
                      ·
                        rfl

theorem cell23_6934424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6934424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934424 prefixEnd_6934424 := by exact prefixLift 6934424
  have htrace : WordTrace (prefixWord ++ tailWord_6934424) baseStart_6934424 baseEnd_6934424 := by
    simpa [prefixWord, tailWord_6934424, baseEnd_6934424] using wordTrace_append hprefix tailTrace_6934424
  have hstable : (prefixWord ++ tailWord_6934424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934424).length < 2 ^ (prefixWord ++ tailWord_6934424).sum := by decide
  have hdescent : baseEnd_6934424 < baseStart_6934424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934447 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 1, 3, 2]
def baseStart_6934447 : Nat := 118140960795 + 6934447 * 2 ^ 59
def prefixEnd_6934447 : Nat := 4983230072969 + 3 ^ 40 * 6934447 * 2
def baseEnd_6934447 : Nat := 3560704384128535677921565

theorem tailTrace_6934447 : CollatzResearch.WordTrace tailWord_6934447 prefixEnd_6934447 3560704384128535677921565 := by
  unfold tailWord_6934447
  simp only [CollatzResearch.WordTrace]
  refine ⟨252920060308690303105033595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168613373539126868736689063 252920060308690303105033595)
  ·
    refine ⟨379380090463035454657550393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252920060308690303105033595 379380090463035454657550393)
    ·
      refine ⟨284535067847276590993162795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379380090463035454657550393 284535067847276590993162795)
      ·
        refine ⟨426802601770914886489744193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284535067847276590993162795 426802601770914886489744193)
        ·
          refine ⟨320101951328186164867308145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426802601770914886489744193 320101951328186164867308145)
          ·
            refine ⟨240076463496139623650481109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320101951328186164867308145 240076463496139623650481109)
            ·
              refine ⟨5626792113190772429308151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 240076463496139623650481109 5626792113190772429308151)
              ·
                refine ⟨8440188169786158643962227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626792113190772429308151 8440188169786158643962227)
                ·
                  refine ⟨12660282254679237965943341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440188169786158643962227 12660282254679237965943341)
                  ·
                    refine ⟨4747605845504714237228753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12660282254679237965943341 4747605845504714237228753)
                    ·
                      refine ⟨3560704384128535677921565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747605845504714237228753 3560704384128535677921565)
                      ·
                        rfl

theorem cell23_6934447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 3, 2].length) (baseStart_6934447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934447 prefixEnd_6934447 := by exact prefixLift 6934447
  have htrace : WordTrace (prefixWord ++ tailWord_6934447) baseStart_6934447 baseEnd_6934447 := by
    simpa [prefixWord, tailWord_6934447, baseEnd_6934447] using wordTrace_append hprefix tailTrace_6934447
  have hstable : (prefixWord ++ tailWord_6934447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934447).length < 2 ^ (prefixWord ++ tailWord_6934447).sum := by decide
  have hdescent : baseEnd_6934447 < baseStart_6934447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934498 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6934498 : Nat := 118140960795 + 6934498 * 2 ^ 59
def prefixEnd_6934498 : Nat := 4983230072969 + 3 ^ 40 * 6934498 * 2
def baseEnd_6934498 : Nat := 3560730571641914978383831

theorem tailTrace_6934498 : CollatzResearch.WordTrace tailWord_6934498 prefixEnd_6934498 3560730571641914978383831 := by
  unfold tailWord_6934498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230480107876384703785037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168614613621003692543426765 63230480107876384703785037)
  ·
    refine ⟨23711430040453644263919389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63230480107876384703785037 23711430040453644263919389)
    ·
      refine ⟨8891786265170116598969771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23711430040453644263919389 8891786265170116598969771)
      ·
        refine ⟨13337679397755174898454657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891786265170116598969771 13337679397755174898454657)
        ·
          refine ⟨10003259548316381173840993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13337679397755174898454657 10003259548316381173840993)
          ·
            refine ⟨7502444661237285880380745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10003259548316381173840993 7502444661237285880380745)
            ·
              refine ⟨5626833495927964410285559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7502444661237285880380745 5626833495927964410285559)
              ·
                refine ⟨8440250243891946615428339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626833495927964410285559 8440250243891946615428339)
                ·
                  refine ⟨12660375365837919923142509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440250243891946615428339 12660375365837919923142509)
                  ·
                    refine ⟨4747640762189219971178441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12660375365837919923142509 4747640762189219971178441)
                    ·
                      refine ⟨3560730571641914978383831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747640762189219971178441 3560730571641914978383831)
                      ·
                        rfl

theorem cell23_6934498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6934498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934498 prefixEnd_6934498 := by exact prefixLift 6934498
  have htrace : WordTrace (prefixWord ++ tailWord_6934498) baseStart_6934498 baseEnd_6934498 := by
    simpa [prefixWord, tailWord_6934498, baseEnd_6934498] using wordTrace_append hprefix tailTrace_6934498
  have hstable : (prefixWord ++ tailWord_6934498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934498).length < 2 ^ (prefixWord ++ tailWord_6934498).sum := by decide
  have hdescent : baseEnd_6934498 < baseStart_6934498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934500 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 5]
def baseStart_6934500 : Nat := 118140960795 + 6934500 * 2 ^ 59
def prefixEnd_6934500 : Nat := 4983230072969 + 3 ^ 40 * 6934500 * 2
def baseEnd_6934500 : Nat := 395636844289247107839869

theorem tailTrace_6934500 : CollatzResearch.WordTrace tailWord_6934500 prefixEnd_6934500 395636844289247107839869 := by
  unfold tailWord_6934500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126460996688749146578356477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168614662251665528771141969 126460996688749146578356477)
  ·
    refine ⟨47422873758280929966883679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126460996688749146578356477 47422873758280929966883679)
    ·
      refine ⟨71134310637421394950325519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47422873758280929966883679 71134310637421394950325519)
      ·
        refine ⟨106701465956132092425488279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71134310637421394950325519 106701465956132092425488279)
        ·
          refine ⟨160052198934198138638232419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106701465956132092425488279 160052198934198138638232419)
          ·
            refine ⟨240078298401297207957348629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160052198934198138638232419 240078298401297207957348629)
            ·
              refine ⟨11253670237560806623000717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240078298401297207957348629 11253670237560806623000717)
              ·
                refine ⟨4220126339085302483625269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11253670237560806623000717 4220126339085302483625269)
                ·
                  refine ⟨395636844289247107839869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220126339085302483625269 395636844289247107839869)
                  ·
                    rfl

theorem cell23_6934500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_6934500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934500 prefixEnd_6934500 := by exact prefixLift 6934500
  have htrace : WordTrace (prefixWord ++ tailWord_6934500) baseStart_6934500 baseEnd_6934500 := by
    simpa [prefixWord, tailWord_6934500, baseEnd_6934500] using wordTrace_append hprefix tailTrace_6934500
  have hstable : (prefixWord ++ tailWord_6934500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934500).length < 2 ^ (prefixWord ++ tailWord_6934500).sum := by decide
  have hdescent : baseEnd_6934500 < baseStart_6934500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934510 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_6934510 : Nat := 118140960795 + 6934510 * 2 ^ 59
def prefixEnd_6934510 : Nat := 4983230072969 + 3 ^ 40 * 6934510 * 2
def baseEnd_6934510 : Nat := 3560736733409768931433775

theorem tailTrace_6934510 : CollatzResearch.WordTrace tailWord_6934510 prefixEnd_6934510 3560736733409768931433775 := by
  unfold tailWord_6934510
  simp only [CollatzResearch.WordTrace]
  refine ⟨31615294763432758108072123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168614905404974709909717989 31615294763432758108072123)
  ·
    refine ⟨47422942145149137162108185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31615294763432758108072123 47422942145149137162108185)
    ·
      refine ⟨35567206608861852871581139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47422942145149137162108185 35567206608861852871581139)
      ·
        refine ⟨53350809913292779307371709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35567206608861852871581139 53350809913292779307371709)
        ·
          refine ⟨20006553717484792240264391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53350809913292779307371709 20006553717484792240264391)
          ·
            refine ⟨30009830576227188360396587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20006553717484792240264391 30009830576227188360396587)
            ·
              refine ⟨45014745864340782540594881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30009830576227188360396587 45014745864340782540594881)
              ·
                refine ⟨33761059398255586905446161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45014745864340782540594881 33761059398255586905446161)
                ·
                  refine ⟨25320794548691690179084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33761059398255586905446161 25320794548691690179084621)
                  ·
                    refine ⟨9495297955759383817156733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25320794548691690179084621 9495297955759383817156733)
                    ·
                      refine ⟨3560736733409768931433775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495297955759383817156733 3560736733409768931433775)
                      ·
                        rfl

theorem cell23_6934510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_6934510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934510 prefixEnd_6934510 := by exact prefixLift 6934510
  have htrace : WordTrace (prefixWord ++ tailWord_6934510) baseStart_6934510 baseEnd_6934510 := by
    simpa [prefixWord, tailWord_6934510, baseEnd_6934510] using wordTrace_append hprefix tailTrace_6934510
  have hstable : (prefixWord ++ tailWord_6934510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934510).length < 2 ^ (prefixWord ++ tailWord_6934510).sum := by decide
  have hdescent : baseEnd_6934510 < baseStart_6934510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934533 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_6934533 : Nat := 118140960795 + 6934533 * 2 ^ 59
def prefixEnd_6934533 : Nat := 4983230072969 + 3 ^ 40 * 6934533 * 2
def baseEnd_6934533 : Nat := 3560748543464822341446169

theorem tailTrace_6934533 : CollatzResearch.WordTrace tailWord_6934533 prefixEnd_6934533 3560748543464822341446169 := by
  unfold tailWord_6934533
  simp only [CollatzResearch.WordTrace]
  refine ⟨252923196986378739792664253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168615464657585826528442835 252923196986378739792664253)
  ·
    refine ⟨94846198869892027422249095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252923196986378739792664253 94846198869892027422249095)
    ·
      refine ⟨142269298304838041133373643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94846198869892027422249095 142269298304838041133373643)
      ·
        refine ⟨213403947457257061700060465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142269298304838041133373643 213403947457257061700060465)
        ·
          refine ⟨160052960592942796275045349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213403947457257061700060465 160052960592942796275045349)
          ·
            refine ⟨30009930111176774301571003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160052960592942796275045349 30009930111176774301571003)
            ·
              refine ⟨45014895166765161452356505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30009930111176774301571003 45014895166765161452356505)
              ·
                refine ⟨33761171375073871089267379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45014895166765161452356505 33761171375073871089267379)
                ·
                  refine ⟨50641757062610806633901069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33761171375073871089267379 50641757062610806633901069)
                  ·
                    refine ⟨18990658898479052487712901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50641757062610806633901069 18990658898479052487712901)
                    ·
                      refine ⟨3560748543464822341446169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18990658898479052487712901 3560748543464822341446169)
                      ·
                        rfl

theorem cell23_6934533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_6934533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934533 prefixEnd_6934533 := by exact prefixLift 6934533
  have htrace : WordTrace (prefixWord ++ tailWord_6934533) baseStart_6934533 baseEnd_6934533 := by
    simpa [prefixWord, tailWord_6934533, baseEnd_6934533] using wordTrace_append hprefix tailTrace_6934533
  have hstable : (prefixWord ++ tailWord_6934533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934533).length < 2 ^ (prefixWord ++ tailWord_6934533).sum := by decide
  have hdescent : baseEnd_6934533 < baseStart_6934533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934577 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_6934577 : Nat := 118140960795 + 6934577 * 2 ^ 59
def prefixEnd_6934577 : Nat := 4983230072969 + 3 ^ 40 * 6934577 * 2
def baseEnd_6934577 : Nat := 1186923712204540056431989

theorem tailTrace_6934577 : CollatzResearch.WordTrace tailWord_6934577 prefixEnd_6934577 1186923712204540056431989 := by
  unfold tailWord_6934577
  simp only [CollatzResearch.WordTrace]
  refine ⟨252924801798219335307265985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168616534532146223538177323 252924801798219335307265985)
  ·
    refine ⟨189693601348664501480449489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252924801798219335307265985 189693601348664501480449489)
    ·
      refine ⟨142270201011498376110337117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189693601348664501480449489 142270201011498376110337117)
      ·
        refine ⟨53351325379311891041376419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142270201011498376110337117 53351325379311891041376419)
        ·
          refine ⟨80026988068967836562064629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53351325379311891041376419 80026988068967836562064629)
          ·
            refine ⟨7502530131465734677693559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80026988068967836562064629 7502530131465734677693559)
            ·
              refine ⟨11253795197198602016540339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502530131465734677693559 11253795197198602016540339)
              ·
                refine ⟨16880692795797903024810509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253795197198602016540339 16880692795797903024810509)
                ·
                  refine ⟨6330259798424213634303941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16880692795797903024810509 6330259798424213634303941)
                  ·
                    refine ⟨1186923712204540056431989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330259798424213634303941 1186923712204540056431989)
                    ·
                      rfl

theorem cell23_6934577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_6934577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934577 prefixEnd_6934577 := by exact prefixLift 6934577
  have htrace : WordTrace (prefixWord ++ tailWord_6934577) baseStart_6934577 baseEnd_6934577 := by
    simpa [prefixWord, tailWord_6934577, baseEnd_6934577] using wordTrace_append hprefix tailTrace_6934577
  have hstable : (prefixWord ++ tailWord_6934577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934577).length < 2 ^ (prefixWord ++ tailWord_6934577).sum := by decide
  have hdescent : baseEnd_6934577 < baseStart_6934577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934603 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 3, 5]
def baseStart_6934603 : Nat := 118140960795 + 6934603 * 2 ^ 59
def prefixEnd_6934603 : Nat := 4983230072969 + 3 ^ 40 * 6934603 * 2
def baseEnd_6934603 : Nat := 1186928162370212355856949

theorem tailTrace_6934603 : CollatzResearch.WordTrace tailWord_6934603 prefixEnd_6934603 1186928162370212355856949 := by
  unfold tailWord_6934603
  simp only [CollatzResearch.WordTrace]
  refine ⟨252925750096125141747712463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168617166730750094498474975 252925750096125141747712463)
  ·
    refine ⟨379388625144187712621568695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252925750096125141747712463 379388625144187712621568695)
    ·
      refine ⟨569082937716281568932353043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379388625144187712621568695 569082937716281568932353043)
      ·
        refine ⟨853624406574422353398529565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569082937716281568932353043 853624406574422353398529565)
        ·
          refine ⟨320109152465408382524448587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853624406574422353398529565 320109152465408382524448587)
          ·
            refine ⟨480163728698112573786672881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320109152465408382524448587 480163728698112573786672881)
            ·
              refine ⟨360122796523584430340004661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480163728698112573786672881 360122796523584430340004661)
              ·
                refine ⟨33761512174086040344375437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360122796523584430340004661 33761512174086040344375437)
                ·
                  refine ⟨12660567065282265129140789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33761512174086040344375437 12660567065282265129140789)
                  ·
                    refine ⟨1186928162370212355856949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12660567065282265129140789 1186928162370212355856949)
                    ·
                      rfl

theorem cell23_6934603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].length) (baseStart_6934603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934603 prefixEnd_6934603 := by exact prefixLift 6934603
  have htrace : WordTrace (prefixWord ++ tailWord_6934603) baseStart_6934603 baseEnd_6934603 := by
    simpa [prefixWord, tailWord_6934603, baseEnd_6934603] using wordTrace_append hprefix tailTrace_6934603
  have hstable : (prefixWord ++ tailWord_6934603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934603).length < 2 ^ (prefixWord ++ tailWord_6934603).sum := by decide
  have hdescent : baseEnd_6934603 < baseStart_6934603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934627 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6934627 : Nat := 118140960795 + 6934627 * 2 ^ 59
def prefixEnd_6934627 : Nat := 4983230072969 + 3 ^ 40 * 6934627 * 2
def baseEnd_6934627 : Nat := 3560796810646344973670737

theorem tailTrace_6934627 : CollatzResearch.WordTrace tailWord_6934627 prefixEnd_6934627 3560796810646344973670737 := by
  unfold tailWord_6934627
  simp only [CollatzResearch.WordTrace]
  refine ⟨252926625448038193846586135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168617750298692129231057423 252926625448038193846586135)
  ·
    refine ⟨379389938172057290769879203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252926625448038193846586135 379389938172057290769879203)
    ·
      refine ⟨569084907258085936154818805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379389938172057290769879203 569084907258085936154818805)
      ·
        refine ⟨53351710055445556514514263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569084907258085936154818805 53351710055445556514514263)
        ·
          refine ⟨80027565083168334771771395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53351710055445556514514263 80027565083168334771771395)
          ·
            refine ⟨120041347624752502157657093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80027565083168334771771395 120041347624752502157657093)
            ·
              refine ⟨22507752679641094154560705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120041347624752502157657093 22507752679641094154560705)
              ·
                refine ⟨16880814509730820615920529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22507752679641094154560705 16880814509730820615920529)
                ·
                  refine ⟨12660610882298115461940397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16880814509730820615920529 12660610882298115461940397)
                  ·
                    refine ⟨4747729080861793298227649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12660610882298115461940397 4747729080861793298227649)
                    ·
                      refine ⟨3560796810646344973670737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747729080861793298227649 3560796810646344973670737)
                      ·
                        rfl

theorem cell23_6934627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6934627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934627 prefixEnd_6934627 := by exact prefixLift 6934627
  have htrace : WordTrace (prefixWord ++ tailWord_6934627) baseStart_6934627 baseEnd_6934627 := by
    simpa [prefixWord, tailWord_6934627, baseEnd_6934627] using wordTrace_append hprefix tailTrace_6934627
  have hstable : (prefixWord ++ tailWord_6934627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934627).length < 2 ^ (prefixWord ++ tailWord_6934627).sum := by decide
  have hdescent : baseEnd_6934627 < baseStart_6934627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934633 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_6934633 : Nat := 118140960795 + 6934633 * 2 ^ 59
def prefixEnd_6934633 : Nat := 4983230072969 + 3 ^ 40 * 6934633 * 2
def baseEnd_6934633 : Nat := 1186933297176757316731903

theorem tailTrace_6934633 : CollatzResearch.WordTrace tailWord_6934633 prefixEnd_6934633 1186933297176757316731903 := by
  unfold tailWord_6934633
  simp only [CollatzResearch.WordTrace]
  refine ⟨252926844286016456871304553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168617896190677637914203035 252926844286016456871304553)
  ·
    refine ⟨189695133214512342653478415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252926844286016456871304553 189695133214512342653478415)
    ·
      refine ⟨284542699821768513980217623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189695133214512342653478415 284542699821768513980217623)
      ·
        refine ⟨426814049732652770970326435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284542699821768513980217623 426814049732652770970326435)
        ·
          refine ⟨640221074598979156455489653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426814049732652770970326435 640221074598979156455489653)
          ·
            refine ⟨60020725743654295917702155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 640221074598979156455489653 60020725743654295917702155)
            ·
              refine ⟨90031088615481443876553233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60020725743654295917702155 90031088615481443876553233)
              ·
                refine ⟨67523316461611082907414925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90031088615481443876553233 67523316461611082907414925)
                ·
                  refine ⟨25321243673104156090280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67523316461611082907414925 25321243673104156090280597)
                  ·
                    refine ⟨1186933297176757316731903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25321243673104156090280597 1186933297176757316731903)
                    ·
                      rfl

theorem cell23_6934633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_6934633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934633 prefixEnd_6934633 := by exact prefixLift 6934633
  have htrace : WordTrace (prefixWord ++ tailWord_6934633) baseStart_6934633 baseEnd_6934633 := by
    simpa [prefixWord, tailWord_6934633, baseEnd_6934633] using wordTrace_append hprefix tailTrace_6934633
  have hstable : (prefixWord ++ tailWord_6934633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934633).length < 2 ^ (prefixWord ++ tailWord_6934633).sum := by decide
  have hdescent : baseEnd_6934633 < baseStart_6934633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934640 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_6934640 : Nat := 118140960795 + 6934640 * 2 ^ 59
def prefixEnd_6934640 : Nat := 4983230072969 + 3 ^ 40 * 6934640 * 2
def baseEnd_6934640 : Nat := 3560803485894853422808177

theorem tailTrace_6934640 : CollatzResearch.WordTrace tailWord_6934640 prefixEnd_6934640 3560803485894853422808177 := by
  unfold tailWord_6934640
  simp only [CollatzResearch.WordTrace]
  refine ⟨126463549798495548533404687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168618066397994064711206249 126463549798495548533404687)
  ·
    refine ⟨189695324697743322800107031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126463549798495548533404687 189695324697743322800107031)
    ·
      refine ⟨284542987046614984200160547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189695324697743322800107031 284542987046614984200160547)
      ·
        refine ⟨426814480569922476300240821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284542987046614984200160547 426814480569922476300240821)
        ·
          refine ⟨40013857553430232153147577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426814480569922476300240821 40013857553430232153147577)
          ·
            refine ⟨30010393165072674114860683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40013857553430232153147577 30010393165072674114860683)
            ·
              refine ⟨45015589747609011172291025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30010393165072674114860683 45015589747609011172291025)
              ·
                refine ⟨33761692310706758379218269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45015589747609011172291025 33761692310706758379218269)
                ·
                  refine ⟨12660634616515034392206851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33761692310706758379218269 12660634616515034392206851)
                  ·
                    refine ⟨18990951924772551588310277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12660634616515034392206851 18990951924772551588310277)
                    ·
                      refine ⟨3560803485894853422808177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18990951924772551588310277 3560803485894853422808177)
                      ·
                        rfl

theorem cell23_6934640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_6934640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934640 prefixEnd_6934640 := by exact prefixLift 6934640
  have htrace : WordTrace (prefixWord ++ tailWord_6934640) baseStart_6934640 baseEnd_6934640 := by
    simpa [prefixWord, tailWord_6934640, baseEnd_6934640] using wordTrace_append hprefix tailTrace_6934640
  have hstable : (prefixWord ++ tailWord_6934640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934640).length < 2 ^ (prefixWord ++ tailWord_6934640).sum := by decide
  have hdescent : baseEnd_6934640 < baseStart_6934640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934663 : List Nat := [1, 1, 4, 2, 1, 1, 2, 11]
def baseStart_6934663 : Nat := 118140960795 + 6934663 * 2 ^ 59
def prefixEnd_6934663 : Nat := 4983230072969 + 3 ^ 40 * 6934663 * 2
def baseEnd_6934663 : Nat := 131882047998144697511873

theorem tailTrace_6934663 : CollatzResearch.WordTrace tailWord_6934663 prefixEnd_6934663 131882047998144697511873 := by
  unfold tailWord_6934663
  simp only [CollatzResearch.WordTrace]
  refine ⟨252927938475907771994896643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168618625650605181329931095 252927938475907771994896643)
  ·
    refine ⟨379391907713861657992344965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252927938475907771994896643 379391907713861657992344965)
    ·
      refine ⟨71135982696349060873564681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379391907713861657992344965 71135982696349060873564681)
      ·
        refine ⟨53351987022261795655173511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71135982696349060873564681 53351987022261795655173511)
        ·
          refine ⟨80027980533392693482760267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53351987022261795655173511 80027980533392693482760267)
          ·
            refine ⟨120041970800089040224140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80027980533392693482760267 120041970800089040224140401)
            ·
              refine ⟨90031478100066780168105301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120041970800089040224140401 90031478100066780168105301)
              ·
                refine ⟨131882047998144697511873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90031478100066780168105301 131882047998144697511873)
                ·
                  rfl

theorem cell23_6934663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 11].length) (baseStart_6934663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934663 prefixEnd_6934663 := by exact prefixLift 6934663
  have htrace : WordTrace (prefixWord ++ tailWord_6934663) baseStart_6934663 baseEnd_6934663 := by
    simpa [prefixWord, tailWord_6934663, baseEnd_6934663] using wordTrace_append hprefix tailTrace_6934663
  have hstable : (prefixWord ++ tailWord_6934663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934663).length < 2 ^ (prefixWord ++ tailWord_6934663).sum := by decide
  have hdescent : baseEnd_6934663 < baseStart_6934663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934674 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6934674 : Nat := 118140960795 + 6934674 * 2 ^ 59
def prefixEnd_6934674 : Nat := 4983230072969 + 3 ^ 40 * 6934674 * 2
def baseEnd_6934674 : Nat := 3560820944237106289783021

theorem tailTrace_6934674 : CollatzResearch.WordTrace tailWord_6934674 prefixEnd_6934674 3560820944237106289783021 := by
  unfold tailWord_6934674
  simp only [CollatzResearch.WordTrace]
  refine ⟨63232084919716980218386769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168618893119245280582364717 63232084919716980218386769)
  ·
    refine ⟨47424063689787735163790077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63232084919716980218386769 47424063689787735163790077)
    ·
      refine ⟨17784023883670400686421279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47424063689787735163790077 17784023883670400686421279)
      ·
        refine ⟨26676035825505601029631919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784023883670400686421279 26676035825505601029631919)
        ·
          refine ⟨40014053738258401544447879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26676035825505601029631919 40014053738258401544447879)
          ·
            refine ⟨60021080607387602316671819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40014053738258401544447879 60021080607387602316671819)
            ·
              refine ⟨90031620911081403475007729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60021080607387602316671819 90031620911081403475007729)
              ·
                refine ⟨67523715683311052606255797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90031620911081403475007729 67523715683311052606255797)
                ·
                  refine ⟨6330348345310411181836481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67523715683311052606255797 6330348345310411181836481)
                  ·
                    refine ⟨4747761258982808386377361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330348345310411181836481 4747761258982808386377361)
                    ·
                      refine ⟨3560820944237106289783021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747761258982808386377361 3560820944237106289783021)
                      ·
                        rfl

theorem cell23_6934674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6934674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934674 prefixEnd_6934674 := by exact prefixLift 6934674
  have htrace : WordTrace (prefixWord ++ tailWord_6934674) baseStart_6934674 baseEnd_6934674 := by
    simpa [prefixWord, tailWord_6934674, baseEnd_6934674] using wordTrace_append hprefix tailTrace_6934674
  have hstable : (prefixWord ++ tailWord_6934674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934674).length < 2 ^ (prefixWord ++ tailWord_6934674).sum := by decide
  have hdescent : baseEnd_6934674 < baseStart_6934674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934677 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_6934677 : Nat := 118140960795 + 6934677 * 2 ^ 59
def prefixEnd_6934677 : Nat := 4983230072969 + 3 ^ 40 * 6934677 * 2
def baseEnd_6934677 : Nat := 3560822484679069778045507

theorem tailTrace_6934677 : CollatzResearch.WordTrace tailWord_6934677 prefixEnd_6934677 3560822484679069778045507 := by
  unfold tailWord_6934677
  simp only [CollatzResearch.WordTrace]
  refine ⟨252928449097857052385906285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168618966065238034923937523 252928449097857052385906285)
  ·
    refine ⟨94848168411696394644714857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252928449097857052385906285 94848168411696394644714857)
    ·
      refine ⟨71136126308772295983536143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94848168411696394644714857 71136126308772295983536143)
      ·
        refine ⟨106704189463158443975304215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71136126308772295983536143 106704189463158443975304215)
        ·
          refine ⟨160056284194737665962956323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106704189463158443975304215 160056284194737665962956323)
          ·
            refine ⟨240084426292106498944434485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160056284194737665962956323 240084426292106498944434485)
            ·
              refine ⟨22507914964884984276040733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240084426292106498944434485 22507914964884984276040733)
              ·
                refine ⟨8440468111831869103515275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22507914964884984276040733 8440468111831869103515275)
                ·
                  refine ⟨12660702167747803655272913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440468111831869103515275 12660702167747803655272913)
                  ·
                    refine ⟨9495526625810852741454685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12660702167747803655272913 9495526625810852741454685)
                    ·
                      refine ⟨3560822484679069778045507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495526625810852741454685 3560822484679069778045507)
                      ·
                        rfl

theorem cell23_6934677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_6934677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934677 prefixEnd_6934677 := by exact prefixLift 6934677
  have htrace : WordTrace (prefixWord ++ tailWord_6934677) baseStart_6934677 baseEnd_6934677 := by
    simpa [prefixWord, tailWord_6934677, baseEnd_6934677] using wordTrace_append hprefix tailTrace_6934677
  have hstable : (prefixWord ++ tailWord_6934677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934677).length < 2 ^ (prefixWord ++ tailWord_6934677).sum := by decide
  have hdescent : baseEnd_6934677 < baseStart_6934677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934680 : List Nat := [2, 1, 2, 4, 3, 1, 10]
def baseStart_6934680 : Nat := 118140960795 + 6934680 * 2 ^ 59
def prefixEnd_6934680 : Nat := 4983230072969 + 3 ^ 40 * 6934680 * 2
def baseEnd_6934680 : Nat := 43960790433593003287753

theorem tailTrace_6934680 : CollatzResearch.WordTrace tailWord_6934680 prefixEnd_6934680 43960790433593003287753 := by
  unfold tailWord_6934680
  simp only [CollatzResearch.WordTrace]
  refine ⟨126464279258423091949132747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168619039011230789265510329 126464279258423091949132747)
  ·
    refine ⟨189696418887634637923699121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126464279258423091949132747 189696418887634637923699121)
    ·
      refine ⟨142272314165725978442774341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189696418887634637923699121 142272314165725978442774341)
      ·
        refine ⟨26676058906073620958020189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142272314165725978442774341 26676058906073620958020189)
        ·
          refine ⟨10003522089777607859257571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26676058906073620958020189 10003522089777607859257571)
          ·
            refine ⟨15005283134666411788886357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10003522089777607859257571 15005283134666411788886357)
            ·
              refine ⟨43960790433593003287753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15005283134666411788886357 43960790433593003287753)
              ·
                rfl

theorem cell23_6934680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 10].length) (baseStart_6934680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934680 prefixEnd_6934680 := by exact prefixLift 6934680
  have htrace : WordTrace (prefixWord ++ tailWord_6934680) baseStart_6934680 baseEnd_6934680 := by
    simpa [prefixWord, tailWord_6934680, baseEnd_6934680] using wordTrace_append hprefix tailTrace_6934680
  have hstable : (prefixWord ++ tailWord_6934680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934680).length < 2 ^ (prefixWord ++ tailWord_6934680).sum := by decide
  have hdescent : baseEnd_6934680 < baseStart_6934680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934701 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6934701 : Nat := 118140960795 + 6934701 * 2 ^ 59
def prefixEnd_6934701 : Nat := 4983230072969 + 3 ^ 40 * 6934701 * 2
def baseEnd_6934701 : Nat := 1186944936071592561381799

theorem tailTrace_6934701 : CollatzResearch.WordTrace tailWord_6934701 prefixEnd_6934701 1186944936071592561381799 := by
  unfold tailWord_6934701
  simp only [CollatzResearch.WordTrace]
  refine ⟨252929324449770104484779957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168619549633180069656519971 252929324449770104484779957)
  ·
    refine ⟨23712124167165947295448121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252929324449770104484779957 23712124167165947295448121)
    ·
      refine ⟨17784093125374460471586091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23712124167165947295448121 17784093125374460471586091)
      ·
        refine ⟨26676139688061690707379137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784093125374460471586091 26676139688061690707379137)
        ·
          refine ⟨20007104766046268030534353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26676139688061690707379137 20007104766046268030534353)
          ·
            refine ⟨15005328574534701022900765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20007104766046268030534353 15005328574534701022900765)
            ·
              refine ⟨5626998215450512883587787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15005328574534701022900765 5626998215450512883587787)
              ·
                refine ⟨8440497323175769325381681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626998215450512883587787 8440497323175769325381681)
                ·
                  refine ⟨6330372992381826994036261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8440497323175769325381681 6330372992381826994036261)
                  ·
                    refine ⟨1186944936071592561381799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330372992381826994036261 1186944936071592561381799)
                    ·
                      rfl

theorem cell23_6934701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6934701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934701 prefixEnd_6934701 := by exact prefixLift 6934701
  have htrace : WordTrace (prefixWord ++ tailWord_6934701) baseStart_6934701 baseEnd_6934701 := by
    simpa [prefixWord, tailWord_6934701, baseEnd_6934701] using wordTrace_append hprefix tailTrace_6934701
  have hstable : (prefixWord ++ tailWord_6934701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934701).length < 2 ^ (prefixWord ++ tailWord_6934701).sum := by decide
  have hdescent : baseEnd_6934701 < baseStart_6934701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934720 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_6934720 : Nat := 118140960795 + 6934720 * 2 ^ 59
def prefixEnd_6934720 : Nat := 4983230072969 + 3 ^ 40 * 6934720 * 2
def baseEnd_6934720 : Nat := 3560844564347213109807809

theorem tailTrace_6934720 : CollatzResearch.WordTrace tailWord_6934720 prefixEnd_6934720 3560844564347213109807809 := by
  unfold tailWord_6934720
  simp only [CollatzResearch.WordTrace]
  refine ⟨126465008718350635364860807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168620011624467513819814409 126465008718350635364860807)
  ·
    refine ⟨189697513077525953047291211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126465008718350635364860807 189697513077525953047291211)
    ·
      refine ⟨284546269616288929570936817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189697513077525953047291211 284546269616288929570936817)
      ·
        refine ⟨213409702212216697178202613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284546269616288929570936817 213409702212216697178202613)
        ·
          refine ⟨20007159582395315360456495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213409702212216697178202613 20007159582395315360456495)
          ·
            refine ⟨30010739373592973040684743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20007159582395315360456495 30010739373592973040684743)
            ·
              refine ⟨45016109060389459561027115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30010739373592973040684743 45016109060389459561027115)
              ·
                refine ⟨67524163590584189341540673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45016109060389459561027115 67524163590584189341540673)
                ·
                  refine ⟨50643122692938142006155505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67524163590584189341540673 50643122692938142006155505)
                  ·
                    refine ⟨37982342019703606504616629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50643122692938142006155505 37982342019703606504616629)
                    ·
                      refine ⟨3560844564347213109807809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37982342019703606504616629 3560844564347213109807809)
                      ·
                        rfl

theorem cell23_6934720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_6934720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934720 prefixEnd_6934720 := by exact prefixLift 6934720
  have htrace : WordTrace (prefixWord ++ tailWord_6934720) baseStart_6934720 baseEnd_6934720 := by
    simpa [prefixWord, tailWord_6934720, baseEnd_6934720] using wordTrace_append hprefix tailTrace_6934720
  have hstable : (prefixWord ++ tailWord_6934720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934720).length < 2 ^ (prefixWord ++ tailWord_6934720).sum := by decide
  have hdescent : baseEnd_6934720 < baseStart_6934720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934724 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6934724 : Nat := 118140960795 + 6934724 * 2 ^ 59
def prefixEnd_6934724 : Nat := 4983230072969 + 3 ^ 40 * 6934724 * 2
def baseEnd_6934724 : Nat := 3560846618269831094157791

theorem tailTrace_6934724 : CollatzResearch.WordTrace tailWord_6934724 prefixEnd_6934724 3560846618269831094157791 := by
  unfold tailWord_6934724
  simp only [CollatzResearch.WordTrace]
  refine ⟨126465081664343389706433613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168620108885791186275244817 126465081664343389706433613)
  ·
    refine ⟨47424405624128771139912605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126465081664343389706433613 47424405624128771139912605)
    ·
      refine ⟨17784152109048289177467227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47424405624128771139912605 17784152109048289177467227)
      ·
        refine ⟨26676228163572433766200841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784152109048289177467227 26676228163572433766200841)
        ·
          refine ⟨20007171122679325324650631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26676228163572433766200841 20007171122679325324650631)
          ·
            refine ⟨30010756684018987986975947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20007171122679325324650631 30010756684018987986975947)
            ·
              refine ⟨45016135026028481980463921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30010756684018987986975947 45016135026028481980463921)
              ·
                refine ⟨33762101269521361485347941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45016135026028481980463921 33762101269521361485347941)
                ·
                  refine ⟨6330393988035255278502739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33762101269521361485347941 6330393988035255278502739)
                  ·
                    refine ⟨9495590982052882917754109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6330393988035255278502739 9495590982052882917754109)
                    ·
                      refine ⟨3560846618269831094157791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495590982052882917754109 3560846618269831094157791)
                      ·
                        rfl

theorem cell23_6934724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6934724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934724 prefixEnd_6934724 := by exact prefixLift 6934724
  have htrace : WordTrace (prefixWord ++ tailWord_6934724) baseStart_6934724 baseEnd_6934724 := by
    simpa [prefixWord, tailWord_6934724, baseEnd_6934724] using wordTrace_append hprefix tailTrace_6934724
  have hstable : (prefixWord ++ tailWord_6934724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934724).length < 2 ^ (prefixWord ++ tailWord_6934724).sum := by decide
  have hdescent : baseEnd_6934724 < baseStart_6934724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934742 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6934742 : Nat := 118140960795 + 6934742 * 2 ^ 59
def prefixEnd_6934742 : Nat := 4983230072969 + 3 ^ 40 * 6934742 * 2
def baseEnd_6934742 : Nat := 3560855860921612023732709

theorem tailTrace_6934742 : CollatzResearch.WordTrace tailWord_6934742 prefixEnd_6934742 3560855860921612023732709 := by
  unfold tailWord_6934742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808176240163848030438905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168620546561747712324681653 15808176240163848030438905)
  ·
    refine ⟨11856132180122886022829179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15808176240163848030438905 11856132180122886022829179)
    ·
      refine ⟨17784198270184329034243769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856132180122886022829179 17784198270184329034243769)
      ·
        refine ⟨13338148702638246775682827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17784198270184329034243769 13338148702638246775682827)
        ·
          refine ⟨20007223053957370163524241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13338148702638246775682827 20007223053957370163524241)
          ·
            refine ⟨15005417290468027622643181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20007223053957370163524241 15005417290468027622643181)
            ·
              refine ⟨5627031483925510358491193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15005417290468027622643181 5627031483925510358491193)
              ·
                refine ⟨4220273612944132768868395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627031483925510358491193 4220273612944132768868395)
                ·
                  refine ⟨6330410419416199153302593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220273612944132768868395 6330410419416199153302593)
                  ·
                    refine ⟨4747807814562149364976945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330410419416199153302593 4747807814562149364976945)
                    ·
                      refine ⟨3560855860921612023732709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4747807814562149364976945 3560855860921612023732709)
                      ·
                        rfl

theorem cell23_6934742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6934742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934742 prefixEnd_6934742 := by exact prefixLift 6934742
  have htrace : WordTrace (prefixWord ++ tailWord_6934742) baseStart_6934742 baseEnd_6934742 := by
    simpa [prefixWord, tailWord_6934742, baseEnd_6934742] using wordTrace_append hprefix tailTrace_6934742
  have hstable : (prefixWord ++ tailWord_6934742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934742).length < 2 ^ (prefixWord ++ tailWord_6934742).sum := by decide
  have hdescent : baseEnd_6934742 < baseStart_6934742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934787 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 5]
def baseStart_6934787 : Nat := 118140960795 + 6934787 * 2 ^ 59
def prefixEnd_6934787 : Nat := 4983230072969 + 3 ^ 40 * 6934787 * 2
def baseEnd_6934787 : Nat := 395653218616784927518889

theorem tailTrace_6934787 : CollatzResearch.WordTrace tailWord_6934787 prefixEnd_6934787 395653218616784927518889 := by
  unfold tailWord_6934787
  simp only [CollatzResearch.WordTrace]
  refine ⟨252932461127458541172410615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168621640751639027448273743 252932461127458541172410615)
  ·
    refine ⟨379398691691187811758615923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252932461127458541172410615 379398691691187811758615923)
    ·
      refine ⟨569098037536781717637923885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379398691691187811758615923 569098037536781717637923885)
      ·
        refine ⟨213411764076293144114221457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569098037536781717637923885 213411764076293144114221457)
        ·
          refine ⟨160058823057219858085666093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213411764076293144114221457 160058823057219858085666093)
          ·
            refine ⟨60022058646457446782124785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160058823057219858085666093 60022058646457446782124785)
            ·
              refine ⟨45016543984843085086593589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60022058646457446782124785 45016543984843085086593589)
              ·
                refine ⟨4220300998579039226868149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45016543984843085086593589 4220300998579039226868149)
                ·
                  refine ⟨395653218616784927518889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220300998579039226868149 395653218616784927518889)
                  ·
                    rfl

theorem cell23_6934787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 5].length) (baseStart_6934787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934787 prefixEnd_6934787 := by exact prefixLift 6934787
  have htrace : WordTrace (prefixWord ++ tailWord_6934787) baseStart_6934787 baseEnd_6934787 := by
    simpa [prefixWord, tailWord_6934787, baseEnd_6934787] using wordTrace_append hprefix tailTrace_6934787
  have hstable : (prefixWord ++ tailWord_6934787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934787).length < 2 ^ (prefixWord ++ tailWord_6934787).sum := by decide
  have hdescent : baseEnd_6934787 < baseStart_6934787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934837 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6934837 : Nat := 118140960795 + 6934837 * 2 ^ 59
def prefixEnd_6934837 : Nat := 4983230072969 + 3 ^ 40 * 6934837 * 2
def baseEnd_6934837 : Nat := 3560904641583789152044771

theorem tailTrace_6934837 : CollatzResearch.WordTrace tailWord_6934837 prefixEnd_6934837 3560904641583789152044771 := by
  unfold tailWord_6934837
  simp only [CollatzResearch.WordTrace]
  refine ⟨252934284777277399711730765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168622856518184933141153843 252934284777277399711730765)
  ·
    refine ⟨94850356791479024891899037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252934284777277399711730765 94850356791479024891899037)
    ·
      refine ⟨35568883796804634334462139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94850356791479024891899037 35568883796804634334462139)
      ·
        refine ⟨53353325695206951501693209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35568883796804634334462139 53353325695206951501693209)
        ·
          refine ⟨40014994271405213626269907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53353325695206951501693209 40014994271405213626269907)
          ·
            refine ⟨60022491407107820439404861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40014994271405213626269907 60022491407107820439404861)
            ·
              refine ⟨22508434277665432664776823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60022491407107820439404861 22508434277665432664776823)
              ·
                refine ⟨33762651416498148997165235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22508434277665432664776823 33762651416498148997165235)
                ·
                  refine ⟨50643977124747223495747853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33762651416498148997165235 50643977124747223495747853)
                  ·
                    refine ⟨18991491421780208810905445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50643977124747223495747853 18991491421780208810905445)
                    ·
                      refine ⟨3560904641583789152044771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18991491421780208810905445 3560904641583789152044771)
                      ·
                        rfl

theorem cell23_6934837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6934837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934837 prefixEnd_6934837 := by exact prefixLift 6934837
  have htrace : WordTrace (prefixWord ++ tailWord_6934837) baseStart_6934837 baseEnd_6934837 := by
    simpa [prefixWord, tailWord_6934837, baseEnd_6934837] using wordTrace_append hprefix tailTrace_6934837
  have hstable : (prefixWord ++ tailWord_6934837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934837).length < 2 ^ (prefixWord ++ tailWord_6934837).sum := by decide
  have hdescent : baseEnd_6934837 < baseStart_6934837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934847 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 5, 4]
def baseStart_6934847 : Nat := 118140960795 + 6934847 * 2 ^ 59
def prefixEnd_6934847 : Nat := 4983230072969 + 3 ^ 40 * 6934847 * 2
def baseEnd_6934847 : Nat := 1186969925463444704306575

theorem tailTrace_6934847 : CollatzResearch.WordTrace tailWord_6934847 prefixEnd_6934847 1186969925463444704306575 := by
  unfold tailWord_6934847
  simp only [CollatzResearch.WordTrace]
  refine ⟨252934649507241171419594795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168623099671494114279729863 252934649507241171419594795)
  ·
    refine ⟨379401974260861757129392193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252934649507241171419594795 379401974260861757129392193)
    ·
      refine ⟨284551480695646317847044145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379401974260861757129392193 284551480695646317847044145)
      ·
        refine ⟨213413610521734738385283109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284551480695646317847044145 213413610521734738385283109)
        ·
          refine ⟨40015051972825263447240583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213413610521734738385283109 40015051972825263447240583)
          ·
            refine ⟨60022577959237895170860875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40015051972825263447240583 60022577959237895170860875)
            ·
              refine ⟨90033866938856842756291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60022577959237895170860875 90033866938856842756291313)
              ·
                refine ⟨67525400204142632067218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90033866938856842756291313 67525400204142632067218485)
                ·
                  refine ⟨6330506269138371756301733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67525400204142632067218485 6330506269138371756301733)
                  ·
                    refine ⟨1186969925463444704306575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330506269138371756301733 1186969925463444704306575)
                    ·
                      rfl

theorem cell23_6934847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_6934847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934847 prefixEnd_6934847 := by exact prefixLift 6934847
  have htrace : WordTrace (prefixWord ++ tailWord_6934847) baseStart_6934847 baseEnd_6934847 := by
    simpa [prefixWord, tailWord_6934847, baseEnd_6934847] using wordTrace_append hprefix tailTrace_6934847
  have hstable : (prefixWord ++ tailWord_6934847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934847).length < 2 ^ (prefixWord ++ tailWord_6934847).sum := by decide
  have hdescent : baseEnd_6934847 < baseStart_6934847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934857 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_6934857 : Nat := 118140960795 + 6934857 * 2 ^ 59
def prefixEnd_6934857 : Nat := 4983230072969 + 3 ^ 40 * 6934857 * 2
def baseEnd_6934857 : Nat := 3560914911196879073794679

theorem tailTrace_6934857 : CollatzResearch.WordTrace tailWord_6934857 prefixEnd_6934857 3560914911196879073794679 := by
  unfold tailWord_6934857
  simp only [CollatzResearch.WordTrace]
  refine ⟨252935014237204943127458825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168623342824803295418305883 252935014237204943127458825)
  ·
    refine ⟨189701260677903707345594119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252935014237204943127458825 189701260677903707345594119)
    ·
      refine ⟨284551891016855561018391179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189701260677903707345594119 284551891016855561018391179)
      ·
        refine ⟨426827836525283341527586769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284551891016855561018391179 426827836525283341527586769)
        ·
          refine ⟨320120877393962506145690077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426827836525283341527586769 320120877393962506145690077)
          ·
            refine ⟨120045329022735939804633779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320120877393962506145690077 120045329022735939804633779)
            ·
              refine ⟨180067993534103909706950669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120045329022735939804633779 180067993534103909706950669)
              ·
                refine ⟨67525497575288966140106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180067993534103909706950669 67525497575288966140106501)
                ·
                  refine ⟨12661030795366681151269969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67525497575288966140106501 12661030795366681151269969)
                  ·
                    refine ⟨9495773096525010863452477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12661030795366681151269969 9495773096525010863452477)
                    ·
                      refine ⟨3560914911196879073794679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495773096525010863452477 3560914911196879073794679)
                      ·
                        rfl

theorem cell23_6934857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_6934857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934857 prefixEnd_6934857 := by exact prefixLift 6934857
  have htrace : WordTrace (prefixWord ++ tailWord_6934857) baseStart_6934857 baseEnd_6934857 := by
    simpa [prefixWord, tailWord_6934857, baseEnd_6934857] using wordTrace_append hprefix tailTrace_6934857
  have hstable : (prefixWord ++ tailWord_6934857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934857).length < 2 ^ (prefixWord ++ tailWord_6934857).sum := by decide
  have hdescent : baseEnd_6934857 < baseStart_6934857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934864 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_6934864 : Nat := 118140960795 + 6934864 * 2 ^ 59
def prefixEnd_6934864 : Nat := 4983230072969 + 3 ^ 40 * 6934864 * 2
def baseEnd_6934864 : Nat := 1186972835187153515469049

theorem tailTrace_6934864 : CollatzResearch.WordTrace tailWord_6934864 prefixEnd_6934864 1186972835187153515469049 := by
  unfold tailWord_6934864
  simp only [CollatzResearch.WordTrace]
  refine ⟨126467634774089791661481823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168623513032119722215309097 126467634774089791661481823)
  ·
    refine ⟨189701452161134687492222735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126467634774089791661481823 189701452161134687492222735)
    ·
      refine ⟨284552178241702031238334103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189701452161134687492222735 284552178241702031238334103)
      ·
        refine ⟨426828267362553046857501155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284552178241702031238334103 426828267362553046857501155)
        ·
          refine ⟨640242401043829570286251733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426828267362553046857501155 640242401043829570286251733)
          ·
            refine ⟨15005681274464755553584025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 640242401043829570286251733 15005681274464755553584025)
            ·
              refine ⟨11254260955848566665188019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15005681274464755553584025 11254260955848566665188019)
              ·
                refine ⟨16881391433772849997782029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11254260955848566665188019 16881391433772849997782029)
                ·
                  refine ⟨6330521787664818749168261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16881391433772849997782029 6330521787664818749168261)
                  ·
                    refine ⟨1186972835187153515469049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330521787664818749168261 1186972835187153515469049)
                    ·
                      rfl

theorem cell23_6934864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_6934864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934864 prefixEnd_6934864 := by exact prefixLift 6934864
  have htrace : WordTrace (prefixWord ++ tailWord_6934864) baseStart_6934864 baseEnd_6934864 := by
    simpa [prefixWord, tailWord_6934864, baseEnd_6934864] using wordTrace_append hprefix tailTrace_6934864
  have hstable : (prefixWord ++ tailWord_6934864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934864).length < 2 ^ (prefixWord ++ tailWord_6934864).sum := by decide
  have hdescent : baseEnd_6934864 < baseStart_6934864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934898 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_6934898 : Nat := 118140960795 + 6934898 * 2 ^ 59
def prefixEnd_6934898 : Nat := 4983230072969 + 3 ^ 40 * 6934898 * 2
def baseEnd_6934898 : Nat := 1186978654634571137793997

theorem tailTrace_6934898 : CollatzResearch.WordTrace tailWord_6934898 prefixEnd_6934898 1186978654634571137793997 := by
  unfold tailWord_6934898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63234127407514101782425337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168624339753370938086467565 63234127407514101782425337)
  ·
    refine ⟨47425595555635576336819003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63234127407514101782425337 47425595555635576336819003)
    ·
      refine ⟨71138393333453364505228505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47425595555635576336819003 71138393333453364505228505)
      ·
        refine ⟨53353795000090023378921379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71138393333453364505228505 53353795000090023378921379)
        ·
          refine ⟨80030692500135035068382069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53353795000090023378921379 80030692500135035068382069)
          ·
            refine ⟨7502877421887659537660819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80030692500135035068382069 7502877421887659537660819)
            ·
              refine ⟨11254316132831489306491229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502877421887659537660819 11254316132831489306491229)
              ·
                refine ⟨4220368549811808489934211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11254316132831489306491229 4220368549811808489934211)
                ·
                  refine ⟨6330552824717712734901317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220368549811808489934211 6330552824717712734901317)
                  ·
                    refine ⟨1186978654634571137793997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330552824717712734901317 1186978654634571137793997)
                    ·
                      rfl

theorem cell23_6934898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_6934898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934898 prefixEnd_6934898 := by exact prefixLift 6934898
  have htrace : WordTrace (prefixWord ++ tailWord_6934898) baseStart_6934898 baseEnd_6934898 := by
    simpa [prefixWord, tailWord_6934898, baseEnd_6934898] using wordTrace_append hprefix tailTrace_6934898
  have hstable : (prefixWord ++ tailWord_6934898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934898).length < 2 ^ (prefixWord ++ tailWord_6934898).sum := by decide
  have hdescent : baseEnd_6934898 < baseStart_6934898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934921 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_6934921 : Nat := 118140960795 + 6934921 * 2 ^ 59
def prefixEnd_6934921 : Nat := 4983230072969 + 3 ^ 40 * 6934921 * 2
def baseEnd_6934921 : Nat := 3560947773958766823394385

theorem tailTrace_6934921 : CollatzResearch.WordTrace tailWord_6934921 prefixEnd_6934921 3560947773958766823394385 := by
  unfold tailWord_6934921
  simp only [CollatzResearch.WordTrace]
  refine ⟨252937348508973082057788617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168624899005982054705192411 252937348508973082057788617)
  ·
    refine ⟨189703011381729811543341463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252937348508973082057788617 189703011381729811543341463)
    ·
      refine ⟨284554517072594717315012195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189703011381729811543341463 284554517072594717315012195)
      ·
        refine ⟨426831775608892075972518293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284554517072594717315012195 426831775608892075972518293)
        ·
          refine ⟨20007739481666816061211795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 426831775608892075972518293 20007739481666816061211795)
          ·
            refine ⟨30011609222500224091817693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20007739481666816061211795 30011609222500224091817693)
            ·
              refine ⟨11254353458437584034431635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30011609222500224091817693 11254353458437584034431635)
              ·
                refine ⟨16881530187656376051647453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11254353458437584034431635 16881530187656376051647453)
                ·
                  refine ⟨6330573820371141019367795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16881530187656376051647453 6330573820371141019367795)
                  ·
                    refine ⟨9495860730556711529051693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6330573820371141019367795 9495860730556711529051693)
                    ·
                      refine ⟨3560947773958766823394385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495860730556711529051693 3560947773958766823394385)
                      ·
                        rfl

theorem cell23_6934921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_6934921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934921 prefixEnd_6934921 := by exact prefixLift 6934921
  have htrace : WordTrace (prefixWord ++ tailWord_6934921) baseStart_6934921 baseEnd_6934921 := by
    simpa [prefixWord, tailWord_6934921, baseEnd_6934921] using wordTrace_append hprefix tailTrace_6934921
  have hstable : (prefixWord ++ tailWord_6934921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934921).length < 2 ^ (prefixWord ++ tailWord_6934921).sum := by decide
  have hdescent : baseEnd_6934921 < baseStart_6934921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934937 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_6934937 : Nat := 118140960795 + 6934937 * 2 ^ 59
def prefixEnd_6934937 : Nat := 4983230072969 + 3 ^ 40 * 6934937 * 2
def baseEnd_6934937 : Nat := 1186985329883079586931437

theorem tailTrace_6934937 : CollatzResearch.WordTrace tailWord_6934937 prefixEnd_6934937 1186985329883079586931437 := by
  unfold tailWord_6934937
  simp only [CollatzResearch.WordTrace]
  refine ⟨252937932076915116790371065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168625288051276744526914043 252937932076915116790371065)
  ·
    refine ⟨189703449057686337592778299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252937932076915116790371065 189703449057686337592778299)
    ·
      refine ⟨284555173586529506389167449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189703449057686337592778299 284555173586529506389167449)
      ·
        refine ⟨213416380189897129791875587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284555173586529506389167449 213416380189897129791875587)
        ·
          refine ⟨320124570284845694687813381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213416380189897129791875587 320124570284845694687813381)
          ·
            refine ⟨60023356928408567753965009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320124570284845694687813381 60023356928408567753965009)
            ·
              refine ⟨45017517696306425815473757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60023356928408567753965009 45017517696306425815473757)
              ·
                refine ⟨16881569136114909680802659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45017517696306425815473757 16881569136114909680802659)
                ·
                  refine ⟨25322353704172364521203989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16881569136114909680802659 25322353704172364521203989)
                  ·
                    refine ⟨1186985329883079586931437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25322353704172364521203989 1186985329883079586931437)
                    ·
                      rfl

theorem cell23_6934937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_6934937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934937 prefixEnd_6934937 := by exact prefixLift 6934937
  have htrace : WordTrace (prefixWord ++ tailWord_6934937) baseStart_6934937 baseEnd_6934937 := by
    simpa [prefixWord, tailWord_6934937, baseEnd_6934937] using wordTrace_append hprefix tailTrace_6934937
  have hstable : (prefixWord ++ tailWord_6934937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934937).length < 2 ^ (prefixWord ++ tailWord_6934937).sum := by decide
  have hdescent : baseEnd_6934937 < baseStart_6934937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934944 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6934944 : Nat := 118140960795 + 6934944 * 2 ^ 59
def prefixEnd_6934944 : Nat := 4983230072969 + 3 ^ 40 * 6934944 * 2
def baseEnd_6934944 : Nat := 3560959584013820233406779

theorem tailTrace_6934944 : CollatzResearch.WordTrace tailWord_6934944 prefixEnd_6934944 3560959584013820233406779 := by
  unfold tailWord_6934944
  simp only [CollatzResearch.WordTrace]
  refine ⟨126469093693944878492937943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168625458258593171323917257 126469093693944878492937943)
  ·
    refine ⟨189703640540917317739406915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126469093693944878492937943 189703640540917317739406915)
    ·
      refine ⟨284555460811375976609110373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189703640540917317739406915 284555460811375976609110373)
      ·
        refine ⟨53354148902132995614208195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284555460811375976609110373 53354148902132995614208195)
        ·
          refine ⟨80031223353199493421312293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53354148902132995614208195 80031223353199493421312293)
          ·
            refine ⟨15005854378724905016496055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80031223353199493421312293 15005854378724905016496055)
            ·
              refine ⟨22508781568087357524744083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15005854378724905016496055 22508781568087357524744083)
              ·
                refine ⟨33763172352131036287116125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22508781568087357524744083 33763172352131036287116125)
                ·
                  refine ⟨12661189632049138607668547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33763172352131036287116125 12661189632049138607668547)
                  ·
                    refine ⟨18991784448073707911502821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12661189632049138607668547 18991784448073707911502821)
                    ·
                      refine ⟨3560959584013820233406779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18991784448073707911502821 3560959584013820233406779)
                      ·
                        rfl

theorem cell23_6934944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6934944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934944 prefixEnd_6934944 := by exact prefixLift 6934944
  have htrace : WordTrace (prefixWord ++ tailWord_6934944) baseStart_6934944 baseEnd_6934944 := by
    simpa [prefixWord, tailWord_6934944, baseEnd_6934944] using wordTrace_append hprefix tailTrace_6934944
  have hstable : (prefixWord ++ tailWord_6934944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934944).length < 2 ^ (prefixWord ++ tailWord_6934944).sum := by decide
  have hdescent : baseEnd_6934944 < baseStart_6934944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934972 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6934972 : Nat := 118140960795 + 6934972 * 2 ^ 59
def prefixEnd_6934972 : Nat := 4983230072969 + 3 ^ 40 * 6934972 * 2
def baseEnd_6934972 : Nat := 3560973961472146123856651

theorem tailTrace_6934972 : CollatzResearch.WordTrace tailWord_6934972 prefixEnd_6934972 3560973961472146123856651 := by
  unfold tailWord_6934972
  simp only [CollatzResearch.WordTrace]
  refine ⟨126469604315894158883947585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168626139087858878511930113 126469604315894158883947585)
  ·
    refine ⟨94852203236920619162960689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126469604315894158883947585 94852203236920619162960689)
    ·
      refine ⟨71139152427690464372220517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94852203236920619162960689 71139152427690464372220517)
      ·
        refine ⟨13338591080191962069791347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71139152427690464372220517 13338591080191962069791347)
        ·
          refine ⟨20007886620287943104687021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13338591080191962069791347 20007886620287943104687021)
          ·
            refine ⟨7502957482607978664257633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20007886620287943104687021 7502957482607978664257633)
            ·
              refine ⟨5627218111955983998193225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7502957482607978664257633 5627218111955983998193225)
              ·
                refine ⟨4220413583966987998644919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627218111955983998193225 4220413583966987998644919)
                ·
                  refine ⟨6330620375950481997967379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220413583966987998644919 6330620375950481997967379)
                  ·
                    refine ⟨9495930563925722996951069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6330620375950481997967379 9495930563925722996951069)
                    ·
                      refine ⟨3560973961472146123856651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495930563925722996951069 3560973961472146123856651)
                      ·
                        rfl

theorem cell23_6934972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6934972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934972 prefixEnd_6934972 := by exact prefixLift 6934972
  have htrace : WordTrace (prefixWord ++ tailWord_6934972) baseStart_6934972 baseEnd_6934972 := by
    simpa [prefixWord, tailWord_6934972, baseEnd_6934972] using wordTrace_append hprefix tailTrace_6934972
  have hstable : (prefixWord ++ tailWord_6934972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934972).length < 2 ^ (prefixWord ++ tailWord_6934972).sum := by decide
  have hdescent : baseEnd_6934972 < baseStart_6934972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934984 : List Nat := [2, 1, 3, 1, 3, 4, 1, 8]
def baseStart_6934984 : Nat := 118140960795 + 6934984 * 2 ^ 59
def prefixEnd_6934984 : Nat := 4983230072969 + 3 ^ 40 * 6934984 * 2
def baseEnd_6934984 : Nat := 131888152712592595440985

theorem tailTrace_6934984 : CollatzResearch.WordTrace tailWord_6934984 prefixEnd_6934984 131888152712592595440985 := by
  unfold tailWord_6934984
  simp only [CollatzResearch.WordTrace]
  refine ⟨126469823153872421908666003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168626430871829895878221337 126469823153872421908666003)
  ·
    refine ⟨189704734730808632862999005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126469823153872421908666003 189704734730808632862999005)
    ·
      refine ⟨71139275524053237323624627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189704734730808632862999005 71139275524053237323624627)
      ·
        refine ⟨106708913286079855985436941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71139275524053237323624627 106708913286079855985436941)
        ·
          refine ⟨40015842482279945994538853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106708913286079855985436941 40015842482279945994538853)
          ·
            refine ⟨7502970465427489873976035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40015842482279945994538853 7502970465427489873976035)
            ·
              refine ⟨11254455698141234810964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502970465427489873976035 11254455698141234810964053)
              ·
                refine ⟨131888152712592595440985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11254455698141234810964053 131888152712592595440985)
                ·
                  rfl

theorem cell23_6934984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 8].length) (baseStart_6934984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934984 prefixEnd_6934984 := by exact prefixLift 6934984
  have htrace : WordTrace (prefixWord ++ tailWord_6934984) baseStart_6934984 baseEnd_6934984 := by
    simpa [prefixWord, tailWord_6934984, baseEnd_6934984] using wordTrace_append hprefix tailTrace_6934984
  have hstable : (prefixWord ++ tailWord_6934984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934984).length < 2 ^ (prefixWord ++ tailWord_6934984).sum := by decide
  have hdescent : baseEnd_6934984 < baseStart_6934984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6934998 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6934998 : Nat := 118140960795 + 6934998 * 2 ^ 59
def prefixEnd_6934998 : Nat := 4983230072969 + 3 ^ 40 * 6934998 * 2
def baseEnd_6934998 : Nat := 3560987311969163022131531

theorem tailTrace_6934998 : CollatzResearch.WordTrace tailWord_6934998 prefixEnd_6934998 3560987311969163022131531 := by
  unfold tailWord_6934998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808759808105882763021353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168626771286462749472227765 15808759808105882763021353)
  ·
    refine ⟨11856569856079412072266015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15808759808105882763021353 11856569856079412072266015)
    ·
      refine ⟨17784854784119118108399023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856569856079412072266015 17784854784119118108399023)
      ·
        refine ⟨26677282176178677162598535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784854784119118108399023 26677282176178677162598535)
        ·
          refine ⟨40015923264268015743897803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26677282176178677162598535 40015923264268015743897803)
          ·
            refine ⟨60023884896402023615846705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40015923264268015743897803 60023884896402023615846705)
            ·
              refine ⟨45017913672301517711885029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60023884896402023615846705 45017913672301517711885029)
              ·
                refine ⟨8440858813556534570978443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45017913672301517711885029 8440858813556534570978443)
                ·
                  refine ⟨12661288220334801856467665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8440858813556534570978443 12661288220334801856467665)
                  ·
                    refine ⟨9495966165251101392350749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12661288220334801856467665 9495966165251101392350749)
                    ·
                      refine ⟨3560987311969163022131531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9495966165251101392350749 3560987311969163022131531)
                      ·
                        rfl

theorem cell23_6934998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6934998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6934998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6934998 prefixEnd_6934998 := by exact prefixLift 6934998
  have htrace : WordTrace (prefixWord ++ tailWord_6934998) baseStart_6934998 baseEnd_6934998 := by
    simpa [prefixWord, tailWord_6934998, baseEnd_6934998] using wordTrace_append hprefix tailTrace_6934998
  have hstable : (prefixWord ++ tailWord_6934998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6934998).length < 2 ^ (prefixWord ++ tailWord_6934998).sum := by decide
  have hdescent : baseEnd_6934998 < baseStart_6934998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6934998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935017 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_6935017 : Nat := 118140960795 + 6935017 * 2 ^ 59
def prefixEnd_6935017 : Nat := 4983230072969 + 3 ^ 40 * 6935017 * 2
def baseEnd_6935017 : Nat := 3560997068101598447793943

theorem tailTrace_6935017 : CollatzResearch.WordTrace tailWord_6935017 prefixEnd_6935017 3560997068101598447793943 := by
  unfold tailWord_6935017
  simp only [CollatzResearch.WordTrace]
  refine ⟨252940849916625290453283305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168627233277750193635522203 252940849916625290453283305)
  ·
    refine ⟨189705637437468967839962479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252940849916625290453283305 189705637437468967839962479)
    ·
      refine ⟨284558456156203451759943719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189705637437468967839962479 284558456156203451759943719)
      ·
        refine ⟨426837684234305177639915579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284558456156203451759943719 426837684234305177639915579)
        ·
          refine ⟨640256526351457766459873369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426837684234305177639915579 640256526351457766459873369)
          ·
            refine ⟨480192394763593324844905027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640256526351457766459873369 480192394763593324844905027)
            ·
              refine ⟨720288592145389987267357541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480192394763593324844905027 720288592145389987267357541)
              ·
                refine ⟨135054111027260622612629539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720288592145389987267357541 135054111027260622612629539)
                ·
                  refine ⟨202581166540890933918944309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135054111027260622612629539 202581166540890933918944309)
                  ·
                    refine ⟨18991984363208525054901029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202581166540890933918944309 18991984363208525054901029)
                    ·
                      refine ⟨3560997068101598447793943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18991984363208525054901029 3560997068101598447793943)
                      ·
                        rfl

theorem cell23_6935017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_6935017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935017 prefixEnd_6935017 := by exact prefixLift 6935017
  have htrace : WordTrace (prefixWord ++ tailWord_6935017) baseStart_6935017 baseEnd_6935017 := by
    simpa [prefixWord, tailWord_6935017, baseEnd_6935017] using wordTrace_append hprefix tailTrace_6935017
  have hstable : (prefixWord ++ tailWord_6935017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935017).length < 2 ^ (prefixWord ++ tailWord_6935017).sum := by decide
  have hdescent : baseEnd_6935017 < baseStart_6935017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935027 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 6]
def baseStart_6935027 : Nat := 118140960795 + 6935027 * 2 ^ 59
def prefixEnd_6935027 : Nat := 4983230072969 + 3 ^ 40 * 6935027 * 2
def baseEnd_6935027 : Nat := 1187000734302714469556299

theorem tailTrace_6935027 : CollatzResearch.WordTrace tailWord_6935027 prefixEnd_6935027 1187000734302714469556299 := by
  unfold tailWord_6935027
  simp only [CollatzResearch.WordTrace]
  refine ⟨252941214646589062161147335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168627476431059374774098223 252941214646589062161147335)
  ·
    refine ⟨379411821969883593241721003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252941214646589062161147335 379411821969883593241721003)
    ·
      refine ⟨569117732954825389862581505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379411821969883593241721003 569117732954825389862581505)
      ·
        refine ⟨426838299716119042396936129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569117732954825389862581505 426838299716119042396936129)
        ·
          refine ⟨320128724787089281797702097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426838299716119042396936129 320128724787089281797702097)
          ·
            refine ⟨240096543590316961348276573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320128724787089281797702097 240096543590316961348276573)
            ·
              refine ⟨90036203846368860505603715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240096543590316961348276573 90036203846368860505603715)
              ·
                refine ⟨135054305769553290758405573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90036203846368860505603715 135054305769553290758405573)
                ·
                  refine ⟨25322682331791242017201045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135054305769553290758405573 25322682331791242017201045)
                  ·
                    refine ⟨1187000734302714469556299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25322682331791242017201045 1187000734302714469556299)
                    ·
                      rfl

theorem cell23_6935027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_6935027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935027 prefixEnd_6935027 := by exact prefixLift 6935027
  have htrace : WordTrace (prefixWord ++ tailWord_6935027) baseStart_6935027 baseEnd_6935027 := by
    simpa [prefixWord, tailWord_6935027, baseEnd_6935027] using wordTrace_append hprefix tailTrace_6935027
  have hstable : (prefixWord ++ tailWord_6935027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935027).length < 2 ^ (prefixWord ++ tailWord_6935027).sum := by decide
  have hdescent : baseEnd_6935027 < baseStart_6935027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935057 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 9]
def baseStart_6935057 : Nat := 118140960795 + 6935057 * 2 ^ 59
def prefixEnd_6935057 : Nat := 4983230072969 + 3 ^ 40 * 6935057 * 2
def baseEnd_6935057 : Nat := 395668623036419810143751

theorem tailTrace_6935057 : CollatzResearch.WordTrace tailWord_6935057 prefixEnd_6935057 395668623036419810143751 := by
  unfold tailWord_6935057
  simp only [CollatzResearch.WordTrace]
  refine ⟨252942308836480377284739425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168628205890986918189826283 252942308836480377284739425)
  ·
    refine ⟨189706731627360282963554569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252942308836480377284739425 189706731627360282963554569)
    ·
      refine ⟨142280048720520212222665927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189706731627360282963554569 142280048720520212222665927)
      ·
        refine ⟨213420073080780318333998891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142280048720520212222665927 213420073080780318333998891)
        ·
          refine ⟨320130109621170477500998337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213420073080780318333998891 320130109621170477500998337)
          ·
            refine ⟨240097582215877858125748753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320130109621170477500998337 240097582215877858125748753)
            ·
              refine ⟨180073186661908393594311565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240097582215877858125748753 180073186661908393594311565)
              ·
                refine ⟨67527444998215647597866837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180073186661908393594311565 67527444998215647597866837)
                ·
                  refine ⟨395668623036419810143751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67527444998215647597866837 395668623036419810143751)
                  ·
                    rfl

theorem cell23_6935057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_6935057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935057 prefixEnd_6935057 := by exact prefixLift 6935057
  have htrace : WordTrace (prefixWord ++ tailWord_6935057) baseStart_6935057 baseEnd_6935057 := by
    simpa [prefixWord, tailWord_6935057, baseEnd_6935057] using wordTrace_append hprefix tailTrace_6935057
  have hstable : (prefixWord ++ tailWord_6935057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935057).length < 2 ^ (prefixWord ++ tailWord_6935057).sum := by decide
  have hdescent : baseEnd_6935057 < baseStart_6935057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935068 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6935068 : Nat := 118140960795 + 6935068 * 2 ^ 59
def prefixEnd_6935068 : Nat := 4983230072969 + 3 ^ 40 * 6935068 * 2
def baseEnd_6935068 : Nat := 3561023255614977748256209

theorem tailTrace_6935068 : CollatzResearch.WordTrace tailWord_6935068 prefixEnd_6935068 3561023255614977748256209 := by
  unfold tailWord_6935068
  simp only [CollatzResearch.WordTrace]
  refine ⟨126471355019720263081694929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168628473359627017442259905 126471355019720263081694929)
  ·
    refine ⟨94853516264790197311271197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126471355019720263081694929 94853516264790197311271197)
    ·
      refine ⟨35570068599296323991726699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94853516264790197311271197 35570068599296323991726699)
      ·
        refine ⟨53355102898944485987590049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35570068599296323991726699 53355102898944485987590049)
        ·
          refine ⟨40016327174208364490692537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53355102898944485987590049 40016327174208364490692537)
          ·
            refine ⟨30012245380656273368019403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40016327174208364490692537 30012245380656273368019403)
            ·
              refine ⟨45018368070984410052029105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30012245380656273368019403 45018368070984410052029105)
              ·
                refine ⟨33763776053238307539021829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45018368070984410052029105 33763776053238307539021829)
                ·
                  refine ⟨6330708009982182663566593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33763776053238307539021829 6330708009982182663566593)
                  ·
                    refine ⟨4748031007486636997674945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330708009982182663566593 4748031007486636997674945)
                    ·
                      refine ⟨3561023255614977748256209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748031007486636997674945 3561023255614977748256209)
                      ·
                        rfl

theorem cell23_6935068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6935068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935068 prefixEnd_6935068 := by exact prefixLift 6935068
  have htrace : WordTrace (prefixWord ++ tailWord_6935068) baseStart_6935068 baseEnd_6935068 := by
    simpa [prefixWord, tailWord_6935068, baseEnd_6935068] using wordTrace_append hprefix tailTrace_6935068
  have hstable : (prefixWord ++ tailWord_6935068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935068).length < 2 ^ (prefixWord ++ tailWord_6935068).sum := by decide
  have hdescent : baseEnd_6935068 < baseStart_6935068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935084 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_6935084 : Nat := 118140960795 + 6935084 * 2 ^ 59
def prefixEnd_6935084 : Nat := 4983230072969 + 3 ^ 40 * 6935084 * 2
def baseEnd_6935084 : Nat := 3561031471305449685656135

theorem tailTrace_6935084 : CollatzResearch.WordTrace tailWord_6935084 prefixEnd_6935084 3561031471305449685656135 := by
  unfold tailWord_6935084
  simp only [CollatzResearch.WordTrace]
  refine ⟨126471646803691280447986153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168628862404921707263981537 126471646803691280447986153)
  ·
    refine ⟨94853735102768460335989615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126471646803691280447986153 94853735102768460335989615)
    ·
      refine ⟨142280602654152690503984423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94853735102768460335989615 142280602654152690503984423)
      ·
        refine ⟨213420903981229035755976635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142280602654152690503984423 213420903981229035755976635)
        ·
          refine ⟨320131355971843553633964953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213420903981229035755976635 320131355971843553633964953)
          ·
            refine ⟨240098516978882665225473715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320131355971843553633964953 240098516978882665225473715)
            ·
              refine ⟨360147775468323997838210573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240098516978882665225473715 360147775468323997838210573)
              ·
                refine ⟨135055415800621499189328965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360147775468323997838210573 135055415800621499189328965)
                ·
                  refine ⟨25322890462616531097999181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135055415800621499189328965 25322890462616531097999181)
                  ·
                    refine ⟨9496083923481199161749693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25322890462616531097999181 9496083923481199161749693)
                    ·
                      refine ⟨3561031471305449685656135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496083923481199161749693 3561031471305449685656135)
                      ·
                        rfl

theorem cell23_6935084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_6935084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935084 prefixEnd_6935084 := by exact prefixLift 6935084
  have htrace : WordTrace (prefixWord ++ tailWord_6935084) baseStart_6935084 baseEnd_6935084 := by
    simpa [prefixWord, tailWord_6935084, baseEnd_6935084] using wordTrace_append hprefix tailTrace_6935084
  have hstable : (prefixWord ++ tailWord_6935084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935084).length < 2 ^ (prefixWord ++ tailWord_6935084).sum := by decide
  have hdescent : baseEnd_6935084 < baseStart_6935084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935087 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 11]
def baseStart_6935087 : Nat := 118140960795 + 6935087 * 2 ^ 59
def prefixEnd_6935087 : Nat := 4983230072969 + 3 ^ 40 * 6935087 * 2
def baseEnd_6935087 : Nat := 1187011003915804391306207

theorem tailTrace_6935087 : CollatzResearch.WordTrace tailWord_6935087 prefixEnd_6935087 1187011003915804391306207 := by
  unfold tailWord_6935087
  simp only [CollatzResearch.WordTrace]
  refine ⟨252943403026371692408331515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168628935350914461605554343 252943403026371692408331515)
  ·
    refine ⟨379415104539557538612497273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252943403026371692408331515 379415104539557538612497273)
    ·
      refine ⟨284561328404668153959372955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379415104539557538612497273 284561328404668153959372955)
      ·
        refine ⟨426841992607002230939059433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284561328404668153959372955 426841992607002230939059433)
        ·
          refine ⟨320131494455251673204294575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426841992607002230939059433 320131494455251673204294575)
          ·
            refine ⟨480197241682877509806441863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320131494455251673204294575 480197241682877509806441863)
            ·
              refine ⟨720295862524316264709662795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480197241682877509806441863 720295862524316264709662795)
              ·
                refine ⟨1080443793786474397064494193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720295862524316264709662795 1080443793786474397064494193)
                ·
                  refine ⟨810332845339855797798370645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080443793786474397064494193 810332845339855797798370645)
                  ·
                    refine ⟨1187011003915804391306207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 810332845339855797798370645 1187011003915804391306207)
                    ·
                      rfl

theorem cell23_6935087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_6935087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935087 prefixEnd_6935087 := by exact prefixLift 6935087
  have htrace : WordTrace (prefixWord ++ tailWord_6935087) baseStart_6935087 baseEnd_6935087 := by
    simpa [prefixWord, tailWord_6935087, baseEnd_6935087] using wordTrace_append hprefix tailTrace_6935087
  have hstable : (prefixWord ++ tailWord_6935087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935087).length < 2 ^ (prefixWord ++ tailWord_6935087).sum := by decide
  have hdescent : baseEnd_6935087 < baseStart_6935087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935121 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_6935121 : Nat := 118140960795 + 6935121 * 2 ^ 59
def prefixEnd_6935121 : Nat := 4983230072969 + 3 ^ 40 * 6935121 * 2
def baseEnd_6935121 : Nat := 1187016823363222013631155

theorem tailTrace_6935121 : CollatzResearch.WordTrace tailWord_6935121 prefixEnd_6935121 1187016823363222013631155 := by
  unfold tailWord_6935121
  simp only [CollatzResearch.WordTrace]
  refine ⟨252944643108248516215069217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168629762072165677476712811 252944643108248516215069217)
  ·
    refine ⟨189708482331186387161301913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252944643108248516215069217 189708482331186387161301913)
    ·
      refine ⟨142281361748389790370976435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189708482331186387161301913 142281361748389790370976435)
      ·
        refine ⟨213422042622584685556464653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142281361748389790370976435 213422042622584685556464653)
        ·
          refine ⟨80033265983469257083674245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213422042622584685556464653 80033265983469257083674245)
          ·
            refine ⟨15006237371900485703188921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80033265983469257083674245 15006237371900485703188921)
            ·
              refine ⟨11254678028925364277391691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15006237371900485703188921 11254678028925364277391691)
              ·
                refine ⟨16882017043388046416087537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11254678028925364277391691 16882017043388046416087537)
                ·
                  refine ⟨12661512782541034812065653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16882017043388046416087537 12661512782541034812065653)
                  ·
                    refine ⟨1187016823363222013631155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12661512782541034812065653 1187016823363222013631155)
                    ·
                      rfl

theorem cell23_6935121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_6935121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935121 prefixEnd_6935121 := by exact prefixLift 6935121
  have htrace : WordTrace (prefixWord ++ tailWord_6935121) baseStart_6935121 baseEnd_6935121 := by
    simpa [prefixWord, tailWord_6935121, baseEnd_6935121] using wordTrace_append hprefix tailTrace_6935121
  have hstable : (prefixWord ++ tailWord_6935121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935121).length < 2 ^ (prefixWord ++ tailWord_6935121).sum := by decide
  have hdescent : baseEnd_6935121 < baseStart_6935121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935178 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6935178 : Nat := 118140960795 + 6935178 * 2 ^ 59
def prefixEnd_6935178 : Nat := 4983230072969 + 3 ^ 40 * 6935178 * 2
def baseEnd_6935178 : Nat := 3561079738486972317880703

theorem tailTrace_6935178 : CollatzResearch.WordTrace tailWord_6935178 prefixEnd_6935178 3561079738486972317880703 := by
  unfold tailWord_6935178
  simp only [CollatzResearch.WordTrace]
  refine ⟨63236680517260503737473547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168631148046028009966596125 63236680517260503737473547)
  ·
    refine ⟨94855020775890755606210321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63236680517260503737473547 94855020775890755606210321)
    ·
      refine ⟨71141265581918066704657741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94855020775890755606210321 71141265581918066704657741)
      ·
        refine ⟨26677974593219275014246653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71141265581918066704657741 26677974593219275014246653)
        ·
          refine ⟨10004240472457228130342495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26677974593219275014246653 10004240472457228130342495)
          ·
            refine ⟨15006360708685842195513743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004240472457228130342495 15006360708685842195513743)
            ·
              refine ⟨22509541063028763293270615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15006360708685842195513743 22509541063028763293270615)
              ·
                refine ⟨33764311594543144939905923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22509541063028763293270615 33764311594543144939905923)
                ·
                  refine ⟨50646467391814717409858885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33764311594543144939905923 50646467391814717409858885)
                  ·
                    refine ⟨9496212635965259514348541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50646467391814717409858885 9496212635965259514348541)
                    ·
                      refine ⟨3561079738486972317880703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496212635965259514348541 3561079738486972317880703)
                      ·
                        rfl

theorem cell23_6935178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6935178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935178 prefixEnd_6935178 := by exact prefixLift 6935178
  have htrace : WordTrace (prefixWord ++ tailWord_6935178) baseStart_6935178 baseEnd_6935178 := by
    simpa [prefixWord, tailWord_6935178, baseEnd_6935178] using wordTrace_append hprefix tailTrace_6935178
  have hstable : (prefixWord ++ tailWord_6935178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935178).length < 2 ^ (prefixWord ++ tailWord_6935178).sum := by decide
  have hdescent : baseEnd_6935178 < baseStart_6935178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935228 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_6935228 : Nat := 118140960795 + 6935228 * 2 ^ 59
def prefixEnd_6935228 : Nat := 4983230072969 + 3 ^ 40 * 6935228 * 2
def baseEnd_6935228 : Nat := 1187035137506565707418491

theorem tailTrace_6935228 : CollatzResearch.WordTrace tailWord_6935228 prefixEnd_6935228 1187035137506565707418491 := by
  unfold tailWord_6935228
  simp only [CollatzResearch.WordTrace]
  refine ⟨126474272859430436744607169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168632363812573915659476225 126474272859430436744607169)
  ·
    refine ⟨94855704644572827558455377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126474272859430436744607169 94855704644572827558455377)
    ·
      refine ⟨71141778483429620668841533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94855704644572827558455377 71141778483429620668841533)
      ·
        refine ⟨26678166931286107750815575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71141778483429620668841533 26678166931286107750815575)
        ·
          refine ⟨40017250396929161626223363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26678166931286107750815575 40017250396929161626223363)
          ·
            refine ⟨60025875595393742439335045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40017250396929161626223363 60025875595393742439335045)
            ·
              refine ⟨11254851674136326707375321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60025875595393742439335045 11254851674136326707375321)
              ·
                refine ⟨8441138755602245030531491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11254851674136326707375321 8441138755602245030531491)
                ·
                  refine ⟨12661708133403367545797237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8441138755602245030531491 12661708133403367545797237)
                  ·
                    refine ⟨1187035137506565707418491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12661708133403367545797237 1187035137506565707418491)
                    ·
                      rfl

theorem cell23_6935228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_6935228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935228 prefixEnd_6935228 := by exact prefixLift 6935228
  have htrace : WordTrace (prefixWord ++ tailWord_6935228) baseStart_6935228 baseEnd_6935228 := by
    simpa [prefixWord, tailWord_6935228, baseEnd_6935228] using wordTrace_append hprefix tailTrace_6935228
  have hstable : (prefixWord ++ tailWord_6935228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935228).length < 2 ^ (prefixWord ++ tailWord_6935228).sum := by decide
  have hdescent : baseEnd_6935228 < baseStart_6935228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935242 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_6935242 : Nat := 118140960795 + 6935242 * 2 ^ 59
def prefixEnd_6935242 : Nat := 4983230072969 + 3 ^ 40 * 6935242 * 2
def baseEnd_6935242 : Nat := 3561112601248860067480409

theorem tailTrace_6935242 : CollatzResearch.WordTrace tailWord_6935242 prefixEnd_6935242 3561112601248860067480409 := by
  unfold tailWord_6935242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63237264085202538470055995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168632704227206769253482653 63237264085202538470055995)
  ·
    refine ⟨94855896127803807705083993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63237264085202538470055995 94855896127803807705083993)
    ·
      refine ⟨71141922095852855778812995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94855896127803807705083993 71141922095852855778812995)
      ·
        refine ⟨106712883143779283668219493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71141922095852855778812995 106712883143779283668219493)
        ·
          refine ⟨20008665589458615687791155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106712883143779283668219493 20008665589458615687791155)
          ·
            refine ⟨30012998384187923531686733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20008665589458615687791155 30012998384187923531686733)
            ·
              refine ⟨11254874394070471324382525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30012998384187923531686733 11254874394070471324382525)
              ·
                refine ⟨4220577897776426746643447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11254874394070471324382525 4220577897776426746643447)
                ·
                  refine ⟨6330866846664640119965171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220577897776426746643447 6330866846664640119965171)
                  ·
                    refine ⟨9496300269996960179947757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6330866846664640119965171 9496300269996960179947757)
                    ·
                      refine ⟨3561112601248860067480409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496300269996960179947757 3561112601248860067480409)
                      ·
                        rfl

theorem cell23_6935242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_6935242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935242 prefixEnd_6935242 := by exact prefixLift 6935242
  have htrace : WordTrace (prefixWord ++ tailWord_6935242) baseStart_6935242 baseEnd_6935242 := by
    simpa [prefixWord, tailWord_6935242, baseEnd_6935242] using wordTrace_append hprefix tailTrace_6935242
  have hstable : (prefixWord ++ tailWord_6935242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935242).length < 2 ^ (prefixWord ++ tailWord_6935242).sum := by decide
  have hdescent : baseEnd_6935242 < baseStart_6935242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935252 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6935252 : Nat := 118140960795 + 6935252 * 2 ^ 59
def prefixEnd_6935252 : Nat := 4983230072969 + 3 ^ 40 * 6935252 * 2
def baseEnd_6935252 : Nat := 3561117736055405028355363

theorem tailTrace_6935252 : CollatzResearch.WordTrace tailWord_6935252 prefixEnd_6935252 3561117736055405028355363 := by
  unfold tailWord_6935252
  simp only [CollatzResearch.WordTrace]
  refine ⟨126474710535386962794044005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168632947380515950392058673 126474710535386962794044005)
  ·
    refine ⟨23714008225385055523883251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126474710535386962794044005 23714008225385055523883251)
    ·
      refine ⟨35571012338077583285824877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23714008225385055523883251 35571012338077583285824877)
      ·
        refine ⟨13339129626779093732184329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35571012338077583285824877 13339129626779093732184329)
        ·
          refine ⟨10004347220084320299138247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13339129626779093732184329 10004347220084320299138247)
          ·
            refine ⟨15006520830126480448707371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004347220084320299138247 15006520830126480448707371)
            ·
              refine ⟨22509781245189720673061057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15006520830126480448707371 22509781245189720673061057)
              ·
                refine ⟨16882335933892290504795793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22509781245189720673061057 16882335933892290504795793)
                ·
                  refine ⟨12661751950419217878596845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16882335933892290504795793 12661751950419217878596845)
                  ·
                    refine ⟨4748156981407206704473817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12661751950419217878596845 4748156981407206704473817)
                    ·
                      refine ⟨3561117736055405028355363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748156981407206704473817 3561117736055405028355363)
                      ·
                        rfl

theorem cell23_6935252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6935252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935252 prefixEnd_6935252 := by exact prefixLift 6935252
  have htrace : WordTrace (prefixWord ++ tailWord_6935252) baseStart_6935252 baseEnd_6935252 := by
    simpa [prefixWord, tailWord_6935252, baseEnd_6935252] using wordTrace_append hprefix tailTrace_6935252
  have hstable : (prefixWord ++ tailWord_6935252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935252).length < 2 ^ (prefixWord ++ tailWord_6935252).sum := by decide
  have hdescent : baseEnd_6935252 < baseStart_6935252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935258 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_6935258 : Nat := 118140960795 + 6935258 * 2 ^ 59
def prefixEnd_6935258 : Nat := 4983230072969 + 3 ^ 40 * 6935258 * 2
def baseEnd_6935258 : Nat := 1187040272313110668293445

theorem tailTrace_6935258 : CollatzResearch.WordTrace tailWord_6935258 prefixEnd_6935258 1187040272313110668293445 := by
  unfold tailWord_6935258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63237409977188047153201607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168633093272501459075204285 63237409977188047153201607)
  ·
    refine ⟨94856114965782070729802411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63237409977188047153201607 94856114965782070729802411)
    ·
      refine ⟨142284172448673106094703617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94856114965782070729802411 142284172448673106094703617)
      ·
        refine ⟨106713129336504829571027713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142284172448673106094703617 106713129336504829571027713)
        ·
          refine ⟨80034847002378622178270785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106713129336504829571027713 80034847002378622178270785)
          ·
            refine ⟨60026135251783966633703089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80034847002378622178270785 60026135251783966633703089)
            ·
              refine ⟨45019601438837974975277317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60026135251783966633703089 45019601438837974975277317)
              ·
                refine ⟨8441175269782120307864497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45019601438837974975277317 8441175269782120307864497)
                ·
                  refine ⟨6330881452336590230898373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8441175269782120307864497 6330881452336590230898373)
                  ·
                    refine ⟨1187040272313110668293445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330881452336590230898373 1187040272313110668293445)
                    ·
                      rfl

theorem cell23_6935258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_6935258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935258 prefixEnd_6935258 := by exact prefixLift 6935258
  have htrace : WordTrace (prefixWord ++ tailWord_6935258) baseStart_6935258 baseEnd_6935258 := by
    simpa [prefixWord, tailWord_6935258, baseEnd_6935258] using wordTrace_append hprefix tailTrace_6935258
  have hstable : (prefixWord ++ tailWord_6935258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935258).length < 2 ^ (prefixWord ++ tailWord_6935258).sum := by decide
  have hdescent : baseEnd_6935258 < baseStart_6935258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935315 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 3]
def baseStart_6935315 : Nat := 118140960795 + 6935315 * 2 ^ 59
def prefixEnd_6935315 : Nat := 4983230072969 + 3 ^ 40 * 6935315 * 2
def baseEnd_6935315 : Nat := 3561150085336638281867573

theorem tailTrace_6935315 : CollatzResearch.WordTrace tailWord_6935315 prefixEnd_6935315 3561150085336638281867573 := by
  unfold tailWord_6935315
  simp only [CollatzResearch.WordTrace]
  refine ⟨252951718869545687347631399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168634479246363791565087599 252951718869545687347631399)
  ·
    refine ⟨379427578304318531021447099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252951718869545687347631399 379427578304318531021447099)
    ·
      refine ⟨569141367456477796532170649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379427578304318531021447099 569141367456477796532170649)
      ·
        refine ⟨426856025592358347399127987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569141367456477796532170649 426856025592358347399127987)
        ·
          refine ⟨640284038388537521098691981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426856025592358347399127987 640284038388537521098691981)
          ·
            refine ⟨240106514395701570412009493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640284038388537521098691981 240106514395701570412009493)
            ·
              refine ⟨11254992862298511113062945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240106514395701570412009493 11254992862298511113062945)
              ·
                refine ⟨8441244646723883334797209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11254992862298511113062945 8441244646723883334797209)
                ·
                  refine ⟨6330933485042912501097907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8441244646723883334797209 6330933485042912501097907)
                  ·
                    refine ⟨9496400227564368751646861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6330933485042912501097907 9496400227564368751646861)
                    ·
                      refine ⟨3561150085336638281867573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496400227564368751646861 3561150085336638281867573)
                      ·
                        rfl

theorem cell23_6935315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_6935315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935315 prefixEnd_6935315 := by exact prefixLift 6935315
  have htrace : WordTrace (prefixWord ++ tailWord_6935315) baseStart_6935315 baseEnd_6935315 := by
    simpa [prefixWord, tailWord_6935315, baseEnd_6935315] using wordTrace_append hprefix tailTrace_6935315
  have hstable : (prefixWord ++ tailWord_6935315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935315).length < 2 ^ (prefixWord ++ tailWord_6935315).sum := by decide
  have hdescent : baseEnd_6935315 < baseStart_6935315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935342 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6935342 : Nat := 118140960795 + 6935342 * 2 ^ 59
def prefixEnd_6935342 : Nat := 4983230072969 + 3 ^ 40 * 6935342 * 2
def baseEnd_6935342 : Nat := 3561163949314309676229949

theorem tailTrace_6935342 : CollatzResearch.WordTrace tailWord_6935342 prefixEnd_6935342 3561163949314309676229949 := by
  unfold tailWord_6935342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619087955055983869858035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168635135760298580639242853 31619087955055983869858035)
  ·
    refine ⟨47428631932583975804787053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31619087955055983869858035 47428631932583975804787053)
    ·
      refine ⟨17785736974718990926795145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47428631932583975804787053 17785736974718990926795145)
      ·
        refine ⟨13339302731039243195096359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17785736974718990926795145 13339302731039243195096359)
        ·
          refine ⟨20008954096558864792644539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339302731039243195096359 20008954096558864792644539)
          ·
            refine ⟨30013431144838297188966809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20008954096558864792644539 30013431144838297188966809)
            ·
              refine ⟨22510073358628722891725107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30013431144838297188966809 22510073358628722891725107)
              ·
                refine ⟨33765110037943084337587661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22510073358628722891725107 33765110037943084337587661)
                ·
                  refine ⟨12661916264228656626595373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33765110037943084337587661 12661916264228656626595373)
                  ·
                    refine ⟨4748218599085746234973265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12661916264228656626595373 4748218599085746234973265)
                    ·
                      refine ⟨3561163949314309676229949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748218599085746234973265 3561163949314309676229949)
                      ·
                        rfl

theorem cell23_6935342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6935342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935342 prefixEnd_6935342 := by exact prefixLift 6935342
  have htrace : WordTrace (prefixWord ++ tailWord_6935342) baseStart_6935342 baseEnd_6935342 := by
    simpa [prefixWord, tailWord_6935342, baseEnd_6935342] using wordTrace_append hprefix tailTrace_6935342
  have hstable : (prefixWord ++ tailWord_6935342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935342).length < 2 ^ (prefixWord ++ tailWord_6935342).sum := by decide
  have hdescent : baseEnd_6935342 < baseStart_6935342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935351 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_6935351 : Nat := 118140960795 + 6935351 * 2 ^ 59
def prefixEnd_6935351 : Nat := 4983230072969 + 3 ^ 40 * 6935351 * 2
def baseEnd_6935351 : Nat := 3561168570640200141017407

theorem tailTrace_6935351 : CollatzResearch.WordTrace tailWord_6935351 prefixEnd_6935351 3561168570640200141017407 := by
  unfold tailWord_6935351
  simp only [CollatzResearch.WordTrace]
  refine ⟨252953031897415265495941907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168635354598276843663961271 252953031897415265495941907)
  ·
    refine ⟨379429547846122898243912861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252953031897415265495941907 379429547846122898243912861)
    ·
      refine ⟨142286080442296086841467323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379429547846122898243912861 142286080442296086841467323)
      ·
        refine ⟨213429120663444130262200985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142286080442296086841467323 213429120663444130262200985)
        ·
          refine ⟨160071840497583097696650739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213429120663444130262200985 160071840497583097696650739)
          ·
            refine ⟨240107760746374646544976109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160071840497583097696650739 240107760746374646544976109)
            ·
              refine ⟨90040410279890492454366041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240107760746374646544976109 90040410279890492454366041)
              ·
                refine ⟨67530307709917869340774531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90040410279890492454366041 67530307709917869340774531)
                ·
                  refine ⟨101295461564876804011161797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67530307709917869340774531 101295461564876804011161797)
                  ·
                    refine ⟨18992899043414400752092837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101295461564876804011161797 18992899043414400752092837)
                    ·
                      refine ⟨3561168570640200141017407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18992899043414400752092837 3561168570640200141017407)
                      ·
                        rfl

theorem cell23_6935351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_6935351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935351 prefixEnd_6935351 := by exact prefixLift 6935351
  have htrace : WordTrace (prefixWord ++ tailWord_6935351) baseStart_6935351 baseEnd_6935351 := by
    simpa [prefixWord, tailWord_6935351, baseEnd_6935351] using wordTrace_append hprefix tailTrace_6935351
  have hstable : (prefixWord ++ tailWord_6935351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935351).length < 2 ^ (prefixWord ++ tailWord_6935351).sum := by decide
  have hdescent : baseEnd_6935351 < baseStart_6935351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935359 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 1, 3, 2]
def baseStart_6935359 : Nat := 118140960795 + 6935359 * 2 ^ 59
def prefixEnd_6935359 : Nat := 4983230072969 + 3 ^ 40 * 6935359 * 2
def baseEnd_6935359 : Nat := 3561172678485436109717371

theorem tailTrace_6935359 : CollatzResearch.WordTrace tailWord_6935359 prefixEnd_6935359 3561172678485436109717371 := by
  unfold tailWord_6935359
  simp only [CollatzResearch.WordTrace]
  refine ⟨252953323681386282862233131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168635549120924188574822087 252953323681386282862233131)
  ·
    refine ⟨379429985522079424293349697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252953323681386282862233131 379429985522079424293349697)
    ·
      refine ⟨284572489141559568220012273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379429985522079424293349697 284572489141559568220012273)
      ·
        refine ⟨213429366856169676165009205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284572489141559568220012273 213429366856169676165009205)
        ·
          refine ⟨20009003142765907140469613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213429366856169676165009205 20009003142765907140469613)
          ·
            refine ⟨7503376178537215177676105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20009003142765907140469613 7503376178537215177676105)
            ·
              refine ⟨5627532133902911383257079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7503376178537215177676105 5627532133902911383257079)
              ·
                refine ⟨8441298200854367074885619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627532133902911383257079 8441298200854367074885619)
                ·
                  refine ⟨12661947301281550612328429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8441298200854367074885619 12661947301281550612328429)
                  ·
                    refine ⟨4748230237980581479623161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12661947301281550612328429 4748230237980581479623161)
                    ·
                      refine ⟨3561172678485436109717371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748230237980581479623161 3561172678485436109717371)
                      ·
                        rfl

theorem cell23_6935359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_6935359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935359 prefixEnd_6935359 := by exact prefixLift 6935359
  have htrace : WordTrace (prefixWord ++ tailWord_6935359) baseStart_6935359 baseEnd_6935359 := by
    simpa [prefixWord, tailWord_6935359, baseEnd_6935359] using wordTrace_append hprefix tailTrace_6935359
  have hstable : (prefixWord ++ tailWord_6935359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935359).length < 2 ^ (prefixWord ++ tailWord_6935359).sum := by decide
  have hdescent : baseEnd_6935359 < baseStart_6935359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935372 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_6935372 : Nat := 118140960795 + 6935372 * 2 ^ 59
def prefixEnd_6935372 : Nat := 4983230072969 + 3 ^ 40 * 6935372 * 2
def baseEnd_6935372 : Nat := 3561179353733944558854811

theorem tailTrace_6935372 : CollatzResearch.WordTrace tailWord_6935372 prefixEnd_6935372 3561179353733944558854811 := by
  unfold tailWord_6935372
  simp only [CollatzResearch.WordTrace]
  refine ⟨126476898915169593041228185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168635865220226124054970913 126476898915169593041228185)
  ·
    refine ⟨94857674186377194780921139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126476898915169593041228185 94857674186377194780921139)
    ·
      refine ⟨142286511279565792171381709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94857674186377194780921139 142286511279565792171381709)
      ·
        refine ⟨53357441729837172064268141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142286511279565792171381709 53357441729837172064268141)
        ·
          refine ⟨20009040648688939524100553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53357441729837172064268141 20009040648688939524100553)
          ·
            refine ⟨15006780486516704643075415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20009040648688939524100553 15006780486516704643075415)
            ·
              refine ⟨22510170729775056964613123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15006780486516704643075415 22510170729775056964613123)
              ·
                refine ⟨33765256094662585446919685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22510170729775056964613123 33765256094662585446919685)
                ·
                  refine ⟨6330985517749234771297441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33765256094662585446919685 6330985517749234771297441)
                  ·
                    refine ⟨4748239138311926078473081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330985517749234771297441 4748239138311926078473081)
                    ·
                      refine ⟨3561179353733944558854811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748239138311926078473081 3561179353733944558854811)
                      ·
                        rfl

theorem cell23_6935372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_6935372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935372 prefixEnd_6935372 := by exact prefixLift 6935372
  have htrace : WordTrace (prefixWord ++ tailWord_6935372) baseStart_6935372 baseEnd_6935372 := by
    simpa [prefixWord, tailWord_6935372, baseEnd_6935372] using wordTrace_append hprefix tailTrace_6935372
  have hstable : (prefixWord ++ tailWord_6935372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935372).length < 2 ^ (prefixWord ++ tailWord_6935372).sum := by decide
  have hdescent : baseEnd_6935372 < baseStart_6935372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935378 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_6935378 : Nat := 118140960795 + 6935378 * 2 ^ 59
def prefixEnd_6935378 : Nat := 4983230072969 + 3 ^ 40 * 6935378 * 2
def baseEnd_6935378 : Nat := 395686937179763503931087

theorem tailTrace_6935378 : CollatzResearch.WordTrace tailWord_6935378 prefixEnd_6935378 395686937179763503931087 := by
  unfold tailWord_6935378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63238504167079362276793697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168636011112211632738116525 63238504167079362276793697)
  ·
    refine ⟨47428878125309521707595273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63238504167079362276793697 47428878125309521707595273)
    ·
      refine ⟨35571658593982141280696455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47428878125309521707595273 35571658593982141280696455)
      ·
        refine ⟨53357487890973211921044683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35571658593982141280696455 53357487890973211921044683)
        ·
          refine ⟨80036231836459817881567025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53357487890973211921044683 80036231836459817881567025)
          ·
            refine ⟨60027173877344863411175269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80036231836459817881567025 60027173877344863411175269)
            ·
              refine ⟨11255095102002161889595363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60027173877344863411175269 11255095102002161889595363)
              ·
                refine ⟨16882642653003242834393045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255095102002161889595363 16882642653003242834393045)
                ·
                  refine ⟨395686937179763503931087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16882642653003242834393045 395686937179763503931087)
                  ·
                    rfl

theorem cell23_6935378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_6935378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935378 prefixEnd_6935378 := by exact prefixLift 6935378
  have htrace : WordTrace (prefixWord ++ tailWord_6935378) baseStart_6935378 baseEnd_6935378 := by
    simpa [prefixWord, tailWord_6935378, baseEnd_6935378] using wordTrace_append hprefix tailTrace_6935378
  have hstable : (prefixWord ++ tailWord_6935378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935378).length < 2 ^ (prefixWord ++ tailWord_6935378).sum := by decide
  have hdescent : baseEnd_6935378 < baseStart_6935378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935391 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 7]
def baseStart_6935391 : Nat := 118140960795 + 6935391 * 2 ^ 59
def prefixEnd_6935391 : Nat := 4983230072969 + 3 ^ 40 * 6935391 * 2
def baseEnd_6935391 : Nat := 1187063036622126661505741

theorem tailTrace_6935391 : CollatzResearch.WordTrace tailWord_6935391 prefixEnd_6935391 1187063036622126661505741 := by
  unfold tailWord_6935391
  simp only [CollatzResearch.WordTrace]
  refine ⟨252954490817270352327398027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168636327211513568218265351 252954490817270352327398027)
  ·
    refine ⟨379431736225905528491097041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252954490817270352327398027 379431736225905528491097041)
    ·
      refine ⟨284573802169429146368322781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379431736225905528491097041 284573802169429146368322781)
      ·
        refine ⟨106715175813535929888121043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284573802169429146368322781 106715175813535929888121043)
        ·
          refine ⟨160072763720303894832181565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106715175813535929888121043 160072763720303894832181565)
          ·
            refine ⟨60027286395113960562068087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160072763720303894832181565 60027286395113960562068087)
            ·
              refine ⟨90040929592670940843102131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60027286395113960562068087 90040929592670940843102131)
              ·
                refine ⟨135061394389006411264653197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90040929592670940843102131 135061394389006411264653197)
                ·
                  refine ⟨50648022895877404224244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135061394389006411264653197 50648022895877404224244949)
                  ·
                    refine ⟨1187063036622126661505741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50648022895877404224244949 1187063036622126661505741)
                    ·
                      rfl

theorem cell23_6935391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_6935391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935391 prefixEnd_6935391 := by exact prefixLift 6935391
  have htrace : WordTrace (prefixWord ++ tailWord_6935391) baseStart_6935391 baseEnd_6935391 := by
    simpa [prefixWord, tailWord_6935391, baseEnd_6935391] using wordTrace_append hprefix tailTrace_6935391
  have hstable : (prefixWord ++ tailWord_6935391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935391).length < 2 ^ (prefixWord ++ tailWord_6935391).sum := by decide
  have hdescent : baseEnd_6935391 < baseStart_6935391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935401 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_6935401 : Nat := 118140960795 + 6935401 * 2 ^ 59
def prefixEnd_6935401 : Nat := 4983230072969 + 3 ^ 40 * 6935401 * 2
def baseEnd_6935401 : Nat := 3561194244672924945392177

theorem tailTrace_6935401 : CollatzResearch.WordTrace tailWord_6935401 prefixEnd_6935401 3561194244672924945392177 := by
  unfold tailWord_6935401
  simp only [CollatzResearch.WordTrace]
  refine ⟨252954855547234124035262057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168636570364822749356841371 252954855547234124035262057)
  ·
    refine ⟨189716141660425593026446543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252954855547234124035262057 189716141660425593026446543)
    ·
      refine ⟨284574212490638389539669815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189716141660425593026446543 284574212490638389539669815)
      ·
        refine ⟨426861318735957584309504723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284574212490638389539669815 426861318735957584309504723)
        ·
          refine ⟨640291978103936376464257085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426861318735957584309504723 640291978103936376464257085)
          ·
            refine ⟨240109491788976141174096407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640291978103936376464257085 240109491788976141174096407)
            ·
              refine ⟨360164237683464211761144611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240109491788976141174096407 360164237683464211761144611)
              ·
                refine ⟨540246356525196317641716917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360164237683464211761144611 540246356525196317641716917)
                ·
                  refine ⟨50648095924237154778910961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540246356525196317641716917 50648095924237154778910961)
                  ·
                    refine ⟨37986071943177866084183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50648095924237154778910961 37986071943177866084183221)
                    ·
                      refine ⟨3561194244672924945392177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37986071943177866084183221 3561194244672924945392177)
                      ·
                        rfl

theorem cell23_6935401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_6935401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935401 prefixEnd_6935401 := by exact prefixLift 6935401
  have htrace : WordTrace (prefixWord ++ tailWord_6935401) baseStart_6935401 baseEnd_6935401 := by
    simpa [prefixWord, tailWord_6935401, baseEnd_6935401] using wordTrace_append hprefix tailTrace_6935401
  have hstable : (prefixWord ++ tailWord_6935401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935401).length < 2 ^ (prefixWord ++ tailWord_6935401).sum := by decide
  have hdescent : baseEnd_6935401 < baseStart_6935401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935465 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_6935465 : Nat := 118140960795 + 6935465 * 2 ^ 59
def prefixEnd_6935465 : Nat := 4983230072969 + 3 ^ 40 * 6935465 * 2
def baseEnd_6935465 : Nat := 3561227107434812694991883

theorem tailTrace_6935465 : CollatzResearch.WordTrace tailWord_6935465 prefixEnd_6935465 3561227107434812694991883 := by
  unfold tailWord_6935465
  simp only [CollatzResearch.WordTrace]
  refine ⟨252957189819002262965591849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168638126546001508643727899 252957189819002262965591849)
  ·
    refine ⟨189717892364251697224193887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252957189819002262965591849 189717892364251697224193887)
    ·
      refine ⟨284576838546377545836290831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189717892364251697224193887 284576838546377545836290831)
      ·
        refine ⟨426865257819566318754436247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284576838546377545836290831 426865257819566318754436247)
        ·
          refine ⟨640297886729349478131654371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426865257819566318754436247 640297886729349478131654371)
          ·
            refine ⟨960446830094024217197481557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640297886729349478131654371 960446830094024217197481557)
            ·
              refine ⟨11255236290164346295282987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 960446830094024217197481557 11255236290164346295282987)
              ·
                refine ⟨16882854435246519442924481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255236290164346295282987 16882854435246519442924481)
                ·
                  refine ⟨12662140826434889582193361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16882854435246519442924481 12662140826434889582193361)
                  ·
                    refine ⟨9496605619826167186645021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12662140826434889582193361 9496605619826167186645021)
                    ·
                      refine ⟨3561227107434812694991883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496605619826167186645021 3561227107434812694991883)
                      ·
                        rfl

theorem cell23_6935465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_6935465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935465 prefixEnd_6935465 := by exact prefixLift 6935465
  have htrace : WordTrace (prefixWord ++ tailWord_6935465) baseStart_6935465 baseEnd_6935465 := by
    simpa [prefixWord, tailWord_6935465, baseEnd_6935465] using wordTrace_append hprefix tailTrace_6935465
  have hstable : (prefixWord ++ tailWord_6935465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935465).length < 2 ^ (prefixWord ++ tailWord_6935465).sum := by decide
  have hdescent : baseEnd_6935465 < baseStart_6935465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935505 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_6935505 : Nat := 118140960795 + 6935505 * 2 ^ 59
def prefixEnd_6935505 : Nat := 4983230072969 + 3 ^ 40 * 6935505 * 2
def baseEnd_6935505 : Nat := 3561247646660992538491699

theorem tailTrace_6935505 : CollatzResearch.WordTrace tailWord_6935505 prefixEnd_6935505 3561247646660992538491699 := by
  unfold tailWord_6935505
  simp only [CollatzResearch.WordTrace]
  refine ⟨252958648738857349797047969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168639099159238233198031979 252958648738857349797047969)
  ·
    refine ⟨189718986554143012347785977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252958648738857349797047969 189718986554143012347785977)
    ·
      refine ⟨142289239915607259260839483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189718986554143012347785977 142289239915607259260839483)
      ·
        refine ⟨213433859873410888891259225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142289239915607259260839483 213433859873410888891259225)
        ·
          refine ⟨160075394905058166668444419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213433859873410888891259225 160075394905058166668444419)
          ·
            refine ⟨240113092357587250002666629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160075394905058166668444419 240113092357587250002666629)
            ·
              refine ⟨45021204817047609375499993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240113092357587250002666629 45021204817047609375499993)
              ·
                refine ⟨33765903612785707031624995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45021204817047609375499993 33765903612785707031624995)
                ·
                  refine ⟨50648855419178560547437493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33765903612785707031624995 50648855419178560547437493)
                  ·
                    refine ⟨4748330195547990051322265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50648855419178560547437493 4748330195547990051322265)
                    ·
                      refine ⟨3561247646660992538491699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748330195547990051322265 3561247646660992538491699)
                      ·
                        rfl

theorem cell23_6935505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_6935505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935505 prefixEnd_6935505 := by exact prefixLift 6935505
  have htrace : WordTrace (prefixWord ++ tailWord_6935505) baseStart_6935505 baseEnd_6935505 := by
    simpa [prefixWord, tailWord_6935505, baseEnd_6935505] using wordTrace_append hprefix tailTrace_6935505
  have hstable : (prefixWord ++ tailWord_6935505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935505).length < 2 ^ (prefixWord ++ tailWord_6935505).sum := by decide
  have hdescent : baseEnd_6935505 < baseStart_6935505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935512 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_6935512 : Nat := 118140960795 + 6935512 * 2 ^ 59
def prefixEnd_6935512 : Nat := 4983230072969 + 3 ^ 40 * 6935512 * 2
def baseEnd_6935512 : Nat := 3561251241025574011104167

theorem tailTrace_6935512 : CollatzResearch.WordTrace tailWord_6935512 prefixEnd_6935512 3561251241025574011104167 := by
  unfold tailWord_6935512
  simp only [CollatzResearch.WordTrace]
  refine ⟨126479452024915994996276395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168639269366554659995035193 126479452024915994996276395)
  ·
    refine ⟨189719178037373992494414593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126479452024915994996276395 189719178037373992494414593)
    ·
      refine ⟨142289383528030494370810945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189719178037373992494414593 142289383528030494370810945)
      ·
        refine ⟨106717037646022870778108209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142289383528030494370810945 106717037646022870778108209)
        ·
          refine ⟨80037778234517153083581157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106717037646022870778108209 80037778234517153083581157)
          ·
            refine ⟨15007083418971966203171467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80037778234517153083581157 15007083418971966203171467)
            ·
              refine ⟨22510625128457949304757201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007083418971966203171467 22510625128457949304757201)
              ·
                refine ⟨16882968846343461978567901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22510625128457949304757201 16882968846343461978567901)
                ·
                  refine ⟨6331113317378798241962963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16882968846343461978567901 6331113317378798241962963)
                  ·
                    refine ⟨9496669976068197362944445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331113317378798241962963 9496669976068197362944445)
                    ·
                      refine ⟨3561251241025574011104167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496669976068197362944445 3561251241025574011104167)
                      ·
                        rfl

theorem cell23_6935512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_6935512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935512 prefixEnd_6935512 := by exact prefixLift 6935512
  have htrace : WordTrace (prefixWord ++ tailWord_6935512) baseStart_6935512 baseEnd_6935512 := by
    simpa [prefixWord, tailWord_6935512, baseEnd_6935512] using wordTrace_append hprefix tailTrace_6935512
  have hstable : (prefixWord ++ tailWord_6935512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935512).length < 2 ^ (prefixWord ++ tailWord_6935512).sum := by decide
  have hdescent : baseEnd_6935512 < baseStart_6935512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935545 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_6935545 : Nat := 118140960795 + 6935545 * 2 ^ 59
def prefixEnd_6935545 : Nat := 4983230072969 + 3 ^ 40 * 6935545 * 2
def baseEnd_6935545 : Nat := 1187089395295724127330505

theorem tailTrace_6935545 : CollatzResearch.WordTrace tailWord_6935545 prefixEnd_6935545 1187089395295724127330505 := by
  unfold tailWord_6935545
  simp only [CollatzResearch.WordTrace]
  refine ⟨252960107658712436628504089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168640071772474957752336059 252960107658712436628504089)
  ·
    refine ⟨189720080744034327471378067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252960107658712436628504089 189720080744034327471378067)
    ·
      refine ⟨284580121116051491207067101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189720080744034327471378067 284580121116051491207067101)
      ·
        refine ⟨106717545418519309202650163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284580121116051491207067101 106717545418519309202650163)
        ·
          refine ⟨160076318127778963803975245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106717545418519309202650163 160076318127778963803975245)
          ·
            refine ⟨60028619297917111426490717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160076318127778963803975245 60028619297917111426490717)
            ·
              refine ⟨22510732236718916784934019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60028619297917111426490717 22510732236718916784934019)
              ·
                refine ⟨33766098355078375177401029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22510732236718916784934019 33766098355078375177401029)
                ·
                  refine ⟨6331143441577195345762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33766098355078375177401029 6331143441577195345762693)
                  ·
                    refine ⟨1187089395295724127330505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331143441577195345762693 1187089395295724127330505)
                    ·
                      rfl

theorem cell23_6935545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_6935545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935545 prefixEnd_6935545 := by exact prefixLift 6935545
  have htrace : WordTrace (prefixWord ++ tailWord_6935545) baseStart_6935545 baseEnd_6935545 := by
    simpa [prefixWord, tailWord_6935545, baseEnd_6935545] using wordTrace_append hprefix tailTrace_6935545
  have hstable : (prefixWord ++ tailWord_6935545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935545).length < 2 ^ (prefixWord ++ tailWord_6935545).sum := by decide
  have hdescent : baseEnd_6935545 < baseStart_6935545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935562 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_6935562 : Nat := 118140960795 + 6935562 * 2 ^ 59
def prefixEnd_6935562 : Nat := 4983230072969 + 3 ^ 40 * 6935562 * 2
def baseEnd_6935562 : Nat := 1187092305019432938492979

theorem tailTrace_6935562 : CollatzResearch.WordTrace tailWord_6935562 prefixEnd_6935562 1187092305019432938492979 := by
  unfold tailWord_6935562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63240181924912712132968235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168640485133100565687915293 63240181924912712132968235)
  ·
    refine ⟨94860272887369068199452353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63240181924912712132968235 94860272887369068199452353)
    ·
      refine ⟨71145204665526801149589265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94860272887369068199452353 71145204665526801149589265)
      ·
        refine ⟨53358903499145100862191949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71145204665526801149589265 53358903499145100862191949)
        ·
          refine ⟨20009588812179412823321981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53358903499145100862191949 20009588812179412823321981)
          ·
            refine ⟨7503595804567279808745743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20009588812179412823321981 7503595804567279808745743)
            ·
              refine ⟨11255393706850919713118615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503595804567279808745743 11255393706850919713118615)
              ·
                refine ⟨16883090560276379569677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255393706850919713118615 16883090560276379569677923)
                ·
                  refine ⟨25324635840414569354516885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16883090560276379569677923 25324635840414569354516885)
                  ·
                    refine ⟨1187092305019432938492979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25324635840414569354516885 1187092305019432938492979)
                    ·
                      rfl

theorem cell23_6935562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_6935562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935562 prefixEnd_6935562 := by exact prefixLift 6935562
  have htrace : WordTrace (prefixWord ++ tailWord_6935562) baseStart_6935562 baseEnd_6935562 := by
    simpa [prefixWord, tailWord_6935562, baseEnd_6935562] using wordTrace_append hprefix tailTrace_6935562
  have hstable : (prefixWord ++ tailWord_6935562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935562).length < 2 ^ (prefixWord ++ tailWord_6935562).sum := by decide
  have hdescent : baseEnd_6935562 < baseStart_6935562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935575 : List Nat := [1, 1, 3, 5, 1, 2, 1, 9]
def baseStart_6935575 : Nat := 118140960795 + 6935575 * 2 ^ 59
def prefixEnd_6935575 : Nat := 4983230072969 + 3 ^ 40 * 6935575 * 2
def baseEnd_6935575 : Nat := 131899392233585454245051

theorem tailTrace_6935575 : CollatzResearch.WordTrace tailWord_6935575 prefixEnd_6935575 131899392233585454245051 := by
  unfold tailWord_6935575
  simp only [CollatzResearch.WordTrace]
  refine ⟨252961201848603751752096179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168640801232402501168064119 252961201848603751752096179)
  ·
    refine ⟨379441802772905627628144269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252961201848603751752096179 379441802772905627628144269)
    ·
      refine ⟨142290676039839610360554101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379441802772905627628144269 142290676039839610360554101)
      ·
        refine ⟨13339750878734963471301947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142290676039839610360554101 13339750878734963471301947)
        ·
          refine ⟨20009626318102445206952921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339750878734963471301947 20009626318102445206952921)
          ·
            refine ⟨15007219738576833905214691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20009626318102445206952921 15007219738576833905214691)
            ·
              refine ⟨22510829607865250857822037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007219738576833905214691 22510829607865250857822037)
              ·
                refine ⟨131899392233585454245051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22510829607865250857822037 131899392233585454245051)
                ·
                  rfl

theorem cell23_6935575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 9].length) (baseStart_6935575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935575 prefixEnd_6935575 := by exact prefixLift 6935575
  have htrace : WordTrace (prefixWord ++ tailWord_6935575) baseStart_6935575 baseEnd_6935575 := by
    simpa [prefixWord, tailWord_6935575, baseEnd_6935575] using wordTrace_append hprefix tailTrace_6935575
  have hstable : (prefixWord ++ tailWord_6935575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935575).length < 2 ^ (prefixWord ++ tailWord_6935575).sum := by decide
  have hdescent : baseEnd_6935575 < baseStart_6935575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935602 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_6935602 : Nat := 118140960795 + 6935602 * 2 ^ 59
def prefixEnd_6935602 : Nat := 4983230072969 + 3 ^ 40 * 6935602 * 2
def baseEnd_6935602 : Nat := 3561297454284478658978753

theorem tailTrace_6935602 : CollatzResearch.WordTrace tailWord_6935602 prefixEnd_6935602 3561297454284478658978753 := by
  unfold tailWord_6935602
  simp only [CollatzResearch.WordTrace]
  refine ⟨63240546654876483840832265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168641457746337290242219373 63240546654876483840832265)
  ·
    refine ⟨47430409991157362880624199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63240546654876483840832265 47430409991157362880624199)
    ·
      refine ⟨71145614986736044320936299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47430409991157362880624199 71145614986736044320936299)
      ·
        refine ⟨106718422480104066481404449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71145614986736044320936299 106718422480104066481404449)
        ·
          refine ⟨80038816860078049861053337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106718422480104066481404449 80038816860078049861053337)
          ·
            refine ⟨60029112645058537395790003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80038816860078049861053337 60029112645058537395790003)
            ·
              refine ⟨90043668967587806093685005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60029112645058537395790003 90043668967587806093685005)
              ·
                refine ⟨33766375862845427285131877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90043668967587806093685005 33766375862845427285131877)
                ·
                  refine ⟨6331195474283517615962227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33766375862845427285131877 6331195474283517615962227)
                  ·
                    refine ⟨9496793211425276423943341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331195474283517615962227 9496793211425276423943341)
                    ·
                      refine ⟨3561297454284478658978753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496793211425276423943341 3561297454284478658978753)
                      ·
                        rfl

theorem cell23_6935602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_6935602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935602 prefixEnd_6935602 := by exact prefixLift 6935602
  have htrace : WordTrace (prefixWord ++ tailWord_6935602) baseStart_6935602 baseEnd_6935602 := by
    simpa [prefixWord, tailWord_6935602, baseEnd_6935602] using wordTrace_append hprefix tailTrace_6935602
  have hstable : (prefixWord ++ tailWord_6935602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935602).length < 2 ^ (prefixWord ++ tailWord_6935602).sum := by decide
  have hdescent : baseEnd_6935602 < baseStart_6935602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935662 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6935662 : Nat := 118140960795 + 6935662 * 2 ^ 59
def prefixEnd_6935662 : Nat := 4983230072969 + 3 ^ 40 * 6935662 * 2
def baseEnd_6935662 : Nat := 3561328263123748424228477

theorem tailTrace_6935662 : CollatzResearch.WordTrace tailWord_6935662 prefixEnd_6935662 3561328263123748424228477 := by
  unfold tailWord_6935662
  simp only [CollatzResearch.WordTrace]
  refine ⟨31620546874911070701314155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168642916666192377073675493 31620546874911070701314155)
  ·
    refine ⟨47430820312366606051971233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31620546874911070701314155 47430820312366606051971233)
    ·
      refine ⟨35573115234274954538978425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47430820312366606051971233 35573115234274954538978425)
      ·
        refine ⟨26679836425706215904233819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35573115234274954538978425 26679836425706215904233819)
        ·
          refine ⟨40019754638559323856350729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26679836425706215904233819 40019754638559323856350729)
          ·
            refine ⟨30014815978919492892263047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40019754638559323856350729 30014815978919492892263047)
            ·
              refine ⟨45022223968379239338394571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30014815978919492892263047 45022223968379239338394571)
              ·
                refine ⟨67533335952568859007591857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45022223968379239338394571 67533335952568859007591857)
                ·
                  refine ⟨50650001964426644255693893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67533335952568859007591857 50650001964426644255693893)
                  ·
                    refine ⟨9496875368329995797942605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50650001964426644255693893 9496875368329995797942605)
                    ·
                      refine ⟨3561328263123748424228477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496875368329995797942605 3561328263123748424228477)
                      ·
                        rfl

theorem cell23_6935662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6935662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935662 prefixEnd_6935662 := by exact prefixLift 6935662
  have htrace : WordTrace (prefixWord ++ tailWord_6935662) baseStart_6935662 baseEnd_6935662 := by
    simpa [prefixWord, tailWord_6935662, baseEnd_6935662] using wordTrace_append hprefix tailTrace_6935662
  have hstable : (prefixWord ++ tailWord_6935662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935662).length < 2 ^ (prefixWord ++ tailWord_6935662).sum := by decide
  have hdescent : baseEnd_6935662 < baseStart_6935662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935669 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6935669 : Nat := 118140960795 + 6935669 * 2 ^ 59
def prefixEnd_6935669 : Nat := 4983230072969 + 3 ^ 40 * 6935669 * 2
def baseEnd_6935669 : Nat := 1187110619162776632280315

theorem tailTrace_6935669 : CollatzResearch.WordTrace tailWord_6935669 prefixEnd_6935669 1187110619162776632280315 := by
  unfold tailWord_6935669
  simp only [CollatzResearch.WordTrace]
  refine ⟨252964630310263205806018061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168643086873508803870678707 252964630310263205806018061)
  ·
    refine ⟨94861736366348702177256773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252964630310263205806018061 94861736366348702177256773)
    ·
      refine ⟨17786575568690381658235645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94861736366348702177256773 17786575568690381658235645)
      ·
        refine ⟨6669965838258893121838367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17786575568690381658235645 6669965838258893121838367)
        ·
          refine ⟨10004948757388339682757551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669965838258893121838367 10004948757388339682757551)
          ·
            refine ⟨15007423136082509524136327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004948757388339682757551 15007423136082509524136327)
            ·
              refine ⟨22511134704123764286204491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007423136082509524136327 22511134704123764286204491)
              ·
                refine ⟨33766702056185646429306737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22511134704123764286204491 33766702056185646429306737)
                ·
                  refine ⟨25325026542139234821980053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33766702056185646429306737 25325026542139234821980053)
                  ·
                    refine ⟨1187110619162776632280315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25325026542139234821980053 1187110619162776632280315)
                    ·
                      rfl

theorem cell23_6935669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6935669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935669 prefixEnd_6935669 := by exact prefixLift 6935669
  have htrace : WordTrace (prefixWord ++ tailWord_6935669) baseStart_6935669 baseEnd_6935669 := by
    simpa [prefixWord, tailWord_6935669, baseEnd_6935669] using wordTrace_append hprefix tailTrace_6935669
  have hstable : (prefixWord ++ tailWord_6935669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935669).length < 2 ^ (prefixWord ++ tailWord_6935669).sum := by decide
  have hdescent : baseEnd_6935669 < baseStart_6935669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935710 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6935710 : Nat := 118140960795 + 6935710 * 2 ^ 59
def prefixEnd_6935710 : Nat := 4983230072969 + 3 ^ 40 * 6935710 * 2
def baseEnd_6935710 : Nat := 3561352910195164236428257

theorem tailTrace_6935710 : CollatzResearch.WordTrace tailWord_6935710 prefixEnd_6935710 3561352910195164236428257 := by
  unfold tailWord_6935710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31620765712889333726032573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168644083802076446538840389 31620765712889333726032573)
  ·
    refine ⟨11857787142333500147262215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31620765712889333726032573 11857787142333500147262215)
    ·
      refine ⟨17786680713500250220893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11857787142333500147262215 17786680713500250220893323)
      ·
        refine ⟨26680021070250375331339985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17786680713500250220893323 26680021070250375331339985)
        ·
          refine ⟨20010015802687781498504989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26680021070250375331339985 20010015802687781498504989)
          ·
            refine ⟨7503755926007918061939371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20010015802687781498504989 7503755926007918061939371)
            ·
              refine ⟨11255633889011877092909057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503755926007918061939371 11255633889011877092909057)
              ·
                refine ⟨8441725416758907819681793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11255633889011877092909057 8441725416758907819681793)
                ·
                  refine ⟨6331294062569180864761345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8441725416758907819681793 6331294062569180864761345)
                  ·
                    refine ⟨4748470546926885648571009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6331294062569180864761345 4748470546926885648571009)
                    ·
                      refine ⟨3561352910195164236428257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748470546926885648571009 3561352910195164236428257)
                      ·
                        rfl

theorem cell23_6935710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6935710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935710 prefixEnd_6935710 := by exact prefixLift 6935710
  have htrace : WordTrace (prefixWord ++ tailWord_6935710) baseStart_6935710 baseEnd_6935710 := by
    simpa [prefixWord, tailWord_6935710, baseEnd_6935710] using wordTrace_append hprefix tailTrace_6935710
  have hstable : (prefixWord ++ tailWord_6935710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935710).length < 2 ^ (prefixWord ++ tailWord_6935710).sum := by decide
  have hdescent : baseEnd_6935710 < baseStart_6935710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935752 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_6935752 : Nat := 118140960795 + 6935752 * 2 ^ 59
def prefixEnd_6935752 : Nat := 4983230072969 + 3 ^ 40 * 6935752 * 2
def baseEnd_6935752 : Nat := 3561374476382653072103063

theorem tailTrace_6935752 : CollatzResearch.WordTrace tailWord_6935752 prefixEnd_6935752 3561374476382653072103063 := by
  unfold tailWord_6935752
  simp only [CollatzResearch.WordTrace]
  refine ⟨126483828784481255490644755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168645105045975007320859673 126483828784481255490644755)
  ·
    refine ⟨189725743176721883235967133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126483828784481255490644755 189725743176721883235967133)
    ·
      refine ⟨71147153691270706213487675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189725743176721883235967133 71147153691270706213487675)
      ·
        refine ⟨106720730536906059320231513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71147153691270706213487675 106720730536906059320231513)
        ·
          refine ⟨80040547902679544490173635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106720730536906059320231513 80040547902679544490173635)
          ·
            refine ⟨120060821854019316735260453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80040547902679544490173635 120060821854019316735260453)
            ·
              refine ⟨22511404097628621887861335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120060821854019316735260453 22511404097628621887861335)
              ·
                refine ⟨33767106146442932831792003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22511404097628621887861335 33767106146442932831792003)
                ·
                  refine ⟨50650659219664399247688005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33767106146442932831792003 50650659219664399247688005)
                  ·
                    refine ⟨9496998603687074858941501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50650659219664399247688005 9496998603687074858941501)
                    ·
                      refine ⟨3561374476382653072103063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9496998603687074858941501 3561374476382653072103063)
                      ·
                        rfl

theorem cell23_6935752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_6935752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935752 prefixEnd_6935752 := by exact prefixLift 6935752
  have htrace : WordTrace (prefixWord ++ tailWord_6935752) baseStart_6935752 baseEnd_6935752 := by
    simpa [prefixWord, tailWord_6935752, baseEnd_6935752] using wordTrace_append hprefix tailTrace_6935752
  have hstable : (prefixWord ++ tailWord_6935752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935752).length < 2 ^ (prefixWord ++ tailWord_6935752).sum := by decide
  have hdescent : baseEnd_6935752 < baseStart_6935752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935759 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 1, 4]
def baseStart_6935759 : Nat := 118140960795 + 6935759 * 2 ^ 59
def prefixEnd_6935759 : Nat := 4983230072969 + 3 ^ 40 * 6935759 * 2
def baseEnd_6935759 : Nat := 1187126023582411514905177

theorem tailTrace_6935759 : CollatzResearch.WordTrace tailWord_6935759 prefixEnd_6935759 1187126023582411514905177 := by
  unfold tailWord_6935759
  simp only [CollatzResearch.WordTrace]
  refine ⟨252967912879937151176794331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168645275253291434117862887 252967912879937151176794331)
  ·
    refine ⟨379451869319905726765191497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252967912879937151176794331 379451869319905726765191497)
    ·
      refine ⟨284588901989929295073893623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379451869319905726765191497 284588901989929295073893623)
      ·
        refine ⟨426883352984893942610840435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284588901989929295073893623 426883352984893942610840435)
        ·
          refine ⟨640325029477340913916260653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426883352984893942610840435 640325029477340913916260653)
          ·
            refine ⟨240121886054002842718597745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640325029477340913916260653 240121886054002842718597745)
            ·
              refine ⟨180091414540502132038948309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240121886054002842718597745 180091414540502132038948309)
              ·
                refine ⟨4220892528293018719662851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180091414540502132038948309 4220892528293018719662851)
                ·
                  refine ⟨6331338792439528079494277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220892528293018719662851 6331338792439528079494277)
                  ·
                    refine ⟨1187126023582411514905177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331338792439528079494277 1187126023582411514905177)
                    ·
                      rfl

theorem cell23_6935759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_6935759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935759 prefixEnd_6935759 := by exact prefixLift 6935759
  have htrace : WordTrace (prefixWord ++ tailWord_6935759) baseStart_6935759 baseEnd_6935759 := by
    simpa [prefixWord, tailWord_6935759, baseEnd_6935759] using wordTrace_append hprefix tailTrace_6935759
  have hstable : (prefixWord ++ tailWord_6935759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935759).length < 2 ^ (prefixWord ++ tailWord_6935759).sum := by decide
  have hdescent : baseEnd_6935759 < baseStart_6935759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935775 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_6935775 : Nat := 118140960795 + 6935775 * 2 ^ 59
def prefixEnd_6935775 : Nat := 4983230072969 + 3 ^ 40 * 6935775 * 2
def baseEnd_6935775 : Nat := 3561386286437706482115457

theorem tailTrace_6935775 : CollatzResearch.WordTrace tailWord_6935775 prefixEnd_6935775 3561386286437706482115457 := by
  unfold tailWord_6935775
  simp only [CollatzResearch.WordTrace]
  refine ⟨252968496447879185909376779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168645664298586123939584519 252968496447879185909376779)
  ·
    refine ⟨379452744671818778864065169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252968496447879185909376779 379452744671818778864065169)
    ·
      refine ⟨284589558503864084148048877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379452744671818778864065169 284589558503864084148048877)
      ·
        refine ⟨106721084438949031555518329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284589558503864084148048877 106721084438949031555518329)
        ·
          refine ⟨80040813329211773666638747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106721084438949031555518329 80040813329211773666638747)
          ·
            refine ⟨120061219993817660499958121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80040813329211773666638747 120061219993817660499958121)
            ·
              refine ⟨90045914995363245374968591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120061219993817660499958121 90045914995363245374968591)
              ·
                refine ⟨135068872493044868062452887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90045914995363245374968591 135068872493044868062452887)
                ·
                  refine ⟨202603308739567302093679331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135068872493044868062452887 202603308739567302093679331)
                  ·
                    refine ⟨303904963109350953140518997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202603308739567302093679331 303904963109350953140518997)
                    ·
                      refine ⟨3561386286437706482115457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 303904963109350953140518997 3561386286437706482115457)
                      ·
                        rfl

theorem cell23_6935775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_6935775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935775 prefixEnd_6935775 := by exact prefixLift 6935775
  have htrace : WordTrace (prefixWord ++ tailWord_6935775) baseStart_6935775 baseEnd_6935775 := by
    simpa [prefixWord, tailWord_6935775, baseEnd_6935775] using wordTrace_append hprefix tailTrace_6935775
  have hstable : (prefixWord ++ tailWord_6935775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935775).length < 2 ^ (prefixWord ++ tailWord_6935775).sum := by decide
  have hdescent : baseEnd_6935775 < baseStart_6935775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935789 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 6]
def baseStart_6935789 : Nat := 118140960795 + 6935789 * 2 ^ 59
def prefixEnd_6935789 : Nat := 4983230072969 + 3 ^ 40 * 6935789 * 2
def baseEnd_6935789 : Nat := 395710386129652158593377

theorem tailTrace_6935789 : CollatzResearch.WordTrace tailWord_6935789 prefixEnd_6935789 395710386129652158593377 := by
  unfold tailWord_6935789
  simp only [CollatzResearch.WordTrace]
  refine ⟨252969007069828466300386421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168646004713218977533590947 252969007069828466300386421)
  ·
    refine ⟨23715844412796418715661227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252969007069828466300386421 23715844412796418715661227)
    ·
      refine ⟨35573766619194628073491841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23715844412796418715661227 35573766619194628073491841)
      ·
        refine ⟨26680324964395971055118881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35573766619194628073491841 26680324964395971055118881)
        ·
          refine ⟨20010243723296978291339161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26680324964395971055118881 20010243723296978291339161)
          ·
            refine ⟨15007682792472733718504371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20010243723296978291339161 15007682792472733718504371)
            ·
              refine ⟨22511524188709100577756557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007682792472733718504371 22511524188709100577756557)
              ·
                refine ⟨8441821570765912716658709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22511524188709100577756557 8441821570765912716658709)
                ·
                  refine ⟨395710386129652158593377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8441821570765912716658709 395710386129652158593377)
                  ·
                    rfl

theorem cell23_6935789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_6935789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935789 prefixEnd_6935789 := by exact prefixLift 6935789
  have htrace : WordTrace (prefixWord ++ tailWord_6935789) baseStart_6935789 baseEnd_6935789 := by
    simpa [prefixWord, tailWord_6935789, baseEnd_6935789] using wordTrace_append hprefix tailTrace_6935789
  have hstable : (prefixWord ++ tailWord_6935789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935789).length < 2 ^ (prefixWord ++ tailWord_6935789).sum := by decide
  have hdescent : baseEnd_6935789 < baseStart_6935789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935802 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_6935802 : Nat := 118140960795 + 6935802 * 2 ^ 59
def prefixEnd_6935802 : Nat := 4983230072969 + 3 ^ 40 * 6935802 * 2
def baseEnd_6935802 : Nat := 1187133383471792625492611

theorem tailTrace_6935802 : CollatzResearch.WordTrace tailWord_6935802 prefixEnd_6935802 1187133383471792625492611 := by
  unfold tailWord_6935802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63242370304695342380152415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168646320812520913013739773 63242370304695342380152415)
  ·
    refine ⟨94863555457043013570228623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63242370304695342380152415 94863555457043013570228623)
    ·
      refine ⟨142295333185564520355342935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94863555457043013570228623 142295333185564520355342935)
      ·
        refine ⟨213442999778346780533014403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142295333185564520355342935 213442999778346780533014403)
        ·
          refine ⟨320164499667520170799521605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213442999778346780533014403 320164499667520170799521605)
          ·
            refine ⟨60030843687660032024910301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320164499667520170799521605 60030843687660032024910301)
            ·
              refine ⟨22511566382872512009341363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60030843687660032024910301 22511566382872512009341363)
              ·
                refine ⟨33767349574308768014012045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22511566382872512009341363 33767349574308768014012045)
                ·
                  refine ⟨12662756090365788005254517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33767349574308768014012045 12662756090365788005254517)
                  ·
                    refine ⟨1187133383471792625492611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12662756090365788005254517 1187133383471792625492611)
                    ·
                      rfl

theorem cell23_6935802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_6935802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935802 prefixEnd_6935802 := by exact prefixLift 6935802
  have htrace : WordTrace (prefixWord ++ tailWord_6935802) baseStart_6935802 baseEnd_6935802 := by
    simpa [prefixWord, tailWord_6935802, baseEnd_6935802] using wordTrace_append hprefix tailTrace_6935802
  have hstable : (prefixWord ++ tailWord_6935802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935802).length < 2 ^ (prefixWord ++ tailWord_6935802).sum := by decide
  have hdescent : baseEnd_6935802 < baseStart_6935802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935856 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2]
def baseStart_6935856 : Nat := 118140960795 + 6935856 * 2 ^ 59
def prefixEnd_6935856 : Nat := 4983230072969 + 3 ^ 40 * 6935856 * 2
def baseEnd_6935856 : Nat := 3561427878370720665202585

theorem tailTrace_6935856 : CollatzResearch.WordTrace tailWord_6935856 prefixEnd_6935856 3561427878370720665202585 := by
  unfold tailWord_6935856
  simp only [CollatzResearch.WordTrace]
  refine ⟨126485725380292868371537711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168647633840390491162050281 126485725380292868371537711)
  ·
    refine ⟨189728588070439302557306567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126485725380292868371537711 189728588070439302557306567)
    ·
      refine ⟨284592882105658953835959851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189728588070439302557306567 284592882105658953835959851)
      ·
        refine ⟨426889323158488430753939777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284592882105658953835959851 426889323158488430753939777)
        ·
          refine ⟨320166992368866323065454833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426889323158488430753939777 320166992368866323065454833)
          ·
            refine ⟨240125244276649742299091125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320166992368866323065454833 240125244276649742299091125)
            ·
              refine ⟨22511741650935913340539793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240125244276649742299091125 22511741650935913340539793)
              ·
                refine ⟨16883806238201935005404845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22511741650935913340539793 16883806238201935005404845)
                ·
                  refine ⟨6331427339325725627026817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16883806238201935005404845 6331427339325725627026817)
                  ·
                    refine ⟨4748570504494294220270113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6331427339325725627026817 4748570504494294220270113)
                    ·
                      refine ⟨3561427878370720665202585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748570504494294220270113 3561427878370720665202585)
                      ·
                        rfl

theorem cell23_6935856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2].length) (baseStart_6935856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935856 prefixEnd_6935856 := by exact prefixLift 6935856
  have htrace : WordTrace (prefixWord ++ tailWord_6935856) baseStart_6935856 baseEnd_6935856 := by
    simpa [prefixWord, tailWord_6935856, baseEnd_6935856] using wordTrace_append hprefix tailTrace_6935856
  have hstable : (prefixWord ++ tailWord_6935856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935856).length < 2 ^ (prefixWord ++ tailWord_6935856).sum := by decide
  have hdescent : baseEnd_6935856 < baseStart_6935856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935859 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3]
def baseStart_6935859 : Nat := 118140960795 + 6935859 * 2 ^ 59
def prefixEnd_6935859 : Nat := 4983230072969 + 3 ^ 40 * 6935859 * 2
def baseEnd_6935859 : Nat := 3561429418812684153465071

theorem tailTrace_6935859 : CollatzResearch.WordTrace tailWord_6935859 prefixEnd_6935859 3561429418812684153465071 := by
  unfold tailWord_6935859
  simp only [CollatzResearch.WordTrace]
  refine ⟨252971560179574868255434631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168647706786383245503623087 252971560179574868255434631)
  ·
    refine ⟨379457340269362302383151947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252971560179574868255434631 379457340269362302383151947)
    ·
      refine ⟨569186010404043453574727921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379457340269362302383151947 569186010404043453574727921)
      ·
        refine ⟨426889507803032590181045941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569186010404043453574727921 426889507803032590181045941)
        ·
          refine ⟨40020891356534305329473057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426889507803032590181045941 40020891356534305329473057)
          ·
            refine ⟨30015668517400728997104793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40020891356534305329473057 30015668517400728997104793)
            ·
              refine ⟨22511751388050546747828595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30015668517400728997104793 22511751388050546747828595)
              ·
                refine ⟨33767627082075820121742893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22511751388050546747828595 33767627082075820121742893)
                ·
                  refine ⟨12662860155778432545653585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33767627082075820121742893 12662860155778432545653585)
                  ·
                    refine ⟨9497145116833824409240189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12662860155778432545653585 9497145116833824409240189)
                    ·
                      refine ⟨3561429418812684153465071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497145116833824409240189 3561429418812684153465071)
                      ·
                        rfl

theorem cell23_6935859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_6935859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935859 prefixEnd_6935859 := by exact prefixLift 6935859
  have htrace : WordTrace (prefixWord ++ tailWord_6935859) baseStart_6935859 baseEnd_6935859 := by
    simpa [prefixWord, tailWord_6935859, baseEnd_6935859] using wordTrace_append hprefix tailTrace_6935859
  have hstable : (prefixWord ++ tailWord_6935859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935859).length < 2 ^ (prefixWord ++ tailWord_6935859).sum := by decide
  have hdescent : baseEnd_6935859 < baseStart_6935859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6935873 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6935873 : Nat := 118140960795 + 6935873 * 2 ^ 59
def prefixEnd_6935873 : Nat := 4983230072969 + 3 ^ 40 * 6935873 * 2
def baseEnd_6935873 : Nat := 3561436607541847098690007

theorem tailTrace_6935873 : CollatzResearch.WordTrace tailWord_6935873 prefixEnd_6935873 3561436607541847098690007 := by
  unfold tailWord_6935873
  simp only [CollatzResearch.WordTrace]
  refine ⟨252972070801524148646444273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168648047201016099097629515 252972070801524148646444273)
  ·
    refine ⟨189729053101143111484833205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252972070801524148646444273 189729053101143111484833205)
    ·
      refine ⟨17787098728232166701703113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189729053101143111484833205 17787098728232166701703113)
      ·
        refine ⟨13340324046174125026277335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17787098728232166701703113 13340324046174125026277335)
        ·
          refine ⟨20010486069261187539416003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13340324046174125026277335 20010486069261187539416003)
          ·
            refine ⟨30015729103891781309124005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20010486069261187539416003 30015729103891781309124005)
            ·
              refine ⟨5627949206979708995460751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30015729103891781309124005 5627949206979708995460751)
              ·
                refine ⟨8441923810469563493191127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627949206979708995460751 8441923810469563493191127)
                ·
                  refine ⟨12662885715704345239786691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8441923810469563493191127 12662885715704345239786691)
                  ·
                    refine ⟨18994328573556517859680037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12662885715704345239786691 18994328573556517859680037)
                    ·
                      refine ⟨3561436607541847098690007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18994328573556517859680037 3561436607541847098690007)
                      ·
                        rfl

theorem cell23_6935873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6935873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6935873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6935873 prefixEnd_6935873 := by exact prefixLift 6935873
  have htrace : WordTrace (prefixWord ++ tailWord_6935873) baseStart_6935873 baseEnd_6935873 := by
    simpa [prefixWord, tailWord_6935873, baseEnd_6935873] using wordTrace_append hprefix tailTrace_6935873
  have hstable : (prefixWord ++ tailWord_6935873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6935873).length < 2 ^ (prefixWord ++ tailWord_6935873).sum := by decide
  have hdescent : baseEnd_6935873 < baseStart_6935873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6935873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936046 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_6936046 : Nat := 118140960795 + 6936046 * 2 ^ 59
def prefixEnd_6936046 : Nat := 4983230072969 + 3 ^ 40 * 6936046 * 2
def baseEnd_6936046 : Nat := 1187175146565024973942237

theorem tailTrace_6936046 : CollatzResearch.WordTrace tailWord_6936046 prefixEnd_6936046 1187175146565024973942237 := by
  unfold tailWord_6936046
  simp only [CollatzResearch.WordTrace]
  refine ⟨31622297578737174899061499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168652253753264932794994661 31622297578737174899061499)
  ·
    refine ⟨47433446368105762348592249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31622297578737174899061499 47433446368105762348592249)
    ·
      refine ⟨35575084776079321761444187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47433446368105762348592249 35575084776079321761444187)
      ·
        refine ⟨53362627164118982642166281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35575084776079321761444187 53362627164118982642166281)
        ·
          refine ⟨40021970373089236981624711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53362627164118982642166281 40021970373089236981624711)
          ·
            refine ⟨60032955559633855472437067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40021970373089236981624711 60032955559633855472437067)
            ·
              refine ⟨90049433339450783208655601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60032955559633855472437067 90049433339450783208655601)
              ·
                refine ⟨67537075004588087406491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90049433339450783208655601 67537075004588087406491701)
                ·
                  refine ⟨6331600781680133194358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67537075004588087406491701 6331600781680133194358597)
                  ·
                    refine ⟨1187175146565024973942237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331600781680133194358597 1187175146565024973942237)
                    ·
                      rfl

theorem cell23_6936046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_6936046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936046 prefixEnd_6936046 := by exact prefixLift 6936046
  have htrace : WordTrace (prefixWord ++ tailWord_6936046) baseStart_6936046 baseEnd_6936046 := by
    simpa [prefixWord, tailWord_6936046, baseEnd_6936046] using wordTrace_append hprefix tailTrace_6936046
  have hstable : (prefixWord ++ tailWord_6936046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936046).length < 2 ^ (prefixWord ++ tailWord_6936046).sum := by decide
  have hdescent : baseEnd_6936046 < baseStart_6936046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936049 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_6936049 : Nat := 118140960795 + 6936049 * 2 ^ 59
def prefixEnd_6936049 : Nat := 4983230072969 + 3 ^ 40 * 6936049 * 2
def baseEnd_6936049 : Nat := 3561526980137038410089197

theorem tailTrace_6936049 : CollatzResearch.WordTrace tailWord_6936049 prefixEnd_6936049 3561526980137038410089197 := by
  unfold tailWord_6936049
  simp only [CollatzResearch.WordTrace]
  refine ⟨252978490048886530704851201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168652326699257687136567467 252978490048886530704851201)
  ·
    refine ⟨189733867536664898028638401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252978490048886530704851201 189733867536664898028638401)
    ·
      refine ⟨142300400652498673521478801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189733867536664898028638401 142300400652498673521478801)
      ·
        refine ⟨106725300489374005141109101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142300400652498673521478801 106725300489374005141109101)
        ·
          refine ⟨40021987683515251927915913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106725300489374005141109101 40021987683515251927915913)
          ·
            refine ⟨30016490762636438945936935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40021987683515251927915913 30016490762636438945936935)
            ·
              refine ⟨45024736143954658418905403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30016490762636438945936935 45024736143954658418905403)
              ·
                refine ⟨67537104215931987628358105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45024736143954658418905403 67537104215931987628358105)
                ·
                  refine ⟨50652828161948990721268579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67537104215931987628358105 50652828161948990721268579)
                  ·
                    refine ⟨75979242242923486081902869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50652828161948990721268579 75979242242923486081902869)
                    ·
                      refine ⟨3561526980137038410089197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75979242242923486081902869 3561526980137038410089197)
                      ·
                        rfl

theorem cell23_6936049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_6936049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936049 prefixEnd_6936049 := by exact prefixLift 6936049
  have htrace : WordTrace (prefixWord ++ tailWord_6936049) baseStart_6936049 baseEnd_6936049 := by
    simpa [prefixWord, tailWord_6936049, baseEnd_6936049] using wordTrace_append hprefix tailTrace_6936049
  have hstable : (prefixWord ++ tailWord_6936049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936049).length < 2 ^ (prefixWord ++ tailWord_6936049).sum := by decide
  have hdescent : baseEnd_6936049 < baseStart_6936049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936120 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_6936120 : Nat := 118140960795 + 6936120 * 2 ^ 59
def prefixEnd_6936120 : Nat := 4983230072969 + 3 ^ 40 * 6936120 * 2
def baseEnd_6936120 : Nat := 3561563437263507632301371

theorem tailTrace_6936120 : CollatzResearch.WordTrace tailWord_6936120 prefixEnd_6936120 3561563437263507632301371 := by
  unfold tailWord_6936120
  simp only [CollatzResearch.WordTrace]
  refine ⟨126490539815814654915342907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168654053087752873220457209 126490539815814654915342907)
  ·
    refine ⟨189735809723721982373014361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126490539815814654915342907 189735809723721982373014361)
    ·
      refine ⟨142301857292791486779760771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189735809723721982373014361 142301857292791486779760771)
      ·
        refine ⟨213452785939187230169641157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142301857292791486779760771 213452785939187230169641157)
        ·
          refine ⟨40022397363597605656807717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213452785939187230169641157 40022397363597605656807717)
          ·
            refine ⟨7504199505674551060651447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40022397363597605656807717 7504199505674551060651447)
            ·
              refine ⟨11256299258511826590977171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504199505674551060651447 11256299258511826590977171)
              ·
                refine ⟨16884448887767739886465757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11256299258511826590977171 16884448887767739886465757)
                ·
                  refine ⟨6331668332912902457424659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16884448887767739886465757 6331668332912902457424659)
                  ·
                    refine ⟨9497502499369353686136989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331668332912902457424659 9497502499369353686136989)
                    ·
                      refine ⟨3561563437263507632301371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497502499369353686136989 3561563437263507632301371)
                      ·
                        rfl

theorem cell23_6936120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_6936120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936120 prefixEnd_6936120 := by exact prefixLift 6936120
  have htrace : WordTrace (prefixWord ++ tailWord_6936120) baseStart_6936120 baseEnd_6936120 := by
    simpa [prefixWord, tailWord_6936120, baseEnd_6936120] using wordTrace_append hprefix tailTrace_6936120
  have hstable : (prefixWord ++ tailWord_6936120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936120).length < 2 ^ (prefixWord ++ tailWord_6936120).sum := by decide
  have hdescent : baseEnd_6936120 < baseStart_6936120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936143 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 5, 2, 2]
def baseStart_6936143 : Nat := 118140960795 + 6936143 * 2 ^ 59
def prefixEnd_6936143 : Nat := 4983230072969 + 3 ^ 40 * 6936143 * 2
def baseEnd_6936143 : Nat := 3561575247318561042313765

theorem tailTrace_6936143 : CollatzResearch.WordTrace tailWord_6936143 prefixEnd_6936143 3561575247318561042313765 := by
  unfold tailWord_6936143
  simp only [CollatzResearch.WordTrace]
  refine ⟨252981918510545984758773083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168654612340363989839182055 252981918510545984758773083)
  ·
    refine ⟨379472877765818977138159625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252981918510545984758773083 379472877765818977138159625)
    ·
      refine ⟨284604658324364232853619719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379472877765818977138159625 284604658324364232853619719)
      ·
        refine ⟨426906987486546349280429579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284604658324364232853619719 426906987486546349280429579)
        ·
          refine ⟨640360481229819523920644369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426906987486546349280429579 640360481229819523920644369)
          ·
            refine ⟨480270360922364642940483277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640360481229819523920644369 480270360922364642940483277)
            ·
              refine ⟨180101385345886741102681229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480270360922364642940483277 180101385345886741102681229)
              ·
                refine ⟨67538019504707527913505461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180101385345886741102681229 67538019504707527913505461)
                ·
                  refine ⟨6331689328566330741891137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67538019504707527913505461 6331689328566330741891137)
                  ·
                    refine ⟨4748766996424748056418353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6331689328566330741891137 4748766996424748056418353)
                    ·
                      refine ⟨3561575247318561042313765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748766996424748056418353 3561575247318561042313765)
                      ·
                        rfl

theorem cell23_6936143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2, 2].length) (baseStart_6936143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936143 prefixEnd_6936143 := by exact prefixLift 6936143
  have htrace : WordTrace (prefixWord ++ tailWord_6936143) baseStart_6936143 baseEnd_6936143 := by
    simpa [prefixWord, tailWord_6936143, baseEnd_6936143] using wordTrace_append hprefix tailTrace_6936143
  have hstable : (prefixWord ++ tailWord_6936143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936143).length < 2 ^ (prefixWord ++ tailWord_6936143).sum := by decide
  have hdescent : baseEnd_6936143 < baseStart_6936143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936163 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6936163 : Nat := 118140960795 + 6936163 * 2 ^ 59
def prefixEnd_6936163 : Nat := 4983230072969 + 3 ^ 40 * 6936163 * 2
def baseEnd_6936163 : Nat := 3561585516931650964063673

theorem tailTrace_6936163 : CollatzResearch.WordTrace tailWord_6936163 prefixEnd_6936163 3561585516931650964063673 := by
  unfold tailWord_6936163
  simp only [CollatzResearch.WordTrace]
  refine ⟨252982647970473528174501143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168655098646982352116334095 252982647970473528174501143)
  ·
    refine ⟨379473971955710292261751715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252982647970473528174501143 379473971955710292261751715)
    ·
      refine ⟨569210957933565438392627573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379473971955710292261751715 569210957933565438392627573)
      ·
        refine ⟨53363527306271759849308835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569210957933565438392627573 53363527306271759849308835)
        ·
          refine ⟨80045290959407639773963253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53363527306271759849308835 80045290959407639773963253)
          ·
            refine ⟨7504246027444466228809055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80045290959407639773963253 7504246027444466228809055)
            ·
              refine ⟨11256369041166699343213583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504246027444466228809055 11256369041166699343213583)
              ·
                refine ⟨16884553561750049014820375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11256369041166699343213583 16884553561750049014820375)
                ·
                  refine ⟨25326830342625073522230563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16884553561750049014820375 25326830342625073522230563)
                  ·
                    refine ⟨37990245513937610283345845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25326830342625073522230563 37990245513937610283345845)
                    ·
                      refine ⟨3561585516931650964063673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37990245513937610283345845 3561585516931650964063673)
                      ·
                        rfl

theorem cell23_6936163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6936163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936163 prefixEnd_6936163 := by exact prefixLift 6936163
  have htrace : WordTrace (prefixWord ++ tailWord_6936163) baseStart_6936163 baseEnd_6936163 := by
    simpa [prefixWord, tailWord_6936163, baseEnd_6936163] using wordTrace_append hprefix tailTrace_6936163
  have hstable : (prefixWord ++ tailWord_6936163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936163).length < 2 ^ (prefixWord ++ tailWord_6936163).sum := by decide
  have hdescent : baseEnd_6936163 < baseStart_6936163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936170 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_6936170 : Nat := 118140960795 + 6936170 * 2 ^ 59
def prefixEnd_6936170 : Nat := 4983230072969 + 3 ^ 40 * 6936170 * 2
def baseEnd_6936170 : Nat := 1187196370432077478892047

theorem tailTrace_6936170 : CollatzResearch.WordTrace tailWord_6936170 prefixEnd_6936170 1187196370432077478892047 := by
  unfold tailWord_6936170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63245725820362042092501491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168655268854298778913337309 63245725820362042092501491)
  ·
    refine ⟨94868588730543063138752237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63245725820362042092501491 94868588730543063138752237)
    ·
      refine ⟨35575720773953648677032089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94868588730543063138752237 35575720773953648677032089)
      ·
        refine ⟨26681790580465236507774067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35575720773953648677032089 26681790580465236507774067)
        ·
          refine ⟨40022685870697854761661101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26681790580465236507774067 40022685870697854761661101)
          ·
            refine ⟨15008507201511695535622913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40022685870697854761661101 15008507201511695535622913)
            ·
              refine ⟨11256380401133771651717185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15008507201511695535622913 11256380401133771651717185)
              ·
                refine ⟨8442285300850328738787889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256380401133771651717185 8442285300850328738787889)
                ·
                  refine ⟨6331713975637746554090917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8442285300850328738787889 6331713975637746554090917)
                  ·
                    refine ⟨1187196370432077478892047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331713975637746554090917 1187196370432077478892047)
                    ·
                      rfl

theorem cell23_6936170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_6936170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936170 prefixEnd_6936170 := by exact prefixLift 6936170
  have htrace : WordTrace (prefixWord ++ tailWord_6936170) baseStart_6936170 baseEnd_6936170 := by
    simpa [prefixWord, tailWord_6936170, baseEnd_6936170] using wordTrace_append hprefix tailTrace_6936170
  have hstable : (prefixWord ++ tailWord_6936170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936170).length < 2 ^ (prefixWord ++ tailWord_6936170).sum := by decide
  have hdescent : baseEnd_6936170 < baseStart_6936170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936193 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6936193 : Nat := 118140960795 + 6936193 * 2 ^ 59
def prefixEnd_6936193 : Nat := 4983230072969 + 3 ^ 40 * 6936193 * 2
def baseEnd_6936193 : Nat := 3561600921351285846688535

theorem tailTrace_6936193 : CollatzResearch.WordTrace tailWord_6936193 prefixEnd_6936193 3561600921351285846688535 := by
  unfold tailWord_6936193
  simp only [CollatzResearch.WordTrace]
  refine ⟨252983742160364843298093233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168655828106909895532062155 252983742160364843298093233)
  ·
    refine ⟨189737806620273632473569925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252983742160364843298093233 189737806620273632473569925)
    ·
      refine ⟨35575838741301306088794361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189737806620273632473569925 35575838741301306088794361)
      ·
        refine ⟨26681879055975979566595771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35575838741301306088794361 26681879055975979566595771)
        ·
          refine ⟨40022818583963969349893657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26681879055975979566595771 40022818583963969349893657)
          ·
            refine ⟨30017113937972977012420243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40022818583963969349893657 30017113937972977012420243)
            ·
              refine ⟨45025670906959465518630365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30017113937972977012420243 45025670906959465518630365)
              ·
                refine ⟨16884626590109799569486387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45025670906959465518630365 16884626590109799569486387)
                ·
                  refine ⟨25326939885164699354229581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16884626590109799569486387 25326939885164699354229581)
                  ·
                    refine ⟨9497602456936762257836093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25326939885164699354229581 9497602456936762257836093)
                    ·
                      refine ⟨3561600921351285846688535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497602456936762257836093 3561600921351285846688535)
                      ·
                        rfl

theorem cell23_6936193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6936193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936193 prefixEnd_6936193 := by exact prefixLift 6936193
  have htrace : WordTrace (prefixWord ++ tailWord_6936193) baseStart_6936193 baseEnd_6936193 := by
    simpa [prefixWord, tailWord_6936193, baseEnd_6936193] using wordTrace_append hprefix tailTrace_6936193
  have hstable : (prefixWord ++ tailWord_6936193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936193).length < 2 ^ (prefixWord ++ tailWord_6936193).sum := by decide
  have hdescent : baseEnd_6936193 < baseStart_6936193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936200 : List Nat := [2, 1, 3, 5, 1, 1, 3, 7]
def baseStart_6936200 : Nat := 118140960795 + 6936200 * 2 ^ 59
def prefixEnd_6936200 : Nat := 4983230072969 + 3 ^ 40 * 6936200 * 2
def baseEnd_6936200 : Nat := 131911278359846937751889

theorem tailTrace_6936200 : CollatzResearch.WordTrace tailWord_6936200 prefixEnd_6936200 131911278359846937751889 := by
  unfold tailWord_6936200
  simp only [CollatzResearch.WordTrace]
  refine ⟨126491998735669741746799027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168655998314226322329065369 126491998735669741746799027)
  ·
    refine ⟨189737998103504612620198541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126491998735669741746799027 189737998103504612620198541)
    ·
      refine ⟨71151749288814229732574453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189737998103504612620198541 71151749288814229732574453)
      ·
        refine ⟨6670476495826334037428855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71151749288814229732574453 6670476495826334037428855)
        ·
          refine ⟨10005714743739501056143283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670476495826334037428855 10005714743739501056143283)
          ·
            refine ⟨15008572115609251584214925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005714743739501056143283 15008572115609251584214925)
            ·
              refine ⟨5628214543353469344080597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15008572115609251584214925 5628214543353469344080597)
              ·
                refine ⟨131911278359846937751889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5628214543353469344080597 131911278359846937751889)
                ·
                  rfl

theorem cell23_6936200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 7].length) (baseStart_6936200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936200 prefixEnd_6936200 := by exact prefixLift 6936200
  have htrace : WordTrace (prefixWord ++ tailWord_6936200) baseStart_6936200 baseEnd_6936200 := by
    simpa [prefixWord, tailWord_6936200, baseEnd_6936200] using wordTrace_append hprefix tailTrace_6936200
  have hstable : (prefixWord ++ tailWord_6936200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936200).length < 2 ^ (prefixWord ++ tailWord_6936200).sum := by decide
  have hdescent : baseEnd_6936200 < baseStart_6936200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936203 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 3, 3, 2]
def baseStart_6936203 : Nat := 118140960795 + 6936203 * 2 ^ 59
def prefixEnd_6936203 : Nat := 4983230072969 + 3 ^ 40 * 6936203 * 2
def baseEnd_6936203 : Nat := 3561606056157830807563489

theorem tailTrace_6936203 : CollatzResearch.WordTrace tailWord_6936203 prefixEnd_6936203 3561606056157830807563489 := by
  unfold tailWord_6936203
  simp only [CollatzResearch.WordTrace]
  refine ⟨252984106890328615005957263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168656071260219076670638175 252984106890328615005957263)
  ·
    refine ⟨379476160335492922508935895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252984106890328615005957263 379476160335492922508935895)
    ·
      refine ⟨569214240503239383763403843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379476160335492922508935895 569214240503239383763403843)
      ·
        refine ⟨853821360754859075645105765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569214240503239383763403843 853821360754859075645105765)
        ·
          refine ⟨160091505141536076683457331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 853821360754859075645105765 160091505141536076683457331)
          ·
            refine ⟨240137257712304115025185997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160091505141536076683457331 240137257712304115025185997)
            ·
              refine ⟨90051471642114043134444749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240137257712304115025185997 90051471642114043134444749)
              ·
                refine ⟨33769301865792766175416781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90051471642114043134444749 33769301865792766175416781)
                ·
                  refine ⟨12663488199672287315781293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33769301865792766175416781 12663488199672287315781293)
                  ·
                    refine ⟨4748808074877107743417985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12663488199672287315781293 4748808074877107743417985)
                    ·
                      refine ⟨3561606056157830807563489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748808074877107743417985 3561606056157830807563489)
                      ·
                        rfl

theorem cell23_6936203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3, 2].length) (baseStart_6936203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936203 prefixEnd_6936203 := by exact prefixLift 6936203
  have htrace : WordTrace (prefixWord ++ tailWord_6936203) baseStart_6936203 baseEnd_6936203 := by
    simpa [prefixWord, tailWord_6936203, baseEnd_6936203] using wordTrace_append hprefix tailTrace_6936203
  have hstable : (prefixWord ++ tailWord_6936203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936203).length < 2 ^ (prefixWord ++ tailWord_6936203).sum := by decide
  have hdescent : baseEnd_6936203 < baseStart_6936203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936250 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_6936250 : Nat := 118140960795 + 6936250 * 2 ^ 59
def prefixEnd_6936250 : Nat := 4983230072969 + 3 ^ 40 * 6936250 * 2
def baseEnd_6936250 : Nat := 3561630189748592123675773

theorem tailTrace_6936250 : CollatzResearch.WordTrace tailWord_6936250 prefixEnd_6936250 3561630189748592123675773 := by
  unfold tailWord_6936250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63246455280289585508229551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168657214080772228021945469 63246455280289585508229551)
  ·
    refine ⟨94869682920434378262344327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63246455280289585508229551 94869682920434378262344327)
    ·
      refine ⟨142304524380651567393516491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94869682920434378262344327 142304524380651567393516491)
      ·
        refine ⟨213456786570977351090274737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142304524380651567393516491 213456786570977351090274737)
        ·
          refine ⟨160092589928233013317706053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213456786570977351090274737 160092589928233013317706053)
          ·
            refine ⟨30017360611543689997069885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160092589928233013317706053 30017360611543689997069885)
            ·
              refine ⟨11256510229328883748901207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30017360611543689997069885 11256510229328883748901207)
              ·
                refine ⟨16884765343993325623351811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11256510229328883748901207 16884765343993325623351811)
                ·
                  refine ⟨25327148015989988435027717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16884765343993325623351811 25327148015989988435027717)
                  ·
                    refine ⟨4748840252998122831567697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25327148015989988435027717 4748840252998122831567697)
                    ·
                      refine ⟨3561630189748592123675773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748840252998122831567697 3561630189748592123675773)
                      ·
                        rfl

theorem cell23_6936250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_6936250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936250 prefixEnd_6936250 := by exact prefixLift 6936250
  have htrace : WordTrace (prefixWord ++ tailWord_6936250) baseStart_6936250 baseEnd_6936250 := by
    simpa [prefixWord, tailWord_6936250, baseEnd_6936250] using wordTrace_append hprefix tailTrace_6936250
  have hstable : (prefixWord ++ tailWord_6936250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936250).length < 2 ^ (prefixWord ++ tailWord_6936250).sum := by decide
  have hdescent : baseEnd_6936250 < baseStart_6936250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936256 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 7]
def baseStart_6936256 : Nat := 118140960795 + 6936256 * 2 ^ 59
def prefixEnd_6936256 : Nat := 4983230072969 + 3 ^ 40 * 6936256 * 2
def baseEnd_6936256 : Nat := 395737030070279900022305

theorem tailTrace_6936256 : CollatzResearch.WordTrace tailWord_6936256 prefixEnd_6936256 395737030070279900022305 := by
  unfold tailWord_6936256
  simp only [CollatzResearch.WordTrace]
  refine ⟨126493019979568302528818311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168657359972757736705091081 126493019979568302528818311)
  ·
    refine ⟨189739529969352453793227467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126493019979568302528818311 189739529969352453793227467)
    ·
      refine ⟨284609294954028680689841201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189739529969352453793227467 284609294954028680689841201)
      ·
        refine ⟨213456971215521510517380901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284609294954028680689841201 213456971215521510517380901)
        ·
          refine ⟨40023182102910283222008919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213456971215521510517380901 40023182102910283222008919)
          ·
            refine ⟨60034773154365424833013379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40023182102910283222008919 60034773154365424833013379)
            ·
              refine ⟨90052159731548137249520069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60034773154365424833013379 90052159731548137249520069)
              ·
                refine ⟨16884779949665275734285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90052159731548137249520069 16884779949665275734285013)
                ·
                  refine ⟨395737030070279900022305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16884779949665275734285013 395737030070279900022305)
                  ·
                    rfl

theorem cell23_6936256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_6936256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936256 prefixEnd_6936256 := by exact prefixLift 6936256
  have htrace : WordTrace (prefixWord ++ tailWord_6936256) baseStart_6936256 baseEnd_6936256 := by
    simpa [prefixWord, tailWord_6936256, baseEnd_6936256] using wordTrace_append hprefix tailTrace_6936256
  have hstable : (prefixWord ++ tailWord_6936256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936256).length < 2 ^ (prefixWord ++ tailWord_6936256).sum := by decide
  have hdescent : baseEnd_6936256 < baseStart_6936256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936301 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6936301 : Nat := 118140960795 + 6936301 * 2 ^ 59
def prefixEnd_6936301 : Nat := 4983230072969 + 3 ^ 40 * 6936301 * 2
def baseEnd_6936301 : Nat := 3561656377261971424138039

theorem tailTrace_6936301 : CollatzResearch.WordTrace tailWord_6936301 prefixEnd_6936301 3561656377261971424138039 := by
  unfold tailWord_6936301
  simp only [CollatzResearch.WordTrace]
  refine ⟨252987681243973577743024757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168658454162649051828683171 252987681243973577743024757)
  ·
    refine ⟨23717595116622522913408571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252987681243973577743024757 23717595116622522913408571)
    ·
      refine ⟨35576392674933784370112857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23717595116622522913408571 35576392674933784370112857)
      ·
        refine ⟨26682294506200338277584643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35576392674933784370112857 26682294506200338277584643)
        ·
          refine ⟨40023441759300507416376965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26682294506200338277584643 40023441759300507416376965)
          ·
            refine ⟨7504395329868845140570681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40023441759300507416376965 7504395329868845140570681)
            ·
              refine ⟨5628296497401633855428011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504395329868845140570681 5628296497401633855428011)
              ·
                refine ⟨8442444746102450783142017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628296497401633855428011 8442444746102450783142017)
                ·
                  refine ⟨6331833559576838087356513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8442444746102450783142017 6331833559576838087356513)
                  ·
                    refine ⟨4748875169682628565517385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6331833559576838087356513 4748875169682628565517385)
                    ·
                      refine ⟨3561656377261971424138039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748875169682628565517385 3561656377261971424138039)
                      ·
                        rfl

theorem cell23_6936301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6936301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936301 prefixEnd_6936301 := by exact prefixLift 6936301
  have htrace : WordTrace (prefixWord ++ tailWord_6936301) baseStart_6936301 baseEnd_6936301 := by
    simpa [prefixWord, tailWord_6936301, baseEnd_6936301] using wordTrace_append hprefix tailTrace_6936301
  have hstable : (prefixWord ++ tailWord_6936301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936301).length < 2 ^ (prefixWord ++ tailWord_6936301).sum := by decide
  have hdescent : baseEnd_6936301 < baseStart_6936301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936323 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4]
def baseStart_6936323 : Nat := 118140960795 + 6936323 * 2 ^ 59
def prefixEnd_6936323 : Nat := 4983230072969 + 3 ^ 40 * 6936323 * 2
def baseEnd_6936323 : Nat := 3561667673836370338062937

theorem tailTrace_6936323 : CollatzResearch.WordTrace tailWord_6936323 prefixEnd_6936323 3561667673836370338062937 := by
  unfold tailWord_6936323
  simp only [CollatzResearch.WordTrace]
  refine ⟨252988483649893875500325623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168658989099929250333550415 252988483649893875500325623)
  ·
    refine ⟨379482725474840813250488435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252988483649893875500325623 379482725474840813250488435)
    ·
      refine ⟨569224088212261219875732653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379482725474840813250488435 569224088212261219875732653)
      ·
        refine ⟨213459033079597957453399745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569224088212261219875732653 213459033079597957453399745)
        ·
          refine ⟨160094274809698468090049809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213459033079597957453399745 160094274809698468090049809)
          ·
            refine ⟨120070706107273851067537357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160094274809698468090049809 120070706107273851067537357)
            ·
              refine ⟨45026514790227694150326509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120070706107273851067537357 45026514790227694150326509)
              ·
                refine ⟨16884943046335385306372441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45026514790227694150326509 16884943046335385306372441)
                ·
                  refine ⟨12663707284751538979779331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16884943046335385306372441 12663707284751538979779331)
                  ·
                    refine ⟨18995560927127308469668997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12663707284751538979779331 18995560927127308469668997)
                    ·
                      refine ⟨3561667673836370338062937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18995560927127308469668997 3561667673836370338062937)
                      ·
                        rfl

theorem cell23_6936323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_6936323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936323 prefixEnd_6936323 := by exact prefixLift 6936323
  have htrace : WordTrace (prefixWord ++ tailWord_6936323) baseStart_6936323 baseEnd_6936323 := by
    simpa [prefixWord, tailWord_6936323, baseEnd_6936323] using wordTrace_append hprefix tailTrace_6936323
  have hstable : (prefixWord ++ tailWord_6936323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936323).length < 2 ^ (prefixWord ++ tailWord_6936323).sum := by decide
  have hdescent : baseEnd_6936323 < baseStart_6936323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936374 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6936374 : Nat := 118140960795 + 6936374 * 2 ^ 59
def prefixEnd_6936374 : Nat := 4983230072969 + 3 ^ 40 * 6936374 * 2
def baseEnd_6936374 : Nat := 3561693861349749638525203

theorem tailTrace_6936374 : CollatzResearch.WordTrace tailWord_6936374 prefixEnd_6936374 3561693861349749638525203 := by
  unfold tailWord_6936374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811896485794319450652011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168660229181806074140288117 15811896485794319450652011)
  ·
    refine ⟨23717844728691479175978017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15811896485794319450652011 23717844728691479175978017)
    ·
      refine ⟨17788383546518609381983513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23717844728691479175978017 17788383546518609381983513)
      ·
        refine ⟨13341287659888957036487635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788383546518609381983513 13341287659888957036487635)
        ·
          refine ⟨20011931489833435554731453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341287659888957036487635 20011931489833435554731453)
          ·
            refine ⟨7504474308687538333024295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20011931489833435554731453 7504474308687538333024295)
            ·
              refine ⟨11256711463031307499536443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504474308687538333024295 11256711463031307499536443)
              ·
                refine ⟨16885067194546961249304665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11256711463031307499536443 16885067194546961249304665)
                ·
                  refine ⟨12663800395910220936978499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16885067194546961249304665 12663800395910220936978499)
                  ·
                    refine ⟨18995700593865331405467749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12663800395910220936978499 18995700593865331405467749)
                    ·
                      refine ⟨3561693861349749638525203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18995700593865331405467749 3561693861349749638525203)
                      ·
                        rfl

theorem cell23_6936374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6936374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936374 prefixEnd_6936374 := by exact prefixLift 6936374
  have htrace : WordTrace (prefixWord ++ tailWord_6936374) baseStart_6936374 baseEnd_6936374 := by
    simpa [prefixWord, tailWord_6936374, baseEnd_6936374] using wordTrace_append hprefix tailTrace_6936374
  have hstable : (prefixWord ++ tailWord_6936374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936374).length < 2 ^ (prefixWord ++ tailWord_6936374).sum := by decide
  have hdescent : baseEnd_6936374 < baseStart_6936374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936377 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6936377 : Nat := 118140960795 + 6936377 * 2 ^ 59
def prefixEnd_6936377 : Nat := 4983230072969 + 3 ^ 40 * 6936377 * 2
def baseEnd_6936377 : Nat := 3561695401791713126787689

theorem tailTrace_6936377 : CollatzResearch.WordTrace tailWord_6936377 prefixEnd_6936377 3561695401791713126787689 := by
  unfold tailWord_6936377
  simp only [CollatzResearch.WordTrace]
  refine ⟨252990453191698242722791385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168660302127798828481860923 252990453191698242722791385)
  ·
    refine ⟨189742839893773682042093539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252990453191698242722791385 189742839893773682042093539)
    ·
      refine ⟨284614259840660523063140309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189742839893773682042093539 284614259840660523063140309)
      ·
        refine ⟨6670646715015481009292351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 284614259840660523063140309 6670646715015481009292351)
        ·
          refine ⟨10005970072523221513938527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670646715015481009292351 10005970072523221513938527)
          ·
            refine ⟨15008955108784832270907791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005970072523221513938527 15008955108784832270907791)
            ·
              refine ⟨22513432663177248406361687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15008955108784832270907791 22513432663177248406361687)
              ·
                refine ⟨33770148994765872609542531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22513432663177248406361687 33770148994765872609542531)
                ·
                  refine ⟨50655223492148808914313797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33770148994765872609542531 50655223492148808914313797)
                  ·
                    refine ⟨9497854404777901671433837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50655223492148808914313797 9497854404777901671433837)
                    ·
                      refine ⟨3561695401791713126787689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497854404777901671433837 3561695401791713126787689)
                      ·
                        rfl

theorem cell23_6936377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6936377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936377 prefixEnd_6936377 := by exact prefixLift 6936377
  have htrace : WordTrace (prefixWord ++ tailWord_6936377) baseStart_6936377 baseEnd_6936377 := by
    simpa [prefixWord, tailWord_6936377, baseEnd_6936377] using wordTrace_append hprefix tailTrace_6936377
  have hstable : (prefixWord ++ tailWord_6936377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936377).length < 2 ^ (prefixWord ++ tailWord_6936377).sum := by decide
  have hdescent : baseEnd_6936377 < baseStart_6936377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936397 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 6]
def baseStart_6936397 : Nat := 118140960795 + 6936397 * 2 ^ 59
def prefixEnd_6936397 : Nat := 4983230072969 + 3 ^ 40 * 6936397 * 2
def baseEnd_6936397 : Nat := 395745074600533672059733

theorem tailTrace_6936397 : CollatzResearch.WordTrace tailWord_6936397 prefixEnd_6936397 395745074600533672059733 := by
  unfold tailWord_6936397
  simp only [CollatzResearch.WordTrace]
  refine ⟨252991182651625786138519445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168660788434417190759012963 252991182651625786138519445)
  ·
    refine ⟨11858961686794958725243099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252991182651625786138519445 11858961686794958725243099)
    ·
      refine ⟨17788442530192438087864649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858961686794958725243099 17788442530192438087864649)
      ·
        refine ⟨13341331897644328565898487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788442530192438087864649 13341331897644328565898487)
        ·
          refine ⟨20011997846466492848847731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341331897644328565898487 20011997846466492848847731)
          ·
            refine ⟨30017996769699739273271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20011997846466492848847731 30017996769699739273271597)
            ·
              refine ⟨11256748788637402227476849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30017996769699739273271597 11256748788637402227476849)
              ·
                refine ⟨8442561591478051670607637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256748788637402227476849 8442561591478051670607637)
                ·
                  refine ⟨395745074600533672059733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8442561591478051670607637 395745074600533672059733)
                  ·
                    rfl

theorem cell23_6936397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_6936397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936397 prefixEnd_6936397 := by exact prefixLift 6936397
  have htrace : WordTrace (prefixWord ++ tailWord_6936397) baseStart_6936397 baseEnd_6936397 := by
    simpa [prefixWord, tailWord_6936397, baseEnd_6936397] using wordTrace_append hprefix tailTrace_6936397
  have hstable : (prefixWord ++ tailWord_6936397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936397).length < 2 ^ (prefixWord ++ tailWord_6936397).sum := by decide
  have hdescent : baseEnd_6936397 < baseStart_6936397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936400 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2]
def baseStart_6936400 : Nat := 118140960795 + 6936400 * 2 ^ 59
def prefixEnd_6936400 : Nat := 4983230072969 + 3 ^ 40 * 6936400 * 2
def baseEnd_6936400 : Nat := 3561707211846766536800083

theorem tailTrace_6936400 : CollatzResearch.WordTrace tailWord_6936400 prefixEnd_6936400 3561707211846766536800083 := by
  unfold tailWord_6936400
  simp only [CollatzResearch.WordTrace]
  refine ⟨126495646035307458825439327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168660861380409945100585769 126495646035307458825439327)
  ·
    refine ⟨189743469052961188238158991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126495646035307458825439327 189743469052961188238158991)
    ·
      refine ⟨284615203579441782357238487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189743469052961188238158991 284615203579441782357238487)
      ·
        refine ⟨426922805369162673535857731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284615203579441782357238487 426922805369162673535857731)
        ·
          refine ⟨640384208053744010303786597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426922805369162673535857731 640384208053744010303786597)
          ·
            refine ⟨120072039010077001931959987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 640384208053744010303786597 120072039010077001931959987)
            ·
              refine ⟨180108058515115502897939981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120072039010077001931959987 180108058515115502897939981)
              ·
                refine ⟨67540521943168313586727493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180108058515115502897939981 67540521943168313586727493)
                ·
                  refine ⟨12663847864344058797511405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67540521943168313586727493 12663847864344058797511405)
                  ·
                    refine ⟨4748942949129022049066777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12663847864344058797511405 4748942949129022049066777)
                    ·
                      refine ⟨3561707211846766536800083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4748942949129022049066777 3561707211846766536800083)
                      ·
                        rfl

theorem cell23_6936400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2].length) (baseStart_6936400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936400 prefixEnd_6936400 := by exact prefixLift 6936400
  have htrace : WordTrace (prefixWord ++ tailWord_6936400) baseStart_6936400 baseEnd_6936400 := by
    simpa [prefixWord, tailWord_6936400, baseEnd_6936400] using wordTrace_append hprefix tailTrace_6936400
  have hstable : (prefixWord ++ tailWord_6936400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936400).length < 2 ^ (prefixWord ++ tailWord_6936400).sum := by decide
  have hdescent : baseEnd_6936400 < baseStart_6936400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936433 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_6936433 : Nat := 118140960795 + 6936433 * 2 ^ 59
def prefixEnd_6936433 : Nat := 4983230072969 + 3 ^ 40 * 6936433 * 2
def baseEnd_6936433 : Nat := 3561724156708364907687431

theorem tailTrace_6936433 : CollatzResearch.WordTrace tailWord_6936433 prefixEnd_6936433 3561724156708364907687431 := by
  unfold tailWord_6936433
  simp only [CollatzResearch.WordTrace]
  refine ⟨252992495679495364286829953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168661663786330242857886635 252992495679495364286829953)
  ·
    refine ⟨189744371759621523215122465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252992495679495364286829953 189744371759621523215122465)
    ·
      refine ⟨142308278819716142411341849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189744371759621523215122465 142308278819716142411341849)
      ·
        refine ⟨106731209114787106808506387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142308278819716142411341849 106731209114787106808506387)
        ·
          refine ⟨160096813672180660212759581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106731209114787106808506387 160096813672180660212759581)
          ·
            refine ⟨60036305127067747579784843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160096813672180660212759581 60036305127067747579784843)
            ·
              refine ⟨90054457690601621369677265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60036305127067747579784843 90054457690601621369677265)
              ·
                refine ⟨67540843267951216027257949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90054457690601621369677265 67540843267951216027257949)
                ·
                  refine ⟨25327816225481706010221731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67540843267951216027257949 25327816225481706010221731)
                  ·
                    refine ⟨37991724338222559015332597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25327816225481706010221731 37991724338222559015332597)
                    ·
                      refine ⟨3561724156708364907687431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37991724338222559015332597 3561724156708364907687431)
                      ·
                        rfl

theorem cell23_6936433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_6936433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936433 prefixEnd_6936433 := by exact prefixLift 6936433
  have htrace : WordTrace (prefixWord ++ tailWord_6936433) baseStart_6936433 baseEnd_6936433 := by
    simpa [prefixWord, tailWord_6936433, baseEnd_6936433] using wordTrace_append hprefix tailTrace_6936433
  have hstable : (prefixWord ++ tailWord_6936433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936433).length < 2 ^ (prefixWord ++ tailWord_6936433).sum := by decide
  have hdescent : baseEnd_6936433 < baseStart_6936433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936443 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_6936443 : Nat := 118140960795 + 6936443 * 2 ^ 59
def prefixEnd_6936443 : Nat := 4983230072969 + 3 ^ 40 * 6936443 * 2
def baseEnd_6936443 : Nat := 3561729291514909868562385

theorem tailTrace_6936443 : CollatzResearch.WordTrace tailWord_6936443 prefixEnd_6936443 3561729291514909868562385 := by
  unfold tailWord_6936443
  simp only [CollatzResearch.WordTrace]
  refine ⟨252992860409459135994693983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168661906939639423996462655 252992860409459135994693983)
  ·
    refine ⟨379489290614188703992040975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252992860409459135994693983 379489290614188703992040975)
    ·
      refine ⟨569233935921283055988061463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379489290614188703992040975 569233935921283055988061463)
      ·
        refine ⟨853850903881924583982092195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569233935921283055988061463 853850903881924583982092195)
        ·
          refine ⟨1280776355822886875973138293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853850903881924583982092195 1280776355822886875973138293)
          ·
            refine ⟨120072783358395644622481715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1280776355822886875973138293 120072783358395644622481715)
            ·
              refine ⟨180109175037593466933722573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120072783358395644622481715 180109175037593466933722573)
              ·
                refine ⟨67540940639097550100145965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180109175037593466933722573 67540940639097550100145965)
                ·
                  refine ⟨25327852739661581287554737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67540940639097550100145965 25327852739661581287554737)
                  ·
                    refine ⟨18995889554746185965666053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25327852739661581287554737 18995889554746185965666053)
                    ·
                      refine ⟨3561729291514909868562385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18995889554746185965666053 3561729291514909868562385)
                      ·
                        rfl

theorem cell23_6936443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_6936443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936443 prefixEnd_6936443 := by exact prefixLift 6936443
  have htrace : WordTrace (prefixWord ++ tailWord_6936443) baseStart_6936443 baseEnd_6936443 := by
    simpa [prefixWord, tailWord_6936443, baseEnd_6936443] using wordTrace_append hprefix tailTrace_6936443
  have hstable : (prefixWord ++ tailWord_6936443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936443).length < 2 ^ (prefixWord ++ tailWord_6936443).sum := by decide
  have hdescent : baseEnd_6936443 < baseStart_6936443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936458 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6936458 : Nat := 118140960795 + 6936458 * 2 ^ 59
def prefixEnd_6936458 : Nat := 4983230072969 + 3 ^ 40 * 6936458 * 2
def baseEnd_6936458 : Nat := 3561736993724727309874817

theorem tailTrace_6936458 : CollatzResearch.WordTrace tailWord_6936458 prefixEnd_6936458 3561736993724727309874817 := by
  unfold tailWord_6936458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248351876101198389122507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168662271669603195704326685 63248351876101198389122507)
  ·
    refine ⟨94872527814151797583683761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63248351876101198389122507 94872527814151797583683761)
    ·
      refine ⟨71154395860613848187762821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94872527814151797583683761 71154395860613848187762821)
      ·
        refine ⟨13341449223865096535205529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71154395860613848187762821 13341449223865096535205529)
        ·
          refine ⟨10006086917898822401404147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341449223865096535205529 10006086917898822401404147)
          ·
            refine ⟨15009130376848233602106221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006086917898822401404147 15009130376848233602106221)
            ·
              refine ⟨5628423891318087600789833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15009130376848233602106221 5628423891318087600789833)
              ·
                refine ⟨4221317918488565700592375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628423891318087600789833 4221317918488565700592375)
                ·
                  refine ⟨6331976877732848550888563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221317918488565700592375 6331976877732848550888563)
                  ·
                    refine ⟨9497965316599272826332845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331976877732848550888563 9497965316599272826332845)
                    ·
                      refine ⟨3561736993724727309874817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497965316599272826332845 3561736993724727309874817)
                      ·
                        rfl

theorem cell23_6936458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6936458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936458 prefixEnd_6936458 := by exact prefixLift 6936458
  have htrace : WordTrace (prefixWord ++ tailWord_6936458) baseStart_6936458 baseEnd_6936458 := by
    simpa [prefixWord, tailWord_6936458, baseEnd_6936458] using wordTrace_append hprefix tailTrace_6936458
  have hstable : (prefixWord ++ tailWord_6936458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936458).length < 2 ^ (prefixWord ++ tailWord_6936458).sum := by decide
  have hdescent : baseEnd_6936458 < baseStart_6936458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936474 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_6936474 : Nat := 118140960795 + 6936474 * 2 ^ 59
def prefixEnd_6936474 : Nat := 4983230072969 + 3 ^ 40 * 6936474 * 2
def baseEnd_6936474 : Nat := 1187248403138399749091581

theorem tailTrace_6936474 : CollatzResearch.WordTrace tailWord_6936474 prefixEnd_6936474 1187248403138399749091581 := by
  unfold tailWord_6936474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248497768086707072268119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168662660714897885526048317 63248497768086707072268119)
  ·
    refine ⟨94872746652130060608402179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63248497768086707072268119 94872746652130060608402179)
    ·
      refine ⟨142309119978195090912603269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94872746652130060608402179 142309119978195090912603269)
      ·
        refine ⟨26682959995911579546113113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142309119978195090912603269 26682959995911579546113113)
        ·
          refine ⟨20012219996933684659584835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26682959995911579546113113 20012219996933684659584835)
          ·
            refine ⟨30018329995400526989377253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012219996933684659584835 30018329995400526989377253)
            ·
              refine ⟨5628436874137598810508235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30018329995400526989377253 5628436874137598810508235)
              ·
                refine ⟨8442655311206398215762353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628436874137598810508235 8442655311206398215762353)
                ·
                  refine ⟨6331991483404798661821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8442655311206398215762353 6331991483404798661821765)
                  ·
                    refine ⟨1187248403138399749091581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6331991483404798661821765 1187248403138399749091581)
                    ·
                      rfl

theorem cell23_6936474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_6936474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936474 prefixEnd_6936474 := by exact prefixLift 6936474
  have htrace : WordTrace (prefixWord ++ tailWord_6936474) baseStart_6936474 baseEnd_6936474 := by
    simpa [prefixWord, tailWord_6936474, baseEnd_6936474] using wordTrace_append hprefix tailTrace_6936474
  have hstable : (prefixWord ++ tailWord_6936474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936474).length < 2 ^ (prefixWord ++ tailWord_6936474).sum := by decide
  have hdescent : baseEnd_6936474 < baseStart_6936474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936478 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6936478 : Nat := 118140960795 + 6936478 * 2 ^ 59
def prefixEnd_6936478 : Nat := 4983230072969 + 3 ^ 40 * 6936478 * 2
def baseEnd_6936478 : Nat := 1187249087779272410541575

theorem tailTrace_6936478 : CollatzResearch.WordTrace tailWord_6936478 prefixEnd_6936478 1187249087779272410541575 := by
  unfold tailWord_6936478
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624267120541542121527261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168662757976221557981478725 31624267120541542121527261)
  ·
    refine ⟨11859100170203078295572723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31624267120541542121527261 11859100170203078295572723)
    ·
      refine ⟨17788650255304617443359085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859100170203078295572723 17788650255304617443359085)
      ·
        refine ⟨6670743845739231541259657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17788650255304617443359085 6670743845739231541259657)
        ·
          refine ⟨5003057884304423655944743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6670743845739231541259657 5003057884304423655944743)
          ·
            refine ⟨7504586826456635483917115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003057884304423655944743 7504586826456635483917115)
            ·
              refine ⟨11256880239684953225875673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504586826456635483917115 11256880239684953225875673)
              ·
                refine ⟨8442660179763714919406755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256880239684953225875673 8442660179763714919406755)
                ·
                  refine ⟨12663990269645572379110133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442660179763714919406755 12663990269645572379110133)
                  ·
                    refine ⟨1187249087779272410541575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12663990269645572379110133 1187249087779272410541575)
                    ·
                      rfl

theorem cell23_6936478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6936478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936478 prefixEnd_6936478 := by exact prefixLift 6936478
  have htrace : WordTrace (prefixWord ++ tailWord_6936478) baseStart_6936478 baseEnd_6936478 := by
    simpa [prefixWord, tailWord_6936478, baseEnd_6936478] using wordTrace_append hprefix tailTrace_6936478
  have hstable : (prefixWord ++ tailWord_6936478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936478).length < 2 ^ (prefixWord ++ tailWord_6936478).sum := by decide
  have hdescent : baseEnd_6936478 < baseStart_6936478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936480 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_6936480 : Nat := 118140960795 + 6936480 * 2 ^ 59
def prefixEnd_6936480 : Nat := 4983230072969 + 3 ^ 40 * 6936480 * 2
def baseEnd_6936480 : Nat := 3561748290299126223799715

theorem tailTrace_6936480 : CollatzResearch.WordTrace tailWord_6936480 prefixEnd_6936480 3561748290299126223799715 := by
  unfold tailWord_6936480
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497104955162545656895447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168662806606883394209193929 126497104955162545656895447)
  ·
    refine ⟨189745657432743818485343171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126497104955162545656895447 189745657432743818485343171)
    ·
      refine ⟨284618486149115727728014757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189745657432743818485343171 284618486149115727728014757)
      ·
        refine ⟨53365966152959198949002767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284618486149115727728014757 53365966152959198949002767)
        ·
          refine ⟨80048949229438798423504151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53365966152959198949002767 80048949229438798423504151)
          ·
            refine ⟨120073423844158197635256227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80048949229438798423504151 120073423844158197635256227)
            ·
              refine ⟨180110135766237296452884341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120073423844158197635256227 180110135766237296452884341)
              ·
                refine ⟨16885325228084746542457907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180110135766237296452884341 16885325228084746542457907)
                ·
                  refine ⟨25327987842127119813686861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16885325228084746542457907 25327987842127119813686861)
                  ·
                    refine ⟨9497995440797669930132573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25327987842127119813686861 9497995440797669930132573)
                    ·
                      refine ⟨3561748290299126223799715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9497995440797669930132573 3561748290299126223799715)
                      ·
                        rfl

theorem cell23_6936480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_6936480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936480 prefixEnd_6936480 := by exact prefixLift 6936480
  have htrace : WordTrace (prefixWord ++ tailWord_6936480) baseStart_6936480 baseEnd_6936480 := by
    simpa [prefixWord, tailWord_6936480, baseEnd_6936480] using wordTrace_append hprefix tailTrace_6936480
  have hstable : (prefixWord ++ tailWord_6936480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936480).length < 2 ^ (prefixWord ++ tailWord_6936480).sum := by decide
  have hdescent : baseEnd_6936480 < baseStart_6936480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936481 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6936481 : Nat := 118140960795 + 6936481 * 2 ^ 59
def prefixEnd_6936481 : Nat := 4983230072969 + 3 ^ 40 * 6936481 * 2
def baseEnd_6936481 : Nat := 3561748803779780719887211

theorem tailTrace_6936481 : CollatzResearch.WordTrace tailWord_6936481 prefixEnd_6936481 3561748803779780719887211 := by
  unfold tailWord_6936481
  simp only [CollatzResearch.WordTrace]
  refine ⟨252994246383321468484577297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168662830922214312323051531 252994246383321468484577297)
  ·
    refine ⟨189745684787491101363432973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252994246383321468484577297 189745684787491101363432973)
    ·
      refine ⟨71154631795309163011287365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189745684787491101363432973 71154631795309163011287365)
      ·
        refine ⟨13341493461620468064616381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71154631795309163011287365 13341493461620468064616381)
        ·
          refine ⟨5003060048107675524231143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13341493461620468064616381 5003060048107675524231143)
          ·
            refine ⟨7504590072161513286346715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003060048107675524231143 7504590072161513286346715)
            ·
              refine ⟨11256885108242269929520073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504590072161513286346715 11256885108242269929520073)
              ·
                refine ⟨8442663831181702447140055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256885108242269929520073 8442663831181702447140055)
                ·
                  refine ⟨12663995746772553670710083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442663831181702447140055 12663995746772553670710083)
                  ·
                    refine ⟨18995993620158830506065125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12663995746772553670710083 18995993620158830506065125)
                    ·
                      refine ⟨3561748803779780719887211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18995993620158830506065125 3561748803779780719887211)
                      ·
                        rfl

theorem cell23_6936481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6936481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936481 prefixEnd_6936481 := by exact prefixLift 6936481
  have htrace : WordTrace (prefixWord ++ tailWord_6936481) baseStart_6936481 baseEnd_6936481 := by
    simpa [prefixWord, tailWord_6936481, baseEnd_6936481] using wordTrace_append hprefix tailTrace_6936481
  have hstable : (prefixWord ++ tailWord_6936481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936481).length < 2 ^ (prefixWord ++ tailWord_6936481).sum := by decide
  have hdescent : baseEnd_6936481 < baseStart_6936481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936484 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_6936484 : Nat := 118140960795 + 6936484 * 2 ^ 59
def prefixEnd_6936484 : Nat := 4983230072969 + 3 ^ 40 * 6936484 * 2
def baseEnd_6936484 : Nat := 3561750344221744208149697

theorem tailTrace_6936484 : CollatzResearch.WordTrace tailWord_6936484 prefixEnd_6936484 3561750344221744208149697 := by
  unfold tailWord_6936484
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497177901155299998468253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168662903868207066664624337 126497177901155299998468253)
  ·
    refine ⟨47436441712933237499425595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126497177901155299998468253 47436441712933237499425595)
    ·
      refine ⟨71154662569399856249138393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47436441712933237499425595 71154662569399856249138393)
      ·
        refine ⟨53365996927049892186853795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71154662569399856249138393 53365996927049892186853795)
        ·
          refine ⟨80048995390574838280280693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53365996927049892186853795 80048995390574838280280693)
          ·
            refine ⟨7504593317866391088776315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80048995390574838280280693 7504593317866391088776315)
            ·
              refine ⟨11256889976799586633164473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504593317866391088776315 11256889976799586633164473)
              ·
                refine ⟨8442667482599689974873355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256889976799586633164473 8442667482599689974873355)
                ·
                  refine ⟨12664001223899534962310033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442667482599689974873355 12664001223899534962310033)
                  ·
                    refine ⟨9498000917924651221732525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12664001223899534962310033 9498000917924651221732525)
                    ·
                      refine ⟨3561750344221744208149697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498000917924651221732525 3561750344221744208149697)
                      ·
                        rfl

theorem cell23_6936484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_6936484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936484 prefixEnd_6936484 := by exact prefixLift 6936484
  have htrace : WordTrace (prefixWord ++ tailWord_6936484) baseStart_6936484 baseEnd_6936484 := by
    simpa [prefixWord, tailWord_6936484, baseEnd_6936484] using wordTrace_append hprefix tailTrace_6936484
  have hstable : (prefixWord ++ tailWord_6936484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936484).length < 2 ^ (prefixWord ++ tailWord_6936484).sum := by decide
  have hdescent : baseEnd_6936484 < baseStart_6936484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936497 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6936497 : Nat := 118140960795 + 6936497 * 2 ^ 59
def prefixEnd_6936497 : Nat := 4983230072969 + 3 ^ 40 * 6936497 * 2
def baseEnd_6936497 : Nat := 3561757019470252657287137

theorem tailTrace_6936497 : CollatzResearch.WordTrace tailWord_6936497 prefixEnd_6936497 3561757019470252657287137 := by
  unfold tailWord_6936497
  simp only [CollatzResearch.WordTrace]
  refine ⟨252994829951263503217159745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168663219967509002144773163 252994829951263503217159745)
  ·
    refine ⟨189746122463447627412869809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252994829951263503217159745 189746122463447627412869809)
    ·
      refine ⟨142309591847585720559652357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189746122463447627412869809 142309591847585720559652357)
      ·
        refine ⟨26683048471422322604934817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142309591847585720559652357 26683048471422322604934817)
        ·
          refine ⟨20012286353566741953701113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26683048471422322604934817 20012286353566741953701113)
          ·
            refine ⟨15009214765175056465275835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20012286353566741953701113 15009214765175056465275835)
            ·
              refine ⟨22513822147762584697913753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009214765175056465275835 22513822147762584697913753)
              ·
                refine ⟨16885366610821938523435315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22513822147762584697913753 16885366610821938523435315)
                ·
                  refine ⟨25328049916232907785152973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16885366610821938523435315 25328049916232907785152973)
                  ·
                    refine ⟨9498018718587340419432365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25328049916232907785152973 9498018718587340419432365)
                    ·
                      refine ⟨3561757019470252657287137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498018718587340419432365 3561757019470252657287137)
                      ·
                        rfl

theorem cell23_6936497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6936497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936497 prefixEnd_6936497 := by exact prefixLift 6936497
  have htrace : WordTrace (prefixWord ++ tailWord_6936497) baseStart_6936497 baseEnd_6936497 := by
    simpa [prefixWord, tailWord_6936497, baseEnd_6936497] using wordTrace_append hprefix tailTrace_6936497
  have hstable : (prefixWord ++ tailWord_6936497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936497).length < 2 ^ (prefixWord ++ tailWord_6936497).sum := by decide
  have hdescent : baseEnd_6936497 < baseStart_6936497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936520 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6936520 : Nat := 118140960795 + 6936520 * 2 ^ 59
def prefixEnd_6936520 : Nat := 4983230072969 + 3 ^ 40 * 6936520 * 2
def baseEnd_6936520 : Nat := 3561768829525306067299531

theorem tailTrace_6936520 : CollatzResearch.WordTrace tailWord_6936520 prefixEnd_6936520 3561768829525306067299531 := by
  unfold tailWord_6936520
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497834415090089072623507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168663779220120118763498009 126497834415090089072623507)
  ·
    refine ⟨189746751622635133608935261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126497834415090089072623507 189746751622635133608935261)
    ·
      refine ⟨71155031858488175103350723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189746751622635133608935261 71155031858488175103350723)
      ·
        refine ⟨106732547787732262655026085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71155031858488175103350723 106732547787732262655026085)
        ·
          refine ⟨20012352710199799247817391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106732547787732262655026085 20012352710199799247817391)
          ·
            refine ⟨30018529065299698871726087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012352710199799247817391 30018529065299698871726087)
            ·
              refine ⟨45027793597949548307589131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30018529065299698871726087 45027793597949548307589131)
              ·
                refine ⟨67541690396924322461383697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45027793597949548307589131 67541690396924322461383697)
                ·
                  refine ⟨50656267797693241846037773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67541690396924322461383697 50656267797693241846037773)
                  ·
                    refine ⟨18996100424134965692264165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50656267797693241846037773 18996100424134965692264165)
                    ·
                      refine ⟨3561768829525306067299531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18996100424134965692264165 3561768829525306067299531)
                      ·
                        rfl

theorem cell23_6936520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6936520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936520 prefixEnd_6936520 := by exact prefixLift 6936520
  have htrace : WordTrace (prefixWord ++ tailWord_6936520) baseStart_6936520 baseEnd_6936520 := by
    simpa [prefixWord, tailWord_6936520, baseEnd_6936520] using wordTrace_append hprefix tailTrace_6936520
  have hstable : (prefixWord ++ tailWord_6936520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936520).length < 2 ^ (prefixWord ++ tailWord_6936520).sum := by decide
  have hdescent : baseEnd_6936520 < baseStart_6936520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936554 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_6936554 : Nat := 118140960795 + 6936554 * 2 ^ 59
def prefixEnd_6936554 : Nat := 4983230072969 + 3 ^ 40 * 6936554 * 2
def baseEnd_6936554 : Nat := 3561786287867558934274375

theorem tailTrace_6936554 : CollatzResearch.WordTrace tailWord_6936554 prefixEnd_6936554 3561786287867558934274375 := by
  unfold tailWord_6936554
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249227228014250487996179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168664605941371334634656477 63249227228014250487996179)
  ·
    refine ⟨94873840842021375731994269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63249227228014250487996179 94873840842021375731994269)
    ·
      refine ⟨35577690315758015899497851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94873840842021375731994269 35577690315758015899497851)
      ·
        refine ⟨53366535473637023849246777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35577690315758015899497851 53366535473637023849246777)
        ·
          refine ⟨40024901605227767886935083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53366535473637023849246777 40024901605227767886935083)
          ·
            refine ⟨60037352407841651830402625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40024901605227767886935083 60037352407841651830402625)
            ·
              refine ⟨45028014305881238872801969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60037352407841651830402625 45028014305881238872801969)
              ·
                refine ⟨33771010729410929154601477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45028014305881238872801969 33771010729410929154601477)
                ·
                  refine ⟨6332064511764549216487777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33771010729410929154601477 6332064511764549216487777)
                  ·
                    refine ⟨4749048383823411912365833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332064511764549216487777 4749048383823411912365833)
                    ·
                      refine ⟨3561786287867558934274375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749048383823411912365833 3561786287867558934274375)
                      ·
                        rfl

theorem cell23_6936554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_6936554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936554 prefixEnd_6936554 := by exact prefixLift 6936554
  have htrace : WordTrace (prefixWord ++ tailWord_6936554) baseStart_6936554 baseEnd_6936554 := by
    simpa [prefixWord, tailWord_6936554, baseEnd_6936554] using wordTrace_append hprefix tailTrace_6936554
  have hstable : (prefixWord ++ tailWord_6936554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936554).length < 2 ^ (prefixWord ++ tailWord_6936554).sum := by decide
  have hdescent : baseEnd_6936554 < baseStart_6936554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936558 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_6936558 : Nat := 118140960795 + 6936558 * 2 ^ 59
def prefixEnd_6936558 : Nat := 4983230072969 + 3 ^ 40 * 6936558 * 2
def baseEnd_6936558 : Nat := 3561788341790176918624357

theorem tailTrace_6936558 : CollatzResearch.WordTrace tailWord_6936558 prefixEnd_6936558 3561788341790176918624357 := by
  unfold tailWord_6936558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624631850505313829391291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168664703202695007090086885 31624631850505313829391291)
  ·
    refine ⟨47436947775757970744086937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31624631850505313829391291 47436947775757970744086937)
    ·
      refine ⟨35577710831818478058065203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47436947775757970744086937 35577710831818478058065203)
      ·
        refine ⟨53366566247727717087097805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35577710831818478058065203 53366566247727717087097805)
        ·
          refine ⟨20012462342897893907661677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53366566247727717087097805 20012462342897893907661677)
          ·
            refine ⟨7504673378586710215373129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20012462342897893907661677 7504673378586710215373129)
            ·
              refine ⟨5628505033940032661529847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504673378586710215373129 5628505033940032661529847)
              ·
                refine ⟨8442757550910048992294771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628505033940032661529847 8442757550910048992294771)
                ·
                  refine ⟨12664136326365073488442157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442757550910048992294771 12664136326365073488442157)
                  ·
                    refine ⟨4749051122386902558165809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12664136326365073488442157 4749051122386902558165809)
                    ·
                      refine ⟨3561788341790176918624357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749051122386902558165809 3561788341790176918624357)
                      ·
                        rfl

theorem cell23_6936558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_6936558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936558 prefixEnd_6936558 := by exact prefixLift 6936558
  have htrace : WordTrace (prefixWord ++ tailWord_6936558) baseStart_6936558 baseEnd_6936558 := by
    simpa [prefixWord, tailWord_6936558, baseEnd_6936558] using wordTrace_append hprefix tailTrace_6936558
  have hstable : (prefixWord ++ tailWord_6936558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936558).length < 2 ^ (prefixWord ++ tailWord_6936558).sum := by decide
  have hdescent : baseEnd_6936558 < baseStart_6936558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936577 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 5]
def baseStart_6936577 : Nat := 118140960795 + 6936577 * 2 ^ 59
def prefixEnd_6936577 : Nat := 4983230072969 + 3 ^ 40 * 6936577 * 2
def baseEnd_6936577 : Nat := 395755344213623593809641

theorem tailTrace_6936577 : CollatzResearch.WordTrace tailWord_6936577 prefixEnd_6936577 395755344213623593809641 := by
  unfold tailWord_6936577
  simp only [CollatzResearch.WordTrace]
  refine ⟨252997747790973676880071985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168665165193982451253381323 252997747790973676880071985)
  ·
    refine ⟨189748310843230257660053989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252997747790973676880071985 189748310843230257660053989)
    ·
      refine ⟨35577808283105673311260123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189748310843230257660053989 35577808283105673311260123)
      ·
        refine ⟨53366712424658509966890185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35577808283105673311260123 53366712424658509966890185)
        ·
          refine ⟨40025034318493882475167639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53366712424658509966890185 40025034318493882475167639)
          ·
            refine ⟨60037551477740823712751459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40025034318493882475167639 60037551477740823712751459)
            ·
              refine ⟨90056327216611235569127189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60037551477740823712751459 90056327216611235569127189)
              ·
                refine ⟨4221390338278651667302837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90056327216611235569127189 4221390338278651667302837)
                ·
                  refine ⟨395755344213623593809641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221390338278651667302837 395755344213623593809641)
                  ·
                    rfl

theorem cell23_6936577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 5].length) (baseStart_6936577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936577 prefixEnd_6936577 := by exact prefixLift 6936577
  have htrace : WordTrace (prefixWord ++ tailWord_6936577) baseStart_6936577 baseEnd_6936577 := by
    simpa [prefixWord, tailWord_6936577, baseEnd_6936577] using wordTrace_append hprefix tailTrace_6936577
  have hstable : (prefixWord ++ tailWord_6936577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936577).length < 2 ^ (prefixWord ++ tailWord_6936577).sum := by decide
  have hdescent : baseEnd_6936577 < baseStart_6936577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936582 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6936582 : Nat := 118140960795 + 6936582 * 2 ^ 59
def prefixEnd_6936582 : Nat := 4983230072969 + 3 ^ 40 * 6936582 * 2
def baseEnd_6936582 : Nat := 3561800665325884824724247

theorem tailTrace_6936582 : CollatzResearch.WordTrace tailWord_6936582 prefixEnd_6936582 3561800665325884824724247 := by
  unfold tailWord_6936582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906185317373611335437625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168665286770637041822669333 7906185317373611335437625)
  ·
    refine ⟨5929638988030208501578219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7906185317373611335437625 5929638988030208501578219)
    ·
      refine ⟨8894458482045312752367329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929638988030208501578219 8894458482045312752367329)
      ·
        refine ⟨6670843861533984564275497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8894458482045312752367329 6670843861533984564275497)
        ·
          refine ⟨5003132896150488423206623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6670843861533984564275497 5003132896150488423206623)
          ·
            refine ⟨7504699344225732634809935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003132896150488423206623 7504699344225732634809935)
            ·
              refine ⟨11257049016338598952214903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504699344225732634809935 11257049016338598952214903)
              ·
                refine ⟨16885573524507898428322355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257049016338598952214903 16885573524507898428322355)
                ·
                  refine ⟨25328360286761847642483533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16885573524507898428322355 25328360286761847642483533)
                  ·
                    refine ⟨9498135107535692865931325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25328360286761847642483533 9498135107535692865931325)
                    ·
                      refine ⟨3561800665325884824724247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498135107535692865931325 3561800665325884824724247)
                      ·
                        rfl

theorem cell23_6936582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6936582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936582 prefixEnd_6936582 := by exact prefixLift 6936582
  have htrace : WordTrace (prefixWord ++ tailWord_6936582) baseStart_6936582 baseEnd_6936582 := by
    simpa [prefixWord, tailWord_6936582, baseEnd_6936582] using wordTrace_append hprefix tailTrace_6936582
  have hstable : (prefixWord ++ tailWord_6936582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936582).length < 2 ^ (prefixWord ++ tailWord_6936582).sum := by decide
  have hdescent : baseEnd_6936582 < baseStart_6936582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936590 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_6936590 : Nat := 118140960795 + 6936590 * 2 ^ 59
def prefixEnd_6936590 : Nat := 4983230072969 + 3 ^ 40 * 6936590 * 2
def baseEnd_6936590 : Nat := 1187268257723706931141403

theorem tailTrace_6936590 : CollatzResearch.WordTrace tailWord_6936590 prefixEnd_6936590 1187268257723706931141403 := by
  unfold tailWord_6936590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624777742490822512536903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168665481293284386733530149 31624777742490822512536903)
  ·
    refine ⟨47437166613736233768805355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31624777742490822512536903 47437166613736233768805355)
    ·
      refine ⟨71155749920604350653208033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47437166613736233768805355 71155749920604350653208033)
      ·
        refine ⟨53366812440453262989906025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71155749920604350653208033 53366812440453262989906025)
        ·
          refine ⟨40025109330339947242429519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53366812440453262989906025 40025109330339947242429519)
          ·
            refine ⟨60037663995509920863644279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40025109330339947242429519 60037663995509920863644279)
            ·
              refine ⟨90056495993264881295466419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60037663995509920863644279 90056495993264881295466419)
              ·
                refine ⟨135084743989897321943199629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90056495993264881295466419 135084743989897321943199629)
                ·
                  refine ⟨50656778996211495728699861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135084743989897321943199629 50656778996211495728699861)
                  ·
                    refine ⟨1187268257723706931141403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50656778996211495728699861 1187268257723706931141403)
                    ·
                      rfl

theorem cell23_6936590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_6936590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936590 prefixEnd_6936590 := by exact prefixLift 6936590
  have htrace : WordTrace (prefixWord ++ tailWord_6936590) baseStart_6936590 baseEnd_6936590 := by
    simpa [prefixWord, tailWord_6936590, baseEnd_6936590] using wordTrace_append hprefix tailTrace_6936590
  have hstable : (prefixWord ++ tailWord_6936590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936590).length < 2 ^ (prefixWord ++ tailWord_6936590).sum := by decide
  have hdescent : baseEnd_6936590 < baseStart_6936590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936627 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 4, 2]
def baseStart_6936627 : Nat := 118140960795 + 6936627 * 2 ^ 59
def prefixEnd_6936627 : Nat := 4983230072969 + 3 ^ 40 * 6936627 * 2
def baseEnd_6936627 : Nat := 3561823771955337148661539

theorem tailTrace_6936627 : CollatzResearch.WordTrace tailWord_6936627 prefixEnd_6936627 3561823771955337148661539 := by
  unfold tailWord_6936627
  simp only [CollatzResearch.WordTrace]
  refine ⟨252999571440792535419392135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168666380960528356946261423 252999571440792535419392135)
  ·
    refine ⟨379499357161188803129088203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252999571440792535419392135 379499357161188803129088203)
    ·
      refine ⟨569249035741783204693632305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379499357161188803129088203 569249035741783204693632305)
      ·
        refine ⟨426936776806337403520224229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569249035741783204693632305 426936776806337403520224229)
        ·
          refine ⟨80050645651188263160042043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426936776806337403520224229 80050645651188263160042043)
          ·
            refine ⟨120075968476782394740063065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80050645651188263160042043 120075968476782394740063065)
            ·
              refine ⟨90056976357586796055047299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120075968476782394740063065 90056976357586796055047299)
              ·
                refine ⟨135085464536380194082570949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90056976357586796055047299 135085464536380194082570949)
                ·
                  refine ⟨25328524600571286390482053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135085464536380194082570949 25328524600571286390482053)
                  ·
                    refine ⟨4749098362607116198215385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25328524600571286390482053 4749098362607116198215385)
                    ·
                      refine ⟨3561823771955337148661539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749098362607116198215385 3561823771955337148661539)
                      ·
                        rfl

theorem cell23_6936627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4, 2].length) (baseStart_6936627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936627 prefixEnd_6936627 := by exact prefixLift 6936627
  have htrace : WordTrace (prefixWord ++ tailWord_6936627) baseStart_6936627 baseEnd_6936627 := by
    simpa [prefixWord, tailWord_6936627, baseEnd_6936627] using wordTrace_append hprefix tailTrace_6936627
  have hstable : (prefixWord ++ tailWord_6936627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936627).length < 2 ^ (prefixWord ++ tailWord_6936627).sum := by decide
  have hdescent : baseEnd_6936627 < baseStart_6936627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936628 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 5]
def baseStart_6936628 : Nat := 118140960795 + 6936628 * 2 ^ 59
def prefixEnd_6936628 : Nat := 4983230072969 + 3 ^ 40 * 6936628 * 2
def baseEnd_6936628 : Nat := 395758253937332404972115

theorem tailTrace_6936628 : CollatzResearch.WordTrace tailWord_6936628 prefixEnd_6936628 395758253937332404972115 := by
  unfold tailWord_6936628
  simp only [CollatzResearch.WordTrace]
  refine ⟨126499803956894456295089269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168666405275859275060119025 126499803956894456295089269)
  ·
    refine ⟨11859356620958855277664619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126499803956894456295089269 11859356620958855277664619)
    ·
      refine ⟨17789034931438282916496929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859356620958855277664619 17789034931438282916496929)
      ·
        refine ⟨13341776198578712187372697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17789034931438282916496929 13341776198578712187372697)
        ·
          refine ⟨10006332148934034140529523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341776198578712187372697 10006332148934034140529523)
          ·
            refine ⟨15009498223401051210794285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006332148934034140529523 15009498223401051210794285)
            ·
              refine ⟨5628561833775394204047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15009498223401051210794285 5628561833775394204047857)
              ·
                refine ⟨4221421375331545653035893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628561833775394204047857 4221421375331545653035893)
                ·
                  refine ⟨395758253937332404972115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221421375331545653035893 395758253937332404972115)
                  ·
                    rfl

theorem cell23_6936628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_6936628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936628 prefixEnd_6936628 := by exact prefixLift 6936628
  have htrace : WordTrace (prefixWord ++ tailWord_6936628) baseStart_6936628 baseEnd_6936628 := by
    simpa [prefixWord, tailWord_6936628, baseEnd_6936628] using wordTrace_append hprefix tailTrace_6936628
  have hstable : (prefixWord ++ tailWord_6936628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936628).length < 2 ^ (prefixWord ++ tailWord_6936628).sum := by decide
  have hdescent : baseEnd_6936628 < baseStart_6936628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936647 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_6936647 : Nat := 118140960795 + 6936647 * 2 ^ 59
def prefixEnd_6936647 : Nat := 4983230072969 + 3 ^ 40 * 6936647 * 2
def baseEnd_6936647 : Nat := 3561834041568427070411447

theorem tailTrace_6936647 : CollatzResearch.WordTrace tailWord_6936647 prefixEnd_6936647 3561834041568427070411447 := by
  unfold tailWord_6936647
  simp only [CollatzResearch.WordTrace]
  refine ⟨253000300900720078835120195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168666867267146719223413463 253000300900720078835120195)
  ·
    refine ⟨379500451351080118252680293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253000300900720078835120195 379500451351080118252680293)
    ·
      refine ⟨71156334628327522172377555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379500451351080118252680293 71156334628327522172377555)
      ·
        refine ⟨106734501942491283258566333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71156334628327522172377555 106734501942491283258566333)
        ·
          refine ⟨40025438228434231221962375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106734501942491283258566333 40025438228434231221962375)
          ·
            refine ⟨60038157342651346832943563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40025438228434231221962375 60038157342651346832943563)
            ·
              refine ⟨90057236013977020249415345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60038157342651346832943563 90057236013977020249415345)
              ·
                refine ⟨67542927010482765187061509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90057236013977020249415345 67542927010482765187061509)
                ·
                  refine ⟨12664298814465518472574033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67542927010482765187061509 12664298814465518472574033)
                  ·
                    refine ⟨9498224110849138854430525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12664298814465518472574033 9498224110849138854430525)
                    ·
                      refine ⟨3561834041568427070411447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498224110849138854430525 3561834041568427070411447)
                      ·
                        rfl

theorem cell23_6936647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_6936647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936647 prefixEnd_6936647 := by exact prefixLift 6936647
  have htrace : WordTrace (prefixWord ++ tailWord_6936647) baseStart_6936647 baseEnd_6936647 := by
    simpa [prefixWord, tailWord_6936647, baseEnd_6936647] using wordTrace_append hprefix tailTrace_6936647
  have hstable : (prefixWord ++ tailWord_6936647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936647).length < 2 ^ (prefixWord ++ tailWord_6936647).sum := by decide
  have hdescent : baseEnd_6936647 < baseStart_6936647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936664 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_6936664 : Nat := 118140960795 + 6936664 * 2 ^ 59
def prefixEnd_6936664 : Nat := 4983230072969 + 3 ^ 40 * 6936664 * 2
def baseEnd_6936664 : Nat := 3561842770739553503898869

theorem tailTrace_6936664 : CollatzResearch.WordTrace tailWord_6936664 prefixEnd_6936664 3561842770739553503898869 := by
  unfold tailWord_6936664
  simp only [CollatzResearch.WordTrace]
  refine ⟨126500460470829245369244523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168667280627772327158992697 126500460470829245369244523)
  ·
    refine ⟨189750690706243868053866785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126500460470829245369244523 189750690706243868053866785)
    ·
      refine ⟨142313018029682901040400089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189750690706243868053866785 142313018029682901040400089)
      ·
        refine ⟨106734763522262175780300067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142313018029682901040400089 106734763522262175780300067)
        ·
          refine ⟨160102145283393263670450101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106734763522262175780300067 160102145283393263670450101)
          ·
            refine ⟨15009576120318118469104697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160102145283393263670450101 15009576120318118469104697)
            ·
              refine ⟨11257182090238588851828523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15009576120318118469104697 11257182090238588851828523)
              ·
                refine ⟨16885773135357883277742785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257182090238588851828523 16885773135357883277742785)
                ·
                  refine ⟨12664329851518412458307089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16885773135357883277742785 12664329851518412458307089)
                  ·
                    refine ⟨9498247388638809343730317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12664329851518412458307089 9498247388638809343730317)
                    ·
                      refine ⟨3561842770739553503898869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498247388638809343730317 3561842770739553503898869)
                      ·
                        rfl

theorem cell23_6936664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_6936664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936664 prefixEnd_6936664 := by exact prefixLift 6936664
  have htrace : WordTrace (prefixWord ++ tailWord_6936664) baseStart_6936664 baseEnd_6936664 := by
    simpa [prefixWord, tailWord_6936664, baseEnd_6936664] using wordTrace_append hprefix tailTrace_6936664
  have hstable : (prefixWord ++ tailWord_6936664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936664).length < 2 ^ (prefixWord ++ tailWord_6936664).sum := by decide
  have hdescent : baseEnd_6936664 < baseStart_6936664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936688 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 1, 4]
def baseStart_6936688 : Nat := 118140960795 + 6936688 * 2 ^ 59
def prefixEnd_6936688 : Nat := 4983230072969 + 3 ^ 40 * 6936688 * 2
def baseEnd_6936688 : Nat := 1187285031425087136666253

theorem tailTrace_6936688 : CollatzResearch.WordTrace tailWord_6936688 prefixEnd_6936688 1187285031425087136666253 := by
  unfold tailWord_6936688
  simp only [CollatzResearch.WordTrace]
  refine ⟨126500898146785771418681359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168667864195714361891575145 126500898146785771418681359)
  ·
    refine ⟨189751347220178657128022039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126500898146785771418681359 189751347220178657128022039)
    ·
      refine ⟨284627020830267985692033059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189751347220178657128022039 284627020830267985692033059)
      ·
        refine ⟨426940531245401978538049589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284627020830267985692033059 426940531245401978538049589)
        ·
          refine ⟨40025674804256435487942149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426940531245401978538049589 40025674804256435487942149)
          ·
            refine ⟨7504814025798081653989153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40025674804256435487942149 7504814025798081653989153)
            ·
              refine ⟨5628610519348561240491865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504814025798081653989153 5628610519348561240491865)
              ·
                refine ⟨4221457889511420930368899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628610519348561240491865 4221457889511420930368899)
                ·
                  refine ⟨6332186834267131395553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221457889511420930368899 6332186834267131395553349)
                  ·
                    refine ⟨1187285031425087136666253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332186834267131395553349 1187285031425087136666253)
                    ·
                      rfl

theorem cell23_6936688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_6936688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936688 prefixEnd_6936688 := by exact prefixLift 6936688
  have htrace : WordTrace (prefixWord ++ tailWord_6936688) baseStart_6936688 baseEnd_6936688 := by
    simpa [prefixWord, tailWord_6936688, baseEnd_6936688] using wordTrace_append hprefix tailTrace_6936688
  have hstable : (prefixWord ++ tailWord_6936688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936688).length < 2 ^ (prefixWord ++ tailWord_6936688).sum := by decide
  have hdescent : baseEnd_6936688 < baseStart_6936688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936697 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_6936697 : Nat := 118140960795 + 6936697 * 2 ^ 59
def prefixEnd_6936697 : Nat := 4983230072969 + 3 ^ 40 * 6936697 * 2
def baseEnd_6936697 : Nat := 1187286571867050624928739

theorem tailTrace_6936697 : CollatzResearch.WordTrace tailWord_6936697 prefixEnd_6936697 1187286571867050624928739 := by
  unfold tailWord_6936697
  simp only [CollatzResearch.WordTrace]
  refine ⟨253002124550538937374440345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168668083033692624916293563 253002124550538937374440345)
  ·
    refine ⟨189751593412904203030830259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253002124550538937374440345 189751593412904203030830259)
    ·
      refine ⟨284627390119356304546245389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189751593412904203030830259 284627390119356304546245389)
      ·
        refine ⟨106735271294758614204842021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284627390119356304546245389 106735271294758614204842021)
        ·
          refine ⟨20012863367767240163407879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106735271294758614204842021 20012863367767240163407879)
          ·
            refine ⟨30019295051650860245111819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012863367767240163407879 30019295051650860245111819)
            ·
              refine ⟨45028942577476290367667729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30019295051650860245111819 45028942577476290367667729)
              ·
                refine ⟨33771706933107217775750797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45028942577476290367667729 33771706933107217775750797)
                ·
                  refine ⟨12664390099915206665906549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33771706933107217775750797 12664390099915206665906549)
                  ·
                    refine ⟨1187286571867050624928739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12664390099915206665906549 1187286571867050624928739)
                    ·
                      rfl

theorem cell23_6936697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_6936697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936697 prefixEnd_6936697 := by exact prefixLift 6936697
  have htrace : WordTrace (prefixWord ++ tailWord_6936697) baseStart_6936697 baseEnd_6936697 := by
    simpa [prefixWord, tailWord_6936697, baseEnd_6936697] using wordTrace_append hprefix tailTrace_6936697
  have hstable : (prefixWord ++ tailWord_6936697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936697).length < 2 ^ (prefixWord ++ tailWord_6936697).sum := by decide
  have hdescent : baseEnd_6936697 < baseStart_6936697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936761 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_6936761 : Nat := 118140960795 + 6936761 * 2 ^ 59
def prefixEnd_6936761 : Nat := 4983230072969 + 3 ^ 40 * 6936761 * 2
def baseEnd_6936761 : Nat := 1187297526121013208128641

theorem tailTrace_6936761 : CollatzResearch.WordTrace tailWord_6936761 prefixEnd_6936761 1187297526121013208128641 := by
  unfold tailWord_6936761
  simp only [CollatzResearch.WordTrace]
  refine ⟨253004458822307076304770137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168669639214871384203180091 253004458822307076304770137)
  ·
    refine ⟨189753344116730307228577603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253004458822307076304770137 189753344116730307228577603)
    ·
      refine ⟨284630016175095460842866405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189753344116730307228577603 284630016175095460842866405)
      ·
        refine ⟨53368128032830398908037451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284630016175095460842866405 53368128032830398908037451)
        ·
          refine ⟨80052192049245598362056177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53368128032830398908037451 80052192049245598362056177)
          ·
            refine ⟨60039144036934198771542133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80052192049245598362056177 60039144036934198771542133)
            ·
              refine ⟨5628669753462581134832075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60039144036934198771542133 5628669753462581134832075)
              ·
                refine ⟨8443004630193871702248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628669753462581134832075 8443004630193871702248113)
                ·
                  refine ⟨6332253472645403776686085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443004630193871702248113 6332253472645403776686085)
                  ·
                    refine ⟨1187297526121013208128641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332253472645403776686085 1187297526121013208128641)
                    ·
                      rfl

theorem cell23_6936761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_6936761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936761 prefixEnd_6936761 := by exact prefixLift 6936761
  have htrace : WordTrace (prefixWord ++ tailWord_6936761) baseStart_6936761 baseEnd_6936761 := by
    simpa [prefixWord, tailWord_6936761, baseEnd_6936761] using wordTrace_append hprefix tailTrace_6936761
  have hstable : (prefixWord ++ tailWord_6936761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936761).length < 2 ^ (prefixWord ++ tailWord_6936761).sum := by decide
  have hdescent : baseEnd_6936761 < baseStart_6936761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936764 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6936764 : Nat := 118140960795 + 6936764 * 2 ^ 59
def prefixEnd_6936764 : Nat := 4983230072969 + 3 ^ 40 * 6936764 * 2
def baseEnd_6936764 : Nat := 3561894118805003112648409

theorem tailTrace_6936764 : CollatzResearch.WordTrace tailWord_6936764 prefixEnd_6936764 3561894118805003112648409 := by
  unfold tailWord_6936764
  simp only [CollatzResearch.WordTrace]
  refine ⟨126502284120648103908564673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168669712160864138544752897 126502284120648103908564673)
  ·
    refine ⟨94876713090486077931423505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126502284120648103908564673 94876713090486077931423505)
    ·
      refine ⟨71157534817864558448567629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94876713090486077931423505 71157534817864558448567629)
      ·
        refine ⟨26684075556699209418212861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71157534817864558448567629 26684075556699209418212861)
        ·
          refine ⟨10006528333762203531829823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26684075556699209418212861 10006528333762203531829823)
          ·
            refine ⟨15009792500643305297744735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006528333762203531829823 15009792500643305297744735)
            ·
              refine ⟨22514688750964957946617103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009792500643305297744735 22514688750964957946617103)
              ·
                refine ⟨33772033126447436919925655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22514688750964957946617103 33772033126447436919925655)
                ·
                  refine ⟨50658049689671155379888483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33772033126447436919925655 50658049689671155379888483)
                  ·
                    refine ⟨75987074534506733069832725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50658049689671155379888483 75987074534506733069832725)
                    ·
                      refine ⟨3561894118805003112648409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75987074534506733069832725 3561894118805003112648409)
                      ·
                        rfl

theorem cell23_6936764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6936764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936764 prefixEnd_6936764 := by exact prefixLift 6936764
  have htrace : WordTrace (prefixWord ++ tailWord_6936764) baseStart_6936764 baseEnd_6936764 := by
    simpa [prefixWord, tailWord_6936764, baseEnd_6936764] using wordTrace_append hprefix tailTrace_6936764
  have hstable : (prefixWord ++ tailWord_6936764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936764).length < 2 ^ (prefixWord ++ tailWord_6936764).sum := by decide
  have hdescent : baseEnd_6936764 < baseStart_6936764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936801 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_6936801 : Nat := 118140960795 + 6936801 * 2 ^ 59
def prefixEnd_6936801 : Nat := 4983230072969 + 3 ^ 40 * 6936801 * 2
def baseEnd_6936801 : Nat := 3561913117589219467885739

theorem tailTrace_6936801 : CollatzResearch.WordTrace tailWord_6936801 prefixEnd_6936801 3561913117589219467885739 := by
  unfold tailWord_6936801
  simp only [CollatzResearch.WordTrace]
  refine ⟨253005917742162163136226257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168670611828108108757484171 253005917742162163136226257)
  ·
    refine ⟨189754438306621622352169693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253005917742162163136226257 189754438306621622352169693)
    ·
      refine ⟨71157914364983108382063635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189754438306621622352169693 71157914364983108382063635)
      ·
        refine ⟨106736871547474662573095453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71157914364983108382063635 106736871547474662573095453)
        ·
          refine ⟨40026326830302998464910795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106736871547474662573095453 40026326830302998464910795)
          ·
            refine ⟨60039490245454497697366193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40026326830302998464910795 60039490245454497697366193)
            ·
              refine ⟨45029617684090873273024645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60039490245454497697366193 45029617684090873273024645)
              ·
                refine ⟨8443053315767038738692121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45029617684090873273024645 8443053315767038738692121)
                ·
                  refine ⟨6332289986825279054019091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443053315767038738692121 6332289986825279054019091)
                  ·
                    refine ⟨9498434980237918581028637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6332289986825279054019091 9498434980237918581028637)
                    ·
                      refine ⟨3561913117589219467885739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498434980237918581028637 3561913117589219467885739)
                      ·
                        rfl

theorem cell23_6936801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_6936801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936801 prefixEnd_6936801 := by exact prefixLift 6936801
  have htrace : WordTrace (prefixWord ++ tailWord_6936801) baseStart_6936801 baseEnd_6936801 := by
    simpa [prefixWord, tailWord_6936801, baseEnd_6936801] using wordTrace_append hprefix tailTrace_6936801
  have hstable : (prefixWord ++ tailWord_6936801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936801).length < 2 ^ (prefixWord ++ tailWord_6936801).sum := by decide
  have hdescent : baseEnd_6936801 < baseStart_6936801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936817 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_6936817 : Nat := 118140960795 + 6936817 * 2 ^ 59
def prefixEnd_6936817 : Nat := 4983230072969 + 3 ^ 40 * 6936817 * 2
def baseEnd_6936817 : Nat := 1187307111093230468428555

theorem tailTrace_6936817 : CollatzResearch.WordTrace tailWord_6936817 prefixEnd_6936817 1187307111093230468428555 := by
  unfold tailWord_6936817
  simp only [CollatzResearch.WordTrace]
  refine ⟨253006501310104197868808705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168671000873402798579205803 253006501310104197868808705)
  ·
    refine ⟨189754875982578148401606529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253006501310104197868808705 189754875982578148401606529)
    ·
      refine ⟨142316156986933611301204897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189754875982578148401606529 142316156986933611301204897)
      ·
        refine ⟨106737117740200208475903673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142316156986933611301204897 106737117740200208475903673)
        ·
          refine ⟨80052838305150156356927755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106737117740200208475903673 80052838305150156356927755)
          ·
            refine ⟨120079257457725234535391633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80052838305150156356927755 120079257457725234535391633)
            ·
              refine ⟨90059443093293925901543725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120079257457725234535391633 90059443093293925901543725)
              ·
                refine ⟨33772291159985222213078897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90059443093293925901543725 33772291159985222213078897)
                ·
                  refine ⟨25329218369988916659809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33772291159985222213078897 25329218369988916659809173)
                  ·
                    refine ⟨1187307111093230468428555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25329218369988916659809173 1187307111093230468428555)
                    ·
                      rfl

theorem cell23_6936817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_6936817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936817 prefixEnd_6936817 := by exact prefixLift 6936817
  have htrace : WordTrace (prefixWord ++ tailWord_6936817) baseStart_6936817 baseEnd_6936817 := by
    simpa [prefixWord, tailWord_6936817, baseEnd_6936817] using wordTrace_append hprefix tailTrace_6936817
  have hstable : (prefixWord ++ tailWord_6936817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936817).length < 2 ^ (prefixWord ++ tailWord_6936817).sum := by decide
  have hdescent : baseEnd_6936817 < baseStart_6936817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936818 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_6936818 : Nat := 118140960795 + 6936818 * 2 ^ 59
def prefixEnd_6936818 : Nat := 4983230072969 + 3 ^ 40 * 6936818 * 2
def baseEnd_6936818 : Nat := 3561921846760345901373161

theorem tailTrace_6936818 : CollatzResearch.WordTrace tailWord_6936818 prefixEnd_6936818 3561921846760345901373161 := by
  unfold tailWord_6936818
  simp only [CollatzResearch.WordTrace]
  refine ⟨63251634445775143759898777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168671025188733716693063405 63251634445775143759898777)
  ·
    refine ⟨47438725834331357819924083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63251634445775143759898777 47438725834331357819924083)
    ·
      refine ⟨71158088751497036729886125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47438725834331357819924083 71158088751497036729886125)
      ·
        refine ⟨26684283281811388773707297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71158088751497036729886125 26684283281811388773707297)
        ·
          refine ⟨20013212461358541580280473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26684283281811388773707297 20013212461358541580280473)
          ·
            refine ⟨15009909346018906185210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20013212461358541580280473 15009909346018906185210355)
            ·
              refine ⟨22514864019028359277815533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009909346018906185210355 22514864019028359277815533)
              ·
                refine ⟨8443074007135634729180825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22514864019028359277815533 8443074007135634729180825)
                ·
                  refine ⟨6332305505351726046885619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443074007135634729180825 6332305505351726046885619)
                  ·
                    refine ⟨9498458258027589070328429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6332305505351726046885619 9498458258027589070328429)
                    ·
                      refine ⟨3561921846760345901373161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498458258027589070328429 3561921846760345901373161)
                      ·
                        rfl

theorem cell23_6936818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_6936818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936818 prefixEnd_6936818 := by exact prefixLift 6936818
  have htrace : WordTrace (prefixWord ++ tailWord_6936818) baseStart_6936818 baseEnd_6936818 := by
    simpa [prefixWord, tailWord_6936818, baseEnd_6936818] using wordTrace_append hprefix tailTrace_6936818
  have hstable : (prefixWord ++ tailWord_6936818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936818).length < 2 ^ (prefixWord ++ tailWord_6936818).sum := by decide
  have hdescent : baseEnd_6936818 < baseStart_6936818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_6936824 : Nat := 118140960795 + 6936824 * 2 ^ 59
def prefixEnd_6936824 : Nat := 4983230072969 + 3 ^ 40 * 6936824 * 2
def baseEnd_6936824 : Nat := 3561924927644272877898133

theorem tailTrace_6936824 : CollatzResearch.WordTrace tailWord_6936824 prefixEnd_6936824 3561924927644272877898133 := by
  unfold tailWord_6936824
  simp only [CollatzResearch.WordTrace]
  refine ⟨126503378310539419032156763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168671171080719225376209017 126503378310539419032156763)
  ·
    refine ⟨189755067465809128548235145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126503378310539419032156763 189755067465809128548235145)
    ·
      refine ⟨142316300599356846411176359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189755067465809128548235145 142316300599356846411176359)
      ·
        refine ⟨213474450899035269616764539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142316300599356846411176359 213474450899035269616764539)
        ·
          refine ⟨320211676348552904425146809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213474450899035269616764539 320211676348552904425146809)
          ·
            refine ⟨240158757261414678318860107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320211676348552904425146809 240158757261414678318860107)
            ·
              refine ⟨360238135892122017478290161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240158757261414678318860107 360238135892122017478290161)
              ·
                refine ⟨270178601919091513108717621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360238135892122017478290161 270178601919091513108717621)
                ·
                  refine ⟨25329243929914829353942277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270178601919091513108717621 25329243929914829353942277)
                  ·
                    refine ⟨4749233236859030503864177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25329243929914829353942277 4749233236859030503864177)
                    ·
                      refine ⟨3561924927644272877898133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749233236859030503864177 3561924927644272877898133)
                      ·
                        rfl

theorem cell23_6936824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_6936824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936824 prefixEnd_6936824 := by exact prefixLift 6936824
  have htrace : WordTrace (prefixWord ++ tailWord_6936824) baseStart_6936824 baseEnd_6936824 := by
    simpa [prefixWord, tailWord_6936824, baseEnd_6936824] using wordTrace_append hprefix tailTrace_6936824
  have hstable : (prefixWord ++ tailWord_6936824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936824).length < 2 ^ (prefixWord ++ tailWord_6936824).sum := by decide
  have hdescent : baseEnd_6936824 < baseStart_6936824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936828 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_6936828 : Nat := 118140960795 + 6936828 * 2 ^ 59
def prefixEnd_6936828 : Nat := 4983230072969 + 3 ^ 40 * 6936828 * 2
def baseEnd_6936828 : Nat := 3561926981566890862248115

theorem tailTrace_6936828 : CollatzResearch.WordTrace tailWord_6936828 prefixEnd_6936828 3561926981566890862248115 := by
  unfold tailWord_6936828
  simp only [CollatzResearch.WordTrace]
  refine ⟨126503451256532173373729569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168671268342042897831639425 126503451256532173373729569)
  ·
    refine ⟨94877588442399130030297177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126503451256532173373729569 94877588442399130030297177)
    ·
      refine ⟨71158191331799347522722883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94877588442399130030297177 71158191331799347522722883)
      ·
        refine ⟨106737286997699021284084325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71158191331799347522722883 106737286997699021284084325)
        ·
          refine ⟨20013241312068566490765811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106737286997699021284084325 20013241312068566490765811)
          ·
            refine ⟨30019861968102849736148717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20013241312068566490765811 30019861968102849736148717)
            ·
              refine ⟨11257448238038568651055769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30019861968102849736148717 11257448238038568651055769)
              ·
                refine ⟨8443086178528926488291827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11257448238038568651055769 8443086178528926488291827)
                ·
                  refine ⟨12664629267793389732437741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8443086178528926488291827 12664629267793389732437741)
                  ·
                    refine ⟨4749235975422521149664153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12664629267793389732437741 4749235975422521149664153)
                    ·
                      refine ⟨3561926981566890862248115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749235975422521149664153 3561926981566890862248115)
                      ·
                        rfl

theorem cell23_6936828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_6936828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936828 prefixEnd_6936828 := by exact prefixLift 6936828
  have htrace : WordTrace (prefixWord ++ tailWord_6936828) baseStart_6936828 baseEnd_6936828 := by
    simpa [prefixWord, tailWord_6936828, baseEnd_6936828] using wordTrace_append hprefix tailTrace_6936828
  have hstable : (prefixWord ++ tailWord_6936828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936828).length < 2 ^ (prefixWord ++ tailWord_6936828).sum := by decide
  have hdescent : baseEnd_6936828 < baseStart_6936828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936837 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_6936837 : Nat := 118140960795 + 6936837 * 2 ^ 59
def prefixEnd_6936837 : Nat := 4983230072969 + 3 ^ 40 * 6936837 * 2
def baseEnd_6936837 : Nat := 3561931602892781327035573

theorem tailTrace_6936837 : CollatzResearch.WordTrace tailWord_6936837 prefixEnd_6936837 3561931602892781327035573 := by
  unfold tailWord_6936837
  simp only [CollatzResearch.WordTrace]
  refine ⟨253007230770031741284536765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168671487180021160856357843 253007230770031741284536765)
  ·
    refine ⟨94877711538761902981701287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253007230770031741284536765 94877711538761902981701287)
    ·
      refine ⟨142316567308142854472551931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94877711538761902981701287 142316567308142854472551931)
      ·
        refine ⟨213474850962214281708827897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142316567308142854472551931 213474850962214281708827897)
        ·
          refine ⟨160106138221660711281620923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213474850962214281708827897 160106138221660711281620923)
          ·
            refine ⟨240159207332491066922431385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160106138221660711281620923 240159207332491066922431385)
            ·
              refine ⟨180119405499368300191823539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240159207332491066922431385 180119405499368300191823539)
              ·
                refine ⟨270179108249052450287735309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180119405499368300191823539 270179108249052450287735309)
                ·
                  refine ⟨101317165593394668857900741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270179108249052450287735309 101317165593394668857900741)
                  ·
                    refine ⟨18996968548761500410856389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101317165593394668857900741 18996968548761500410856389)
                    ·
                      refine ⟨3561931602892781327035573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18996968548761500410856389 3561931602892781327035573)
                      ·
                        rfl

theorem cell23_6936837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_6936837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936837 prefixEnd_6936837 := by exact prefixLift 6936837
  have htrace : WordTrace (prefixWord ++ tailWord_6936837) baseStart_6936837 baseEnd_6936837 := by
    simpa [prefixWord, tailWord_6936837, baseEnd_6936837] using wordTrace_append hprefix tailTrace_6936837
  have hstable : (prefixWord ++ tailWord_6936837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936837).length < 2 ^ (prefixWord ++ tailWord_6936837).sum := by decide
  have hdescent : baseEnd_6936837 < baseStart_6936837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936841 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 4, 2]
def baseStart_6936841 : Nat := 118140960795 + 6936841 * 2 ^ 59
def prefixEnd_6936841 : Nat := 4983230072969 + 3 ^ 40 * 6936841 * 2
def baseEnd_6936841 : Nat := 3561933656815399311385555

theorem tailTrace_6936841 : CollatzResearch.WordTrace tailWord_6936841 prefixEnd_6936841 3561933656815399311385555 := by
  unfold tailWord_6936841
  simp only [CollatzResearch.WordTrace]
  refine ⟨253007376662017249967682377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168671584441344833311788251 253007376662017249967682377)
  ·
    refine ⟨189755532496512937475761783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253007376662017249967682377 189755532496512937475761783)
    ·
      refine ⟨284633298744769406213642675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189755532496512937475761783 284633298744769406213642675)
      ·
        refine ⟨426949948117154109320464013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284633298744769406213642675 426949948117154109320464013)
        ·
          refine ⟨160106230543932790995174005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426949948117154109320464013 160106230543932790995174005)
          ·
            refine ⟨15009959113493699155797563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160106230543932790995174005 15009959113493699155797563)
            ·
              refine ⟨22514938670240548733696345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009959113493699155797563 22514938670240548733696345)
              ·
                refine ⟨16886204002680411550272259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22514938670240548733696345 16886204002680411550272259)
                ·
                  refine ⟨25329306004020617325408389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16886204002680411550272259 25329306004020617325408389)
                  ·
                    refine ⟨4749244875753865748514073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25329306004020617325408389 4749244875753865748514073)
                    ·
                      refine ⟨3561933656815399311385555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749244875753865748514073 3561933656815399311385555)
                      ·
                        rfl

theorem cell23_6936841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4, 2].length) (baseStart_6936841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936841 prefixEnd_6936841 := by exact prefixLift 6936841
  have htrace : WordTrace (prefixWord ++ tailWord_6936841) baseStart_6936841 baseEnd_6936841 := by
    simpa [prefixWord, tailWord_6936841, baseEnd_6936841] using wordTrace_append hprefix tailTrace_6936841
  have hstable : (prefixWord ++ tailWord_6936841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936841).length < 2 ^ (prefixWord ++ tailWord_6936841).sum := by decide
  have hdescent : baseEnd_6936841 < baseStart_6936841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936887 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_6936887 : Nat := 118140960795 + 6936887 * 2 ^ 59
def prefixEnd_6936887 : Nat := 4983230072969 + 3 ^ 40 * 6936887 * 2
def baseEnd_6936887 : Nat := 3561957276925506131410343

theorem tailTrace_6936887 : CollatzResearch.WordTrace tailWord_6936887 prefixEnd_6936887 3561957276925506131410343 := by
  unfold tailWord_6936887
  simp only [CollatzResearch.WordTrace]
  refine ⟨253009054419850599823856915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168672702946567066549237943 253009054419850599823856915)
  ·
    refine ⟨379513581629775899735785373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253009054419850599823856915 379513581629775899735785373)
    ·
      refine ⟨142317593111165962400919515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379513581629775899735785373 142317593111165962400919515)
      ·
        refine ⟨213476389666748943601379273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142317593111165962400919515 213476389666748943601379273)
        ·
          refine ⟨160107292250061707701034455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213476389666748943601379273 160107292250061707701034455)
          ·
            refine ⟨240160938375092561551551683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160107292250061707701034455 240160938375092561551551683)
            ·
              refine ⟨360241407562638842327327525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240160938375092561551551683 360241407562638842327327525)
              ·
                refine ⟨67545263917994782936373911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360241407562638842327327525 67545263917994782936373911)
                ·
                  refine ⟨101317895876992174404560867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67545263917994782936373911 101317895876992174404560867)
                  ·
                    refine ⟨151976843815488261606841301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101317895876992174404560867 151976843815488261606841301)
                    ·
                      refine ⟨3561957276925506131410343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151976843815488261606841301 3561957276925506131410343)
                      ·
                        rfl

theorem cell23_6936887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_6936887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936887 prefixEnd_6936887 := by exact prefixLift 6936887
  have htrace : WordTrace (prefixWord ++ tailWord_6936887) baseStart_6936887 baseEnd_6936887 := by
    simpa [prefixWord, tailWord_6936887, baseEnd_6936887] using wordTrace_append hprefix tailTrace_6936887
  have hstable : (prefixWord ++ tailWord_6936887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936887).length < 2 ^ (prefixWord ++ tailWord_6936887).sum := by decide
  have hdescent : baseEnd_6936887 < baseStart_6936887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936926 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6936926 : Nat := 118140960795 + 6936926 * 2 ^ 59
def prefixEnd_6936926 : Nat := 4983230072969 + 3 ^ 40 * 6936926 * 2
def baseEnd_6936926 : Nat := 3561977302671031478822665

theorem tailTrace_6936926 : CollatzResearch.WordTrace tailWord_6936926 prefixEnd_6936926 3561977302671031478822665 := by
  unfold tailWord_6936926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626309608338663685565829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168673651244472872989684421 31626309608338663685565829)
  ·
    refine ⟨5929933051563499441043593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31626309608338663685565829 5929933051563499441043593)
    ·
      refine ⟨4447449788672624580782695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5929933051563499441043593 4447449788672624580782695)
      ·
        refine ⟨6671174683008936871174043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447449788672624580782695 6671174683008936871174043)
        ·
          refine ⟨10006762024513405306761065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671174683008936871174043 10006762024513405306761065)
          ·
            refine ⟨7505071518385053980070799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006762024513405306761065 7505071518385053980070799)
            ·
              refine ⟨11257607277577580970106199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505071518385053980070799 11257607277577580970106199)
              ·
                refine ⟨16886410916366371455159299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257607277577580970106199 16886410916366371455159299)
                ·
                  refine ⟨25329616374549557182738949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16886410916366371455159299 25329616374549557182738949)
                  ·
                    refine ⟨4749303070228041971763553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25329616374549557182738949 4749303070228041971763553)
                    ·
                      refine ⟨3561977302671031478822665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749303070228041971763553 3561977302671031478822665)
                      ·
                        rfl

theorem cell23_6936926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6936926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936926 prefixEnd_6936926 := by exact prefixLift 6936926
  have htrace : WordTrace (prefixWord ++ tailWord_6936926) baseStart_6936926 baseEnd_6936926 := by
    simpa [prefixWord, tailWord_6936926, baseEnd_6936926] using wordTrace_append hprefix tailTrace_6936926
  have hstable : (prefixWord ++ tailWord_6936926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936926).length < 2 ^ (prefixWord ++ tailWord_6936926).sum := by decide
  have hdescent : baseEnd_6936926 < baseStart_6936926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936931 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6936931 : Nat := 118140960795 + 6936931 * 2 ^ 59
def prefixEnd_6936931 : Nat := 4983230072969 + 3 ^ 40 * 6936931 * 2
def baseEnd_6936931 : Nat := 3561979870074303959260141

theorem tailTrace_6936931 : CollatzResearch.WordTrace tailWord_6936931 prefixEnd_6936931 3561979870074303959260141 := by
  unfold tailWord_6936931
  simp only [CollatzResearch.WordTrace]
  refine ⟨253010659231691195338458647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168673772821127463558972431 253010659231691195338458647)
  ·
    refine ⟨379515988847536793007687971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253010659231691195338458647 379515988847536793007687971)
    ·
      refine ⟨569273983271305189511531957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379515988847536793007687971 569273983271305189511531957)
      ·
        refine ⟨53369435931684861516706121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569273983271305189511531957 53369435931684861516706121)
        ·
          refine ⟨40027076948763646137529591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53369435931684861516706121 40027076948763646137529591)
          ·
            refine ⟨60040615423145469206294387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40027076948763646137529591 60040615423145469206294387)
            ·
              refine ⟨90060923134718203809441581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60040615423145469206294387 90060923134718203809441581)
              ·
                refine ⟨33772846175519326428540593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90060923134718203809441581 33772846175519326428540593)
                ·
                  refine ⟨25329634631639494821405445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33772846175519326428540593 25329634631639494821405445)
                  ·
                    refine ⟨4749306493432405279013521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25329634631639494821405445 4749306493432405279013521)
                    ·
                      refine ⟨3561979870074303959260141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749306493432405279013521 3561979870074303959260141)
                      ·
                        rfl

theorem cell23_6936931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6936931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936931 prefixEnd_6936931 := by exact prefixLift 6936931
  have htrace : WordTrace (prefixWord ++ tailWord_6936931) baseStart_6936931 baseEnd_6936931 := by
    simpa [prefixWord, tailWord_6936931, baseEnd_6936931] using wordTrace_append hprefix tailTrace_6936931
  have hstable : (prefixWord ++ tailWord_6936931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936931).length < 2 ^ (prefixWord ++ tailWord_6936931).sum := by decide
  have hdescent : baseEnd_6936931 < baseStart_6936931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6936941 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_6936941 : Nat := 118140960795 + 6936941 * 2 ^ 59
def prefixEnd_6936941 : Nat := 4983230072969 + 3 ^ 40 * 6936941 * 2
def baseEnd_6936941 : Nat := 1187328334960282973378365

theorem tailTrace_6936941 : CollatzResearch.WordTrace tailWord_6936941 prefixEnd_6936941 1187328334960282973378365 := by
  unfold tailWord_6936941
  simp only [CollatzResearch.WordTrace]
  refine ⟨253011023961654967046322677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168674015974436644697548451 253011023961654967046322677)
  ·
    refine ⟨23719783496405153160592751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253011023961654967046322677 23719783496405153160592751)
    ·
      refine ⟨35579675244607729740889127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23719783496405153160592751 35579675244607729740889127)
      ·
        refine ⟨53369512866911594611333691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35579675244607729740889127 53369512866911594611333691)
        ·
          refine ⟨80054269300367391917000537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53369512866911594611333691 80054269300367391917000537)
          ·
            refine ⟨60040701975275543937750403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80054269300367391917000537 60040701975275543937750403)
            ·
              refine ⟨90061052962913315906625605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60040701975275543937750403 90061052962913315906625605)
              ·
                refine ⟨16886447430546246732492301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90061052962913315906625605 16886447430546246732492301)
                ·
                  refine ⟨6332417786454842524684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16886447430546246732492301 6332417786454842524684613)
                  ·
                    refine ⟨1187328334960282973378365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332417786454842524684613 1187328334960282973378365)
                    ·
                      rfl

theorem cell23_6936941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_6936941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6936941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6936941 prefixEnd_6936941 := by exact prefixLift 6936941
  have htrace : WordTrace (prefixWord ++ tailWord_6936941) baseStart_6936941 baseEnd_6936941 := by
    simpa [prefixWord, tailWord_6936941, baseEnd_6936941] using wordTrace_append hprefix tailTrace_6936941
  have hstable : (prefixWord ++ tailWord_6936941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6936941).length < 2 ^ (prefixWord ++ tailWord_6936941).sum := by decide
  have hdescent : baseEnd_6936941 < baseStart_6936941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6936941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937032 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_6937032 : Nat := 118140960795 + 6937032 * 2 ^ 59
def prefixEnd_6937032 : Nat := 4983230072969 + 3 ^ 40 * 6937032 * 2
def baseEnd_6937032 : Nat := 3562031731620408064097177

theorem tailTrace_6937032 : CollatzResearch.WordTrace tailWord_6937032 prefixEnd_6937032 3562031731620408064097177 := by
  unfold tailWord_6937032
  simp only [CollatzResearch.WordTrace]
  refine ⟨126507171502162644793942675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168676228669550193058590233 126507171502162644793942675)
  ·
    refine ⟨189760757253243967190914013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126507171502162644793942675 189760757253243967190914013)
    ·
      refine ⟨71160283969966487696592755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189760757253243967190914013 71160283969966487696592755)
      ·
        refine ⟨106740425954949731544889133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71160283969966487696592755 106740425954949731544889133)
        ·
          refine ⟨40027659733106149329333425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106740425954949731544889133 40027659733106149329333425)
          ·
            refine ⟨30020744799829611997000069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40027659733106149329333425 30020744799829611997000069)
            ·
              refine ⟨5628889649968052249437513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30020744799829611997000069 5628889649968052249437513)
              ·
                refine ⟨4221667237476039187078135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628889649968052249437513 4221667237476039187078135)
                ·
                  refine ⟨6332500856214058780617203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221667237476039187078135 6332500856214058780617203)
                  ·
                    refine ⟨9498751284321088170925805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6332500856214058780617203 9498751284321088170925805)
                    ·
                      refine ⟨3562031731620408064097177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498751284321088170925805 3562031731620408064097177)
                      ·
                        rfl

theorem cell23_6937032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_6937032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937032 prefixEnd_6937032 := by exact prefixLift 6937032
  have htrace : WordTrace (prefixWord ++ tailWord_6937032) baseStart_6937032 baseEnd_6937032 := by
    simpa [prefixWord, tailWord_6937032, baseEnd_6937032] using wordTrace_append hprefix tailTrace_6937032
  have hstable : (prefixWord ++ tailWord_6937032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937032).length < 2 ^ (prefixWord ++ tailWord_6937032).sum := by decide
  have hdescent : baseEnd_6937032 < baseStart_6937032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937055 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 3, 2, 2]
def baseStart_6937055 : Nat := 118140960795 + 6937055 * 2 ^ 59
def prefixEnd_6937055 : Nat := 4983230072969 + 3 ^ 40 * 6937055 * 2
def baseEnd_6937055 : Nat := 3562043541675461474109571

theorem tailTrace_6937055 : CollatzResearch.WordTrace tailWord_6937055 prefixEnd_6937055 3562043541675461474109571 := by
  unfold tailWord_6937055
  simp only [CollatzResearch.WordTrace]
  refine ⟨253015181883241964515972619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168676787922161309677315079 253015181883241964515972619)
  ·
    refine ⟨379522772824862946773958929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253015181883241964515972619 379522772824862946773958929)
    ·
      refine ⟨284642079618647210080469197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379522772824862946773958929 284642079618647210080469197)
      ·
        refine ⟨106740779856992703780175949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284642079618647210080469197 106740779856992703780175949)
        ·
          refine ⟨40027792446372263917565981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106740779856992703780175949 40027792446372263917565981)
          ·
            refine ⟨15010422167389598969087243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40027792446372263917565981 15010422167389598969087243)
            ·
              refine ⟨22515633251084398453630865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15010422167389598969087243 22515633251084398453630865)
              ·
                refine ⟨16886724938313298840223149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22515633251084398453630865 16886724938313298840223149)
                ·
                  refine ⟨6332521851867487065083681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16886724938313298840223149 6332521851867487065083681)
                  ·
                    refine ⟨4749391388900615298812761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332521851867487065083681 4749391388900615298812761)
                    ·
                      refine ⟨3562043541675461474109571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749391388900615298812761 3562043541675461474109571)
                      ·
                        rfl

theorem cell23_6937055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_6937055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937055 prefixEnd_6937055 := by exact prefixLift 6937055
  have htrace : WordTrace (prefixWord ++ tailWord_6937055) baseStart_6937055 baseEnd_6937055 := by
    simpa [prefixWord, tailWord_6937055, baseEnd_6937055] using wordTrace_append hprefix tailTrace_6937055
  have hstable : (prefixWord ++ tailWord_6937055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937055).length < 2 ^ (prefixWord ++ tailWord_6937055).sum := by decide
  have hdescent : baseEnd_6937055 < baseStart_6937055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937072 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 1, 2, 2]
def baseStart_6937072 : Nat := 118140960795 + 6937072 * 2 ^ 59
def prefixEnd_6937072 : Nat := 4983230072969 + 3 ^ 40 * 6937072 * 2
def baseEnd_6937072 : Nat := 3562052270846587907596993

theorem tailTrace_6937072 : CollatzResearch.WordTrace tailWord_6937072 prefixEnd_6937072 3562052270846587907596993 := by
  unfold tailWord_6937072
  simp only [CollatzResearch.WordTrace]
  refine ⟨126507900962090188209670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168677201282786917612894313 126507900962090188209670735)
  ·
    refine ⟨189761851443135282314506103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126507900962090188209670735 189761851443135282314506103)
    ·
      refine ⟨284642777164702923471759155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189761851443135282314506103 284642777164702923471759155)
      ·
        refine ⟨426964165747054385207638733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284642777164702923471759155 426964165747054385207638733)
        ·
          refine ⟨160111562155145394452864525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426964165747054385207638733 160111562155145394452864525)
          ·
            refine ⟨60041835808179522919824197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160111562155145394452864525 60041835808179522919824197)
            ·
              refine ⟨11257844214033660547467037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60041835808179522919824197 11257844214033660547467037)
              ·
                refine ⟨4221691580262622705300139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11257844214033660547467037 4221691580262622705300139)
                ·
                  refine ⟨6332537370393934057950209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221691580262622705300139 6332537370393934057950209)
                  ·
                    refine ⟨4749403027795450543462657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332537370393934057950209 4749403027795450543462657)
                    ·
                      refine ⟨3562052270846587907596993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749403027795450543462657 3562052270846587907596993)
                      ·
                        rfl

theorem cell23_6937072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 2, 2].length) (baseStart_6937072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937072 prefixEnd_6937072 := by exact prefixLift 6937072
  have htrace : WordTrace (prefixWord ++ tailWord_6937072) baseStart_6937072 baseEnd_6937072 := by
    simpa [prefixWord, tailWord_6937072, baseEnd_6937072] using wordTrace_append hprefix tailTrace_6937072
  have hstable : (prefixWord ++ tailWord_6937072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937072).length < 2 ^ (prefixWord ++ tailWord_6937072).sum := by decide
  have hdescent : baseEnd_6937072 < baseStart_6937072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937104 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_6937104 : Nat := 118140960795 + 6937104 * 2 ^ 59
def prefixEnd_6937104 : Nat := 4983230072969 + 3 ^ 40 * 6937104 * 2
def baseEnd_6937104 : Nat := 1187356234075843927465615

theorem tailTrace_6937104 : CollatzResearch.WordTrace tailWord_6937104 prefixEnd_6937104 1187356234075843927465615 := by
  unfold tailWord_6937104
  simp only [CollatzResearch.WordTrace]
  refine ⟨126508484530032222942253183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168677979373376297256337577 126508484530032222942253183)
  ·
    refine ⟨189762726795048334413379775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126508484530032222942253183 189762726795048334413379775)
    ·
      refine ⟨284644090192572501620069663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189762726795048334413379775 284644090192572501620069663)
      ·
        refine ⟨426966135288858752430104495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284644090192572501620069663 426966135288858752430104495)
        ·
          refine ⟨640449202933288128645156743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426966135288858752430104495 640449202933288128645156743)
          ·
            refine ⟨960673804399932192967735115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640449202933288128645156743 960673804399932192967735115)
            ·
              refine ⟨1441010706599898289451602673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960673804399932192967735115 1441010706599898289451602673)
              ·
                refine ⟨1080758029949923717088702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441010706599898289451602673 1080758029949923717088702005)
                ·
                  refine ⟨101321065307805348477065813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1080758029949923717088702005 101321065307805348477065813)
                  ·
                    refine ⟨1187356234075843927465615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101321065307805348477065813 1187356234075843927465615)
                    ·
                      rfl

theorem cell23_6937104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_6937104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937104 prefixEnd_6937104 := by exact prefixLift 6937104
  have htrace : WordTrace (prefixWord ++ tailWord_6937104) baseStart_6937104 baseEnd_6937104 := by
    simpa [prefixWord, tailWord_6937104, baseEnd_6937104] using wordTrace_append hprefix tailTrace_6937104
  have hstable : (prefixWord ++ tailWord_6937104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937104).length < 2 ^ (prefixWord ++ tailWord_6937104).sum := by decide
  have hdescent : baseEnd_6937104 < baseStart_6937104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937145 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6937145 : Nat := 118140960795 + 6937145 * 2 ^ 59
def prefixEnd_6937145 : Nat := 4983230072969 + 3 ^ 40 * 6937145 * 2
def baseEnd_6937145 : Nat := 3562089754934366121984157

theorem tailTrace_6937145 : CollatzResearch.WordTrace tailWord_6937145 prefixEnd_6937145 3562089754934366121984157 := by
  unfold tailWord_6937145
  simp only [CollatzResearch.WordTrace]
  refine ⟨253018464452915909886748889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168678976301943939924499259 253018464452915909886748889)
  ·
    refine ⟨189763848339686932415061667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253018464452915909886748889 189763848339686932415061667)
    ·
      refine ⟨284645772509530398622592501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189763848339686932415061667 284645772509530398622592501)
      ·
        refine ⟨26685541172768474870868047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284645772509530398622592501 26685541172768474870868047)
        ·
          refine ⟨40028311759152712306302071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26685541172768474870868047 40028311759152712306302071)
          ·
            refine ⟨60042467638729068459453107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40028311759152712306302071 60042467638729068459453107)
            ·
              refine ⟨90063701458093602689179661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60042467638729068459453107 90063701458093602689179661)
              ·
                refine ⟨33773888046785101008442373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90063701458093602689179661 33773888046785101008442373)
                ·
                  refine ⟨6332604008772206439082945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33773888046785101008442373 6332604008772206439082945)
                  ·
                    refine ⟨4749453006579154829312209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332604008772206439082945 4749453006579154829312209)
                    ·
                      refine ⟨3562089754934366121984157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749453006579154829312209 3562089754934366121984157)
                      ·
                        rfl

theorem cell23_6937145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6937145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937145 prefixEnd_6937145 := by exact prefixLift 6937145
  have htrace : WordTrace (prefixWord ++ tailWord_6937145) baseStart_6937145 baseEnd_6937145 := by
    simpa [prefixWord, tailWord_6937145, baseEnd_6937145] using wordTrace_append hprefix tailTrace_6937145
  have hstable : (prefixWord ++ tailWord_6937145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937145).length < 2 ^ (prefixWord ++ tailWord_6937145).sum := by decide
  have hdescent : baseEnd_6937145 < baseStart_6937145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937156 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6937156 : Nat := 118140960795 + 6937156 * 2 ^ 59
def prefixEnd_6937156 : Nat := 4983230072969 + 3 ^ 40 * 6937156 * 2
def baseEnd_6937156 : Nat := 3562095403221565578946607

theorem tailTrace_6937156 : CollatzResearch.WordTrace tailWord_6937156 prefixEnd_6937156 3562095403221565578946607 := by
  unfold tailWord_6937156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126509432827938029382699661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168679243770584039176932881 126509432827938029382699661)
  ·
    refine ⟨47441037310476761018512373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126509432827938029382699661 47441037310476761018512373)
    ·
      refine ⟨4447597247857196345485535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47441037310476761018512373 4447597247857196345485535)
      ·
        refine ⟨6671395871785794518228303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447597247857196345485535 6671395871785794518228303)
        ·
          refine ⟨10007093807678691777342455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671395871785794518228303 10007093807678691777342455)
          ·
            refine ⟨15010640711518037666013683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10007093807678691777342455 15010640711518037666013683)
            ·
              refine ⟨22515961067277056499020525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15010640711518037666013683 22515961067277056499020525)
              ·
                refine ⟨8443485400228896187132697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22515961067277056499020525 8443485400228896187132697)
                ·
                  refine ⟨6332614050171672140349523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443485400228896187132697 6332614050171672140349523)
                  ·
                    refine ⟨9498921075257508210524285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6332614050171672140349523 9498921075257508210524285)
                    ·
                      refine ⟨3562095403221565578946607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9498921075257508210524285 3562095403221565578946607)
                      ·
                        rfl

theorem cell23_6937156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6937156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937156 prefixEnd_6937156 := by exact prefixLift 6937156
  have htrace : WordTrace (prefixWord ++ tailWord_6937156) baseStart_6937156 baseEnd_6937156 := by
    simpa [prefixWord, tailWord_6937156, baseEnd_6937156] using wordTrace_append hprefix tailTrace_6937156
  have hstable : (prefixWord ++ tailWord_6937156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937156).length < 2 ^ (prefixWord ++ tailWord_6937156).sum := by decide
  have hdescent : baseEnd_6937156 < baseStart_6937156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937162 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_6937162 : Nat := 118140960795 + 6937162 * 2 ^ 59
def prefixEnd_6937162 : Nat := 4983230072969 + 3 ^ 40 * 6937162 * 2
def baseEnd_6937162 : Nat := 3562098484105492555471579

theorem tailTrace_6937162 : CollatzResearch.WordTrace tailWord_6937162 prefixEnd_6937162 3562098484105492555471579 := by
  unfold tailWord_6937162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63254771123463580447529435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168679389662569547860078493 63254771123463580447529435)
  ·
    refine ⟨94882156685195370671294153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63254771123463580447529435 94882156685195370671294153)
    ·
      refine ⟨71161617513896528003470615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94882156685195370671294153 71161617513896528003470615)
      ·
        refine ⟨106742426270844792005205923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71161617513896528003470615 106742426270844792005205923)
        ·
          refine ⟨160113639406267188007808885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106742426270844792005205923 160113639406267188007808885)
          ·
            refine ⟨15010653694337548875732083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160113639406267188007808885 15010653694337548875732083)
            ·
              refine ⟨22515980541506323313598125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15010653694337548875732083 22515980541506323313598125)
              ·
                refine ⟨8443492703064871242599297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22515980541506323313598125 8443492703064871242599297)
                ·
                  refine ⟨6332619527298653431949473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8443492703064871242599297 6332619527298653431949473)
                  ·
                    refine ⟨4749464645473990073962105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332619527298653431949473 4749464645473990073962105)
                    ·
                      refine ⟨3562098484105492555471579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4749464645473990073962105 3562098484105492555471579)
                      ·
                        rfl

theorem cell23_6937162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_6937162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937162 prefixEnd_6937162 := by exact prefixLift 6937162
  have htrace : WordTrace (prefixWord ++ tailWord_6937162) baseStart_6937162 baseEnd_6937162 := by
    simpa [prefixWord, tailWord_6937162, baseEnd_6937162] using wordTrace_append hprefix tailTrace_6937162
  have hstable : (prefixWord ++ tailWord_6937162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937162).length < 2 ^ (prefixWord ++ tailWord_6937162).sum := by decide
  have hdescent : baseEnd_6937162 < baseStart_6937162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937201 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_6937201 : Nat := 118140960795 + 6937201 * 2 ^ 59
def prefixEnd_6937201 : Nat := 4983230072969 + 3 ^ 40 * 6937201 * 2
def baseEnd_6937201 : Nat := 3562118509851017902883899

theorem tailTrace_6937201 : CollatzResearch.WordTrace tailWord_6937201 prefixEnd_6937201 3562118509851017902883899 := by
  unfold tailWord_6937201
  simp only [CollatzResearch.WordTrace]
  refine ⟨253020506940713031450787457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168680337960475354300524971 253020506940713031450787457)
  ·
    refine ⟨189765380205534773588090593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253020506940713031450787457 189765380205534773588090593)
    ·
      refine ⟨142324035154151080191067945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189765380205534773588090593 142324035154151080191067945)
      ·
        refine ⟨106743026365613310143300959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142324035154151080191067945 106743026365613310143300959)
        ·
          refine ⟨160114539548419965214951439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106743026365613310143300959 160114539548419965214951439)
          ·
            refine ⟨240171809322629947822427159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160114539548419965214951439 240171809322629947822427159)
            ·
              refine ⟨360257713983944921733640739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240171809322629947822427159 360257713983944921733640739)
              ·
                refine ⟨540386570975917382600461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360257713983944921733640739 540386570975917382600461109)
                ·
                  refine ⟨50661241028992254618793229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540386570975917382600461109 50661241028992254618793229)
                  ·
                    refine ⟨18997965385872095482047461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50661241028992254618793229 18997965385872095482047461)
                    ·
                      refine ⟨3562118509851017902883899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18997965385872095482047461 3562118509851017902883899)
                      ·
                        rfl

theorem cell23_6937201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_6937201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937201 prefixEnd_6937201 := by exact prefixLift 6937201
  have htrace : WordTrace (prefixWord ++ tailWord_6937201) baseStart_6937201 baseEnd_6937201 := by
    simpa [prefixWord, tailWord_6937201, baseEnd_6937201] using wordTrace_append hprefix tailTrace_6937201
  have hstable : (prefixWord ++ tailWord_6937201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937201).length < 2 ^ (prefixWord ++ tailWord_6937201).sum := by decide
  have hdescent : baseEnd_6937201 < baseStart_6937201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937231 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_6937231 : Nat := 118140960795 + 6937231 * 2 ^ 59
def prefixEnd_6937231 : Nat := 4983230072969 + 3 ^ 40 * 6937231 * 2
def baseEnd_6937231 : Nat := 3562133914270652785508761

theorem tailTrace_6937231 : CollatzResearch.WordTrace tailWord_6937231 prefixEnd_6937231 3562133914270652785508761 := by
  unfold tailWord_6937231
  simp only [CollatzResearch.WordTrace]
  refine ⟨253021601130604346574379547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168681067420402897716253031 253021601130604346574379547)
  ·
    refine ⟨379532401695906519861569321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253021601130604346574379547 379532401695906519861569321)
    ·
      refine ⟨284649301271929889896176991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379532401695906519861569321 284649301271929889896176991)
      ·
        refine ⟨426973951907894834844265487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284649301271929889896176991 426973951907894834844265487)
        ·
          refine ⟨640460927861842252266398231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426973951907894834844265487 640460927861842252266398231)
          ·
            refine ⟨960691391792763378399597347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640460927861842252266398231 960691391792763378399597347)
            ·
              refine ⟨1441037087689145067599396021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960691391792763378399597347 1441037087689145067599396021)
              ·
                refine ⟨135097226970857350087443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441037087689145067599396021 135097226970857350087443377)
                ·
                  refine ⟨101322920228143012565582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135097226970857350087443377 101322920228143012565582533)
                  ·
                    refine ⟨18998047542776814856046725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101322920228143012565582533 18998047542776814856046725)
                    ·
                      refine ⟨3562133914270652785508761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18998047542776814856046725 3562133914270652785508761)
                      ·
                        rfl

theorem cell23_6937231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_6937231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937231 prefixEnd_6937231 := by exact prefixLift 6937231
  have htrace : WordTrace (prefixWord ++ tailWord_6937231) baseStart_6937231 baseEnd_6937231 := by
    simpa [prefixWord, tailWord_6937231, baseEnd_6937231] using wordTrace_append hprefix tailTrace_6937231
  have hstable : (prefixWord ++ tailWord_6937231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937231).length < 2 ^ (prefixWord ++ tailWord_6937231).sum := by decide
  have hdescent : baseEnd_6937231 < baseStart_6937231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937241 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 8]
def baseStart_6937241 : Nat := 118140960795 + 6937241 * 2 ^ 59
def prefixEnd_6937241 : Nat := 4983230072969 + 3 ^ 40 * 6937241 * 2
def baseEnd_6937241 : Nat := 395793227675244194042635

theorem tailTrace_6937241 : CollatzResearch.WordTrace tailWord_6937241 prefixEnd_6937241 395793227675244194042635 := by
  unfold tailWord_6937241
  simp only [CollatzResearch.WordTrace]
  refine ⟨253021965860568118282243577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168681310573712078854829051 253021965860568118282243577)
  ·
    refine ⟨189766474395426088711682683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253021965860568118282243577 189766474395426088711682683)
    ·
      refine ⟨284649711593139133067524025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189766474395426088711682683 284649711593139133067524025)
      ·
        refine ⟨213487283694854349800643019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284649711593139133067524025 213487283694854349800643019)
        ·
          refine ⟨320230925542281524700964529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213487283694854349800643019 320230925542281524700964529)
          ·
            refine ⟨240173194156711143525723397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320230925542281524700964529 240173194156711143525723397)
            ·
              refine ⟨45032473904383339411073137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240173194156711143525723397 45032473904383339411073137)
              ·
                refine ⟨33774355428287504558304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45032473904383339411073137 33774355428287504558304853)
                ·
                  refine ⟨395793227675244194042635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33774355428287504558304853 395793227675244194042635)
                  ·
                    rfl

theorem cell23_6937241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_6937241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937241 prefixEnd_6937241 := by exact prefixLift 6937241
  have htrace : WordTrace (prefixWord ++ tailWord_6937241) baseStart_6937241 baseEnd_6937241 := by
    simpa [prefixWord, tailWord_6937241, baseEnd_6937241] using wordTrace_append hprefix tailTrace_6937241
  have hstable : (prefixWord ++ tailWord_6937241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937241).length < 2 ^ (prefixWord ++ tailWord_6937241).sum := by decide
  have hdescent : baseEnd_6937241 < baseStart_6937241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937262 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6937262 : Nat := 118140960795 + 6937262 * 2 ^ 59
def prefixEnd_6937262 : Nat := 4983230072969 + 3 ^ 40 * 6937262 * 2
def baseEnd_6937262 : Nat := 1187383277390314054740373

theorem tailTrace_6937262 : CollatzResearch.WordTrace tailWord_6937262 prefixEnd_6937262 1187383277390314054740373 := by
  unfold tailWord_6937262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31627841474186504858594755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168681821195661359245838693 31627841474186504858594755)
  ·
    refine ⟨47441762211279757287892133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31627841474186504858594755 47441762211279757287892133)
    ·
      refine ⟨8895330414614954491479775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47441762211279757287892133 8895330414614954491479775)
      ·
        refine ⟨13342995621922431737219663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895330414614954491479775 13342995621922431737219663)
        ·
          refine ⟨20014493432883647605829495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13342995621922431737219663 20014493432883647605829495)
          ·
            refine ⟨30021740149325471408744243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20014493432883647605829495 30021740149325471408744243)
            ·
              refine ⟨45032610223988207113116365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30021740149325471408744243 45032610223988207113116365)
              ·
                refine ⟨16887228833995577667418637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45032610223988207113116365 16887228833995577667418637)
                ·
                  refine ⟨6332710812748341625281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16887228833995577667418637 6332710812748341625281989)
                  ·
                    refine ⟨1187383277390314054740373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332710812748341625281989 1187383277390314054740373)
                    ·
                      rfl

theorem cell23_6937262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6937262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937262 prefixEnd_6937262 := by exact prefixLift 6937262
  have htrace : WordTrace (prefixWord ++ tailWord_6937262) baseStart_6937262 baseEnd_6937262 := by
    simpa [prefixWord, tailWord_6937262, baseEnd_6937262] using wordTrace_append hprefix tailTrace_6937262
  have hstable : (prefixWord ++ tailWord_6937262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937262).length < 2 ^ (prefixWord ++ tailWord_6937262).sum := by decide
  have hdescent : baseEnd_6937262 < baseStart_6937262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937278 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6937278 : Nat := 118140960795 + 6937278 * 2 ^ 59
def prefixEnd_6937278 : Nat := 4983230072969 + 3 ^ 40 * 6937278 * 2
def baseEnd_6937278 : Nat := 3562158047861414101621045

theorem tailTrace_6937278 : CollatzResearch.WordTrace tailWord_6937278 prefixEnd_6937278 3562158047861414101621045 := by
  unfold tailWord_6937278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31627914420179259200167561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168682210240956049067560325 31627914420179259200167561)
  ·
    refine ⟨23720935815134444400125671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31627914420179259200167561 23720935815134444400125671)
    ·
      refine ⟨35581403722701666600188507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23720935815134444400125671 35581403722701666600188507)
      ·
        refine ⟨53372105584052499900282761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35581403722701666600188507 53372105584052499900282761)
        ·
          refine ⟨40029079188039374925212071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53372105584052499900282761 40029079188039374925212071)
          ·
            refine ⟨60043618782059062387818107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40029079188039374925212071 60043618782059062387818107)
            ·
              refine ⟨90065428173088593581727161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60043618782059062387818107 90065428173088593581727161)
              ·
                refine ⟨67549071129816445186295371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90065428173088593581727161 67549071129816445186295371)
                ·
                  refine ⟨101323606694724667779443057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67549071129816445186295371 101323606694724667779443057)
                  ·
                    refine ⟨75992705021043500834582293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101323606694724667779443057 75992705021043500834582293)
                    ·
                      refine ⟨3562158047861414101621045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75992705021043500834582293 3562158047861414101621045)
                      ·
                        rfl

theorem cell23_6937278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6937278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937278 prefixEnd_6937278 := by exact prefixLift 6937278
  have htrace : WordTrace (prefixWord ++ tailWord_6937278) baseStart_6937278 baseEnd_6937278 := by
    simpa [prefixWord, tailWord_6937278, baseEnd_6937278] using wordTrace_append hprefix tailTrace_6937278
  have hstable : (prefixWord ++ tailWord_6937278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937278).length < 2 ^ (prefixWord ++ tailWord_6937278).sum := by decide
  have hdescent : baseEnd_6937278 < baseStart_6937278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937325 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6937325 : Nat := 118140960795 + 6937325 * 2 ^ 59
def prefixEnd_6937325 : Nat := 4983230072969 + 3 ^ 40 * 6937325 * 2
def baseEnd_6937325 : Nat := 3562182181452175417733329

theorem tailTrace_6937325 : CollatzResearch.WordTrace tailWord_6937325 prefixEnd_6937325 3562182181452175417733329 := by
  unfold tailWord_6937325
  simp only [CollatzResearch.WordTrace]
  refine ⟨253025029592263800628301429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168683353061509200418867619 253025029592263800628301429)
  ·
    refine ⟨23721096524274731308903259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253025029592263800628301429 23721096524274731308903259)
    ·
      refine ⟨35581644786412096963354889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721096524274731308903259 35581644786412096963354889)
      ·
        refine ⟨26686233589809072722516167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35581644786412096963354889 26686233589809072722516167)
        ·
          refine ⟨40029350384713609083774251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26686233589809072722516167 40029350384713609083774251)
          ·
            refine ⟨60044025577070413625661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40029350384713609083774251 60044025577070413625661377)
            ·
              refine ⟨45033019182802810219246033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60044025577070413625661377 45033019182802810219246033)
              ·
                refine ⟨33774764387102107664434525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45033019182802810219246033 33774764387102107664434525)
                ·
                  refine ⟨12665536645163290374162947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33774764387102107664434525 12665536645163290374162947)
                  ·
                    refine ⟨18998304967744935561244421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12665536645163290374162947 18998304967744935561244421)
                    ·
                      refine ⟨3562182181452175417733329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18998304967744935561244421 3562182181452175417733329)
                      ·
                        rfl

theorem cell23_6937325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6937325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937325 prefixEnd_6937325 := by exact prefixLift 6937325
  have htrace : WordTrace (prefixWord ++ tailWord_6937325) baseStart_6937325 baseEnd_6937325 := by
    simpa [prefixWord, tailWord_6937325, baseEnd_6937325] using wordTrace_append hprefix tailTrace_6937325
  have hstable : (prefixWord ++ tailWord_6937325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937325).length < 2 ^ (prefixWord ++ tailWord_6937325).sum := by decide
  have hdescent : baseEnd_6937325 < baseStart_6937325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
