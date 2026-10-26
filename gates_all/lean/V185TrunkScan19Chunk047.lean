import V185TrunkScan19Chunk046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_471931 : List Nat := [1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_471931 : Nat := 118140960795 + 471931 * 2 ^ 59
def prefixEnd_471931 : Nat := 4983230072969 + 3 ^ 40 * 471931 * 2
def baseEnd_471931 : Nat := 143601445189391586069413

theorem tailTrace_471931 : CollatzResearch.WordTrace tailWord_471931 prefixEnd_471931 143601445189391586069413 := by
  unfold tailWord_471931
  simp only [CollatzResearch.WordTrace]
  refine ⟨17212737653282061243063647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11475158435521374162042431 17212737653282061243063647)
  ·
    refine ⟨25819106479923091864595471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17212737653282061243063647 25819106479923091864595471)
    ·
      refine ⟨38728659719884637796893207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25819106479923091864595471 38728659719884637796893207)
      ·
        refine ⟨58092989579826956695339811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38728659719884637796893207 58092989579826956695339811)
        ·
          refine ⟨87139484369740435043009717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58092989579826956695339811 87139484369740435043009717)
          ·
            refine ⟨8169326659663165785282161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87139484369740435043009717 8169326659663165785282161)
            ·
              refine ⟨6126994994747374338961621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8169326659663165785282161 6126994994747374338961621)
              ·
                refine ⟨143601445189391586069413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6126994994747374338961621 143601445189391586069413)
                ·
                  rfl

theorem cell19_471931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_471931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471931 prefixEnd_471931 := by exact prefixLift 471931
  have htrace : WordTrace (prefixWord ++ tailWord_471931) baseStart_471931 baseEnd_471931 := by
    simpa [prefixWord, tailWord_471931, baseEnd_471931] using wordTrace_append hprefix tailTrace_471931
  have hstable : (prefixWord ++ tailWord_471931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471931).length < 2 ^ (prefixWord ++ tailWord_471931).sum := by decide
  have hdescent : baseEnd_471931 < baseStart_471931 := by decide
  rcases family_descends (prefixWord ++ tailWord_471931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472007 : List Nat := [1, 1, 4, 1, 1, 2, 9]
def baseStart_472007 : Nat := 118140960795 + 472007 * 2 ^ 59
def prefixEnd_472007 : Nat := 4983230072969 + 3 ^ 40 * 472007 * 2
def baseEnd_472007 : Nat := 47874856945548642793439

theorem tailTrace_472007 : CollatzResearch.WordTrace tailWord_472007 prefixEnd_472007 47874856945548642793439 := by
  unfold tailWord_472007
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215509601006726222830275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11477006400671150815220183 17215509601006726222830275)
  ·
    refine ⟨25823264401510089334245413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17215509601006726222830275 25823264401510089334245413)
    ·
      refine ⟨4841862075283141750171015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25823264401510089334245413 4841862075283141750171015)
      ·
        refine ⟨7262793112924712625256523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841862075283141750171015 7262793112924712625256523)
        ·
          refine ⟨10894189669387068937884785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262793112924712625256523 10894189669387068937884785)
          ·
            refine ⟨8170642252040301703413589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10894189669387068937884785 8170642252040301703413589)
            ·
              refine ⟨47874856945548642793439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8170642252040301703413589 47874856945548642793439)
              ·
                rfl

theorem cell19_472007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_472007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472007 prefixEnd_472007 := by exact prefixLift 472007
  have htrace : WordTrace (prefixWord ++ tailWord_472007) baseStart_472007 baseEnd_472007 := by
    simpa [prefixWord, tailWord_472007, baseEnd_472007] using wordTrace_append hprefix tailTrace_472007
  have hstable : (prefixWord ++ tailWord_472007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472007).length < 2 ^ (prefixWord ++ tailWord_472007).sum := by decide
  have hdescent : baseEnd_472007 < baseStart_472007 := by decide
  rcases family_descends (prefixWord ++ tailWord_472007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472022 : List Nat := [5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_472022 : Nat := 118140960795 + 472022 * 2 ^ 59
def prefixEnd_472022 : Nat := 4983230072969 + 3 ^ 40 * 472022 * 2
def baseEnd_472022 : Nat := 143629135109130338046943

theorem tailTrace_472022 : CollatzResearch.WordTrace tailWord_472022 prefixEnd_472022 143629135109130338046943 := by
  unfold tailWord_472022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076003543497023986539145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11477371130634922523084213 1076003543497023986539145)
  ·
    refine ⟨807002657622767989904359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076003543497023986539145 807002657622767989904359)
    ·
      refine ⟨1210503986434151984856539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807002657622767989904359 1210503986434151984856539)
      ·
        refine ⟨1815755979651227977284809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210503986434151984856539 1815755979651227977284809)
        ·
          refine ⟨1361816984738420982963607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1815755979651227977284809 1361816984738420982963607)
          ·
            refine ⟨2042725477107631474445411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361816984738420982963607 2042725477107631474445411)
            ·
              refine ⟨3064088215661447211668117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042725477107631474445411 3064088215661447211668117)
              ·
                refine ⟨143629135109130338046943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3064088215661447211668117 143629135109130338046943)
                ·
                  rfl

theorem cell19_472022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_472022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472022 prefixEnd_472022 := by exact prefixLift 472022
  have htrace : WordTrace (prefixWord ++ tailWord_472022) baseStart_472022 baseEnd_472022 := by
    simpa [prefixWord, tailWord_472022, baseEnd_472022] using wordTrace_append hprefix tailTrace_472022
  have hstable : (prefixWord ++ tailWord_472022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472022).length < 2 ^ (prefixWord ++ tailWord_472022).sum := by decide
  have hdescent : baseEnd_472022 < baseStart_472022 := by decide
  rcases family_descends (prefixWord ++ tailWord_472022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472024 : List Nat := [2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_472024 : Nat := 118140960795 + 472024 * 2 ^ 59
def prefixEnd_472024 : Nat := 4983230072969 + 3 ^ 40 * 472024 * 2
def baseEnd_472024 : Nat := 143629743678794926002493

theorem tailTrace_472024 : CollatzResearch.WordTrace tailWord_472024 prefixEnd_472024 143629743678794926002493 := by
  unfold tailWord_472024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608064820972569063099563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11477419761296758750799417 8608064820972569063099563)
  ·
    refine ⟨12912097231458853594649345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8608064820972569063099563 12912097231458853594649345)
    ·
      refine ⟨9684072923594140195987009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12912097231458853594649345 9684072923594140195987009)
      ·
        refine ⟨7263054692695605146990257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9684072923594140195987009 7263054692695605146990257)
        ·
          refine ⟨5447291019521703860242693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263054692695605146990257 5447291019521703860242693)
          ·
            refine ⟨1021367066160319473795505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5447291019521703860242693 1021367066160319473795505)
            ·
              refine ⟨766025299620239605346629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021367066160319473795505 766025299620239605346629)
              ·
                refine ⟨143629743678794926002493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 766025299620239605346629 143629743678794926002493)
                ·
                  rfl

theorem cell19_472024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_472024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472024 prefixEnd_472024 := by exact prefixLift 472024
  have htrace : WordTrace (prefixWord ++ tailWord_472024) baseStart_472024 baseEnd_472024 := by
    simpa [prefixWord, tailWord_472024, baseEnd_472024] using wordTrace_append hprefix tailTrace_472024
  have hstable : (prefixWord ++ tailWord_472024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472024).length < 2 ^ (prefixWord ++ tailWord_472024).sum := by decide
  have hdescent : baseEnd_472024 < baseStart_472024 := by decide
  rcases family_descends (prefixWord ++ tailWord_472024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472062 : List Nat := [4, 2, 2, 2, 9]
def baseStart_472062 : Nat := 118140960795 + 472062 * 2 ^ 59
def prefixEnd_472062 : Nat := 4983230072969 + 3 ^ 40 * 472062 * 2
def baseEnd_472062 : Nat := 5320048388978596191035

theorem tailTrace_472062 : CollatzResearch.WordTrace tailWord_472062 prefixEnd_472062 5320048388978596191035 := by
  unfold tailWord_472062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152189451975933827010305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11478343743871647077388293 2152189451975933827010305)
  ·
    refine ⟨1614142088981950370257729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2152189451975933827010305 1614142088981950370257729)
    ·
      refine ⟨1210606566736462777693297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614142088981950370257729 1210606566736462777693297)
      ·
        refine ⟨907954925052347083269973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1210606566736462777693297 907954925052347083269973)
        ·
          refine ⟨5320048388978596191035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 907954925052347083269973 5320048388978596191035)
          ·
            rfl

theorem cell19_472062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_472062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472062 prefixEnd_472062 := by exact prefixLift 472062
  have htrace : WordTrace (prefixWord ++ tailWord_472062) baseStart_472062 baseEnd_472062 := by
    simpa [prefixWord, tailWord_472062, baseEnd_472062] using wordTrace_append hprefix tailTrace_472062
  have hstable : (prefixWord ++ tailWord_472062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472062).length < 2 ^ (prefixWord ++ tailWord_472062).sum := by decide
  have hdescent : baseEnd_472062 < baseStart_472062 := by decide
  rcases family_descends (prefixWord ++ tailWord_472062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472096 : List Nat := [2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_472096 : Nat := 118140960795 + 472096 * 2 ^ 59
def prefixEnd_472096 : Nat := 4983230072969 + 3 ^ 40 * 472096 * 2
def baseEnd_472096 : Nat := 143651652186720092402297

theorem tailTrace_472096 : CollatzResearch.WordTrace tailWord_472096 prefixEnd_472096 143651652186720092402297 := by
  unfold tailWord_472096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609377848842147211410071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11479170465122862948546761 8609377848842147211410071)
  ·
    refine ⟨12914066773263220817115107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609377848842147211410071 12914066773263220817115107)
    ·
      refine ⟨19371100159894831225672661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914066773263220817115107 19371100159894831225672661)
      ·
        refine ⟨454010159997535106851703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19371100159894831225672661 454010159997535106851703)
        ·
          refine ⟨681015239996302660277555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454010159997535106851703 681015239996302660277555)
          ·
            refine ⟨1021522859994453990416333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681015239996302660277555 1021522859994453990416333)
            ·
              refine ⟨383071072497920246406125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021522859994453990416333 383071072497920246406125)
              ·
                refine ⟨143651652186720092402297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383071072497920246406125 143651652186720092402297)
                ·
                  rfl

theorem cell19_472096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_472096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472096 prefixEnd_472096 := by exact prefixLift 472096
  have htrace : WordTrace (prefixWord ++ tailWord_472096) baseStart_472096 baseEnd_472096 := by
    simpa [prefixWord, tailWord_472096, baseEnd_472096] using wordTrace_append hprefix tailTrace_472096
  have hstable : (prefixWord ++ tailWord_472096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472096).length < 2 ^ (prefixWord ++ tailWord_472096).sum := by decide
  have hdescent : baseEnd_472096 < baseStart_472096 := by decide
  rcases family_descends (prefixWord ++ tailWord_472096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472098 : List Nat := [3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_472098 : Nat := 118140960795 + 472098 * 2 ^ 59
def prefixEnd_472098 : Nat := 4983230072969 + 3 ^ 40 * 472098 * 2
def baseEnd_472098 : Nat := 143652260756384680357847

theorem tailTrace_472098 : CollatzResearch.WordTrace tailWord_472098 prefixEnd_472098 143652260756384680357847 := by
  unfold tailWord_472098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304707160919262191098237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11479219095784699176261965 4304707160919262191098237)
  ·
    refine ⟨1614265185344723321661839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4304707160919262191098237 1614265185344723321661839)
    ·
      refine ⟨2421397778017084982492759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614265185344723321661839 2421397778017084982492759)
      ·
        refine ⟨3632096667025627473739139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421397778017084982492759 3632096667025627473739139)
        ·
          refine ⟨5448145000538441210608709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632096667025627473739139 5448145000538441210608709)
          ·
            refine ⟨1021527187600957726989133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5448145000538441210608709 1021527187600957726989133)
            ·
              refine ⟨383072695350359147620925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021527187600957726989133 383072695350359147620925)
              ·
                refine ⟨143652260756384680357847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383072695350359147620925 143652260756384680357847)
                ·
                  rfl

theorem cell19_472098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_472098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472098 prefixEnd_472098 := by exact prefixLift 472098
  have htrace : WordTrace (prefixWord ++ tailWord_472098) baseStart_472098 baseEnd_472098 := by
    simpa [prefixWord, tailWord_472098, baseEnd_472098] using wordTrace_append hprefix tailTrace_472098
  have hstable : (prefixWord ++ tailWord_472098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472098).length < 2 ^ (prefixWord ++ tailWord_472098).sum := by decide
  have hdescent : baseEnd_472098 < baseStart_472098 := by decide
  rcases family_descends (prefixWord ++ tailWord_472098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472140 : List Nat := [2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_472140 : Nat := 118140960795 + 472140 * 2 ^ 59
def prefixEnd_472140 : Nat := 4983230072969 + 3 ^ 40 * 472140 * 2
def baseEnd_472140 : Nat := 143665040719341027424399

theorem tailTrace_472140 : CollatzResearch.WordTrace tailWord_472140 prefixEnd_472140 143665040719341027424399 := by
  unfold tailWord_472140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610180254762444968710937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11480240339683259958281249 8610180254762444968710937)
  ·
    refine ⟨6457635191071833726533203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8610180254762444968710937 6457635191071833726533203)
    ·
      refine ⟨9686452786607750589799805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457635191071833726533203 9686452786607750589799805)
      ·
        refine ⟨3632419794977906471174927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9686452786607750589799805 3632419794977906471174927)
        ·
          refine ⟨5448629692466859706762391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632419794977906471174927 5448629692466859706762391)
          ·
            refine ⟨8172944538700289560143587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448629692466859706762391 8172944538700289560143587)
            ·
              refine ⟨12259416808050434340215381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8172944538700289560143587 12259416808050434340215381)
              ·
                refine ⟨143665040719341027424399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12259416808050434340215381 143665040719341027424399)
                ·
                  rfl

theorem cell19_472140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_472140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472140 prefixEnd_472140 := by exact prefixLift 472140
  have htrace : WordTrace (prefixWord ++ tailWord_472140) baseStart_472140 baseEnd_472140 := by
    simpa [prefixWord, tailWord_472140, baseEnd_472140] using wordTrace_append hprefix tailTrace_472140
  have hstable : (prefixWord ++ tailWord_472140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472140).length < 2 ^ (prefixWord ++ tailWord_472140).sum := by decide
  have hdescent : baseEnd_472140 < baseStart_472140 := by decide
  rcases family_descends (prefixWord ++ tailWord_472140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472159 : List Nat := [1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_472159 : Nat := 118140960795 + 472159 * 2 ^ 59
def prefixEnd_472159 : Nat := 4983230072969 + 3 ^ 40 * 472159 * 2
def baseEnd_472159 : Nat := 143670822131154613002125

theorem tailTrace_472159 : CollatzResearch.WordTrace tailWord_472159 prefixEnd_472159 143670822131154613002125 := by
  unfold tailWord_472159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221053496456056182363531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11480702330970704121575687 17221053496456056182363531)
  ·
    refine ⟨25831580244684084273545297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17221053496456056182363531 25831580244684084273545297)
    ·
      refine ⟨19373685183513063205158973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25831580244684084273545297 19373685183513063205158973)
      ·
        refine ⟨7265131943817398701934615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19373685183513063205158973 7265131943817398701934615)
        ·
          refine ⟨10897697915726098052901923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265131943817398701934615 10897697915726098052901923)
          ·
            refine ⟨16346546873589147079352885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897697915726098052901923 16346546873589147079352885)
            ·
              refine ⟨1532488769398982538689333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16346546873589147079352885 1532488769398982538689333)
              ·
                refine ⟨143670822131154613002125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1532488769398982538689333 143670822131154613002125)
                ·
                  rfl

theorem cell19_472159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_472159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472159 prefixEnd_472159 := by exact prefixLift 472159
  have htrace : WordTrace (prefixWord ++ tailWord_472159) baseStart_472159 baseEnd_472159 := by
    simpa [prefixWord, tailWord_472159, baseEnd_472159] using wordTrace_append hprefix tailTrace_472159
  have hstable : (prefixWord ++ tailWord_472159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472159).length < 2 ^ (prefixWord ++ tailWord_472159).sum := by decide
  have hdescent : baseEnd_472159 < baseStart_472159 := by decide
  rcases family_descends (prefixWord ++ tailWord_472159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472246 : List Nat := [5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_472246 : Nat := 118140960795 + 472246 * 2 ^ 59
def prefixEnd_472246 : Nat := 4983230072969 + 3 ^ 40 * 472246 * 2
def baseEnd_472246 : Nat := 143697294911564189068555

theorem tailTrace_472246 : CollatzResearch.WordTrace tailWord_472246 prefixEnd_472246 143697294911564189068555 := by
  unfold tailWord_472246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076514165446304377548787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11482817764760580027187061 1076514165446304377548787)
  ·
    refine ⟨1614771248169456566323181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076514165446304377548787 1614771248169456566323181)
    ·
      refine ⟨605539218063546212371193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1614771248169456566323181 605539218063546212371193)
      ·
        refine ⟨454154413547659659278395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605539218063546212371193 454154413547659659278395)
        ·
          refine ⟨681231620321489488917593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454154413547659659278395 681231620321489488917593)
          ·
            refine ⟨510923715241117116688195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681231620321489488917593 510923715241117116688195)
            ·
              refine ⟨766385572861675675032293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510923715241117116688195 766385572861675675032293)
              ·
                refine ⟨143697294911564189068555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 766385572861675675032293 143697294911564189068555)
                ·
                  rfl

theorem cell19_472246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_472246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472246 prefixEnd_472246 := by exact prefixLift 472246
  have htrace : WordTrace (prefixWord ++ tailWord_472246) baseStart_472246 baseEnd_472246 := by
    simpa [prefixWord, tailWord_472246, baseEnd_472246] using wordTrace_append hprefix tailTrace_472246
  have hstable : (prefixWord ++ tailWord_472246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472246).length < 2 ^ (prefixWord ++ tailWord_472246).sum := by decide
  have hdescent : baseEnd_472246 < baseStart_472246 := by decide
  rcases family_descends (prefixWord ++ tailWord_472246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472252 : List Nat := [2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_472252 : Nat := 118140960795 + 472252 * 2 ^ 59
def prefixEnd_472252 : Nat := 4983230072969 + 3 ^ 40 * 472252 * 2
def baseEnd_472252 : Nat := 143699120620557952935205

theorem tailTrace_472252 : CollatzResearch.WordTrace tailWord_472252 prefixEnd_472252 143699120620557952935205 := by
  unfold tailWord_472252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612222742559566532749505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11482963656746088710332673 8612222742559566532749505)
  ·
    refine ⟨6459167056919674899562129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8612222742559566532749505 6459167056919674899562129)
    ·
      refine ⟨4844375292689756174671597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6459167056919674899562129 4844375292689756174671597)
      ·
        refine ⟨1816640734758658565501849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4844375292689756174671597 1816640734758658565501849)
        ·
          refine ⟨1362480551068993924126387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816640734758658565501849 1362480551068993924126387)
          ·
            refine ⟨2043720826603490886189581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362480551068993924126387 2043720826603490886189581)
            ·
              refine ⟨766395309976309082321093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2043720826603490886189581 766395309976309082321093)
              ·
                refine ⟨143699120620557952935205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 766395309976309082321093 143699120620557952935205)
                ·
                  rfl

theorem cell19_472252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_472252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472252 prefixEnd_472252 := by exact prefixLift 472252
  have htrace : WordTrace (prefixWord ++ tailWord_472252) baseStart_472252 baseEnd_472252 := by
    simpa [prefixWord, tailWord_472252, baseEnd_472252] using wordTrace_append hprefix tailTrace_472252
  have hstable : (prefixWord ++ tailWord_472252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472252).length < 2 ^ (prefixWord ++ tailWord_472252).sum := by decide
  have hdescent : baseEnd_472252 < baseStart_472252 := by decide
  rcases family_descends (prefixWord ++ tailWord_472252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472322 : List Nat := [3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_472322 : Nat := 118140960795 + 472322 * 2 ^ 59
def prefixEnd_472322 : Nat := 4983230072969 + 3 ^ 40 * 472322 * 2
def baseEnd_472322 : Nat := 143720420558818531379459

theorem tailTrace_472322 : CollatzResearch.WordTrace tailWord_472322 prefixEnd_472322 143720420558818531379459 := by
  unfold tailWord_472322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306749648716383755136805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11484665729910356680364813 4306749648716383755136805)
  ·
    refine ⟨807515559134321954088151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4306749648716383755136805 807515559134321954088151)
    ·
      refine ⟨1211273338701482931132227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807515559134321954088151 1211273338701482931132227)
      ·
        refine ⟨1816910008052224396698341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211273338701482931132227 1816910008052224396698341)
        ·
          refine ⟨340670626509792074380939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1816910008052224396698341 340670626509792074380939)
          ·
            refine ⟨511005939764688111571409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340670626509792074380939 511005939764688111571409)
            ·
              refine ⟨383254454823516083678557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511005939764688111571409 383254454823516083678557)
              ·
                refine ⟨143720420558818531379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383254454823516083678557 143720420558818531379459)
                ·
                  rfl

theorem cell19_472322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_472322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472322 prefixEnd_472322 := by exact prefixLift 472322
  have htrace : WordTrace (prefixWord ++ tailWord_472322) baseStart_472322 baseEnd_472322 := by
    simpa [prefixWord, tailWord_472322, baseEnd_472322] using wordTrace_append hprefix tailTrace_472322
  have hstable : (prefixWord ++ tailWord_472322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472322).length < 2 ^ (prefixWord ++ tailWord_472322).sum := by decide
  have hdescent : baseEnd_472322 < baseStart_472322 := by decide
  rcases family_descends (prefixWord ++ tailWord_472322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472328 : List Nat := [2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_472328 : Nat := 118140960795 + 472328 * 2 ^ 59
def prefixEnd_472328 : Nat := 4983230072969 + 3 ^ 40 * 472328 * 2
def baseEnd_472328 : Nat := 143722246267812295246109

theorem tailTrace_472328 : CollatzResearch.WordTrace tailWord_472328 prefixEnd_472328 143722246267812295246109 := by
  unfold tailWord_472328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613608716421899022632819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11484811621895865363510425 8613608716421899022632819)
  ·
    refine ⟨12920413074632848533949229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8613608716421899022632819 12920413074632848533949229)
    ·
      refine ⟨4845154902987318200230961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12920413074632848533949229 4845154902987318200230961)
      ·
        refine ⟨3633866177240488650173221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845154902987318200230961 3633866177240488650173221)
        ·
          refine ⟨681349908232591621907479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3633866177240488650173221 681349908232591621907479)
          ·
            refine ⟨1022024862348887432861219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681349908232591621907479 1022024862348887432861219)
            ·
              refine ⟨1533037293523331149291829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022024862348887432861219 1533037293523331149291829)
              ·
                refine ⟨143722246267812295246109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533037293523331149291829 143722246267812295246109)
                ·
                  rfl

theorem cell19_472328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_472328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472328 prefixEnd_472328 := by exact prefixLift 472328
  have htrace : WordTrace (prefixWord ++ tailWord_472328) baseStart_472328 baseEnd_472328 := by
    simpa [prefixWord, tailWord_472328, baseEnd_472328] using wordTrace_append hprefix tailTrace_472328
  have hstable : (prefixWord ++ tailWord_472328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472328).length < 2 ^ (prefixWord ++ tailWord_472328).sum := by decide
  have hdescent : baseEnd_472328 < baseStart_472328 := by decide
  rcases family_descends (prefixWord ++ tailWord_472328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472368 : List Nat := [2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_472368 : Nat := 118140960795 + 472368 * 2 ^ 59
def prefixEnd_472368 : Nat := 4983230072969 + 3 ^ 40 * 472368 * 2
def baseEnd_472368 : Nat := 143734417661104054357111

theorem tailTrace_472368 : CollatzResearch.WordTrace tailWord_472368 prefixEnd_472368 143734417661104054357111 := by
  unfold tailWord_472368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614338176349442438360879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11485784235132589917814505 8614338176349442438360879)
  ·
    refine ⟨12921507264524163657541319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8614338176349442438360879 12921507264524163657541319)
    ·
      refine ⟨19382260896786245486311979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921507264524163657541319 19382260896786245486311979)
      ·
        refine ⟨29073391345179368229467969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19382260896786245486311979 29073391345179368229467969)
        ·
          refine ⟨21805043508884526172100977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29073391345179368229467969 21805043508884526172100977)
          ·
            refine ⟨16353782631663394629075733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21805043508884526172100977 16353782631663394629075733)
            ·
              refine ⟨766583560859221623237925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16353782631663394629075733 766583560859221623237925)
              ·
                refine ⟨143734417661104054357111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 766583560859221623237925 143734417661104054357111)
                ·
                  rfl

theorem cell19_472368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_472368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472368 prefixEnd_472368 := by exact prefixLift 472368
  have htrace : WordTrace (prefixWord ++ tailWord_472368) baseStart_472368 baseEnd_472368 := by
    simpa [prefixWord, tailWord_472368, baseEnd_472368] using wordTrace_append hprefix tailTrace_472368
  have hstable : (prefixWord ++ tailWord_472368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472368).length < 2 ^ (prefixWord ++ tailWord_472368).sum := by decide
  have hdescent : baseEnd_472368 < baseStart_472368 := by decide
  rcases family_descends (prefixWord ++ tailWord_472368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472385 : List Nat := [1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_472385 : Nat := 118140960795 + 472385 * 2 ^ 59
def prefixEnd_472385 : Nat := 4983230072969 + 3 ^ 40 * 472385 * 2
def baseEnd_472385 : Nat := 143739590503253051979287

theorem tailTrace_472385 : CollatzResearch.WordTrace tailWord_472385 prefixEnd_472385 143739590503253051979287 := by
  unfold tailWord_472385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229296393637296780090609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11486197595758197853393739 17229296393637296780090609)
  ·
    refine ⟨12921972295227972585067957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17229296393637296780090609 12921972295227972585067957)
    ·
      refine ⟨1211434902677622429850121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12921972295227972585067957 1211434902677622429850121)
      ·
        refine ⟨908576177008216822387591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211434902677622429850121 908576177008216822387591)
        ·
          refine ⟨1362864265512325233581387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908576177008216822387591 1362864265512325233581387)
          ·
            refine ⟨2044296398268487850372081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362864265512325233581387 2044296398268487850372081)
            ·
              refine ⟨1533222298701365887779061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044296398268487850372081 1533222298701365887779061)
              ·
                refine ⟨143739590503253051979287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533222298701365887779061 143739590503253051979287)
                ·
                  rfl

theorem cell19_472385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_472385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472385 prefixEnd_472385 := by exact prefixLift 472385
  have htrace : WordTrace (prefixWord ++ tailWord_472385) baseStart_472385 baseEnd_472385 := by
    simpa [prefixWord, tailWord_472385, baseEnd_472385] using wordTrace_append hprefix tailTrace_472385
  have hstable : (prefixWord ++ tailWord_472385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472385).length < 2 ^ (prefixWord ++ tailWord_472385).sum := by decide
  have hdescent : baseEnd_472385 < baseStart_472385 := by decide
  rcases family_descends (prefixWord ++ tailWord_472385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472558 : List Nat := [4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_472558 : Nat := 118140960795 + 472558 * 2 ^ 59
def prefixEnd_472558 : Nat := 4983230072969 + 3 ^ 40 * 472558 * 2
def baseEnd_472558 : Nat := 143792231779239910134371

theorem tailTrace_472558 : CollatzResearch.WordTrace tailWord_472558 prefixEnd_472558 143792231779239910134371 := by
  unfold tailWord_472558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154450777751318415767291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11490404148007031550758885 2154450777751318415767291)
  ·
    refine ⟨3231676166626977623650937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154450777751318415767291 3231676166626977623650937)
    ·
      refine ⟨2423757124970233217738203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231676166626977623650937 2423757124970233217738203)
      ·
        refine ⟨3635635687455349826607305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423757124970233217738203 3635635687455349826607305)
        ·
          refine ⟨2726726765591512369955479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635635687455349826607305 2726726765591512369955479)
          ·
            refine ⟨4090090148387268554933219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726726765591512369955479 4090090148387268554933219)
            ·
              refine ⟨6135135222580902832399829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090090148387268554933219 6135135222580902832399829)
              ·
                refine ⟨143792231779239910134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6135135222580902832399829 143792231779239910134371)
                ·
                  rfl

theorem cell19_472558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_472558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472558 prefixEnd_472558 := by exact prefixLift 472558
  have htrace : WordTrace (prefixWord ++ tailWord_472558) baseStart_472558 baseEnd_472558 := by
    simpa [prefixWord, tailWord_472558, baseEnd_472558] using wordTrace_append hprefix tailTrace_472558
  have hstable : (prefixWord ++ tailWord_472558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472558).length < 2 ^ (prefixWord ++ tailWord_472558).sum := by decide
  have hdescent : baseEnd_472558 < baseStart_472558 := by decide
  rcases family_descends (prefixWord ++ tailWord_472558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472577 : List Nat := [1, 2, 4, 1, 4, 7]
def baseStart_472577 : Nat := 118140960795 + 472577 * 2 ^ 59
def prefixEnd_472577 : Nat := 4983230072969 + 3 ^ 40 * 472577 * 2
def baseEnd_472577 : Nat := 15977557021228166190233

theorem tailTrace_472577 : CollatzResearch.WordTrace tailWord_472577 prefixEnd_472577 15977557021228166190233 := by
  unfold tailWord_472577
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236299208941713571079985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11490866139294475714053323 17236299208941713571079985)
  ·
    refine ⟨12927224406706285178309989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17236299208941713571079985 12927224406706285178309989)
    ·
      refine ⟨2423854576257428470933123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12927224406706285178309989 2423854576257428470933123)
      ·
        refine ⟨3635781864386142706399685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423854576257428470933123 3635781864386142706399685)
        ·
          refine ⟨681709099572401757449941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3635781864386142706399685 681709099572401757449941)
          ·
            refine ⟨15977557021228166190233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 681709099572401757449941 15977557021228166190233)
            ·
              rfl

theorem cell19_472577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_472577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472577 prefixEnd_472577 := by exact prefixLift 472577
  have htrace : WordTrace (prefixWord ++ tailWord_472577) baseStart_472577 baseEnd_472577 := by
    simpa [prefixWord, tailWord_472577, baseEnd_472577] using wordTrace_append hprefix tailTrace_472577
  have hstable : (prefixWord ++ tailWord_472577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472577).length < 2 ^ (prefixWord ++ tailWord_472577).sum := by decide
  have hdescent : baseEnd_472577 < baseStart_472577 := by decide
  rcases family_descends (prefixWord ++ tailWord_472577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472655 : List Nat := [1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_472655 : Nat := 118140960795 + 472655 * 2 ^ 59
def prefixEnd_472655 : Nat := 4983230072969 + 3 ^ 40 * 472655 * 2
def baseEnd_472655 : Nat := 143821747407972425978551

theorem tailTrace_472655 : CollatzResearch.WordTrace tailWord_472655 prefixEnd_472655 143821747407972425978551 := by
  unfold tailWord_472655
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239144102659132892419419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11492762735106088594946279 17239144102659132892419419)
  ·
    refine ⟨25858716153988699338629129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17239144102659132892419419 25858716153988699338629129)
    ·
      refine ⟨19394037115491524503971847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25858716153988699338629129 19394037115491524503971847)
      ·
        refine ⟨29091055673237286755957771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19394037115491524503971847 29091055673237286755957771)
        ·
          refine ⟨43636583509855930133936657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29091055673237286755957771 43636583509855930133936657)
          ·
            refine ⟨32727437632391947600452493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43636583509855930133936657 32727437632391947600452493)
            ·
              refine ⟨12272789112146980350169685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32727437632391947600452493 12272789112146980350169685)
              ·
                refine ⟨143821747407972425978551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12272789112146980350169685 143821747407972425978551)
                ·
                  rfl

theorem cell19_472655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_472655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472655 prefixEnd_472655 := by exact prefixLift 472655
  have htrace : WordTrace (prefixWord ++ tailWord_472655) baseStart_472655 baseEnd_472655 := by
    simpa [prefixWord, tailWord_472655, baseEnd_472655] using wordTrace_append hprefix tailTrace_472655
  have hstable : (prefixWord ++ tailWord_472655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472655).length < 2 ^ (prefixWord ++ tailWord_472655).sum := by decide
  have hdescent : baseEnd_472655 < baseStart_472655 := by decide
  rcases family_descends (prefixWord ++ tailWord_472655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472662 : List Nat := [5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_472662 : Nat := 118140960795 + 472662 * 2 ^ 59
def prefixEnd_472662 : Nat := 4983230072969 + 3 ^ 40 * 472662 * 2
def baseEnd_472662 : Nat := 143823877401798483822977

theorem tailTrace_472662 : CollatzResearch.WordTrace tailWord_472662 prefixEnd_472662 143823877401798483822977 := by
  unfold tailWord_472662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077462463352110817995265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11492932942422515391949493 1077462463352110817995265)
  ·
    refine ⟨808096847514083113496449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1077462463352110817995265 808096847514083113496449)
    ·
      refine ⟨606072635635562335122337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 808096847514083113496449 606072635635562335122337)
      ·
        refine ⟨454554476726671751341753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606072635635562335122337 454554476726671751341753)
        ·
          refine ⟨340915857545003813506315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454554476726671751341753 340915857545003813506315)
          ·
            refine ⟨511373786317505720259473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340915857545003813506315 511373786317505720259473)
            ·
              refine ⟨383530339738129290194605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511373786317505720259473 383530339738129290194605)
              ·
                refine ⟨143823877401798483822977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383530339738129290194605 143823877401798483822977)
                ·
                  rfl

theorem cell19_472662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_472662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472662 prefixEnd_472662 := by exact prefixLift 472662
  have htrace : WordTrace (prefixWord ++ tailWord_472662) baseStart_472662 baseEnd_472662 := by
    simpa [prefixWord, tailWord_472662, baseEnd_472662] using wordTrace_append hprefix tailTrace_472662
  have hstable : (prefixWord ++ tailWord_472662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472662).length < 2 ^ (prefixWord ++ tailWord_472662).sum := by decide
  have hdescent : baseEnd_472662 < baseStart_472662 := by decide
  rcases family_descends (prefixWord ++ tailWord_472662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472668 : List Nat := [2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_472668 : Nat := 118140960795 + 472668 * 2 ^ 59
def prefixEnd_472668 : Nat := 4983230072969 + 3 ^ 40 * 472668 * 2
def baseEnd_472668 : Nat := 143825703110792247689627

theorem tailTrace_472668 : CollatzResearch.WordTrace tailWord_472668 prefixEnd_472668 143825703110792247689627 := by
  unfold tailWord_472668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619809125806018056321329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11493078834408024075095105 8619809125806018056321329)
  ·
    refine ⟨6464856844354513542240997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8619809125806018056321329 6464856844354513542240997)
    ·
      refine ⟨1212160658316471289170187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6464856844354513542240997 1212160658316471289170187)
      ·
        refine ⟨1818240987474706933755281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212160658316471289170187 1818240987474706933755281)
        ·
          refine ⟨1363680740606030200316461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818240987474706933755281 1363680740606030200316461)
          ·
            refine ⟨511380277727261325118673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363680740606030200316461 511380277727261325118673)
            ·
              refine ⟨383535208295445993839005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511380277727261325118673 383535208295445993839005)
              ·
                refine ⟨143825703110792247689627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383535208295445993839005 143825703110792247689627)
                ·
                  rfl

theorem cell19_472668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_472668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472668 prefixEnd_472668 := by exact prefixLift 472668
  have htrace : WordTrace (prefixWord ++ tailWord_472668) baseStart_472668 baseEnd_472668 := by
    simpa [prefixWord, tailWord_472668, baseEnd_472668] using wordTrace_append hprefix tailTrace_472668
  have hstable : (prefixWord ++ tailWord_472668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472668).length < 2 ^ (prefixWord ++ tailWord_472668).sum := by decide
  have hdescent : baseEnd_472668 < baseStart_472668 := by decide
  rcases family_descends (prefixWord ++ tailWord_472668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472708 : List Nat := [2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_472708 : Nat := 118140960795 + 472708 * 2 ^ 59
def prefixEnd_472708 : Nat := 4983230072969 + 3 ^ 40 * 472708 * 2
def baseEnd_472708 : Nat := 143837874504084006800629

theorem tailTrace_472708 : CollatzResearch.WordTrace tailWord_472708 prefixEnd_472708 143837874504084006800629 := by
  unfold tailWord_472708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620538585733561472049389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11494051447644748629399185 8620538585733561472049389)
  ·
    refine ⟨3232701969650085552018521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8620538585733561472049389 3232701969650085552018521)
    ·
      refine ⟨2424526477237564164013891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232701969650085552018521 2424526477237564164013891)
      ·
        refine ⟨3636789715856346246020837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424526477237564164013891 3636789715856346246020837)
        ·
          refine ⟨681898071723064921128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3636789715856346246020837 681898071723064921128907)
          ·
            refine ⟨1022847107584597381693361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681898071723064921128907 1022847107584597381693361)
            ·
              refine ⟨767135330688448036270021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022847107584597381693361 767135330688448036270021)
              ·
                refine ⟨143837874504084006800629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767135330688448036270021 143837874504084006800629)
                ·
                  rfl

theorem cell19_472708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_472708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472708 prefixEnd_472708 := by exact prefixLift 472708
  have htrace : WordTrace (prefixWord ++ tailWord_472708) baseStart_472708 baseEnd_472708 := by
    simpa [prefixWord, tailWord_472708, baseEnd_472708] using wordTrace_append hprefix tailTrace_472708
  have hstable : (prefixWord ++ tailWord_472708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472708).length < 2 ^ (prefixWord ++ tailWord_472708).sum := by decide
  have hdescent : baseEnd_472708 < baseStart_472708 := by decide
  rcases family_descends (prefixWord ++ tailWord_472708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472744 : List Nat := [2, 1, 7, 1, 1, 7]
def baseStart_472744 : Nat := 118140960795 + 472744 * 2 ^ 59
def prefixEnd_472744 : Nat := 4983230072969 + 3 ^ 40 * 472744 * 2
def baseEnd_472744 : Nat := 15983203195338510000059

theorem tailTrace_472744 : CollatzResearch.WordTrace tailWord_472744 prefixEnd_472744 15983203195338510000059 := by
  unfold tailWord_472744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621195099668350546204643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11494926799557800728272857 8621195099668350546204643)
  ·
    refine ⟨12931792649502525819306965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8621195099668350546204643 12931792649502525819306965)
    ·
      refine ⟨303088890222715448890007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12931792649502525819306965 303088890222715448890007)
      ·
        refine ⟨454633335334073173335011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303088890222715448890007 454633335334073173335011)
        ·
          refine ⟨681950003001109760002517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454633335334073173335011 681950003001109760002517)
          ·
            refine ⟨15983203195338510000059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 681950003001109760002517 15983203195338510000059)
            ·
              rfl

theorem cell19_472744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_472744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472744 prefixEnd_472744 := by exact prefixLift 472744
  have htrace : WordTrace (prefixWord ++ tailWord_472744) baseStart_472744 baseEnd_472744 := by
    simpa [prefixWord, tailWord_472744, baseEnd_472744] using wordTrace_append hprefix tailTrace_472744
  have hstable : (prefixWord ++ tailWord_472744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472744).length < 2 ^ (prefixWord ++ tailWord_472744).sum := by decide
  have hdescent : baseEnd_472744 < baseStart_472744 := by decide
  rcases family_descends (prefixWord ++ tailWord_472744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472826 : List Nat := [3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_472826 : Nat := 118140960795 + 472826 * 2 ^ 59
def prefixEnd_472826 : Nat := 4983230072969 + 3 ^ 40 * 472826 * 2
def baseEnd_472826 : Nat := 143873780114294696178085

theorem tailTrace_472826 : CollatzResearch.WordTrace tailWord_472826 prefixEnd_472826 143873780114294696178085 := by
  unfold tailWord_472826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311345246259907274223583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11496920656693086064596221 4311345246259907274223583)
  ·
    refine ⟨6467017869389860911335375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311345246259907274223583 6467017869389860911335375)
    ·
      refine ⟨9700526804084791367003063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467017869389860911335375 9700526804084791367003063)
      ·
        refine ⟨14550790206127187050504595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700526804084791367003063 14550790206127187050504595)
        ·
          refine ⟨21826185309190780575756893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14550790206127187050504595 21826185309190780575756893)
          ·
            refine ⟨8184819490946542715908835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21826185309190780575756893 8184819490946542715908835)
            ·
              refine ⟨12277229236419814073863253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184819490946542715908835 12277229236419814073863253)
              ·
                refine ⟨143873780114294696178085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12277229236419814073863253 143873780114294696178085)
                ·
                  rfl

theorem cell19_472826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_472826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472826 prefixEnd_472826 := by exact prefixLift 472826
  have htrace : WordTrace (prefixWord ++ tailWord_472826) baseStart_472826 baseEnd_472826 := by
    simpa [prefixWord, tailWord_472826, baseEnd_472826] using wordTrace_append hprefix tailTrace_472826
  have hstable : (prefixWord ++ tailWord_472826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472826).length < 2 ^ (prefixWord ++ tailWord_472826).sum := by decide
  have hdescent : baseEnd_472826 < baseStart_472826 := by decide
  rcases family_descends (prefixWord ++ tailWord_472826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472839 : List Nat := [1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_472839 : Nat := 118140960795 + 472839 * 2 ^ 59
def prefixEnd_472839 : Nat := 4983230072969 + 3 ^ 40 * 472839 * 2
def baseEnd_472839 : Nat := 143877735817114517889161

theorem tailTrace_472839 : CollatzResearch.WordTrace tailWord_472839 prefixEnd_472839 143877735817114517889161 := by
  unfold tailWord_472839
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245855133992532317117571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11497236755995021544745047 17245855133992532317117571)
  ·
    refine ⟨25868782700988798475676357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245855133992532317117571 25868782700988798475676357)
    ·
      refine ⟨4850396756435399714189317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25868782700988798475676357 4850396756435399714189317)
      ·
        refine ⟨909449391831637446410497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4850396756435399714189317 909449391831637446410497)
        ·
          refine ⟨682087043873728084807873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909449391831637446410497 682087043873728084807873)
          ·
            refine ⟨511565282905296063605905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682087043873728084807873 511565282905296063605905)
            ·
              refine ⟨383673962178972047704429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511565282905296063605905 383673962178972047704429)
              ·
                refine ⟨143877735817114517889161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383673962178972047704429 143877735817114517889161)
                ·
                  rfl

theorem cell19_472839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_472839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472839 prefixEnd_472839 := by exact prefixLift 472839
  have htrace : WordTrace (prefixWord ++ tailWord_472839) baseStart_472839 baseEnd_472839 := by
    simpa [prefixWord, tailWord_472839, baseEnd_472839] using wordTrace_append hprefix tailTrace_472839
  have hstable : (prefixWord ++ tailWord_472839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472839).length < 2 ^ (prefixWord ++ tailWord_472839).sum := by decide
  have hdescent : baseEnd_472839 < baseStart_472839 := by decide
  rcases family_descends (prefixWord ++ tailWord_472839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472843 : List Nat := [1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_472843 : Nat := 118140960795 + 472843 * 2 ^ 59
def prefixEnd_472843 : Nat := 4983230072969 + 3 ^ 40 * 472843 * 2
def baseEnd_472843 : Nat := 143878952956443693800261

theorem tailTrace_472843 : CollatzResearch.WordTrace tailWord_472843 prefixEnd_472843 143878952956443693800261 := by
  unfold tailWord_472843
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246001025978041000263183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11497334017318694000175455 17246001025978041000263183)
  ·
    refine ⟨25869001538967061500394775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17246001025978041000263183 25869001538967061500394775)
    ·
      refine ⟨38803502308450592250592163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25869001538967061500394775 38803502308450592250592163)
      ·
        refine ⟨58205253462675888375888245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38803502308450592250592163 58205253462675888375888245)
        ·
          refine ⟨5456742512125864535239523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58205253462675888375888245 5456742512125864535239523)
          ·
            refine ⟨8185113768188796802859285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456742512125864535239523 8185113768188796802859285)
            ·
              refine ⟨383677207883849850134029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8185113768188796802859285 383677207883849850134029)
              ·
                refine ⟨143878952956443693800261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383677207883849850134029 143878952956443693800261)
                ·
                  rfl

theorem cell19_472843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_472843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472843 prefixEnd_472843 := by exact prefixLift 472843
  have htrace : WordTrace (prefixWord ++ tailWord_472843) baseStart_472843 baseEnd_472843 := by
    simpa [prefixWord, tailWord_472843, baseEnd_472843] using wordTrace_append hprefix tailTrace_472843
  have hstable : (prefixWord ++ tailWord_472843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472843).length < 2 ^ (prefixWord ++ tailWord_472843).sum := by decide
  have hdescent : baseEnd_472843 < baseStart_472843 := by decide
  rcases family_descends (prefixWord ++ tailWord_472843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472881 : List Nat := [1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_472881 : Nat := 118140960795 + 472881 * 2 ^ 59
def prefixEnd_472881 : Nat := 4983230072969 + 3 ^ 40 * 472881 * 2
def baseEnd_472881 : Nat := 143890515780070864955713

theorem tailTrace_472881 : CollatzResearch.WordTrace tailWord_472881 prefixEnd_472881 143890515780070864955713 := by
  unfold tailWord_472881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247386999840373490146497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11498257999893582326764331 17247386999840373490146497)
  ·
    refine ⟨12935540249880280117609873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17247386999840373490146497 12935540249880280117609873)
    ·
      refine ⟨9701655187410210088207405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12935540249880280117609873 9701655187410210088207405)
      ·
        refine ⟨3638120695278828783077777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9701655187410210088207405 3638120695278828783077777)
        ·
          refine ⟨2728590521459121587308333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638120695278828783077777 2728590521459121587308333)
          ·
            refine ⟨1023221445547170595240625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2728590521459121587308333 1023221445547170595240625)
            ·
              refine ⟨767416084160377946430469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023221445547170595240625 767416084160377946430469)
              ·
                refine ⟨143890515780070864955713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767416084160377946430469 143890515780070864955713)
                ·
                  rfl

theorem cell19_472881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_472881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472881 prefixEnd_472881 := by exact prefixLift 472881
  have htrace : WordTrace (prefixWord ++ tailWord_472881) baseStart_472881 baseEnd_472881 := by
    simpa [prefixWord, tailWord_472881, baseEnd_472881] using wordTrace_append hprefix tailTrace_472881
  have hstable : (prefixWord ++ tailWord_472881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472881).length < 2 ^ (prefixWord ++ tailWord_472881).sum := by decide
  have hdescent : baseEnd_472881 < baseStart_472881 := by decide
  rcases family_descends (prefixWord ++ tailWord_472881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472919 : List Nat := [1, 1, 3, 2, 6, 6]
def baseStart_472919 : Nat := 118140960795 + 472919 * 2 ^ 59
def prefixEnd_472919 : Nat := 4983230072969 + 3 ^ 40 * 472919 * 2
def baseEnd_472919 : Nat := 15989119844855337345685

theorem tailTrace_472919 : CollatzResearch.WordTrace tailWord_472919 prefixEnd_472919 15989119844855337345685 := by
  unfold tailWord_472919
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248772973702705980029811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11499181982468470653353207 17248772973702705980029811)
  ·
    refine ⟨25873159460554058970044717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17248772973702705980029811 25873159460554058970044717)
    ·
      refine ⟨9702434797707772113766769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25873159460554058970044717 9702434797707772113766769)
      ·
        refine ⟨7276826098280829085325077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9702434797707772113766769 7276826098280829085325077)
        ·
          refine ⟨341101223356913863374613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7276826098280829085325077 341101223356913863374613)
          ·
            refine ⟨15989119844855337345685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 341101223356913863374613 15989119844855337345685)
            ·
              rfl

theorem cell19_472919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_472919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472919 prefixEnd_472919 := by exact prefixLift 472919
  have htrace : WordTrace (prefixWord ++ tailWord_472919) baseStart_472919 baseEnd_472919 := by
    simpa [prefixWord, tailWord_472919, baseEnd_472919] using wordTrace_append hprefix tailTrace_472919
  have hstable : (prefixWord ++ tailWord_472919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472919).length < 2 ^ (prefixWord ++ tailWord_472919).sum := by decide
  have hdescent : baseEnd_472919 < baseStart_472919 := by decide
  rcases family_descends (prefixWord ++ tailWord_472919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472974 : List Nat := [4, 1, 1, 5, 1, 1, 6]
def baseStart_472974 : Nat := 118140960795 + 472974 * 2 ^ 59
def prefixEnd_472974 : Nat := 4983230072969 + 3 ^ 40 * 472974 * 2
def baseEnd_472974 : Nat := 47972938089824734962931

theorem tailTrace_472974 : CollatzResearch.WordTrace tailWord_472974 prefixEnd_472974 47972938089824734962931 := by
  unfold tailWord_472974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156347373562931296660247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11500519325668966915521317 2156347373562931296660247)
  ·
    refine ⟨3234521060344396944990371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156347373562931296660247 3234521060344396944990371)
    ·
      refine ⟨4851781590516595417485557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234521060344396944990371 4851781590516595417485557)
      ·
        refine ⟨454854524110930820389271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4851781590516595417485557 454854524110930820389271)
        ·
          refine ⟨682281786166396230583907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454854524110930820389271 682281786166396230583907)
          ·
            refine ⟨1023422679249594345875861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682281786166396230583907 1023422679249594345875861)
            ·
              refine ⟨47972938089824734962931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1023422679249594345875861 47972938089824734962931)
              ·
                rfl

theorem cell19_472974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_472974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_472974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_472974 prefixEnd_472974 := by exact prefixLift 472974
  have htrace : WordTrace (prefixWord ++ tailWord_472974) baseStart_472974 baseEnd_472974 := by
    simpa [prefixWord, tailWord_472974, baseEnd_472974] using wordTrace_append hprefix tailTrace_472974
  have hstable : (prefixWord ++ tailWord_472974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472974).length < 2 ^ (prefixWord ++ tailWord_472974).sum := by decide
  have hdescent : baseEnd_472974 < baseStart_472974 := by decide
  rcases family_descends (prefixWord ++ tailWord_472974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473006 : List Nat := [4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_473006 : Nat := 118140960795 + 473006 * 2 ^ 59
def prefixEnd_473006 : Nat := 4983230072969 + 3 ^ 40 * 473006 * 2
def baseEnd_473006 : Nat := 143928551384107612177595

theorem tailTrace_473006 : CollatzResearch.WordTrace tailWord_473006 prefixEnd_473006 143928551384107612177595 := by
  unfold tailWord_473006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156493265548439979805859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11501297416258346558964581 2156493265548439979805859)
  ·
    refine ⟨3234739898322659969708789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156493265548439979805859 3234739898322659969708789)
    ·
      refine ⟨303256865467749372160199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3234739898322659969708789 303256865467749372160199)
      ·
        refine ⟨454885298201624058240299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303256865467749372160199 454885298201624058240299)
        ·
          refine ⟨682327947302436087360449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454885298201624058240299 682327947302436087360449)
          ·
            refine ⟨511745960476827065520337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682327947302436087360449 511745960476827065520337)
            ·
              refine ⟨383809470357620299140253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511745960476827065520337 383809470357620299140253)
              ·
                refine ⟨143928551384107612177595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383809470357620299140253 143928551384107612177595)
                ·
                  rfl

theorem cell19_473006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_473006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473006 prefixEnd_473006 := by exact prefixLift 473006
  have htrace : WordTrace (prefixWord ++ tailWord_473006) baseStart_473006 baseEnd_473006 := by
    simpa [prefixWord, tailWord_473006, baseEnd_473006] using wordTrace_append hprefix tailTrace_473006
  have hstable : (prefixWord ++ tailWord_473006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473006).length < 2 ^ (prefixWord ++ tailWord_473006).sum := by decide
  have hdescent : baseEnd_473006 < baseStart_473006 := by decide
  rcases family_descends (prefixWord ++ tailWord_473006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473016 : List Nat := [2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_473016 : Nat := 118140960795 + 473016 * 2 ^ 59
def prefixEnd_473016 : Nat := 4983230072969 + 3 ^ 40 * 473016 * 2
def baseEnd_473016 : Nat := 143931594232430551955345

theorem tailTrace_473016 : CollatzResearch.WordTrace tailWord_473016 prefixEnd_473016 143931594232430551955345 := by
  unfold tailWord_473016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626155427175645773155451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11501540569567527697540601 8626155427175645773155451)
  ·
    refine ⟨12939233140763468659733177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8626155427175645773155451 12939233140763468659733177)
    ·
      refine ⟨9704424855572601494799883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12939233140763468659733177 9704424855572601494799883)
      ·
        refine ⟨14556637283358902242199825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704424855572601494799883 14556637283358902242199825)
        ·
          refine ⟨10917477962519176681649869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14556637283358902242199825 10917477962519176681649869)
          ·
            refine ⟨4094054235944691255618701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10917477962519176681649869 4094054235944691255618701)
            ·
              refine ⟨1535270338479259220857013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094054235944691255618701 1535270338479259220857013)
              ·
                refine ⟨143931594232430551955345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1535270338479259220857013 143931594232430551955345)
                ·
                  rfl

theorem cell19_473016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_473016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473016 prefixEnd_473016 := by exact prefixLift 473016
  have htrace : WordTrace (prefixWord ++ tailWord_473016) baseStart_473016 baseEnd_473016 := by
    simpa [prefixWord, tailWord_473016, baseEnd_473016] using wordTrace_append hprefix tailTrace_473016
  have hstable : (prefixWord ++ tailWord_473016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473016).length < 2 ^ (prefixWord ++ tailWord_473016).sum := by decide
  have hdescent : baseEnd_473016 < baseStart_473016 := by decide
  rcases family_descends (prefixWord ++ tailWord_473016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473101 : List Nat := [1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_473101 : Nat := 118140960795 + 473101 * 2 ^ 59
def prefixEnd_473101 : Nat := 4983230072969 + 3 ^ 40 * 473101 * 2
def baseEnd_473101 : Nat := 143957458443175540066225

theorem tailTrace_473101 : CollatzResearch.WordTrace tailWord_473101 prefixEnd_473101 143957458443175540066225 := by
  unfold tailWord_473101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255411059043351063155157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11503607372695567375436771 17255411059043351063155157)
  ·
    refine ⟨404423696696328540542699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17255411059043351063155157 404423696696328540542699)
    ·
      refine ⟨606635545044492810814049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404423696696328540542699 606635545044492810814049)
      ·
        refine ⟨454976658783369608110537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606635545044492810814049 454976658783369608110537)
        ·
          refine ⟨341232494087527206082903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454976658783369608110537 341232494087527206082903)
          ·
            refine ⟨511848741131290809124355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341232494087527206082903 511848741131290809124355)
            ·
              refine ⟨767773111696936213686533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511848741131290809124355 767773111696936213686533)
              ·
                refine ⟨143957458443175540066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767773111696936213686533 143957458443175540066225)
                ·
                  rfl

theorem cell19_473101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_473101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473101 prefixEnd_473101 := by exact prefixLift 473101
  have htrace : WordTrace (prefixWord ++ tailWord_473101) baseStart_473101 baseEnd_473101 := by
    simpa [prefixWord, tailWord_473101, baseEnd_473101] using wordTrace_append hprefix tailTrace_473101
  have hstable : (prefixWord ++ tailWord_473101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473101).length < 2 ^ (prefixWord ++ tailWord_473101).sum := by decide
  have hdescent : baseEnd_473101 < baseStart_473101 := by decide
  rcases family_descends (prefixWord ++ tailWord_473101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473149 : List Nat := [1, 4, 1, 3, 1, 1, 8]
def baseStart_473149 : Nat := 118140960795 + 473149 * 2 ^ 59
def prefixEnd_473149 : Nat := 4983230072969 + 3 ^ 40 * 473149 * 2
def baseEnd_473149 : Nat := 47990688038375216999809

theorem tailTrace_473149 : CollatzResearch.WordTrace tailWord_473149 prefixEnd_473149 47990688038375216999809 := by
  unfold tailWord_473149
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257161762869455260902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504774508579636840601667 17257161762869455260902501)
  ·
    refine ⟨3235717830538022861419219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17257161762869455260902501 3235717830538022861419219)
    ·
      refine ⟨4853576745807034292128829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235717830538022861419219 4853576745807034292128829)
      ·
        refine ⟨1820091279677637859548311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853576745807034292128829 1820091279677637859548311)
        ·
          refine ⟨2730136919516456789322467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820091279677637859548311 2730136919516456789322467)
          ·
            refine ⟨4095205379274685183983701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730136919516456789322467 4095205379274685183983701)
            ·
              refine ⟨47990688038375216999809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4095205379274685183983701 47990688038375216999809)
              ·
                rfl

theorem cell19_473149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_473149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473149 prefixEnd_473149 := by exact prefixLift 473149
  have htrace : WordTrace (prefixWord ++ tailWord_473149) baseStart_473149 baseEnd_473149 := by
    simpa [prefixWord, tailWord_473149, baseEnd_473149] using wordTrace_append hprefix tailTrace_473149
  have hstable : (prefixWord ++ tailWord_473149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473149).length < 2 ^ (prefixWord ++ tailWord_473149).sum := by decide
  have hdescent : baseEnd_473149 < baseStart_473149 := by decide
  rcases family_descends (prefixWord ++ tailWord_473149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473181 : List Nat := [1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_473181 : Nat := 118140960795 + 473181 * 2 ^ 59
def prefixEnd_473181 : Nat := 4983230072969 + 3 ^ 40 * 473181 * 2
def baseEnd_473181 : Nat := 143981801229759058288229

theorem tailTrace_473181 : CollatzResearch.WordTrace tailWord_473181 prefixEnd_473181 143981801229759058288229 := by
  unfold tailWord_473181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258328898753524726067397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11505552599169016484044931 17258328898753524726067397)
  ·
    refine ⟨3235936668516285886137637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17258328898753524726067397 3235936668516285886137637)
    ·
      refine ⟨606738125346803603650807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3235936668516285886137637 606738125346803603650807)
      ·
        refine ⟨910107188020205405476211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606738125346803603650807 910107188020205405476211)
        ·
          refine ⟨1365160782030308108214317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910107188020205405476211 1365160782030308108214317)
          ·
            refine ⟨511935293261365540580369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365160782030308108214317 511935293261365540580369)
            ·
              refine ⟨383951469946024155435277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511935293261365540580369 383951469946024155435277)
              ·
                refine ⟨143981801229759058288229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383951469946024155435277 143981801229759058288229)
                ·
                  rfl

theorem cell19_473181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_473181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473181 prefixEnd_473181 := by exact prefixLift 473181
  have htrace : WordTrace (prefixWord ++ tailWord_473181) baseStart_473181 baseEnd_473181 := by
    simpa [prefixWord, tailWord_473181, baseEnd_473181] using wordTrace_append hprefix tailTrace_473181
  have hstable : (prefixWord ++ tailWord_473181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473181).length < 2 ^ (prefixWord ++ tailWord_473181).sum := by decide
  have hdescent : baseEnd_473181 < baseStart_473181 := by decide
  rcases family_descends (prefixWord ++ tailWord_473181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473225 : List Nat := [1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_473225 : Nat := 118140960795 + 473225 * 2 ^ 59
def prefixEnd_473225 : Nat := 4983230072969 + 3 ^ 40 * 473225 * 2
def baseEnd_473225 : Nat := 143995189762379993310331

theorem tailTrace_473225 : CollatzResearch.WordTrace tailWord_473225 prefixEnd_473225 143995189762379993310331 := by
  unfold tailWord_473225
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259933710594120240669129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11506622473729413493779419 17259933710594120240669129)
  ·
    refine ⟨12944950282945590180501847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17259933710594120240669129 12944950282945590180501847)
    ·
      refine ⟨19417425424418385270752771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944950282945590180501847 19417425424418385270752771)
      ·
        refine ⟨29126138136627577906129157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19417425424418385270752771 29126138136627577906129157)
        ·
          refine ⟨5461150900617670857399217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29126138136627577906129157 5461150900617670857399217)
          ·
            refine ⟨4095863175463253143049413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461150900617670857399217 4095863175463253143049413)
            ·
              refine ⟨767974345399359964321765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4095863175463253143049413 767974345399359964321765)
              ·
                refine ⟨143995189762379993310331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767974345399359964321765 143995189762379993310331)
                ·
                  rfl

theorem cell19_473225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_473225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473225 prefixEnd_473225 := by exact prefixLift 473225
  have htrace : WordTrace (prefixWord ++ tailWord_473225) baseStart_473225 baseEnd_473225 := by
    simpa [prefixWord, tailWord_473225, baseEnd_473225] using wordTrace_append hprefix tailTrace_473225
  have hstable : (prefixWord ++ tailWord_473225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473225).length < 2 ^ (prefixWord ++ tailWord_473225).sum := by decide
  have hdescent : baseEnd_473225 < baseStart_473225 := by decide
  rcases family_descends (prefixWord ++ tailWord_473225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473244 : List Nat := [2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_473244 : Nat := 118140960795 + 473244 * 2 ^ 59
def prefixEnd_473244 : Nat := 4983230072969 + 3 ^ 40 * 473244 * 2
def baseEnd_473244 : Nat := 144000971174193578888057

theorem tailTrace_473244 : CollatzResearch.WordTrace tailWord_473244 prefixEnd_473244 144000971174193578888057 := by
  unfold tailWord_473244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630313348762643242805393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11507084465016857657073857 8630313348762643242805393)
  ·
    refine ⟨6472735011571982432104045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8630313348762643242805393 6472735011571982432104045)
    ·
      refine ⟨2427275629339493412039017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6472735011571982432104045 2427275629339493412039017)
      ·
        refine ⟨1820456722004620059029263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427275629339493412039017 1820456722004620059029263)
        ·
          refine ⟨2730685083006930088543895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820456722004620059029263 2730685083006930088543895)
          ·
            refine ⟨4096027624510395132815843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730685083006930088543895 4096027624510395132815843)
            ·
              refine ⟨6144041436765592699223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096027624510395132815843 6144041436765592699223765)
              ·
                refine ⟨144000971174193578888057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6144041436765592699223765 144000971174193578888057)
                ·
                  rfl

theorem cell19_473244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_473244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473244 prefixEnd_473244 := by exact prefixLift 473244
  have htrace : WordTrace (prefixWord ++ tailWord_473244) baseStart_473244 baseEnd_473244 := by
    simpa [prefixWord, tailWord_473244, baseEnd_473244] using wordTrace_append hprefix tailTrace_473244
  have hstable : (prefixWord ++ tailWord_473244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473244).length < 2 ^ (prefixWord ++ tailWord_473244).sum := by decide
  have hdescent : baseEnd_473244 < baseStart_473244 := by decide
  rcases family_descends (prefixWord ++ tailWord_473244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473278 : List Nat := [4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_473278 : Nat := 118140960795 + 473278 * 2 ^ 59
def prefixEnd_473278 : Nat := 4983230072969 + 3 ^ 40 * 473278 * 2
def baseEnd_473278 : Nat := 144011316858491574132409

theorem tailTrace_473278 : CollatzResearch.WordTrace tailWord_473278 prefixEnd_473278 144011316858491574132409 := by
  unfold tailWord_473278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157733347425263786543561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11507911186268073528232325 2157733347425263786543561)
  ·
    refine ⟨1618300010568947839907671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2157733347425263786543561 1618300010568947839907671)
    ·
      refine ⟨2427450015853421759861507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618300010568947839907671 2427450015853421759861507)
      ·
        refine ⟨3641175023780132639792261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427450015853421759861507 3641175023780132639792261)
        ·
          refine ⟨682720316958774869961049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3641175023780132639792261 682720316958774869961049)
          ·
            refine ⟨512040237719081152470787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682720316958774869961049 512040237719081152470787)
            ·
              refine ⟨768060356578621728706181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512040237719081152470787 768060356578621728706181)
              ·
                refine ⟨144011316858491574132409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768060356578621728706181 144011316858491574132409)
                ·
                  rfl

theorem cell19_473278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_473278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473278 prefixEnd_473278 := by exact prefixLift 473278
  have htrace : WordTrace (prefixWord ++ tailWord_473278) baseStart_473278 baseEnd_473278 := by
    simpa [prefixWord, tailWord_473278, baseEnd_473278] using wordTrace_append hprefix tailTrace_473278
  have hstable : (prefixWord ++ tailWord_473278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473278).length < 2 ^ (prefixWord ++ tailWord_473278).sum := by decide
  have hdescent : baseEnd_473278 < baseStart_473278 := by decide
  rcases family_descends (prefixWord ++ tailWord_473278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473280 : List Nat := [2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_473280 : Nat := 118140960795 + 473280 * 2 ^ 59
def prefixEnd_473280 : Nat := 4983230072969 + 3 ^ 40 * 473280 * 2
def baseEnd_473280 : Nat := 144011925428156162087959

theorem tailTrace_473280 : CollatzResearch.WordTrace tailWord_473280 prefixEnd_473280 144011925428156162087959 := by
  unfold tailWord_473280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630969862697432316960647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11507959816929909755947529 8630969862697432316960647)
  ·
    refine ⟨12946454794046148475440971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8630969862697432316960647 12946454794046148475440971)
    ·
      refine ⟨19419682191069222713161457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12946454794046148475440971 19419682191069222713161457)
      ·
        refine ⟨14564761643301917034871093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19419682191069222713161457 14564761643301917034871093)
        ·
          refine ⟨1365446404059554722019165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14564761643301917034871093 1365446404059554722019165)
          ·
            refine ⟨512042401522333020757187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365446404059554722019165 512042401522333020757187)
            ·
              refine ⟨768063602283499531135781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512042401522333020757187 768063602283499531135781)
              ·
                refine ⟨144011925428156162087959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768063602283499531135781 144011925428156162087959)
                ·
                  rfl

theorem cell19_473280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_473280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473280 prefixEnd_473280 := by exact prefixLift 473280
  have htrace : WordTrace (prefixWord ++ tailWord_473280) baseStart_473280 baseEnd_473280 := by
    simpa [prefixWord, tailWord_473280, baseEnd_473280] using wordTrace_append hprefix tailTrace_473280
  have hstable : (prefixWord ++ tailWord_473280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473280).length < 2 ^ (prefixWord ++ tailWord_473280).sum := by decide
  have hdescent : baseEnd_473280 < baseStart_473280 := by decide
  rcases family_descends (prefixWord ++ tailWord_473280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473314 : List Nat := [3, 3, 4, 1, 1, 1, 6]
def baseStart_473314 : Nat := 118140960795 + 473314 * 2 ^ 59
def prefixEnd_473314 : Nat := 4983230072969 + 3 ^ 40 * 473314 * 2
def baseEnd_473314 : Nat := 48007423704151385777437

theorem tailTrace_473314 : CollatzResearch.WordTrace tailWord_473314 prefixEnd_473314 48007423704151385777437 := by
  unfold tailWord_473314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315794951817922110164749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11508786538181125627105997 4315794951817922110164749)
  ·
    refine ⟨1618423106931720791311781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4315794951817922110164749 1618423106931720791311781)
    ·
      refine ⟨303454332549697648370959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1618423106931720791311781 303454332549697648370959)
      ·
        refine ⟨455181498824546472556439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303454332549697648370959 455181498824546472556439)
        ·
          refine ⟨682772248236819708834659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455181498824546472556439 682772248236819708834659)
          ·
            refine ⟨1024158372355229563251989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682772248236819708834659 1024158372355229563251989)
            ·
              refine ⟨48007423704151385777437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1024158372355229563251989 48007423704151385777437)
              ·
                rfl

theorem cell19_473314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_473314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473314 prefixEnd_473314 := by exact prefixLift 473314
  have htrace : WordTrace (prefixWord ++ tailWord_473314) baseStart_473314 baseEnd_473314 := by
    simpa [prefixWord, tailWord_473314, baseEnd_473314] using wordTrace_append hprefix tailTrace_473314
  have hstable : (prefixWord ++ tailWord_473314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473314).length < 2 ^ (prefixWord ++ tailWord_473314).sum := by decide
  have hdescent : baseEnd_473314 < baseStart_473314 := by decide
  rcases family_descends (prefixWord ++ tailWord_473314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473320 : List Nat := [2, 1, 4, 1, 2, 3, 6]
def baseStart_473320 : Nat := 118140960795 + 473320 * 2 ^ 59
def prefixEnd_473320 : Nat := 4983230072969 + 3 ^ 40 * 473320 * 2
def baseEnd_473320 : Nat := 48008032273815973732987

theorem tailTrace_473320 : CollatzResearch.WordTrace tailWord_473320 prefixEnd_473320 48008032273815973732987 := by
  unfold tailWord_473320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631699322624975732688707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11508932430166634310251609 8631699322624975732688707)
  ·
    refine ⟨12947548983937463599033061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8631699322624975732688707 12947548983937463599033061)
    ·
      refine ⟨2427665434488274424818699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12947548983937463599033061 2427665434488274424818699)
      ·
        refine ⟨3641498151732411637228049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427665434488274424818699 3641498151732411637228049)
        ·
          refine ⟨2731123613799308727921037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3641498151732411637228049 2731123613799308727921037)
          ·
            refine ⟨1024171355174740772970389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2731123613799308727921037 1024171355174740772970389)
            ·
              refine ⟨48008032273815973732987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1024171355174740772970389 48008032273815973732987)
              ·
                rfl

theorem cell19_473320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_473320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473320 prefixEnd_473320 := by exact prefixLift 473320
  have htrace : WordTrace (prefixWord ++ tailWord_473320) baseStart_473320 baseEnd_473320 := by
    simpa [prefixWord, tailWord_473320, baseEnd_473320] using wordTrace_append hprefix tailTrace_473320
  have hstable : (prefixWord ++ tailWord_473320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473320).length < 2 ^ (prefixWord ++ tailWord_473320).sum := by decide
  have hdescent : baseEnd_473320 < baseStart_473320 := by decide
  rcases family_descends (prefixWord ++ tailWord_473320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473358 : List Nat := [4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_473358 : Nat := 118140960795 + 473358 * 2 ^ 59
def prefixEnd_473358 : Nat := 4983230072969 + 3 ^ 40 * 473358 * 2
def baseEnd_473358 : Nat := 144035659645075092354413

theorem tailTrace_473358 : CollatzResearch.WordTrace tailWord_473358 prefixEnd_473358 144035659645075092354413 := by
  unfold tailWord_473358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158098077389035494407591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11509856412741522636840485 2158098077389035494407591)
  ·
    refine ⟨3237147116083553241611387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2158098077389035494407591 3237147116083553241611387)
    ·
      refine ⟨4855720674125329862417081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237147116083553241611387 4855720674125329862417081)
      ·
        refine ⟨3641790505593997396812811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4855720674125329862417081 3641790505593997396812811)
        ·
          refine ⟨5462685758390996095219217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641790505593997396812811 5462685758390996095219217)
          ·
            refine ⟨4097014318793247071414413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5462685758390996095219217 4097014318793247071414413)
            ·
              refine ⟨1536380369547467651780405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097014318793247071414413 1536380369547467651780405)
              ·
                refine ⟨144035659645075092354413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536380369547467651780405 144035659645075092354413)
                ·
                  rfl

theorem cell19_473358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_473358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473358 prefixEnd_473358 := by exact prefixLift 473358
  have htrace : WordTrace (prefixWord ++ tailWord_473358) baseStart_473358 baseEnd_473358 := by
    simpa [prefixWord, tailWord_473358, baseEnd_473358] using wordTrace_append hprefix tailTrace_473358
  have hstable : (prefixWord ++ tailWord_473358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473358).length < 2 ^ (prefixWord ++ tailWord_473358).sum := by decide
  have hdescent : baseEnd_473358 < baseStart_473358 := by decide
  rcases family_descends (prefixWord ++ tailWord_473358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473373 : List Nat := [1, 4, 2, 3, 3, 1, 5]
def baseStart_473373 : Nat := 118140960795 + 473373 * 2 ^ 59
def prefixEnd_473373 : Nat := 4983230072969 + 3 ^ 40 * 473373 * 2
def baseEnd_473373 : Nat := 48013407972519834007013

theorem tailTrace_473373 : CollatzResearch.WordTrace tailWord_473373 prefixEnd_473373 48013407972519834007013 := by
  unfold tailWord_473373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265331714057941517056773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11510221142705294344704515 17265331714057941517056773)
  ·
    refine ⟨3237249696385864034448145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17265331714057941517056773 3237249696385864034448145)
    ·
      refine ⟨2427937272289398025836109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3237249696385864034448145 2427937272289398025836109)
      ·
        refine ⟨910476477108524259688541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2427937272289398025836109 910476477108524259688541)
        ·
          refine ⟨341428678915696597383203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910476477108524259688541 341428678915696597383203)
          ·
            refine ⟨512143018373544896074805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341428678915696597383203 512143018373544896074805)
            ·
              refine ⟨48013407972519834007013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512143018373544896074805 48013407972519834007013)
              ·
                rfl

theorem cell19_473373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_473373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473373 prefixEnd_473373 := by exact prefixLift 473373
  have htrace : WordTrace (prefixWord ++ tailWord_473373) baseStart_473373 baseEnd_473373 := by
    simpa [prefixWord, tailWord_473373, baseEnd_473373] using wordTrace_append hprefix tailTrace_473373
  have hstable : (prefixWord ++ tailWord_473373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473373).length < 2 ^ (prefixWord ++ tailWord_473373).sum := by decide
  have hdescent : baseEnd_473373 < baseStart_473373 := by decide
  rcases family_descends (prefixWord ++ tailWord_473373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473394 : List Nat := [3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_473394 : Nat := 118140960795 + 473394 * 2 ^ 59
def prefixEnd_473394 : Nat := 4983230072969 + 3 ^ 40 * 473394 * 2
def baseEnd_473394 : Nat := 144046613899037675554315

theorem tailTrace_473394 : CollatzResearch.WordTrace tailWord_473394 prefixEnd_473394 144046613899037675554315 := by
  unfold tailWord_473394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316524411745465525892809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11510731764654574735714157 4316524411745465525892809)
  ·
    refine ⟨3237393308809099144419607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4316524411745465525892809 3237393308809099144419607)
    ·
      refine ⟨4856089963213648716629411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237393308809099144419607 4856089963213648716629411)
      ·
        refine ⟨7284134944820473074944117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856089963213648716629411 7284134944820473074944117)
        ·
          refine ⟨682887651076919350776011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7284134944820473074944117 682887651076919350776011)
          ·
            refine ⟨1024331476615379026164017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682887651076919350776011 1024331476615379026164017)
            ·
              refine ⟨768248607461534269623013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024331476615379026164017 768248607461534269623013)
              ·
                refine ⟨144046613899037675554315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768248607461534269623013 144046613899037675554315)
                ·
                  rfl

theorem cell19_473394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_473394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473394 prefixEnd_473394 := by exact prefixLift 473394
  have htrace : WordTrace (prefixWord ++ tailWord_473394) baseStart_473394 baseEnd_473394 := by
    simpa [prefixWord, tailWord_473394, baseEnd_473394] using wordTrace_append hprefix tailTrace_473394
  have hstable : (prefixWord ++ tailWord_473394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473394).length < 2 ^ (prefixWord ++ tailWord_473394).sum := by decide
  have hdescent : baseEnd_473394 < baseStart_473394 := by decide
  rcases family_descends (prefixWord ++ tailWord_473394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473455 : List Nat := [1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_473455 : Nat := 118140960795 + 473455 * 2 ^ 59
def prefixEnd_473455 : Nat := 4983230072969 + 3 ^ 40 * 473455 * 2
def baseEnd_473455 : Nat := 144065175273807608198593

theorem tailTrace_473455 : CollatzResearch.WordTrace tailWord_473455 prefixEnd_473455 144065175273807608198593 := by
  unfold tailWord_473455
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268322499760869521541819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11512214999840579681027879 17268322499760869521541819)
  ·
    refine ⟨25902483749641304282312729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17268322499760869521541819 25902483749641304282312729)
    ·
      refine ⟨19426862812230978211734547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25902483749641304282312729 19426862812230978211734547)
      ·
        refine ⟨29140294218346467317601821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19426862812230978211734547 29140294218346467317601821)
        ·
          refine ⟨10927610331879925244100683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29140294218346467317601821 10927610331879925244100683)
          ·
            refine ⟨16391415497819887866151025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927610331879925244100683 16391415497819887866151025)
            ·
              refine ⟨12293561623364915899613269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16391415497819887866151025 12293561623364915899613269)
              ·
                refine ⟨144065175273807608198593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12293561623364915899613269 144065175273807608198593)
                ·
                  rfl

theorem cell19_473455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_473455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473455 prefixEnd_473455 := by exact prefixLift 473455
  have htrace : WordTrace (prefixWord ++ tailWord_473455) baseStart_473455 baseEnd_473455 := by
    simpa [prefixWord, tailWord_473455, baseEnd_473455] using wordTrace_append hprefix tailTrace_473455
  have hstable : (prefixWord ++ tailWord_473455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473455).length < 2 ^ (prefixWord ++ tailWord_473455).sum := by decide
  have hdescent : baseEnd_473455 < baseStart_473455 := by decide
  rcases family_descends (prefixWord ++ tailWord_473455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473525 : List Nat := [1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_473525 : Nat := 118140960795 + 473525 * 2 ^ 59
def prefixEnd_473525 : Nat := 4983230072969 + 3 ^ 40 * 473525 * 2
def baseEnd_473525 : Nat := 144086475212068186642847

theorem tailTrace_473525 : CollatzResearch.WordTrace tailWord_473525 prefixEnd_473525 144086475212068186642847 := by
  unfold tailWord_473525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270875609507271476590029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11513917073004847651060019 17270875609507271476590029)
  ·
    refine ⟨6476578353565226803721261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17270875609507271476590029 6476578353565226803721261)
    ·
      refine ⟨2428716882586960051395473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6476578353565226803721261 2428716882586960051395473)
      ·
        refine ⟨1821537661940220038546605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428716882586960051395473 1821537661940220038546605)
        ·
          refine ⟨683076623227582514454977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1821537661940220038546605 683076623227582514454977)
          ·
            refine ⟨512307467420686885841233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683076623227582514454977 512307467420686885841233)
            ·
              refine ⟨384230600565515164380925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512307467420686885841233 384230600565515164380925)
              ·
                refine ⟨144086475212068186642847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384230600565515164380925 144086475212068186642847)
                ·
                  rfl

theorem cell19_473525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_473525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473525 prefixEnd_473525 := by exact prefixLift 473525
  have htrace : WordTrace (prefixWord ++ tailWord_473525) baseStart_473525 baseEnd_473525 := by
    simpa [prefixWord, tailWord_473525, baseEnd_473525] using wordTrace_append hprefix tailTrace_473525
  have hstable : (prefixWord ++ tailWord_473525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473525).length < 2 ^ (prefixWord ++ tailWord_473525).sum := by decide
  have hdescent : baseEnd_473525 < baseStart_473525 := by decide
  rcases family_descends (prefixWord ++ tailWord_473525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473527 : List Nat := [1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_473527 : Nat := 118140960795 + 473527 * 2 ^ 59
def prefixEnd_473527 : Nat := 4983230072969 + 3 ^ 40 * 473527 * 2
def baseEnd_473527 : Nat := 144087083781732774598397

theorem tailTrace_473527 : CollatzResearch.WordTrace tailWord_473527 prefixEnd_473527 144087083781732774598397 := by
  unfold tailWord_473527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270948555500025818162835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11513965703666683878775223 17270948555500025818162835)
  ·
    refine ⟨25906422833250038727244253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17270948555500025818162835 25906422833250038727244253)
    ·
      refine ⟨9714908562468764522716595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25906422833250038727244253 9714908562468764522716595)
      ·
        refine ⟨14572362843703146784074893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9714908562468764522716595 14572362843703146784074893)
        ·
          refine ⟨5464636066388680044028085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14572362843703146784074893 5464636066388680044028085)
          ·
            refine ⟨512309631223938754127633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5464636066388680044028085 512309631223938754127633)
            ·
              refine ⟨384232223417954065595725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512309631223938754127633 384232223417954065595725)
              ·
                refine ⟨144087083781732774598397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384232223417954065595725 144087083781732774598397)
                ·
                  rfl

theorem cell19_473527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_473527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473527 prefixEnd_473527 := by exact prefixLift 473527
  have htrace : WordTrace (prefixWord ++ tailWord_473527) baseStart_473527 baseEnd_473527 := by
    simpa [prefixWord, tailWord_473527, baseEnd_473527] using wordTrace_append hprefix tailTrace_473527
  have hstable : (prefixWord ++ tailWord_473527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473527).length < 2 ^ (prefixWord ++ tailWord_473527).sum := by decide
  have hdescent : baseEnd_473527 < baseStart_473527 := by decide
  rcases family_descends (prefixWord ++ tailWord_473527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473529 : List Nat := [1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_473529 : Nat := 118140960795 + 473529 * 2 ^ 59
def prefixEnd_473529 : Nat := 4983230072969 + 3 ^ 40 * 473529 * 2
def baseEnd_473529 : Nat := 144087692351397362553947

theorem tailTrace_473529 : CollatzResearch.WordTrace tailWord_473529 prefixEnd_473529 144087692351397362553947 := by
  unfold tailWord_473529
  simp only [CollatzResearch.WordTrace]
  refine ⟨17271021501492780159735641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11514014334328520106490427 17271021501492780159735641)
  ·
    refine ⟨12953266126119585119801731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17271021501492780159735641 12953266126119585119801731)
    ·
      refine ⟨19429899189179377679702597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953266126119585119801731 19429899189179377679702597)
      ·
        refine ⟨3643106097971133314944237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19429899189179377679702597 3643106097971133314944237)
        ·
          refine ⟨1366164786739174993104089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3643106097971133314944237 1366164786739174993104089)
          ·
            refine ⟨1024623590054381244828067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366164786739174993104089 1024623590054381244828067)
            ·
              refine ⟨1536935385081571867242101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024623590054381244828067 1536935385081571867242101)
              ·
                refine ⟨144087692351397362553947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536935385081571867242101 144087692351397362553947)
                ·
                  rfl

theorem cell19_473529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_473529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473529 prefixEnd_473529 := by exact prefixLift 473529
  have htrace : WordTrace (prefixWord ++ tailWord_473529) baseStart_473529 baseEnd_473529 := by
    simpa [prefixWord, tailWord_473529, baseEnd_473529] using wordTrace_append hprefix tailTrace_473529
  have hstable : (prefixWord ++ tailWord_473529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473529).length < 2 ^ (prefixWord ++ tailWord_473529).sum := by decide
  have hdescent : baseEnd_473529 < baseStart_473529 := by decide
  rcases family_descends (prefixWord ++ tailWord_473529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473567 : List Nat := [1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_473567 : Nat := 118140960795 + 473567 * 2 ^ 59
def prefixEnd_473567 : Nat := 4983230072969 + 3 ^ 40 * 473567 * 2
def baseEnd_473567 : Nat := 144099255175024533709399

theorem tailTrace_473567 : CollatzResearch.WordTrace tailWord_473567 prefixEnd_473567 144099255175024533709399 := by
  unfold tailWord_473567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17272407475355112649618955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11514938316903408433079303 17272407475355112649618955)
  ·
    refine ⟨25908611213032668974428433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17272407475355112649618955 25908611213032668974428433)
    ·
      refine ⟨19431458409774501730821325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25908611213032668974428433 19431458409774501730821325)
      ·
        refine ⟨7286796903665438149057997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19431458409774501730821325 7286796903665438149057997)
        ·
          refine ⟨2732548838874539305896749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286796903665438149057997 2732548838874539305896749)
          ·
            refine ⟨1024705814577952239711281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2732548838874539305896749 1024705814577952239711281)
            ·
              refine ⟨768529360933464179783461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024705814577952239711281 768529360933464179783461)
              ·
                refine ⟨144099255175024533709399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768529360933464179783461 144099255175024533709399)
                ·
                  rfl

theorem cell19_473567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_473567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473567 prefixEnd_473567 := by exact prefixLift 473567
  have htrace : WordTrace (prefixWord ++ tailWord_473567) baseStart_473567 baseEnd_473567 := by
    simpa [prefixWord, tailWord_473567, baseEnd_473567] using wordTrace_append hprefix tailTrace_473567
  have hstable : (prefixWord ++ tailWord_473567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473567).length < 2 ^ (prefixWord ++ tailWord_473567).sum := by decide
  have hdescent : baseEnd_473567 < baseStart_473567 := by decide
  rcases family_descends (prefixWord ++ tailWord_473567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473607 : List Nat := [1, 1, 4, 3, 10]
def baseStart_473607 : Nat := 118140960795 + 473607 * 2 ^ 59
def prefixEnd_473607 : Nat := 4983230072969 + 3 ^ 40 * 473607 * 2
def baseEnd_473607 : Nat := 5337460243270973808163

theorem tailTrace_473607 : CollatzResearch.WordTrace tailWord_473607 prefixEnd_473607 5337460243270973808163 := by
  unfold tailWord_473607
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273866395210199481075075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11515910930140132987383383 17273866395210199481075075)
  ·
    refine ⟨25910799592815299221612613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17273866395210199481075075 25910799592815299221612613)
    ·
      refine ⟨4858274923652868604052365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25910799592815299221612613 4858274923652868604052365)
      ·
        refine ⟨1821853096369825726519637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4858274923652868604052365 1821853096369825726519637)
        ·
          refine ⟨5337460243270973808163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1821853096369825726519637 5337460243270973808163)
          ·
            rfl

theorem cell19_473607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_473607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473607 prefixEnd_473607 := by exact prefixLift 473607
  have htrace : WordTrace (prefixWord ++ tailWord_473607) baseStart_473607 baseEnd_473607 := by
    simpa [prefixWord, tailWord_473607, baseEnd_473607] using wordTrace_append hprefix tailTrace_473607
  have hstable : (prefixWord ++ tailWord_473607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473607).length < 2 ^ (prefixWord ++ tailWord_473607).sum := by decide
  have hdescent : baseEnd_473607 < baseStart_473607 := by decide
  rcases family_descends (prefixWord ++ tailWord_473607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473620 : List Nat := [2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_473620 : Nat := 118140960795 + 473620 * 2 ^ 59
def prefixEnd_473620 : Nat := 4983230072969 + 3 ^ 40 * 473620 * 2
def baseEnd_473620 : Nat := 144115382271136114531477

theorem tailTrace_473620 : CollatzResearch.WordTrace tailWord_473620 prefixEnd_473620 144115382271136114531477 := by
  unfold tailWord_473620
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637170272081551350649157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11516227029442068467532209 8637170272081551350649157)
  ·
    refine ⟨1619469426015290878246717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8637170272081551350649157 1619469426015290878246717)
    ·
      refine ⟨607301034755734079342519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1619469426015290878246717 607301034755734079342519)
      ·
        refine ⟨910951552133601119013779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607301034755734079342519 910951552133601119013779)
        ·
          refine ⟨1366427328200401678520669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910951552133601119013779 1366427328200401678520669)
          ·
            refine ⟨512410248075150629445251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366427328200401678520669 512410248075150629445251)
            ·
              refine ⟨768615372112725944167877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512410248075150629445251 768615372112725944167877)
              ·
                refine ⟨144115382271136114531477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768615372112725944167877 144115382271136114531477)
                ·
                  rfl

theorem cell19_473620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_473620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473620 prefixEnd_473620 := by exact prefixLift 473620
  have htrace : WordTrace (prefixWord ++ tailWord_473620) baseStart_473620 baseEnd_473620 := by
    simpa [prefixWord, tailWord_473620, baseEnd_473620] using wordTrace_append hprefix tailTrace_473620
  have hstable : (prefixWord ++ tailWord_473620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473620).length < 2 ^ (prefixWord ++ tailWord_473620).sum := by decide
  have hdescent : baseEnd_473620 < baseStart_473620 := by decide
  rcases family_descends (prefixWord ++ tailWord_473620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473624 : List Nat := [2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_473624 : Nat := 118140960795 + 473624 * 2 ^ 59
def prefixEnd_473624 : Nat := 4983230072969 + 3 ^ 40 * 473624 * 2
def baseEnd_473624 : Nat := 144116599410465290442577

theorem tailTrace_473624 : CollatzResearch.WordTrace tailWord_473624 prefixEnd_473624 144116599410465290442577 := by
  unfold tailWord_473624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637243218074305692221963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11516324290765740922962617 8637243218074305692221963)
  ·
    refine ⟨12955864827111458538332945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8637243218074305692221963 12955864827111458538332945)
    ·
      refine ⟨9716898620333593903749709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12955864827111458538332945 9716898620333593903749709)
      ·
        refine ⟨3643836982625097713906141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9716898620333593903749709 3643836982625097713906141)
        ·
          refine ⟨1366438868484411642714803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3643836982625097713906141 1366438868484411642714803)
          ·
            refine ⟨2049658302726617464072205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366438868484411642714803 2049658302726617464072205)
            ·
              refine ⟨768621863522481549027077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2049658302726617464072205 768621863522481549027077)
              ·
                refine ⟨144116599410465290442577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768621863522481549027077 144116599410465290442577)
                ·
                  rfl

theorem cell19_473624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_473624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473624 prefixEnd_473624 := by exact prefixLift 473624
  have htrace : WordTrace (prefixWord ++ tailWord_473624) baseStart_473624 baseEnd_473624 := by
    simpa [prefixWord, tailWord_473624, baseEnd_473624] using wordTrace_append hprefix tailTrace_473624
  have hstable : (prefixWord ++ tailWord_473624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473624).length < 2 ^ (prefixWord ++ tailWord_473624).sum := by decide
  have hdescent : baseEnd_473624 < baseStart_473624 := by decide
  rcases family_descends (prefixWord ++ tailWord_473624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473694 : List Nat := [4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_473694 : Nat := 118140960795 + 473694 * 2 ^ 59
def prefixEnd_473694 : Nat := 4983230072969 + 3 ^ 40 * 473694 * 2
def baseEnd_473694 : Nat := 144137899348725868886831

theorem tailTrace_473694 : CollatzResearch.WordTrace tailWord_473694 prefixEnd_473694 144137899348725868886831 := by
  unfold tailWord_473694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159629943236876667436517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11518026363930008892994757 2159629943236876667436517)
  ·
    refine ⟨404930614356914375144347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2159629943236876667436517 404930614356914375144347)
    ·
      refine ⟨607395921535371562716521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404930614356914375144347 607395921535371562716521)
      ·
        refine ⟨455546941151528672037391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607395921535371562716521 455546941151528672037391)
        ·
          refine ⟨683320411727293008056087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455546941151528672037391 683320411727293008056087)
          ·
            refine ⟨1024980617590939512084131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683320411727293008056087 1024980617590939512084131)
            ·
              refine ⟨1537470926386409268126197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024980617590939512084131 1537470926386409268126197)
              ·
                refine ⟨144137899348725868886831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537470926386409268126197 144137899348725868886831)
                ·
                  rfl

theorem cell19_473694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_473694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473694 prefixEnd_473694 := by exact prefixLift 473694
  have htrace : WordTrace (prefixWord ++ tailWord_473694) baseStart_473694 baseEnd_473694 := by
    simpa [prefixWord, tailWord_473694, baseEnd_473694] using wordTrace_append hprefix tailTrace_473694
  have hstable : (prefixWord ++ tailWord_473694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473694).length < 2 ^ (prefixWord ++ tailWord_473694).sum := by decide
  have hdescent : baseEnd_473694 < baseStart_473694 := by decide
  rcases family_descends (prefixWord ++ tailWord_473694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473717 : List Nat := [1, 3, 4, 2, 2, 2, 5]
def baseStart_473717 : Nat := 118140960795 + 473717 * 2 ^ 59
def prefixEnd_473717 : Nat := 4983230072969 + 3 ^ 40 * 473717 * 2
def baseEnd_473717 : Nat := 48048299299956210125219

theorem tailTrace_473717 : CollatzResearch.WordTrace tailWord_473717 prefixEnd_473717 48048299299956210125219 := by
  unfold tailWord_473717
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277878424811688267579405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11518585616541125511719603 17277878424811688267579405)
  ·
    refine ⟨6479204409304383100342277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17277878424811688267579405 6479204409304383100342277)
    ·
      refine ⟨1214850826744571831314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6479204409304383100342277 1214850826744571831314177)
      ·
        refine ⟨911138120058428873485633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214850826744571831314177 911138120058428873485633)
        ·
          refine ⟨683353590043821655114225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911138120058428873485633 683353590043821655114225)
          ·
            refine ⟨512515192532866241335669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683353590043821655114225 512515192532866241335669)
            ·
              refine ⟨48048299299956210125219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512515192532866241335669 48048299299956210125219)
              ·
                rfl

theorem cell19_473717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_473717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473717 prefixEnd_473717 := by exact prefixLift 473717
  have htrace : WordTrace (prefixWord ++ tailWord_473717) baseStart_473717 baseEnd_473717 := by
    simpa [prefixWord, tailWord_473717, baseEnd_473717] using wordTrace_append hprefix tailTrace_473717
  have hstable : (prefixWord ++ tailWord_473717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473717).length < 2 ^ (prefixWord ++ tailWord_473717).sum := by decide
  have hdescent : baseEnd_473717 < baseStart_473717 := by decide
  rcases family_descends (prefixWord ++ tailWord_473717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473721 : List Nat := [1, 2, 1, 3, 3, 2, 7]
def baseStart_473721 : Nat := 118140960795 + 473721 * 2 ^ 59
def prefixEnd_473721 : Nat := 4983230072969 + 3 ^ 40 * 473721 * 2
def baseEnd_473721 : Nat := 48048705013065935428919

theorem tailTrace_473721 : CollatzResearch.WordTrace tailWord_473721 prefixEnd_473721 48048705013065935428919 := by
  unfold tailWord_473721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17278024316797196950725017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11518682877864797967150011 17278024316797196950725017)
  ·
    refine ⟨12958518237597897713043763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17278024316797196950725017 12958518237597897713043763)
    ·
      refine ⟨19437777356396846569565645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958518237597897713043763 19437777356396846569565645)
      ·
        refine ⟨7289166508648817463587117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19437777356396846569565645 7289166508648817463587117)
        ·
          refine ⟨2733437440743306548845169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7289166508648817463587117 2733437440743306548845169)
          ·
            refine ⟨2050078080557479911633877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733437440743306548845169 2050078080557479911633877)
            ·
              refine ⟨48048705013065935428919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2050078080557479911633877 48048705013065935428919)
              ·
                rfl

theorem cell19_473721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_473721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473721 prefixEnd_473721 := by exact prefixLift 473721
  have htrace : WordTrace (prefixWord ++ tailWord_473721) baseStart_473721 baseEnd_473721 := by
    simpa [prefixWord, tailWord_473721, baseEnd_473721] using wordTrace_append hprefix tailTrace_473721
  have hstable : (prefixWord ++ tailWord_473721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473721).length < 2 ^ (prefixWord ++ tailWord_473721).sum := by decide
  have hdescent : baseEnd_473721 < baseStart_473721 := by decide
  rcases family_descends (prefixWord ++ tailWord_473721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473890 : List Nat := [3, 3, 1, 1, 2, 4, 5]
def baseStart_473890 : Nat := 118140960795 + 473890 * 2 ^ 59
def prefixEnd_473890 : Nat := 4983230072969 + 3 ^ 40 * 473890 * 2
def baseEnd_473890 : Nat := 48065846391951829510247

theorem tailTrace_473890 : CollatzResearch.WordTrace tailWord_473890 prefixEnd_473890 48065846391951829510247 := by
  unfold tailWord_473890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321047063296234703406781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11522792168789959209084749 4321047063296234703406781)
  ·
    refine ⟨1620392648736088013777543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4321047063296234703406781 1620392648736088013777543)
    ·
      refine ⟨2430588973104132020666315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620392648736088013777543 2430588973104132020666315)
      ·
        refine ⟨3645883459656198030999473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430588973104132020666315 3645883459656198030999473)
        ·
          refine ⟨2734412594742148523249605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645883459656198030999473 2734412594742148523249605)
          ·
            refine ⟨512702361514152848109301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2734412594742148523249605 512702361514152848109301)
            ·
              refine ⟨48065846391951829510247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512702361514152848109301 48065846391951829510247)
              ·
                rfl

theorem cell19_473890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_473890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473890 prefixEnd_473890 := by exact prefixLift 473890
  have htrace : WordTrace (prefixWord ++ tailWord_473890) baseStart_473890 baseEnd_473890 := by
    simpa [prefixWord, tailWord_473890, baseEnd_473890] using wordTrace_append hprefix tailTrace_473890
  have hstable : (prefixWord ++ tailWord_473890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473890).length < 2 ^ (prefixWord ++ tailWord_473890).sum := by decide
  have hdescent : baseEnd_473890 < baseStart_473890 := by decide
  rcases family_descends (prefixWord ++ tailWord_473890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473909 : List Nat := [1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_473909 : Nat := 118140960795 + 473909 * 2 ^ 59
def prefixEnd_473909 : Nat := 4983230072969 + 3 ^ 40 * 473909 * 2
def baseEnd_473909 : Nat := 144203320587669074108467

theorem tailTrace_473909 : CollatzResearch.WordTrace tailWord_473909 prefixEnd_473909 144203320587669074108467 := by
  unfold tailWord_473909
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284881240116105058568781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11523254160077403372379187 17284881240116105058568781)
  ·
    refine ⟨6481830465043539396963293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17284881240116105058568781 6481830465043539396963293)
    ·
      refine ⟨2430686424391327273861235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6481830465043539396963293 2430686424391327273861235)
      ·
        refine ⟨3646029636586990910791853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430686424391327273861235 3646029636586990910791853)
        ·
          refine ⟨1367261113720121591546945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3646029636586990910791853 1367261113720121591546945)
          ·
            refine ⟨1025445835290091193660209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367261113720121591546945 1025445835290091193660209)
            ·
              refine ⟨769084376467568395245157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025445835290091193660209 769084376467568395245157)
              ·
                refine ⟨144203320587669074108467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769084376467568395245157 144203320587669074108467)
                ·
                  rfl

theorem cell19_473909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_473909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473909 prefixEnd_473909 := by exact prefixLift 473909
  have htrace : WordTrace (prefixWord ++ tailWord_473909) baseStart_473909 baseEnd_473909 := by
    simpa [prefixWord, tailWord_473909, baseEnd_473909] using wordTrace_append hprefix tailTrace_473909
  have hstable : (prefixWord ++ tailWord_473909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473909).length < 2 ^ (prefixWord ++ tailWord_473909).sum := by decide
  have hdescent : baseEnd_473909 < baseStart_473909 := by decide
  rcases family_descends (prefixWord ++ tailWord_473909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473911 : List Nat := [1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_473911 : Nat := 118140960795 + 473911 * 2 ^ 59
def prefixEnd_473911 : Nat := 4983230072969 + 3 ^ 40 * 473911 * 2
def baseEnd_473911 : Nat := 144203929157333662064017

theorem tailTrace_473911 : CollatzResearch.WordTrace tailWord_473911 prefixEnd_473911 144203929157333662064017 := by
  unfold tailWord_473911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284954186108859400141587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11523302790739239600094391 17284954186108859400141587)
  ·
    refine ⟨25927431279163289100212381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17284954186108859400141587 25927431279163289100212381)
    ·
      refine ⟨9722786729686233412579643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25927431279163289100212381 9722786729686233412579643)
      ·
        refine ⟨14584180094529350118869465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722786729686233412579643 14584180094529350118869465)
        ·
          refine ⟨10938135070897012589152099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14584180094529350118869465 10938135070897012589152099)
          ·
            refine ⟨16407202606345518883728149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938135070897012589152099 16407202606345518883728149)
            ·
              refine ⟨769087622172446197674757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16407202606345518883728149 769087622172446197674757)
              ·
                refine ⟨144203929157333662064017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769087622172446197674757 144203929157333662064017)
                ·
                  rfl

theorem cell19_473911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_473911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473911 prefixEnd_473911 := by exact prefixLift 473911
  have htrace : WordTrace (prefixWord ++ tailWord_473911) baseStart_473911 baseEnd_473911 := by
    simpa [prefixWord, tailWord_473911, baseEnd_473911] using wordTrace_append hprefix tailTrace_473911
  have hstable : (prefixWord ++ tailWord_473911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473911).length < 2 ^ (prefixWord ++ tailWord_473911).sum := by decide
  have hdescent : baseEnd_473911 < baseStart_473911 := by decide
  rcases family_descends (prefixWord ++ tailWord_473911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473968 : List Nat := [2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_473968 : Nat := 118140960795 + 473968 * 2 ^ 59
def prefixEnd_473968 : Nat := 4983230072969 + 3 ^ 40 * 473968 * 2
def baseEnd_473968 : Nat := 144221273392774418797195

theorem tailTrace_473968 : CollatzResearch.WordTrace tailWord_473968 prefixEnd_473968 144221273392774418797195 := by
  unfold tailWord_473968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643516573451179067483279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11524688764601572089977705 8643516573451179067483279)
  ·
    refine ⟨12965274860176768601224919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8643516573451179067483279 12965274860176768601224919)
    ·
      refine ⟨19447912290265152901837379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12965274860176768601224919 19447912290265152901837379)
      ·
        refine ⟨29171868435397729352756069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19447912290265152901837379 29171868435397729352756069)
        ·
          refine ⟨5469725331637074253641763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29171868435397729352756069 5469725331637074253641763)
          ·
            refine ⟨8204587997455611380462645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469725331637074253641763 8204587997455611380462645)
            ·
              refine ⟨769180124761463566918373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8204587997455611380462645 769180124761463566918373)
              ·
                refine ⟨144221273392774418797195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769180124761463566918373 144221273392774418797195)
                ·
                  rfl

theorem cell19_473968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_473968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_473968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_473968 prefixEnd_473968 := by exact prefixLift 473968
  have htrace : WordTrace (prefixWord ++ tailWord_473968) baseStart_473968 baseEnd_473968 := by
    simpa [prefixWord, tailWord_473968, baseEnd_473968] using wordTrace_append hprefix tailTrace_473968
  have hstable : (prefixWord ++ tailWord_473968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473968).length < 2 ^ (prefixWord ++ tailWord_473968).sum := by decide
  have hdescent : baseEnd_473968 < baseStart_473968 := by decide
  rcases family_descends (prefixWord ++ tailWord_473968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474063 : List Nat := [1, 1, 2, 1, 1, 8, 5]
def baseStart_474063 : Nat := 118140960795 + 474063 * 2 ^ 59
def prefixEnd_474063 : Nat := 4983230072969 + 3 ^ 40 * 474063 * 2
def baseEnd_474063 : Nat := 48083393483947448895275

theorem tailTrace_474063 : CollatzResearch.WordTrace tailWord_474063 prefixEnd_474063 48083393483947448895275 := by
  unfold tailWord_474063
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290498081558189359674843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11526998721038792906449895 17290498081558189359674843)
  ·
    refine ⟨25935747122337284039512265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290498081558189359674843 25935747122337284039512265)
    ·
      refine ⟨19451810341752963029634199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25935747122337284039512265 19451810341752963029634199)
      ·
        refine ⟨29177715512629444544451299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19451810341752963029634199 29177715512629444544451299)
        ·
          refine ⟨43766573268944166816676949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29177715512629444544451299 43766573268944166816676949)
          ·
            refine ⟨512889530495439454882933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43766573268944166816676949 512889530495439454882933)
            ·
              refine ⟨48083393483947448895275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512889530495439454882933 48083393483947448895275)
              ·
                rfl

theorem cell19_474063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_474063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474063 prefixEnd_474063 := by exact prefixLift 474063
  have htrace : WordTrace (prefixWord ++ tailWord_474063) baseStart_474063 baseEnd_474063 := by
    simpa [prefixWord, tailWord_474063, baseEnd_474063] using wordTrace_append hprefix tailTrace_474063
  have hstable : (prefixWord ++ tailWord_474063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474063).length < 2 ^ (prefixWord ++ tailWord_474063).sum := by decide
  have hdescent : baseEnd_474063 < baseStart_474063 := by decide
  rcases family_descends (prefixWord ++ tailWord_474063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474154 : List Nat := [3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_474154 : Nat := 118140960795 + 474154 * 2 ^ 59
def prefixEnd_474154 : Nat := 4983230072969 + 3 ^ 40 * 474154 * 2
def baseEnd_474154 : Nat := 144277870371581098663355

theorem tailTrace_474154 : CollatzResearch.WordTrace tailWord_474154 prefixEnd_474154 144277870371581098663355 := by
  unfold tailWord_474154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323454281057127975309379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11529211416152341267491677 4323454281057127975309379)
  ·
    refine ⟨6485181421585691962964069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323454281057127975309379 6485181421585691962964069)
    ·
      refine ⟨1215971516547317243055763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6485181421585691962964069 1215971516547317243055763)
      ·
        refine ⟨1823957274820975864583645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215971516547317243055763 1823957274820975864583645)
        ·
          refine ⟨683983978057865949218867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823957274820975864583645 683983978057865949218867)
          ·
            refine ⟨1025975967086798923828301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683983978057865949218867 1025975967086798923828301)
            ·
              refine ⟨384740987657549596435613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025975967086798923828301 384740987657549596435613)
              ·
                refine ⟨144277870371581098663355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384740987657549596435613 144277870371581098663355)
                ·
                  rfl

theorem cell19_474154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_474154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474154 prefixEnd_474154 := by exact prefixLift 474154
  have htrace : WordTrace (prefixWord ++ tailWord_474154) baseStart_474154 baseEnd_474154 := by
    simpa [prefixWord, tailWord_474154, baseEnd_474154] using wordTrace_append hprefix tailTrace_474154
  have hstable : (prefixWord ++ tailWord_474154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474154).length < 2 ^ (prefixWord ++ tailWord_474154).sum := by decide
  have hdescent : baseEnd_474154 < baseStart_474154 := by decide
  rcases family_descends (prefixWord ++ tailWord_474154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474179 : List Nat := [1, 1, 1, 3, 1, 2, 10]
def baseStart_474179 : Nat := 118140960795 + 474179 * 2 ^ 59
def prefixEnd_474179 : Nat := 4983230072969 + 3 ^ 40 * 474179 * 2
def baseEnd_474179 : Nat := 48095159164129482702577

theorem tailTrace_474179 : CollatzResearch.WordTrace tailWord_474179 prefixEnd_474179 48095159164129482702577 := by
  unfold tailWord_474179
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294728949137941170897591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11529819299425294113931727 17294728949137941170897591)
  ·
    refine ⟨25942093423706911756346387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17294728949137941170897591 25942093423706911756346387)
    ·
      refine ⟨38913140135560367634519581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25942093423706911756346387 38913140135560367634519581)
      ·
        refine ⟨14592427550835137862944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38913140135560367634519581 14592427550835137862944843)
        ·
          refine ⟨21888641326252706794417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592427550835137862944843 21888641326252706794417265)
          ·
            refine ⟨16416480994689530095812949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21888641326252706794417265 16416480994689530095812949)
            ·
              refine ⟨48095159164129482702577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16416480994689530095812949 48095159164129482702577)
              ·
                rfl

theorem cell19_474179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_474179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474179 prefixEnd_474179 := by exact prefixLift 474179
  have htrace : WordTrace (prefixWord ++ tailWord_474179) baseStart_474179 baseEnd_474179 := by
    simpa [prefixWord, tailWord_474179, baseEnd_474179] using wordTrace_append hprefix tailTrace_474179
  have hstable : (prefixWord ++ tailWord_474179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474179).length < 2 ^ (prefixWord ++ tailWord_474179).sum := by decide
  have hdescent : baseEnd_474179 < baseStart_474179 := by decide
  rcases family_descends (prefixWord ++ tailWord_474179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474215 : List Nat := [1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_474215 : Nat := 118140960795 + 474215 * 2 ^ 59
def prefixEnd_474215 : Nat := 4983230072969 + 3 ^ 40 * 474215 * 2
def baseEnd_474215 : Nat := 144296431746351031307633

theorem tailTrace_474215 : CollatzResearch.WordTrace tailWord_474215 prefixEnd_474215 144296431746351031307633 := by
  unfold tailWord_474215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296041977007519319208099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530694651338346212805399 17296041977007519319208099)
  ·
    refine ⟨25944062965511278978812149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296041977007519319208099 25944062965511278978812149)
    ·
      refine ⟨2432255903016682404263639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25944062965511278978812149 2432255903016682404263639)
      ·
        refine ⟨3648383854525023606395459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432255903016682404263639 3648383854525023606395459)
        ·
          refine ⟨5472575781787535409593189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648383854525023606395459 5472575781787535409593189)
          ·
            refine ⟨1026107959085162889298723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5472575781787535409593189 1026107959085162889298723)
            ·
              refine ⟨1539161938627744333948085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026107959085162889298723 1539161938627744333948085)
              ·
                refine ⟨144296431746351031307633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1539161938627744333948085 144296431746351031307633)
                ·
                  rfl

theorem cell19_474215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_474215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474215 prefixEnd_474215 := by exact prefixLift 474215
  have htrace : WordTrace (prefixWord ++ tailWord_474215) baseStart_474215 baseEnd_474215 := by
    simpa [prefixWord, tailWord_474215, baseEnd_474215] using wordTrace_append hprefix tailTrace_474215
  have hstable : (prefixWord ++ tailWord_474215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474215).length < 2 ^ (prefixWord ++ tailWord_474215).sum := by decide
  have hdescent : baseEnd_474215 < baseStart_474215 := by decide
  rcases family_descends (prefixWord ++ tailWord_474215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474270 : List Nat := [4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_474270 : Nat := 118140960795 + 474270 * 2 ^ 59
def prefixEnd_474270 : Nat := 4983230072969 + 3 ^ 40 * 474270 * 2
def baseEnd_474270 : Nat := 144313167412127200085261

theorem tailTrace_474270 : CollatzResearch.WordTrace tailWord_474270 prefixEnd_474270 144313167412127200085261 := by
  unfold tailWord_474270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162255998976032964057533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11532031994538842474973509 2162255998976032964057533)
  ·
    refine ⟨810845999616012361521575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2162255998976032964057533 810845999616012361521575)
    ·
      refine ⟨1216268999424018542282363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810845999616012361521575 1216268999424018542282363)
      ·
        refine ⟨1824403499136027813423545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216268999424018542282363 1824403499136027813423545)
        ·
          refine ⟨1368302624352020860067659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824403499136027813423545 1368302624352020860067659)
          ·
            refine ⟨2052453936528031290101489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368302624352020860067659 2052453936528031290101489)
            ·
              refine ⟨1539340452396023467576117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052453936528031290101489 1539340452396023467576117)
              ·
                refine ⟨144313167412127200085261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1539340452396023467576117 144313167412127200085261)
                ·
                  rfl

theorem cell19_474270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_474270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474270 prefixEnd_474270 := by exact prefixLift 474270
  have htrace : WordTrace (prefixWord ++ tailWord_474270) baseStart_474270 baseEnd_474270 := by
    simpa [prefixWord, tailWord_474270, baseEnd_474270] using wordTrace_append hprefix tailTrace_474270
  have hstable : (prefixWord ++ tailWord_474270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474270).length < 2 ^ (prefixWord ++ tailWord_474270).sum := by decide
  have hdescent : baseEnd_474270 < baseStart_474270 := by decide
  rcases family_descends (prefixWord ++ tailWord_474270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474293 : List Nat := [1, 3, 3, 12]
def baseStart_474293 : Nat := 118140960795 + 474293 * 2 ^ 59
def prefixEnd_474293 : Nat := 4983230072969 + 3 ^ 40 * 474293 * 2
def baseEnd_474293 : Nat := 1781730443990987179927

theorem tailTrace_474293 : CollatzResearch.WordTrace tailWord_474293 prefixEnd_474293 1781730443990987179927 := by
  unfold tailWord_474293
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298886870724938640547533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11532591247149959093698355 17298886870724938640547533)
  ·
    refine ⟨6487082576521851990205325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17298886870724938640547533 6487082576521851990205325)
    ·
      refine ⟨2432655966195694496326997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6487082576521851990205325 2432655966195694496326997)
      ·
        refine ⟨1781730443990987179927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2432655966195694496326997 1781730443990987179927)
        ·
          rfl

theorem cell19_474293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 12].length) (baseStart_474293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474293 prefixEnd_474293 := by exact prefixLift 474293
  have htrace : WordTrace (prefixWord ++ tailWord_474293) baseStart_474293 baseEnd_474293 := by
    simpa [prefixWord, tailWord_474293, baseEnd_474293] using wordTrace_append hprefix tailTrace_474293
  have hstable : (prefixWord ++ tailWord_474293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474293).length < 2 ^ (prefixWord ++ tailWord_474293).sum := by decide
  have hdescent : baseEnd_474293 < baseStart_474293 := by decide
  rcases family_descends (prefixWord ++ tailWord_474293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474405 : List Nat := [1, 3, 1, 2, 4, 3, 5]
def baseStart_474405 : Nat := 118140960795 + 474405 * 2 ^ 59
def prefixEnd_474405 : Nat := 4983230072969 + 3 ^ 40 * 474405 * 2
def baseEnd_474405 : Nat := 48118081954828962361631

theorem tailTrace_474405 : CollatzResearch.WordTrace tailWord_474405 prefixEnd_474405 48118081954828962361631 := by
  unfold tailWord_474405
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302971846319181768624669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11535314564212787845749779 17302971846319181768624669)
  ·
    refine ⟨6488614442369693163234251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17302971846319181768624669 6488614442369693163234251)
    ·
      refine ⟨9732921663554539744851377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488614442369693163234251 9732921663554539744851377)
      ·
        refine ⟨7299691247665904808638533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732921663554539744851377 7299691247665904808638533)
        ·
          refine ⟨1368692108937357151619725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7299691247665904808638533 1368692108937357151619725)
          ·
            refine ⟨513259540851508931857397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368692108937357151619725 513259540851508931857397)
            ·
              refine ⟨48118081954828962361631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 513259540851508931857397 48118081954828962361631)
              ·
                rfl

theorem cell19_474405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_474405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474405 prefixEnd_474405 := by exact prefixLift 474405
  have htrace : WordTrace (prefixWord ++ tailWord_474405) baseStart_474405 baseEnd_474405 := by
    simpa [prefixWord, tailWord_474405, baseEnd_474405] using wordTrace_append hprefix tailTrace_474405
  have hstable : (prefixWord ++ tailWord_474405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474405).length < 2 ^ (prefixWord ++ tailWord_474405).sum := by decide
  have hdescent : baseEnd_474405 < baseStart_474405 := by decide
  rcases family_descends (prefixWord ++ tailWord_474405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474464 : List Nat := [2, 1, 1, 3, 4, 8]
def baseStart_474464 : Nat := 118140960795 + 474464 * 2 ^ 59
def prefixEnd_474464 : Nat := 4983230072969 + 3 ^ 40 * 474464 * 2
def baseEnd_474464 : Nat := 16041355407732470197069

theorem tailTrace_474464 : CollatzResearch.WordTrace tailWord_474464 prefixEnd_474464 16041355407732470197069 := by
  unfold tailWord_474464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652561876552717422511223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11536749168736956563348297 8652561876552717422511223)
  ·
    refine ⟨12978842814829076133766835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652561876552717422511223 12978842814829076133766835)
    ·
      refine ⟨19468264222243614200650253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12978842814829076133766835 19468264222243614200650253)
      ·
        refine ⟨7300599083341355325243845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19468264222243614200650253 7300599083341355325243845)
        ·
          refine ⟨1368862328126504123483221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7300599083341355325243845 1368862328126504123483221)
          ·
            refine ⟨16041355407732470197069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1368862328126504123483221 16041355407732470197069)
            ·
              rfl

theorem cell19_474464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_474464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474464 prefixEnd_474464 := by exact prefixLift 474464
  have htrace : WordTrace (prefixWord ++ tailWord_474464) baseStart_474464 baseEnd_474464 := by
    simpa [prefixWord, tailWord_474464, baseEnd_474464] using wordTrace_append hprefix tailTrace_474464
  have hstable : (prefixWord ++ tailWord_474464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474464).length < 2 ^ (prefixWord ++ tailWord_474464).sum := by decide
  have hdescent : baseEnd_474464 < baseStart_474464 := by decide
  rcases family_descends (prefixWord ++ tailWord_474464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474494 : List Nat := [4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_474494 : Nat := 118140960795 + 474494 * 2 ^ 59
def prefixEnd_474494 : Nat := 4983230072969 + 3 ^ 40 * 474494 * 2
def baseEnd_474494 : Nat := 144381327214561051106873

theorem tailTrace_474494 : CollatzResearch.WordTrace tailWord_474494 prefixEnd_474494 144381327214561051106873 := by
  unfold tailWord_474494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163277242874593746076817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11537478628664499979076357 2163277242874593746076817)
  ·
    refine ⟨1622457932155945309557613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2163277242874593746076817 1622457932155945309557613)
    ·
      refine ⟨608421724558479491084105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1622457932155945309557613 608421724558479491084105)
      ·
        refine ⟨456316293418859618313079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608421724558479491084105 456316293418859618313079)
        ·
          refine ⟨684474440128289427469619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456316293418859618313079 684474440128289427469619)
          ·
            refine ⟨1026711660192434141204429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684474440128289427469619 1026711660192434141204429)
            ·
              refine ⟨385016872572162802951661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026711660192434141204429 385016872572162802951661)
              ·
                refine ⟨144381327214561051106873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385016872572162802951661 144381327214561051106873)
                ·
                  rfl

theorem cell19_474494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_474494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474494 prefixEnd_474494 := by exact prefixLift 474494
  have htrace : WordTrace (prefixWord ++ tailWord_474494) baseStart_474494 baseEnd_474494 := by
    simpa [prefixWord, tailWord_474494, baseEnd_474494] using wordTrace_append hprefix tailTrace_474494
  have hstable : (prefixWord ++ tailWord_474494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474494).length < 2 ^ (prefixWord ++ tailWord_474494).sum := by decide
  have hdescent : baseEnd_474494 < baseStart_474494 := by decide
  rcases family_descends (prefixWord ++ tailWord_474494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474521 : List Nat := [1, 2, 1, 2, 1, 6, 6]
def baseStart_474521 : Nat := 118140960795 + 474521 * 2 ^ 59
def prefixEnd_474521 : Nat := 4983230072969 + 3 ^ 40 * 474521 * 2
def baseEnd_474521 : Nat := 48129847635010996168933

theorem tailTrace_474521 : CollatzResearch.WordTrace tailWord_474521 prefixEnd_474521 48129847635010996168933 := by
  unfold tailWord_474521
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307202713898933579847417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11538135142599289053231611 17307202713898933579847417)
  ·
    refine ⟨12980402035424200184885563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17307202713898933579847417 12980402035424200184885563)
    ·
      refine ⟨19470603053136300277328345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12980402035424200184885563 19470603053136300277328345)
      ·
        refine ⟨14602952289852225207996259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19470603053136300277328345 14602952289852225207996259)
        ·
          refine ⟨21904428434778337811994389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602952289852225207996259 21904428434778337811994389)
          ·
            refine ⟨1026770082880234584937237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21904428434778337811994389 1026770082880234584937237)
            ·
              refine ⟨48129847635010996168933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1026770082880234584937237 48129847635010996168933)
              ·
                rfl

theorem cell19_474521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_474521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474521 prefixEnd_474521 := by exact prefixLift 474521
  have htrace : WordTrace (prefixWord ++ tailWord_474521) baseStart_474521 baseEnd_474521 := by
    simpa [prefixWord, tailWord_474521, baseEnd_474521] using wordTrace_append hprefix tailTrace_474521
  have hstable : (prefixWord ++ tailWord_474521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474521).length < 2 ^ (prefixWord ++ tailWord_474521).sum := by decide
  have hdescent : baseEnd_474521 < baseStart_474521 := by decide
  rcases family_descends (prefixWord ++ tailWord_474521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474553 : List Nat := [1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_474553 : Nat := 118140960795 + 474553 * 2 ^ 59
def prefixEnd_474553 : Nat := 4983230072969 + 3 ^ 40 * 474553 * 2
def baseEnd_474553 : Nat := 144399280019666395795601

theorem tailTrace_474553 : CollatzResearch.WordTrace tailWord_474553 prefixEnd_474553 144399280019666395795601 := by
  unfold tailWord_474553
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308369849783003045012313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11538913233188668696674875 17308369849783003045012313)
  ·
    refine ⟨12981277387337252283759235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17308369849783003045012313 12981277387337252283759235)
    ·
      refine ⟨19471916081005878425638853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981277387337252283759235 19471916081005878425638853)
      ·
        refine ⟨3650984265188602204807285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19471916081005878425638853 3650984265188602204807285)
        ·
          refine ⟨342279774861431456700683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3650984265188602204807285 342279774861431456700683)
          ·
            refine ⟨513419662292147185051025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342279774861431456700683 513419662292147185051025)
            ·
              refine ⟨385064746719110388788269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513419662292147185051025 385064746719110388788269)
              ·
                refine ⟨144399280019666395795601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385064746719110388788269 144399280019666395795601)
                ·
                  rfl

theorem cell19_474553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_474553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474553 prefixEnd_474553 := by exact prefixLift 474553
  have htrace : WordTrace (prefixWord ++ tailWord_474553) baseStart_474553 baseEnd_474553 := by
    simpa [prefixWord, tailWord_474553, baseEnd_474553] using wordTrace_append hprefix tailTrace_474553
  have hstable : (prefixWord ++ tailWord_474553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474553).length < 2 ^ (prefixWord ++ tailWord_474553).sum := by decide
  have hdescent : baseEnd_474553 < baseStart_474553 := by decide
  rcases family_descends (prefixWord ++ tailWord_474553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474595 : List Nat := [1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_474595 : Nat := 118140960795 + 474595 * 2 ^ 59
def prefixEnd_474595 : Nat := 4983230072969 + 3 ^ 40 * 474595 * 2
def baseEnd_474595 : Nat := 144412059982622742862153

theorem tailTrace_474595 : CollatzResearch.WordTrace tailWord_474595 prefixEnd_474595 144412059982622742862153 := by
  unfold tailWord_474595
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309901715630844218041239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11539934477087229478694159 17309901715630844218041239)
  ·
    refine ⟨25964852573446266327061859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309901715630844218041239 25964852573446266327061859)
    ·
      refine ⟨38947278860169399490592789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25964852573446266327061859 38947278860169399490592789)
      ·
        refine ⟨1825653696570440601121537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38947278860169399490592789 1825653696570440601121537)
        ·
          refine ⟨1369240272427830450841153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825653696570440601121537 1369240272427830450841153)
          ·
            refine ⟨1026930204320872838130865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369240272427830450841153 1026930204320872838130865)
            ·
              refine ⟨770197653240654628598149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026930204320872838130865 770197653240654628598149)
              ·
                refine ⟨144412059982622742862153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770197653240654628598149 144412059982622742862153)
                ·
                  rfl

theorem cell19_474595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_474595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474595 prefixEnd_474595 := by exact prefixLift 474595
  have htrace : WordTrace (prefixWord ++ tailWord_474595) baseStart_474595 baseEnd_474595 := by
    simpa [prefixWord, tailWord_474595, baseEnd_474595] using wordTrace_append hprefix tailTrace_474595
  have hstable : (prefixWord ++ tailWord_474595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474595).length < 2 ^ (prefixWord ++ tailWord_474595).sum := by decide
  have hdescent : baseEnd_474595 < baseStart_474595 := by decide
  rcases family_descends (prefixWord ++ tailWord_474595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474614 : List Nat := [5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_474614 : Nat := 118140960795 + 474614 * 2 ^ 59
def prefixEnd_474614 : Nat := 4983230072969 + 3 ^ 40 * 474614 * 2
def baseEnd_474614 : Nat := 144417841394436328439879

theorem tailTrace_474614 : CollatzResearch.WordTrace tailWord_474614 prefixEnd_474614 144417841394436328439879 := by
  unfold tailWord_474614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081912168910125653936431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11540396468374673641988597 1081912168910125653936431)
  ·
    refine ⟨1622868253365188480904647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1081912168910125653936431 1622868253365188480904647)
    ·
      refine ⟨2434302380047782721356971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622868253365188480904647 2434302380047782721356971)
      ·
        refine ⟨3651453570071674082035457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434302380047782721356971 3651453570071674082035457)
        ·
          refine ⟨2738590177553755561526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651453570071674082035457 2738590177553755561526593)
          ·
            refine ⟨2053942633165316671144945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738590177553755561526593 2053942633165316671144945)
            ·
              refine ⟨1540456974873987503358709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053942633165316671144945 1540456974873987503358709)
              ·
                refine ⟨144417841394436328439879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1540456974873987503358709 144417841394436328439879)
                ·
                  rfl

theorem cell19_474614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_474614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474614 prefixEnd_474614 := by exact prefixLift 474614
  have htrace : WordTrace (prefixWord ++ tailWord_474614) baseStart_474614 baseEnd_474614 := by
    simpa [prefixWord, tailWord_474614, baseEnd_474614] using wordTrace_append hprefix tailTrace_474614
  have hstable : (prefixWord ++ tailWord_474614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474614).length < 2 ^ (prefixWord ++ tailWord_474614).sum := by decide
  have hdescent : baseEnd_474614 < baseStart_474614 := by decide
  rcases family_descends (prefixWord ++ tailWord_474614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474616 : List Nat := [2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_474616 : Nat := 118140960795 + 474616 * 2 ^ 59
def prefixEnd_474616 : Nat := 4983230072969 + 3 ^ 40 * 474616 * 2
def baseEnd_474616 : Nat := 144418449964100916395429

theorem tailTrace_474616 : CollatzResearch.WordTrace tailWord_474616 prefixEnd_474616 144418449964100916395429 := by
  unfold tailWord_474616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655333824277382402277851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11540445099036509869703801 8655333824277382402277851)
  ·
    refine ⟨12983000736416073603416777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655333824277382402277851 12983000736416073603416777)
    ·
      refine ⟨9737250552312055202562583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12983000736416073603416777 9737250552312055202562583)
      ·
        refine ⟨14605875828468082803843875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9737250552312055202562583 14605875828468082803843875)
        ·
          refine ⟨21908813742702124205765813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14605875828468082803843875 21908813742702124205765813)
          ·
            refine ⟨2053951288378324144290545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21908813742702124205765813 2053951288378324144290545)
            ·
              refine ⟨1540463466283743108217909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053951288378324144290545 1540463466283743108217909)
              ·
                refine ⟨144418449964100916395429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1540463466283743108217909 144418449964100916395429)
                ·
                  rfl

theorem cell19_474616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_474616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474616 prefixEnd_474616 := by exact prefixLift 474616
  have htrace : WordTrace (prefixWord ++ tailWord_474616) baseStart_474616 baseEnd_474616 := by
    simpa [prefixWord, tailWord_474616, baseEnd_474616] using wordTrace_append hprefix tailTrace_474616
  have hstable : (prefixWord ++ tailWord_474616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474616).length < 2 ^ (prefixWord ++ tailWord_474616).sum := by decide
  have hdescent : baseEnd_474616 < baseStart_474616 := by decide
  rcases family_descends (prefixWord ++ tailWord_474616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474635 : List Nat := [1, 1, 1, 1, 8, 7]
def baseStart_474635 : Nat := 118140960795 + 474635 * 2 ^ 59
def prefixEnd_474635 : Nat := 4983230072969 + 3 ^ 40 * 474635 * 2
def baseEnd_474635 : Nat := 16047136819546055774795

theorem tailTrace_474635 : CollatzResearch.WordTrace tailWord_474635 prefixEnd_474635 16047136819546055774795 := by
  unfold tailWord_474635
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311360635485931049497359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11540907090323954032998239 17311360635485931049497359)
  ·
    refine ⟨25967040953228896574246039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17311360635485931049497359 25967040953228896574246039)
    ·
      refine ⟨38950561429843344861369059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25967040953228896574246039 38950561429843344861369059)
      ·
        refine ⟨58425842144765017292053589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38950561429843344861369059 58425842144765017292053589)
        ·
          refine ⟨684677837633965046391253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 58425842144765017292053589 684677837633965046391253)
          ·
            refine ⟨16047136819546055774795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 684677837633965046391253 16047136819546055774795)
            ·
              rfl

theorem cell19_474635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_474635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474635 prefixEnd_474635 := by exact prefixLift 474635
  have htrace : WordTrace (prefixWord ++ tailWord_474635) baseStart_474635 baseEnd_474635 := by
    simpa [prefixWord, tailWord_474635, baseEnd_474635] using wordTrace_append hprefix tailTrace_474635
  have hstable : (prefixWord ++ tailWord_474635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474635).length < 2 ^ (prefixWord ++ tailWord_474635).sum := by decide
  have hdescent : baseEnd_474635 < baseStart_474635 := by decide
  rcases family_descends (prefixWord ++ tailWord_474635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474728 : List Nat := [2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_474728 : Nat := 118140960795 + 474728 * 2 ^ 59
def prefixEnd_474728 : Nat := 4983230072969 + 3 ^ 40 * 474728 * 2
def baseEnd_474728 : Nat := 144452529865317841906235

theorem tailTrace_474728 : CollatzResearch.WordTrace tailWord_474728 prefixEnd_474728 144452529865317841906235 := by
  unfold tailWord_474728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657376312074503966316419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11543168416099338621755225 8657376312074503966316419)
  ·
    refine ⟨12986064468111755949474629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657376312074503966316419 12986064468111755949474629)
    ·
      refine ⟨2434887087770954240526493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12986064468111755949474629 2434887087770954240526493)
      ·
        refine ⟨913082657914107840197435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2434887087770954240526493 913082657914107840197435)
        ·
          refine ⟨1369623986871161760296153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913082657914107840197435 1369623986871161760296153)
          ·
            refine ⟨1027217990153371320222115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369623986871161760296153 1027217990153371320222115)
            ·
              refine ⟨1540826985230056980333173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027217990153371320222115 1540826985230056980333173)
              ·
                refine ⟨144452529865317841906235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1540826985230056980333173 144452529865317841906235)
                ·
                  rfl

theorem cell19_474728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_474728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474728 prefixEnd_474728 := by exact prefixLift 474728
  have htrace : WordTrace (prefixWord ++ tailWord_474728) baseStart_474728 baseEnd_474728 := by
    simpa [prefixWord, tailWord_474728, baseEnd_474728] using wordTrace_append hprefix tailTrace_474728
  have hstable : (prefixWord ++ tailWord_474728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474728).length < 2 ^ (prefixWord ++ tailWord_474728).sum := by decide
  have hdescent : baseEnd_474728 < baseStart_474728 := by decide
  rcases family_descends (prefixWord ++ tailWord_474728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474749 : List Nat := [1, 4, 1, 1, 4, 1, 7]
def baseStart_474749 : Nat := 118140960795 + 474749 * 2 ^ 59
def prefixEnd_474749 : Nat := 4983230072969 + 3 ^ 40 * 474749 * 2
def baseEnd_474749 : Nat := 48152973282265338479837

theorem tailTrace_474749 : CollatzResearch.WordTrace tailWord_474749 prefixEnd_474749 48152973282265338479837 := by
  unfold tailWord_474749
  simp only [CollatzResearch.WordTrace]
  refine ⟨17315518557072928519147301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11543679038048619012764867 17315518557072928519147301)
  ·
    refine ⟨3246659729451174097340119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17315518557072928519147301 3246659729451174097340119)
    ·
      refine ⟨4869989594176761146010179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246659729451174097340119 4869989594176761146010179)
      ·
        refine ⟨7304984391265141719015269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869989594176761146010179 7304984391265141719015269)
        ·
          refine ⟨1369684573362214072315363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7304984391265141719015269 1369684573362214072315363)
          ·
            refine ⟨2054526860043321108473045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369684573362214072315363 2054526860043321108473045)
            ·
              refine ⟨48152973282265338479837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2054526860043321108473045 48152973282265338479837)
              ·
                rfl

theorem cell19_474749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_474749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474749 prefixEnd_474749 := by exact prefixLift 474749
  have htrace : WordTrace (prefixWord ++ tailWord_474749) baseStart_474749 baseEnd_474749 := by
    simpa [prefixWord, tailWord_474749, baseEnd_474749] using wordTrace_append hprefix tailTrace_474749
  have hstable : (prefixWord ++ tailWord_474749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474749).length < 2 ^ (prefixWord ++ tailWord_474749).sum := by decide
  have hdescent : baseEnd_474749 < baseStart_474749 := by decide
  rcases family_descends (prefixWord ++ tailWord_474749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474766 : List Nat := [4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_474766 : Nat := 118140960795 + 474766 * 2 ^ 59
def prefixEnd_474766 : Nat := 4983230072969 + 3 ^ 40 * 474766 * 2
def baseEnd_474766 : Nat := 144464092688945013061687

theorem tailTrace_474766 : CollatzResearch.WordTrace tailWord_474766 prefixEnd_474766 144464092688945013061687 := by
  unfold tailWord_474766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164517324751417552814519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11544092398674226948344101 2164517324751417552814519)
  ·
    refine ⟨3246775987127126329221779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164517324751417552814519 3246775987127126329221779)
    ·
      refine ⟨4870163980690689493832669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246775987127126329221779 4870163980690689493832669)
      ·
        refine ⟨1826311492759008560187251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4870163980690689493832669 1826311492759008560187251)
        ·
          refine ⟨2739467239138512840280877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826311492759008560187251 2739467239138512840280877)
          ·
            refine ⟨1027300214676942315105329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2739467239138512840280877 1027300214676942315105329)
            ·
              refine ⟨770475161007706736328997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027300214676942315105329 770475161007706736328997)
              ·
                refine ⟨144464092688945013061687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770475161007706736328997 144464092688945013061687)
                ·
                  rfl

theorem cell19_474766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_474766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474766 prefixEnd_474766 := by exact prefixLift 474766
  have htrace : WordTrace (prefixWord ++ tailWord_474766) baseStart_474766 baseEnd_474766 := by
    simpa [prefixWord, tailWord_474766, baseEnd_474766] using wordTrace_append hprefix tailTrace_474766
  have hstable : (prefixWord ++ tailWord_474766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474766).length < 2 ^ (prefixWord ++ tailWord_474766).sum := by decide
  have hdescent : baseEnd_474766 < baseStart_474766 := by decide
  rcases family_descends (prefixWord ++ tailWord_474766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474842 : List Nat := [3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_474842 : Nat := 118140960795 + 474842 * 2 ^ 59
def prefixEnd_474842 : Nat := 4983230072969 + 3 ^ 40 * 474842 * 2
def baseEnd_474842 : Nat := 144487218336199355372591

theorem tailTrace_474842 : CollatzResearch.WordTrace tailWord_474842 prefixEnd_474842 144487218336199355372591 := by
  unfold tailWord_474842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329727636434001350570695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11545940363824003601521853 4329727636434001350570695)
  ·
    refine ⟨6494591454651002025856043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329727636434001350570695 6494591454651002025856043)
    ·
      refine ⟨9741887181976503038784065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494591454651002025856043 9741887181976503038784065)
      ·
        refine ⟨7306415386482377279088049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741887181976503038784065 7306415386482377279088049)
        ·
          refine ⟨5479811539861782959316037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7306415386482377279088049 5479811539861782959316037)
          ·
            refine ⟨1027464663724084304871757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5479811539861782959316037 1027464663724084304871757)
            ·
              refine ⟨385299248896531614326909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027464663724084304871757 385299248896531614326909)
              ·
                refine ⟨144487218336199355372591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385299248896531614326909 144487218336199355372591)
                ·
                  rfl

theorem cell19_474842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_474842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474842 prefixEnd_474842 := by exact prefixLift 474842
  have htrace : WordTrace (prefixWord ++ tailWord_474842) baseStart_474842 baseEnd_474842 := by
    simpa [prefixWord, tailWord_474842, baseEnd_474842] using wordTrace_append hprefix tailTrace_474842
  have hstable : (prefixWord ++ tailWord_474842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474842).length < 2 ^ (prefixWord ++ tailWord_474842).sum := by decide
  have hdescent : baseEnd_474842 < baseStart_474842 := by decide
  rcases family_descends (prefixWord ++ tailWord_474842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474893 : List Nat := [1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_474893 : Nat := 118140960795 + 474893 * 2 ^ 59
def prefixEnd_474893 : Nat := 4983230072969 + 3 ^ 40 * 474893 * 2
def baseEnd_474893 : Nat := 144502736862646348239119

theorem tailTrace_474893 : CollatzResearch.WordTrace tailWord_474893 prefixEnd_474893 144502736862646348239119 := by
  unfold tailWord_474893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17320770668551241112389333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11547180445700827408259555 17320770668551241112389333)
  ·
    refine ⟨405955562544169713571625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17320770668551241112389333 405955562544169713571625)
    ·
      refine ⟨304466671908127285178719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405955562544169713571625 304466671908127285178719)
      ·
        refine ⟨456700007862190927768079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304466671908127285178719 456700007862190927768079)
        ·
          refine ⟨685050011793286391652119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456700007862190927768079 685050011793286391652119)
          ·
            refine ⟨1027575017689929587478179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685050011793286391652119 1027575017689929587478179)
            ·
              refine ⟨1541362526534894381217269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027575017689929587478179 1541362526534894381217269)
              ·
                refine ⟨144502736862646348239119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1541362526534894381217269 144502736862646348239119)
                ·
                  rfl

theorem cell19_474893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_474893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474893 prefixEnd_474893 := by exact prefixLift 474893
  have htrace : WordTrace (prefixWord ++ tailWord_474893) baseStart_474893 baseEnd_474893 := by
    simpa [prefixWord, tailWord_474893, baseEnd_474893] using wordTrace_append hprefix tailTrace_474893
  have hstable : (prefixWord ++ tailWord_474893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474893).length < 2 ^ (prefixWord ++ tailWord_474893).sum := by decide
  have hdescent : baseEnd_474893 < baseStart_474893 := by decide
  rcases family_descends (prefixWord ++ tailWord_474893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474901 : List Nat := [1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_474901 : Nat := 118140960795 + 474901 * 2 ^ 59
def prefixEnd_474901 : Nat := 4983230072969 + 3 ^ 40 * 474901 * 2
def baseEnd_474901 : Nat := 144505171141304700061319

theorem tailTrace_474901 : CollatzResearch.WordTrace tailWord_474901 prefixEnd_474901 144505171141304700061319 := by
  unfold tailWord_474901
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321062452522258478680557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11547374968348172319120371 17321062452522258478680557)
  ·
    refine ⟨6495398419695846929505209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17321062452522258478680557 6495398419695846929505209)
    ·
      refine ⟨4871548814771885197128907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6495398419695846929505209 4871548814771885197128907)
      ·
        refine ⟨7307323222157827795693361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871548814771885197128907 7307323222157827795693361)
        ·
          refine ⟨5480492416618370846770021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7307323222157827795693361 5480492416618370846770021)
          ·
            refine ⟨1027592328115944533769379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5480492416618370846770021 1027592328115944533769379)
            ·
              refine ⟨1541388492173916800654069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027592328115944533769379 1541388492173916800654069)
              ·
                refine ⟨144505171141304700061319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1541388492173916800654069 144505171141304700061319)
                ·
                  rfl

theorem cell19_474901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_474901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474901 prefixEnd_474901 := by exact prefixLift 474901
  have htrace : WordTrace (prefixWord ++ tailWord_474901) baseStart_474901 baseEnd_474901 := by
    simpa [prefixWord, tailWord_474901, baseEnd_474901] using wordTrace_append hprefix tailTrace_474901
  have hstable : (prefixWord ++ tailWord_474901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474901).length < 2 ^ (prefixWord ++ tailWord_474901).sum := by decide
  have hdescent : baseEnd_474901 < baseStart_474901 := by decide
  rcases family_descends (prefixWord ++ tailWord_474901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474920 : List Nat := [2, 1, 5, 1, 1, 2, 7]
def baseStart_474920 : Nat := 118140960795 + 474920 * 2 ^ 59
def prefixEnd_474920 : Nat := 4983230072969 + 3 ^ 40 * 474920 * 2
def baseEnd_474920 : Nat := 48170317517706095213015

theorem tailTrace_474920 : CollatzResearch.WordTrace tailWord_474920 prefixEnd_474920 48170317517706095213015 := by
  unfold tailWord_474920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660877719726712361811107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11547836959635616482414809 8660877719726712361811107)
  ·
    refine ⟨12991316579590068542716661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8660877719726712361811107 12991316579590068542716661)
    ·
      refine ⟨1217935929336568925879687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12991316579590068542716661 1217935929336568925879687)
      ·
        refine ⟨1826903894004853388819531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217935929336568925879687 1826903894004853388819531)
        ·
          refine ⟨2740355841007280083229297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826903894004853388819531 2740355841007280083229297)
          ·
            refine ⟨2055266880755460062421973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740355841007280083229297 2055266880755460062421973)
            ·
              refine ⟨48170317517706095213015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2055266880755460062421973 48170317517706095213015)
              ·
                rfl

theorem cell19_474920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_474920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474920 prefixEnd_474920 := by exact prefixLift 474920
  have htrace : WordTrace (prefixWord ++ tailWord_474920) baseStart_474920 baseEnd_474920 := by
    simpa [prefixWord, tailWord_474920, baseEnd_474920] using wordTrace_append hprefix tailTrace_474920
  have hstable : (prefixWord ++ tailWord_474920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474920).length < 2 ^ (prefixWord ++ tailWord_474920).sum := by decide
  have hdescent : baseEnd_474920 < baseStart_474920 := by decide
  rcases family_descends (prefixWord ++ tailWord_474920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474979 : List Nat := [1, 1, 1, 5, 11]
def baseStart_474979 : Nat := 118140960795 + 474979 * 2 ^ 59
def prefixEnd_474979 : Nat := 4983230072969 + 3 ^ 40 * 474979 * 2
def baseEnd_474979 : Nat := 5352922420674949271399

theorem tailTrace_474979 : CollatzResearch.WordTrace tailWord_474979 prefixEnd_474979 5352922420674949271399 := by
  unfold tailWord_474979
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323907346239677800019991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11549271564159785200013327 17323907346239677800019991)
  ·
    refine ⟨25985861019359516700029987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17323907346239677800019991 25985861019359516700029987)
    ·
      refine ⟨38978791529039275050044981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25985861019359516700029987 38978791529039275050044981)
      ·
        refine ⟨3654261705847432035941717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38978791529039275050044981 3654261705847432035941717)
        ·
          refine ⟨5352922420674949271399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3654261705847432035941717 5352922420674949271399)
          ·
            rfl

theorem cell19_474979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_474979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_474979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_474979 prefixEnd_474979 := by exact prefixLift 474979
  have htrace : WordTrace (prefixWord ++ tailWord_474979) baseStart_474979 baseEnd_474979 := by
    simpa [prefixWord, tailWord_474979, baseEnd_474979] using wordTrace_append hprefix tailTrace_474979
  have hstable : (prefixWord ++ tailWord_474979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474979).length < 2 ^ (prefixWord ++ tailWord_474979).sum := by decide
  have hdescent : baseEnd_474979 < baseStart_474979 := by decide
  rcases family_descends (prefixWord ++ tailWord_474979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475032 : List Nat := [2, 1, 2, 6, 1, 1, 6]
def baseStart_475032 : Nat := 118140960795 + 475032 * 2 ^ 59
def prefixEnd_475032 : Nat := 4983230072969 + 3 ^ 40 * 475032 * 2
def baseEnd_475032 : Nat := 48181677484778403716617

theorem tailTrace_475032 : CollatzResearch.WordTrace tailWord_475032 prefixEnd_475032 48181677484778403716617 := by
  unfold tailWord_475032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662920207523833925849675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11550560276698445234466233 8662920207523833925849675)
  ·
    refine ⟨12994380311285750888774513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8662920207523833925849675 12994380311285750888774513)
    ·
      refine ⟨9745785233464313166580885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12994380311285750888774513 9745785233464313166580885)
      ·
        refine ⟨456833682818639679683479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9745785233464313166580885 456833682818639679683479)
        ·
          refine ⟨685250524227959519525219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456833682818639679683479 685250524227959519525219)
          ·
            refine ⟨1027875786341939279287829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685250524227959519525219 1027875786341939279287829)
            ·
              refine ⟨48181677484778403716617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1027875786341939279287829 48181677484778403716617)
              ·
                rfl

theorem cell19_475032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_475032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475032 prefixEnd_475032 := by exact prefixLift 475032
  have htrace : WordTrace (prefixWord ++ tailWord_475032) baseStart_475032 baseEnd_475032 := by
    simpa [prefixWord, tailWord_475032, baseEnd_475032] using wordTrace_append hprefix tailTrace_475032
  have hstable : (prefixWord ++ tailWord_475032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475032).length < 2 ^ (prefixWord ++ tailWord_475032).sum := by decide
  have hdescent : baseEnd_475032 < baseStart_475032 := by decide
  rcases family_descends (prefixWord ++ tailWord_475032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475034 : List Nat := [3, 1, 1, 4, 2, 2, 6]
def baseStart_475034 : Nat := 118140960795 + 475034 * 2 ^ 59
def prefixEnd_475034 : Nat := 4983230072969 + 3 ^ 40 * 475034 * 2
def baseEnd_475034 : Nat := 48181880341333266368467

theorem tailTrace_475034 : CollatzResearch.WordTrace tailWord_475034 prefixEnd_475034 48181880341333266368467 := by
  unfold tailWord_475034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331478340260105548318039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11550608907360281462181437 4331478340260105548318039)
  ·
    refine ⟨6497217510390158322477059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331478340260105548318039 6497217510390158322477059)
    ·
      refine ⟨9745826265585237483715589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497217510390158322477059 9745826265585237483715589)
      ·
        refine ⟨1827342424797232028196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9745826265585237483715589 1827342424797232028196673)
        ·
          refine ⟨1370506818597924021147505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827342424797232028196673 1370506818597924021147505)
          ·
            refine ⟨1027880113948443015860629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370506818597924021147505 1027880113948443015860629)
            ·
              refine ⟨48181880341333266368467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1027880113948443015860629 48181880341333266368467)
              ·
                rfl

theorem cell19_475034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_475034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475034 prefixEnd_475034 := by exact prefixLift 475034
  have htrace : WordTrace (prefixWord ++ tailWord_475034) baseStart_475034 baseEnd_475034 := by
    simpa [prefixWord, tailWord_475034, baseEnd_475034] using wordTrace_append hprefix tailTrace_475034
  have hstable : (prefixWord ++ tailWord_475034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475034).length < 2 ^ (prefixWord ++ tailWord_475034).sum := by decide
  have hdescent : baseEnd_475034 < baseStart_475034 := by decide
  rcases family_descends (prefixWord ++ tailWord_475034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475055 : List Nat := [1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_475055 : Nat := 118140960795 + 475055 * 2 ^ 59
def prefixEnd_475055 : Nat := 4983230072969 + 3 ^ 40 * 475055 * 2
def baseEnd_475055 : Nat := 144552031005477972638677

theorem tailTrace_475055 : CollatzResearch.WordTrace tailWord_475055 prefixEnd_475055 144552031005477972638677 := by
  unfold tailWord_475055
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326679293964342779786619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11551119529309561853191079 17326679293964342779786619)
  ·
    refine ⟨25990018940946514169679929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17326679293964342779786619 25990018940946514169679929)
    ·
      refine ⟨19492514205709885627259947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25990018940946514169679929 19492514205709885627259947)
      ·
        refine ⟨29238771308564828440889921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492514205709885627259947 29238771308564828440889921)
        ·
          refine ⟨21929078481423621330667441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29238771308564828440889921 21929078481423621330667441)
          ·
            refine ⟨16446808861067715998000581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21929078481423621330667441 16446808861067715998000581)
            ·
              refine ⟨3083776661450196749625109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16446808861067715998000581 3083776661450196749625109)
              ·
                refine ⟨144552031005477972638677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3083776661450196749625109 144552031005477972638677)
                ·
                  rfl

theorem cell19_475055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_475055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475055 prefixEnd_475055 := by exact prefixLift 475055
  have htrace : WordTrace (prefixWord ++ tailWord_475055) baseStart_475055 baseEnd_475055 := by
    simpa [prefixWord, tailWord_475055, baseEnd_475055] using wordTrace_append hprefix tailTrace_475055
  have hstable : (prefixWord ++ tailWord_475055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475055).length < 2 ^ (prefixWord ++ tailWord_475055).sum := by decide
  have hdescent : baseEnd_475055 < baseStart_475055 := by decide
  rcases family_descends (prefixWord ++ tailWord_475055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475070 : List Nat := [4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_475070 : Nat := 118140960795 + 475070 * 2 ^ 59
def prefixEnd_475070 : Nat := 4983230072969 + 3 ^ 40 * 475070 * 2
def baseEnd_475070 : Nat := 144556595277962382305303

theorem tailTrace_475070 : CollatzResearch.WordTrace tailWord_475070 prefixEnd_475070 144556595277962382305303 := by
  unfold tailWord_475070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165903298613750042697833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11551484259273333561055109 2165903298613750042697833)
  ·
    refine ⟨1624427473960312532023375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2165903298613750042697833 1624427473960312532023375)
    ·
      refine ⟨2436641210940468798035063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624427473960312532023375 2436641210940468798035063)
      ·
        refine ⟨3654961816410703197052595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436641210940468798035063 3654961816410703197052595)
        ·
          refine ⟨5482442724616054795578893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654961816410703197052595 5482442724616054795578893)
          ·
            refine ⟨2055916021731020548342085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5482442724616054795578893 2055916021731020548342085)
            ·
              refine ⟨385484254074566352814141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2055916021731020548342085 385484254074566352814141)
              ·
                refine ⟨144556595277962382305303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385484254074566352814141 144556595277962382305303)
                ·
                  rfl

theorem cell19_475070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_475070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475070 prefixEnd_475070 := by exact prefixLift 475070
  have htrace : WordTrace (prefixWord ++ tailWord_475070) baseStart_475070 baseEnd_475070 := by
    simpa [prefixWord, tailWord_475070, baseEnd_475070] using wordTrace_append hprefix tailTrace_475070
  have hstable : (prefixWord ++ tailWord_475070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475070).length < 2 ^ (prefixWord ++ tailWord_475070).sum := by decide
  have hdescent : baseEnd_475070 < baseStart_475070 := by decide
  rcases family_descends (prefixWord ++ tailWord_475070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475106 : List Nat := [3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_475106 : Nat := 118140960795 + 475106 * 2 ^ 59
def prefixEnd_475106 : Nat := 4983230072969 + 3 ^ 40 * 475106 * 2
def baseEnd_475106 : Nat := 144567549531924965505205

theorem tailTrace_475106 : CollatzResearch.WordTrace tailWord_475106 prefixEnd_475106 144567549531924965505205 := by
  unfold tailWord_475106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332134854194894622473293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11552359611186385659928781 4332134854194894622473293)
  ·
    refine ⟨1624550570323085483427485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4332134854194894622473293 1624550570323085483427485)
    ·
      refine ⟨609206463871157056285307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1624550570323085483427485 609206463871157056285307)
      ·
        refine ⟨913809695806735584427961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609206463871157056285307 913809695806735584427961)
        ·
          refine ⟨685357271855051688320971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913809695806735584427961 685357271855051688320971)
          ·
            refine ⟨1028035907782577532481457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685357271855051688320971 1028035907782577532481457)
            ·
              refine ⟨771026930836933149361093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028035907782577532481457 771026930836933149361093)
              ·
                refine ⟨144567549531924965505205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771026930836933149361093 144567549531924965505205)
                ·
                  rfl

theorem cell19_475106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_475106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475106 prefixEnd_475106 := by exact prefixLift 475106
  have htrace : WordTrace (prefixWord ++ tailWord_475106) baseStart_475106 baseEnd_475106 := by
    simpa [prefixWord, tailWord_475106, baseEnd_475106] using wordTrace_append hprefix tailTrace_475106
  have hstable : (prefixWord ++ tailWord_475106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475106).length < 2 ^ (prefixWord ++ tailWord_475106).sum := by decide
  have hdescent : baseEnd_475106 < baseStart_475106 := by decide
  rcases family_descends (prefixWord ++ tailWord_475106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475131 : List Nat := [1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_475131 : Nat := 118140960795 + 475131 * 2 ^ 59
def prefixEnd_475131 : Nat := 4983230072969 + 3 ^ 40 * 475131 * 2
def baseEnd_475131 : Nat := 144575156652732314949581

theorem tailTrace_475131 : CollatzResearch.WordTrace tailWord_475131 prefixEnd_475131 144575156652732314949581 := by
  unfold tailWord_475131
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329451241689007759553247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11552967494459338506368831 17329451241689007759553247)
  ·
    refine ⟨25994176862533511639329871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17329451241689007759553247 25994176862533511639329871)
    ·
      refine ⟨38991265293800267458994807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25994176862533511639329871 38991265293800267458994807)
      ·
        refine ⟨58486897940700401188492211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38991265293800267458994807 58486897940700401188492211)
        ·
          refine ⟨87730346911050601782738317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58486897940700401188492211 87730346911050601782738317)
          ·
            refine ⟨32898880091643975668526869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87730346911050601782738317 32898880091643975668526869)
            ·
              refine ⟨1542135004295811359462197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32898880091643975668526869 1542135004295811359462197)
              ·
                refine ⟨144575156652732314949581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1542135004295811359462197 144575156652732314949581)
                ·
                  rfl

theorem cell19_475131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_475131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475131 prefixEnd_475131 := by exact prefixLift 475131
  have htrace : WordTrace (prefixWord ++ tailWord_475131) baseStart_475131 baseEnd_475131 := by
    simpa [prefixWord, tailWord_475131, baseEnd_475131] using wordTrace_append hprefix tailTrace_475131
  have hstable : (prefixWord ++ tailWord_475131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475131).length < 2 ^ (prefixWord ++ tailWord_475131).sum := by decide
  have hdescent : baseEnd_475131 < baseStart_475131 := by decide
  rcases family_descends (prefixWord ++ tailWord_475131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475142 : List Nat := [6, 2, 1, 2, 1, 7]
def baseStart_475142 : Nat := 118140960795 + 475142 * 2 ^ 59
def prefixEnd_475142 : Nat := 4983230072969 + 3 ^ 40 * 475142 * 2
def baseEnd_475142 : Nat := 16064278198431949856123

theorem tailTrace_475142 : CollatzResearch.WordTrace tailWord_475142 prefixEnd_475142 16064278198431949856123 := by
  unfold tailWord_475142
  simp only [CollatzResearch.WordTrace]
  refine ⟨541557888895286144943865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11553234963099437758802453 541557888895286144943865)
  ·
    refine ⟨406168416671464608707899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 541557888895286144943865 406168416671464608707899)
    ·
      refine ⟨609252625007196913061849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406168416671464608707899 609252625007196913061849)
      ·
        refine ⟨456939468755397684796387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609252625007196913061849 456939468755397684796387)
        ·
          refine ⟨685409203133096527194581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456939468755397684796387 685409203133096527194581)
          ·
            refine ⟨16064278198431949856123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 685409203133096527194581 16064278198431949856123)
            ·
              rfl

theorem cell19_475142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_475142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475142 prefixEnd_475142 := by exact prefixLift 475142
  have htrace : WordTrace (prefixWord ++ tailWord_475142) baseStart_475142 baseEnd_475142 := by
    simpa [prefixWord, tailWord_475142, baseEnd_475142] using wordTrace_append hprefix tailTrace_475142
  have hstable : (prefixWord ++ tailWord_475142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475142).length < 2 ^ (prefixWord ++ tailWord_475142).sum := by decide
  have hdescent : baseEnd_475142 < baseStart_475142 := by decide
  rcases family_descends (prefixWord ++ tailWord_475142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475165 : List Nat := [1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_475165 : Nat := 118140960795 + 475165 * 2 ^ 59
def prefixEnd_475165 : Nat := 4983230072969 + 3 ^ 40 * 475165 * 2
def baseEnd_475165 : Nat := 144585502337030310193933

theorem tailTrace_475165 : CollatzResearch.WordTrace tailWord_475165 prefixEnd_475165 144585502337030310193933 := by
  unfold tailWord_475165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330691323565831566290949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11553794215710554377527299 17330691323565831566290949)
  ·
    refine ⟨3249504623168593418679553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17330691323565831566290949 3249504623168593418679553)
    ·
      refine ⟨2437128467376445064009665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3249504623168593418679553 2437128467376445064009665)
      ·
        refine ⟨1827846350532333798007249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437128467376445064009665 1827846350532333798007249)
        ·
          refine ⟨1370884762899250348505437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827846350532333798007249 1370884762899250348505437)
          ·
            refine ⟨514081786087218880689539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1370884762899250348505437 514081786087218880689539)
            ·
              refine ⟨771122679130828321034309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514081786087218880689539 771122679130828321034309)
              ·
                refine ⟨144585502337030310193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771122679130828321034309 144585502337030310193933)
                ·
                  rfl

theorem cell19_475165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_475165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475165 prefixEnd_475165 := by exact prefixLift 475165
  have htrace : WordTrace (prefixWord ++ tailWord_475165) baseStart_475165 baseEnd_475165 := by
    simpa [prefixWord, tailWord_475165, baseEnd_475165] using wordTrace_append hprefix tailTrace_475165
  have hstable : (prefixWord ++ tailWord_475165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475165).length < 2 ^ (prefixWord ++ tailWord_475165).sum := by decide
  have hdescent : baseEnd_475165 < baseStart_475165 := by decide
  rcases family_descends (prefixWord ++ tailWord_475165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475207 : List Nat := [1, 1, 4, 1, 3, 1, 8]
def baseStart_475207 : Nat := 118140960795 + 475207 * 2 ^ 59
def prefixEnd_475207 : Nat := 4983230072969 + 3 ^ 40 * 475207 * 2
def baseEnd_475207 : Nat := 48199427433328885753495

theorem tailTrace_475207 : CollatzResearch.WordTrace tailWord_475207 prefixEnd_475207 48199427433328885753495 := by
  unfold tailWord_475207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17332223189413672739319875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11554815459609115159546583 17332223189413672739319875)
  ·
    refine ⟨25998334784120509108979813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17332223189413672739319875 25998334784120509108979813)
    ·
      refine ⟨4874687772022595457933715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25998334784120509108979813 4874687772022595457933715)
      ·
        refine ⟨7312031658033893186900573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874687772022595457933715 7312031658033893186900573)
        ·
          refine ⟨2742011871762709945087715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7312031658033893186900573 2742011871762709945087715)
          ·
            refine ⟨4113017807644064917631573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742011871762709945087715 4113017807644064917631573)
            ·
              refine ⟨48199427433328885753495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4113017807644064917631573 48199427433328885753495)
              ·
                rfl

theorem cell19_475207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_475207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475207 prefixEnd_475207 := by exact prefixLift 475207
  have htrace : WordTrace (prefixWord ++ tailWord_475207) baseStart_475207 baseEnd_475207 := by
    simpa [prefixWord, tailWord_475207, baseEnd_475207] using wordTrace_append hprefix tailTrace_475207
  have hstable : (prefixWord ++ tailWord_475207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475207).length < 2 ^ (prefixWord ++ tailWord_475207).sum := by decide
  have hdescent : baseEnd_475207 < baseStart_475207 := by decide
  rcases family_descends (prefixWord ++ tailWord_475207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475226 : List Nat := [3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_475226 : Nat := 118140960795 + 475226 * 2 ^ 59
def prefixEnd_475226 : Nat := 4983230072969 + 3 ^ 40 * 475226 * 2
def baseEnd_475226 : Nat := 144604063711800242838211

theorem tailTrace_475226 : CollatzResearch.WordTrace tailWord_475226 prefixEnd_475226 144604063711800242838211 := by
  unfold tailWord_475226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333229044086209746065383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11555277450896559322841021 4333229044086209746065383)
  ·
    refine ⟨6499843566129314619098075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333229044086209746065383 6499843566129314619098075)
    ·
      refine ⟨9749765349193971928647113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499843566129314619098075 9749765349193971928647113)
      ·
        refine ⟨7312324011895478946485335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9749765349193971928647113 7312324011895478946485335)
        ·
          refine ⟨10968486017843218419728003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312324011895478946485335 10968486017843218419728003)
          ·
            refine ⟨16452729026764827629592005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10968486017843218419728003 16452729026764827629592005)
            ·
              refine ⟨3084886692518405180548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16452729026764827629592005 3084886692518405180548501)
              ·
                refine ⟨144604063711800242838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3084886692518405180548501 144604063711800242838211)
                ·
                  rfl

theorem cell19_475226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_475226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475226 prefixEnd_475226 := by exact prefixLift 475226
  have htrace : WordTrace (prefixWord ++ tailWord_475226) baseStart_475226 baseEnd_475226 := by
    simpa [prefixWord, tailWord_475226, baseEnd_475226] using wordTrace_append hprefix tailTrace_475226
  have hstable : (prefixWord ++ tailWord_475226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475226).length < 2 ^ (prefixWord ++ tailWord_475226).sum := by decide
  have hdescent : baseEnd_475226 < baseStart_475226 := by decide
  rcases family_descends (prefixWord ++ tailWord_475226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475317 : List Nat := [1, 3, 3, 4, 2, 6]
def baseStart_475317 : Nat := 118140960795 + 475317 * 2 ^ 59
def prefixEnd_475317 : Nat := 4983230072969 + 3 ^ 40 * 475317 * 2
def baseEnd_475317 : Nat := 16070194847948777201749

theorem tailTrace_475317 : CollatzResearch.WordTrace tailWord_475317 prefixEnd_475317 16070194847948777201749 := by
  unfold tailWord_475317
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336235219015161525824205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11557490146010107683882803 17336235219015161525824205)
  ·
    refine ⟨6501088207130685572184077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17336235219015161525824205 6501088207130685572184077)
    ·
      refine ⟨2437908077674007089569029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6501088207130685572184077 2437908077674007089569029)
      ·
        refine ⟨457107764563876329294193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2437908077674007089569029 457107764563876329294193)
        ·
          refine ⟨342830823422907246970645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457107764563876329294193 342830823422907246970645)
          ·
            refine ⟨16070194847948777201749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 342830823422907246970645 16070194847948777201749)
            ·
              rfl

theorem cell19_475317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_475317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475317 prefixEnd_475317 := by exact prefixLift 475317
  have htrace : WordTrace (prefixWord ++ tailWord_475317) baseStart_475317 baseEnd_475317 := by
    simpa [prefixWord, tailWord_475317, baseEnd_475317] using wordTrace_append hprefix tailTrace_475317
  have hstable : (prefixWord ++ tailWord_475317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475317).length < 2 ^ (prefixWord ++ tailWord_475317).sum := by decide
  have hdescent : baseEnd_475317 < baseStart_475317 := by decide
  rcases family_descends (prefixWord ++ tailWord_475317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475416 : List Nat := [2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_475416 : Nat := 118140960795 + 475416 * 2 ^ 59
def prefixEnd_475416 : Nat := 4983230072969 + 3 ^ 40 * 475416 * 2
def baseEnd_475416 : Nat := 144661877829936098615471

theorem tailTrace_475416 : CollatzResearch.WordTrace tailWord_475416 prefixEnd_475416 144661877829936098615471 := by
  unfold tailWord_475416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669923022828250716839051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11559897363771000955785401 8669923022828250716839051)
  ·
    refine ⟨13004884534242376075258577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669923022828250716839051 13004884534242376075258577)
    ·
      refine ⟨9753663400681782056443933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13004884534242376075258577 9753663400681782056443933)
      ·
        refine ⟨3657623775255668271166475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9753663400681782056443933 3657623775255668271166475)
        ·
          refine ⟨5486435662883502406749713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657623775255668271166475 5486435662883502406749713)
          ·
            refine ⟨4114826747162626805062285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5486435662883502406749713 4114826747162626805062285)
            ·
              refine ⟨1543060030185985051898357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4114826747162626805062285 1543060030185985051898357)
              ·
                refine ⟨144661877829936098615471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1543060030185985051898357 144661877829936098615471)
                ·
                  rfl

theorem cell19_475416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_475416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475416 prefixEnd_475416 := by exact prefixLift 475416
  have htrace : WordTrace (prefixWord ++ tailWord_475416) baseStart_475416 baseEnd_475416 := by
    simpa [prefixWord, tailWord_475416, baseEnd_475416] using wordTrace_append hprefix tailTrace_475416
  have hstable : (prefixWord ++ tailWord_475416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475416).length < 2 ^ (prefixWord ++ tailWord_475416).sum := by decide
  have hdescent : baseEnd_475416 < baseStart_475416 := by decide
  rcases family_descends (prefixWord ++ tailWord_475416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475473 : List Nat := [1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_475473 : Nat := 118140960795 + 475473 * 2 ^ 59
def prefixEnd_475473 : Nat := 4983230072969 + 3 ^ 40 * 475473 * 2
def baseEnd_475473 : Nat := 144679222065376855348649

theorem tailTrace_475473 : CollatzResearch.WordTrace tailWord_475473 prefixEnd_475473 144679222065376855348649 := by
  unfold tailWord_475473
  simp only [CollatzResearch.WordTrace]
  refine ⟨17341925006450000168503073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11561283337633333445668715 17341925006450000168503073)
  ·
    refine ⟨13006443754837500126377305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17341925006450000168503073 13006443754837500126377305)
    ·
      refine ⟨9754832816128125094782979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006443754837500126377305 9754832816128125094782979)
      ·
        refine ⟨14632249224192187642174469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754832816128125094782979 14632249224192187642174469)
        ·
          refine ⟨2743546729536035182907713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14632249224192187642174469 2743546729536035182907713)
          ·
            refine ⟨2057660047152026387180785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743546729536035182907713 2057660047152026387180785)
            ·
              refine ⟨1543245035364019790385589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057660047152026387180785 1543245035364019790385589)
              ·
                refine ⟨144679222065376855348649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1543245035364019790385589 144679222065376855348649)
                ·
                  rfl

theorem cell19_475473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_475473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475473 prefixEnd_475473 := by exact prefixLift 475473
  have htrace : WordTrace (prefixWord ++ tailWord_475473) baseStart_475473 baseEnd_475473 := by
    simpa [prefixWord, tailWord_475473, baseEnd_475473] using wordTrace_append hprefix tailTrace_475473
  have hstable : (prefixWord ++ tailWord_475473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475473).length < 2 ^ (prefixWord ++ tailWord_475473).sum := by decide
  have hdescent : baseEnd_475473 < baseStart_475473 := by decide
  rcases family_descends (prefixWord ++ tailWord_475473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475486 : List Nat := [4, 4, 2, 1, 8]
def baseStart_475486 : Nat := 118140960795 + 475486 * 2 ^ 59
def prefixEnd_475486 : Nat := 4983230072969 + 3 ^ 40 * 475486 * 2
def baseEnd_475486 : Nat := 5358636213636913965175

theorem tailTrace_475486 : CollatzResearch.WordTrace tailWord_475486 prefixEnd_475486 5358636213636913965175 := by
  unfold tailWord_475486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167799894425362923590789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11561599436935268925817541 2167799894425362923590789)
  ·
    refine ⟨406462480204755548173273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2167799894425362923590789 406462480204755548173273)
    ·
      refine ⟨304846860153566661129955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406462480204755548173273 304846860153566661129955)
      ·
        refine ⟨457270290230349991694933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304846860153566661129955 457270290230349991694933)
        ·
          refine ⟨5358636213636913965175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 457270290230349991694933 5358636213636913965175)
          ·
            rfl

theorem cell19_475486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_475486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475486 prefixEnd_475486 := by exact prefixLift 475486
  have htrace : WordTrace (prefixWord ++ tailWord_475486) baseStart_475486 baseEnd_475486 := by
    simpa [prefixWord, tailWord_475486, baseEnd_475486] using wordTrace_append hprefix tailTrace_475486
  have hstable : (prefixWord ++ tailWord_475486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475486).length < 2 ^ (prefixWord ++ tailWord_475486).sum := by decide
  have hdescent : baseEnd_475486 < baseStart_475486 := by decide
  rcases family_descends (prefixWord ++ tailWord_475486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475509 : List Nat := [1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_475509 : Nat := 118140960795 + 475509 * 2 ^ 59
def prefixEnd_475509 : Nat := 4983230072969 + 3 ^ 40 * 475509 * 2
def baseEnd_475509 : Nat := 144690176319339438548551

theorem tailTrace_475509 : CollatzResearch.WordTrace tailWord_475509 prefixEnd_475509 144690176319339438548551 := by
  unfold tailWord_475509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343238034319578316813581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11562158689546385544542387 17343238034319578316813581)
  ·
    refine ⟨6503714262869841868805093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17343238034319578316813581 6503714262869841868805093)
    ·
      refine ⟨1219446424288095350400955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6503714262869841868805093 1219446424288095350400955)
      ·
        refine ⟨1829169636432143025601433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219446424288095350400955 1829169636432143025601433)
        ·
          refine ⟨1371877227324107269201075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829169636432143025601433 1371877227324107269201075)
          ·
            refine ⟨2057815840986160903801613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371877227324107269201075 2057815840986160903801613)
            ·
              refine ⟨771680940369810338925605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2057815840986160903801613 771680940369810338925605)
              ·
                refine ⟨144690176319339438548551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771680940369810338925605 144690176319339438548551)
                ·
                  rfl

theorem cell19_475509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_475509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475509 prefixEnd_475509 := by exact prefixLift 475509
  have htrace : WordTrace (prefixWord ++ tailWord_475509) baseStart_475509 baseEnd_475509 := by
    simpa [prefixWord, tailWord_475509, baseEnd_475509] using wordTrace_append hprefix tailTrace_475509
  have hstable : (prefixWord ++ tailWord_475509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475509).length < 2 ^ (prefixWord ++ tailWord_475509).sum := by decide
  have hdescent : baseEnd_475509 < baseStart_475509 := by decide
  rcases family_descends (prefixWord ++ tailWord_475509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475528 : List Nat := [2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_475528 : Nat := 118140960795 + 475528 * 2 ^ 59
def prefixEnd_475528 : Nat := 4983230072969 + 3 ^ 40 * 475528 * 2
def baseEnd_475528 : Nat := 144695957731153024126277

theorem tailTrace_475528 : CollatzResearch.WordTrace tailWord_475528 prefixEnd_475528 144695957731153024126277 := by
  unfold tailWord_475528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671965510625372280877619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11562620680833829707836825 8671965510625372280877619)
  ·
    refine ⟨13007948265938058421316429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671965510625372280877619 13007948265938058421316429)
    ·
      refine ⟨4877980599726771907993661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13007948265938058421316429 4877980599726771907993661)
      ·
        refine ⟨1829242724897539465497623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4877980599726771907993661 1829242724897539465497623)
        ·
          refine ⟨2743864087346309198246435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829242724897539465497623 2743864087346309198246435)
          ·
            refine ⟨4115796131019463797369653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743864087346309198246435 4115796131019463797369653)
            ·
              refine ⟨385855887283074731003405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4115796131019463797369653 385855887283074731003405)
              ·
                refine ⟨144695957731153024126277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385855887283074731003405 144695957731153024126277)
                ·
                  rfl

theorem cell19_475528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_475528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475528 prefixEnd_475528 := by exact prefixLift 475528
  have htrace : WordTrace (prefixWord ++ tailWord_475528) baseStart_475528 baseEnd_475528 := by
    simpa [prefixWord, tailWord_475528, baseEnd_475528] using wordTrace_append hprefix tailTrace_475528
  have hstable : (prefixWord ++ tailWord_475528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475528).length < 2 ^ (prefixWord ++ tailWord_475528).sum := by decide
  have hdescent : baseEnd_475528 < baseStart_475528 := by decide
  rcases family_descends (prefixWord ++ tailWord_475528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475602 : List Nat := [3, 2, 2, 4, 1, 2, 5]
def baseStart_475602 : Nat := 118140960795 + 475602 * 2 ^ 59
def prefixEnd_475602 : Nat := 4983230072969 + 3 ^ 40 * 475602 * 2
def baseEnd_475602 : Nat := 48239491602914259493877

theorem tailTrace_475602 : CollatzResearch.WordTrace tailWord_475602 prefixEnd_475602 48239491602914259493877 := by
  unfold tailWord_475602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336657505745663799987265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11564420015321770133299373 4336657505745663799987265)
  ·
    refine ⟨3252493129309247849990449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336657505745663799987265 3252493129309247849990449)
    ·
      refine ⟨2439369846981935887492837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252493129309247849990449 2439369846981935887492837)
      ·
        refine ⟨457381846309112978904907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2439369846981935887492837 457381846309112978904907)
        ·
          refine ⟨686072769463669468357361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457381846309112978904907 686072769463669468357361)
          ·
            refine ⟨514554577097752101268021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686072769463669468357361 514554577097752101268021)
            ·
              refine ⟨48239491602914259493877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 514554577097752101268021 48239491602914259493877)
              ·
                rfl

theorem cell19_475602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_475602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475602 prefixEnd_475602 := by exact prefixLift 475602
  have htrace : WordTrace (prefixWord ++ tailWord_475602) baseStart_475602 baseEnd_475602 := by
    simpa [prefixWord, tailWord_475602, baseEnd_475602] using wordTrace_append hprefix tailTrace_475602
  have hstable : (prefixWord ++ tailWord_475602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475602).length < 2 ^ (prefixWord ++ tailWord_475602).sum := by decide
  have hdescent : baseEnd_475602 < baseStart_475602 := by decide
  rcases family_descends (prefixWord ++ tailWord_475602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475604 : List Nat := [2, 4, 1, 2, 2, 3, 5]
def baseStart_475604 : Nat := 118140960795 + 475604 * 2 ^ 59
def prefixEnd_475604 : Nat := 4983230072969 + 3 ^ 40 * 475604 * 2
def baseEnd_475604 : Nat := 48239694459469122145727

theorem tailTrace_475604 : CollatzResearch.WordTrace tailWord_475604 prefixEnd_475604 48239694459469122145727 := by
  unfold tailWord_475604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673351484487704770760933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11564468645983606361014577 8673351484487704770760933)
  ·
    refine ⟨1626253403341444644517675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8673351484487704770760933 1626253403341444644517675)
    ·
      refine ⟨2439380105012166966776513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626253403341444644517675 2439380105012166966776513)
      ·
        refine ⟨1829535078759125225082385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439380105012166966776513 1829535078759125225082385)
        ·
          refine ⟨1372151309069343918811789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829535078759125225082385 1372151309069343918811789)
          ·
            refine ⟨514556740901003969554421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1372151309069343918811789 514556740901003969554421)
            ·
              refine ⟨48239694459469122145727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 514556740901003969554421 48239694459469122145727)
              ·
                rfl

theorem cell19_475604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_475604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475604 prefixEnd_475604 := by exact prefixLift 475604
  have htrace : WordTrace (prefixWord ++ tailWord_475604) baseStart_475604 baseEnd_475604 := by
    simpa [prefixWord, tailWord_475604, baseEnd_475604] using wordTrace_append hprefix tailTrace_475604
  have hstable : (prefixWord ++ tailWord_475604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475604).length < 2 ^ (prefixWord ++ tailWord_475604).sum := by decide
  have hdescent : baseEnd_475604 < baseStart_475604 := by decide
  rcases family_descends (prefixWord ++ tailWord_475604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475693 : List Nat := [1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_475693 : Nat := 118140960795 + 475693 * 2 ^ 59
def prefixEnd_475693 : Nat := 4983230072969 + 3 ^ 40 * 475693 * 2
def baseEnd_475693 : Nat := 144746164728481530459161

theorem tailTrace_475693 : CollatzResearch.WordTrace tailWord_475693 prefixEnd_475693 144746164728481530459161 := by
  unfold tailWord_475693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17349949065652977741511733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11566632710435318494341155 17349949065652977741511733)
  ·
    refine ⟨1626557724904966663266725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17349949065652977741511733 1626557724904966663266725)
    ·
      refine ⟨304979573419681249362511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1626557724904966663266725 304979573419681249362511)
      ·
        refine ⟨457469360129521874043767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304979573419681249362511 457469360129521874043767)
        ·
          refine ⟨686204040194282811065651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457469360129521874043767 686204040194282811065651)
          ·
            refine ⟨1029306060291424216598477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686204040194282811065651 1029306060291424216598477)
            ·
              refine ⟨385989772609284081224429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029306060291424216598477 385989772609284081224429)
              ·
                refine ⟨144746164728481530459161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385989772609284081224429 144746164728481530459161)
                ·
                  rfl

theorem cell19_475693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_475693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475693 prefixEnd_475693 := by exact prefixLift 475693
  have htrace : WordTrace (prefixWord ++ tailWord_475693) baseStart_475693 baseEnd_475693 := by
    simpa [prefixWord, tailWord_475693, baseEnd_475693] using wordTrace_append hprefix tailTrace_475693
  have hstable : (prefixWord ++ tailWord_475693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475693).length < 2 ^ (prefixWord ++ tailWord_475693).sum := by decide
  have hdescent : baseEnd_475693 < baseStart_475693 := by decide
  rcases family_descends (prefixWord ++ tailWord_475693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475752 : List Nat := [2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_475752 : Nat := 118140960795 + 475752 * 2 ^ 59
def prefixEnd_475752 : Nat := 4983230072969 + 3 ^ 40 * 475752 * 2
def baseEnd_475752 : Nat := 144764117533586875147889

theorem tailTrace_475752 : CollatzResearch.WordTrace tailWord_475752 prefixEnd_475752 144764117533586875147889 := by
  unfold tailWord_475752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676050486219615408954755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11568067314959487211939673 8676050486219615408954755)
  ·
    refine ⟨13014075729329423113432133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8676050486219615408954755 13014075729329423113432133)
    ·
      refine ⟨2440139199249266833768525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13014075729329423113432133 2440139199249266833768525)
      ·
        refine ⟨915052199718475062663197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2440139199249266833768525 915052199718475062663197)
        ·
          refine ⟨343144574894428148498699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915052199718475062663197 343144574894428148498699)
          ·
            refine ⟨514716862341642222748049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343144574894428148498699 514716862341642222748049)
            ·
              refine ⟨386037646756231667061037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514716862341642222748049 386037646756231667061037)
              ·
                refine ⟨144764117533586875147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386037646756231667061037 144764117533586875147889)
                ·
                  rfl

theorem cell19_475752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_475752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475752 prefixEnd_475752 := by exact prefixLift 475752
  have htrace : WordTrace (prefixWord ++ tailWord_475752) baseStart_475752 baseEnd_475752 := by
    simpa [prefixWord, tailWord_475752, baseEnd_475752] using wordTrace_append hprefix tailTrace_475752
  have hstable : (prefixWord ++ tailWord_475752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475752).length < 2 ^ (prefixWord ++ tailWord_475752).sum := by decide
  have hdescent : baseEnd_475752 < baseStart_475752 := by decide
  rcases family_descends (prefixWord ++ tailWord_475752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475779 : List Nat := [1, 1, 1, 3, 3, 1, 9]
def baseStart_475779 : Nat := 118140960795 + 475779 * 2 ^ 59
def prefixEnd_475779 : Nat := 4983230072969 + 3 ^ 40 * 475779 * 2
def baseEnd_475779 : Nat := 48257444408019604182605

theorem tailTrace_475779 : CollatzResearch.WordTrace tailWord_475779 prefixEnd_475779 48257444408019604182605 := by
  unfold tailWord_475779
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353085743341414429142391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11568723828894276286094927 17353085743341414429142391)
  ·
    refine ⟨26029628615012121643713587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17353085743341414429142391 26029628615012121643713587)
    ·
      refine ⟨39044442922518182465570381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26029628615012121643713587 39044442922518182465570381)
      ·
        refine ⟨14641666095944318424588893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39044442922518182465570381 14641666095944318424588893)
        ·
          refine ⟨5490624785979119409220835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14641666095944318424588893 5490624785979119409220835)
          ·
            refine ⟨8235937178968679113831253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490624785979119409220835 8235937178968679113831253)
            ·
              refine ⟨48257444408019604182605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8235937178968679113831253 48257444408019604182605)
              ·
                rfl

theorem cell19_475779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_475779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475779 prefixEnd_475779 := by exact prefixLift 475779
  have htrace : WordTrace (prefixWord ++ tailWord_475779) baseStart_475779 baseEnd_475779 := by
    simpa [prefixWord, tailWord_475779, baseEnd_475779] using wordTrace_append hprefix tailTrace_475779
  have hstable : (prefixWord ++ tailWord_475779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475779).length < 2 ^ (prefixWord ++ tailWord_475779).sum := by decide
  have hdescent : baseEnd_475779 < baseStart_475779 := by decide
  rcases family_descends (prefixWord ++ tailWord_475779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475794 : List Nat := [3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_475794 : Nat := 118140960795 + 475794 * 2 ^ 59
def prefixEnd_475794 : Nat := 4983230072969 + 3 ^ 40 * 475794 * 2
def baseEnd_475794 : Nat := 144776897496543222214441

theorem tailTrace_475794 : CollatzResearch.WordTrace tailWord_475794 prefixEnd_475794 144776897496543222214441 := by
  unfold tailWord_475794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338408209571767997734609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11569088558858047993958957 4338408209571767997734609)
  ·
    refine ⟨3253806157178825998300957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4338408209571767997734609 3253806157178825998300957)
    ·
      refine ⟨1220177308942059749362859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3253806157178825998300957 1220177308942059749362859)
      ·
        refine ⟨1830265963413089624044289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220177308942059749362859 1830265963413089624044289)
        ·
          refine ⟨1372699472559817218033217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830265963413089624044289 1372699472559817218033217)
          ·
            refine ⟨1029524604419862913524913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372699472559817218033217 1029524604419862913524913)
            ·
              refine ⟨772143453314897185143685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029524604419862913524913 772143453314897185143685)
              ·
                refine ⟨144776897496543222214441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772143453314897185143685 144776897496543222214441)
                ·
                  rfl

theorem cell19_475794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_475794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475794 prefixEnd_475794 := by exact prefixLift 475794
  have htrace : WordTrace (prefixWord ++ tailWord_475794) baseStart_475794 baseEnd_475794 := by
    simpa [prefixWord, tailWord_475794, baseEnd_475794] using wordTrace_append hprefix tailTrace_475794
  have hstable : (prefixWord ++ tailWord_475794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475794).length < 2 ^ (prefixWord ++ tailWord_475794).sum := by decide
  have hdescent : baseEnd_475794 < baseStart_475794 := by decide
  rcases family_descends (prefixWord ++ tailWord_475794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475830 : List Nat := [5, 1, 3, 1, 3, 6]
def baseStart_475830 : Nat := 118140960795 + 475830 * 2 ^ 59
def prefixEnd_475830 : Nat := 4983230072969 + 3 ^ 40 * 475830 * 2
def baseEnd_475830 : Nat := 16087539083389533934927

theorem tailTrace_475830 : CollatzResearch.WordTrace tailWord_475830 prefixEnd_475830 16087539083389533934927 := by
  unfold tailWord_475830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084684116634790633703059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11569963910771100092832629 1084684116634790633703059)
  ·
    refine ⟨1627026174952185950554589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1084684116634790633703059 1627026174952185950554589)
    ·
      refine ⟨610134815607069731457971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1627026174952185950554589 610134815607069731457971)
      ·
        refine ⟨915202223410604597186957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610134815607069731457971 915202223410604597186957)
        ·
          refine ⟨343200833778976723945109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915202223410604597186957 343200833778976723945109)
          ·
            refine ⟨16087539083389533934927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 343200833778976723945109 16087539083389533934927)
            ·
              rfl

theorem cell19_475830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_475830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475830 prefixEnd_475830 := by exact prefixLift 475830
  have htrace : WordTrace (prefixWord ++ tailWord_475830) baseStart_475830 baseEnd_475830 := by
    simpa [prefixWord, tailWord_475830, baseEnd_475830] using wordTrace_append hprefix tailTrace_475830
  have hstable : (prefixWord ++ tailWord_475830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475830).length < 2 ^ (prefixWord ++ tailWord_475830).sum := by decide
  have hdescent : baseEnd_475830 < baseStart_475830 := by decide
  rcases family_descends (prefixWord ++ tailWord_475830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475868 : List Nat := [2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_475868 : Nat := 118140960795 + 475868 * 2 ^ 59
def prefixEnd_475868 : Nat := 4983230072969 + 3 ^ 40 * 475868 * 2
def baseEnd_475868 : Nat := 144799414574132976569795

theorem tailTrace_475868 : CollatzResearch.WordTrace tailWord_475868 prefixEnd_475868 144799414574132976569795 := by
  unfold tailWord_475868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678165920009491314566129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11570887893345988419421505 8678165920009491314566129)
  ·
    refine ⟨6508624440007118485924597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678165920009491314566129 6508624440007118485924597)
    ·
      refine ⟨610183541250667358055431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6508624440007118485924597 610183541250667358055431)
      ·
        refine ⟨915275311876001037083147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610183541250667358055431 915275311876001037083147)
        ·
          refine ⟨1372912967814001555624721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915275311876001037083147 1372912967814001555624721)
          ·
            refine ⟨1029684725860501166718541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372912967814001555624721 1029684725860501166718541)
            ·
              refine ⟨386131772197687937519453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029684725860501166718541 386131772197687937519453)
              ·
                refine ⟨144799414574132976569795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386131772197687937519453 144799414574132976569795)
                ·
                  rfl

theorem cell19_475868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_475868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475868 prefixEnd_475868 := by exact prefixLift 475868
  have htrace : WordTrace (prefixWord ++ tailWord_475868) baseStart_475868 baseEnd_475868 := by
    simpa [prefixWord, tailWord_475868, baseEnd_475868] using wordTrace_append hprefix tailTrace_475868
  have hstable : (prefixWord ++ tailWord_475868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475868).length < 2 ^ (prefixWord ++ tailWord_475868).sum := by decide
  have hdescent : baseEnd_475868 < baseStart_475868 := by decide
  rcases family_descends (prefixWord ++ tailWord_475868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475965 : List Nat := [1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_475965 : Nat := 118140960795 + 475965 * 2 ^ 59
def prefixEnd_475965 : Nat := 4983230072969 + 3 ^ 40 * 475965 * 2
def baseEnd_475965 : Nat := 144828930202865492413975

theorem tailTrace_475965 : CollatzResearch.WordTrace tailWord_475965 prefixEnd_475965 144828930202865492413975 := by
  unfold tailWord_475965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359869720667568195413349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11573246480445045463608899 17359869720667568195413349)
  ·
    refine ⟨3254975572625169036640003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17359869720667568195413349 3254975572625169036640003)
    ·
      refine ⟨4882463358937753554960005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254975572625169036640003 4882463358937753554960005)
      ·
        refine ⟨915461879800828791555001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4882463358937753554960005 915461879800828791555001)
        ·
          refine ⟨686596409850621593666251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915461879800828791555001 686596409850621593666251)
          ·
            refine ⟨1029894614775932390499377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686596409850621593666251 1029894614775932390499377)
            ·
              refine ⟨772420961081949292874533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029894614775932390499377 772420961081949292874533)
              ·
                refine ⟨144828930202865492413975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772420961081949292874533 144828930202865492413975)
                ·
                  rfl

theorem cell19_475965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_475965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475965 prefixEnd_475965 := by exact prefixLift 475965
  have htrace : WordTrace (prefixWord ++ tailWord_475965) baseStart_475965 baseEnd_475965 := by
    simpa [prefixWord, tailWord_475965, baseEnd_475965] using wordTrace_append hprefix tailTrace_475965
  have hstable : (prefixWord ++ tailWord_475965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475965).length < 2 ^ (prefixWord ++ tailWord_475965).sum := by decide
  have hdescent : baseEnd_475965 < baseStart_475965 := by decide
  rcases family_descends (prefixWord ++ tailWord_475965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475967 : List Nat := [1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_475967 : Nat := 118140960795 + 475967 * 2 ^ 59
def prefixEnd_475967 : Nat := 4983230072969 + 3 ^ 40 * 475967 * 2
def baseEnd_475967 : Nat := 144829538772530080369525

theorem tailTrace_475967 : CollatzResearch.WordTrace tailWord_475967 prefixEnd_475967 144829538772530080369525 := by
  unfold tailWord_475967
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359942666660322536986155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11573295111106881691324103 17359942666660322536986155)
  ·
    refine ⟨26039913999990483805479233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17359942666660322536986155 26039913999990483805479233)
    ·
      refine ⟨19529935499992862854109425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26039913999990483805479233 19529935499992862854109425)
      ·
        refine ⟨14647451624994647140582069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19529935499992862854109425 14647451624994647140582069)
        ·
          refine ⟨1373198589843248169429569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14647451624994647140582069 1373198589843248169429569)
          ·
            refine ⟨1029898942382436127072177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373198589843248169429569 1029898942382436127072177)
            ·
              refine ⟨772424206786827095304133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029898942382436127072177 772424206786827095304133)
              ·
                refine ⟨144829538772530080369525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772424206786827095304133 144829538772530080369525)
                ·
                  rfl

theorem cell19_475967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_475967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_475967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_475967 prefixEnd_475967 := by exact prefixLift 475967
  have htrace : WordTrace (prefixWord ++ tailWord_475967) baseStart_475967 baseEnd_475967 := by
    simpa [prefixWord, tailWord_475967, baseEnd_475967] using wordTrace_append hprefix tailTrace_475967
  have hstable : (prefixWord ++ tailWord_475967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475967).length < 2 ^ (prefixWord ++ tailWord_475967).sum := by decide
  have hdescent : baseEnd_475967 < baseStart_475967 := by decide
  rcases family_descends (prefixWord ++ tailWord_475967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476007 : List Nat := [1, 1, 5, 1, 2, 9]
def baseStart_476007 : Nat := 118140960795 + 476007 * 2 ^ 59
def prefixEnd_476007 : Nat := 4983230072969 + 3 ^ 40 * 476007 * 2
def baseEnd_476007 : Nat := 16093523351757982164503

theorem tailTrace_476007 : CollatzResearch.WordTrace tailWord_476007 prefixEnd_476007 16093523351757982164503 := by
  unfold tailWord_476007
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361401586515409368442275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11574267724343606245628183 17361401586515409368442275)
  ·
    refine ⟨26042102379773114052663413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17361401586515409368442275 26042102379773114052663413)
    ·
      refine ⟨2441447098103729442437195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26042102379773114052663413 2441447098103729442437195)
      ·
        refine ⟨3662170647155594163655793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441447098103729442437195 3662170647155594163655793)
        ·
          refine ⟨2746627985366695622741845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662170647155594163655793 2746627985366695622741845)
          ·
            refine ⟨16093523351757982164503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2746627985366695622741845 16093523351757982164503)
            ·
              rfl

theorem cell19_476007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_476007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476007 prefixEnd_476007 := by exact prefixLift 476007
  have htrace : WordTrace (prefixWord ++ tailWord_476007) baseStart_476007 baseEnd_476007 := by
    simpa [prefixWord, tailWord_476007, baseEnd_476007] using wordTrace_append hprefix tailTrace_476007
  have hstable : (prefixWord ++ tailWord_476007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476007).length < 2 ^ (prefixWord ++ tailWord_476007).sum := by decide
  have hdescent : baseEnd_476007 < baseStart_476007 := by decide
  rcases family_descends (prefixWord ++ tailWord_476007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476022 : List Nat := [5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_476022 : Nat := 118140960795 + 476022 * 2 ^ 59
def prefixEnd_476022 : Nat := 4983230072969 + 3 ^ 40 * 476022 * 2
def baseEnd_476022 : Nat := 144846274438306249147153

theorem tailTrace_476022 : CollatzResearch.WordTrace tailWord_476022 prefixEnd_476022 144846274438306249147153 := by
  unfold tailWord_476022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085121792591316683139895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11574632454307377953492213 1085121792591316683139895)
  ·
    refine ⟨1627682688886975024709843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085121792591316683139895 1627682688886975024709843)
    ·
      refine ⟨2441524033330462537064765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627682688886975024709843 2441524033330462537064765)
      ·
        refine ⟨915571512498923451399287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2441524033330462537064765 915571512498923451399287)
        ·
          refine ⟨1373357268748385177098931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915571512498923451399287 1373357268748385177098931)
          ·
            refine ⟨2060035903122577765648397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373357268748385177098931 2060035903122577765648397)
            ·
              refine ⟨772513463670966662118149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060035903122577765648397 772513463670966662118149)
              ·
                refine ⟨144846274438306249147153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772513463670966662118149 144846274438306249147153)
                ·
                  rfl

theorem cell19_476022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_476022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476022 prefixEnd_476022 := by exact prefixLift 476022
  have htrace : WordTrace (prefixWord ++ tailWord_476022) baseStart_476022 baseEnd_476022 := by
    simpa [prefixWord, tailWord_476022, baseEnd_476022] using wordTrace_append hprefix tailTrace_476022
  have hstable : (prefixWord ++ tailWord_476022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476022).length < 2 ^ (prefixWord ++ tailWord_476022).sum := by decide
  have hdescent : baseEnd_476022 < baseStart_476022 := by decide
  rcases family_descends (prefixWord ++ tailWord_476022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476117 : List Nat := [1, 3, 2, 3, 4, 1, 5]
def baseStart_476117 : Nat := 118140960795 + 476117 * 2 ^ 59
def prefixEnd_476117 : Nat := 4983230072969 + 3 ^ 40 * 476117 * 2
def baseEnd_476117 : Nat := 48291727165791392345261

theorem tailTrace_476117 : CollatzResearch.WordTrace tailWord_476117 prefixEnd_476117 48291727165791392345261 := by
  unfold tailWord_476117
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365413616116898154946605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11576942410744598769964403 17365413616116898154946605)
  ·
    refine ⟨6512030106043836808104977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17365413616116898154946605 6512030106043836808104977)
    ·
      refine ⟨4884022579532877606078733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6512030106043836808104977 4884022579532877606078733)
      ·
        refine ⟨1831508467324829102279525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4884022579532877606078733 1831508467324829102279525)
        ·
          refine ⟨343407837623405456677411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1831508467324829102279525 343407837623405456677411)
          ·
            refine ⟨515111756435108185016117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343407837623405456677411 515111756435108185016117)
            ·
              refine ⟨48291727165791392345261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 515111756435108185016117 48291727165791392345261)
              ·
                rfl

theorem cell19_476117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_476117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476117 prefixEnd_476117 := by exact prefixLift 476117
  have htrace : WordTrace (prefixWord ++ tailWord_476117) baseStart_476117 baseEnd_476117 := by
    simpa [prefixWord, tailWord_476117, baseEnd_476117] using wordTrace_append hprefix tailTrace_476117
  have hstable : (prefixWord ++ tailWord_476117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476117).length < 2 ^ (prefixWord ++ tailWord_476117).sum := by decide
  have hdescent : baseEnd_476117 < baseStart_476117 := by decide
  rcases family_descends (prefixWord ++ tailWord_476117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476121 : List Nat := [1, 2, 1, 2, 5, 1, 7]
def baseStart_476121 : Nat := 118140960795 + 476121 * 2 ^ 59
def prefixEnd_476121 : Nat := 4983230072969 + 3 ^ 40 * 476121 * 2
def baseEnd_476121 : Nat := 48292132878901117648961

theorem tailTrace_476121 : CollatzResearch.WordTrace tailWord_476121 prefixEnd_476121 48292132878901117648961 := by
  unfold tailWord_476121
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365559508102406838092217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11577039672068271225394811 17365559508102406838092217)
  ·
    refine ⟨13024169631076805128569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17365559508102406838092217 13024169631076805128569163)
    ·
      refine ⟨19536254446615207692853745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13024169631076805128569163 19536254446615207692853745)
      ·
        refine ⟨14652190834961405769640309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19536254446615207692853745 14652190834961405769640309)
        ·
          refine ⟨1373642890777631790903779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14652190834961405769640309 1373642890777631790903779)
          ·
            refine ⟨2060464336166447686355669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373642890777631790903779 2060464336166447686355669)
            ·
              refine ⟨48292132878901117648961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2060464336166447686355669 48292132878901117648961)
              ·
                rfl

theorem cell19_476121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_476121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476121 prefixEnd_476121 := by exact prefixLift 476121
  have htrace : WordTrace (prefixWord ++ tailWord_476121) baseStart_476121 baseEnd_476121 := by
    simpa [prefixWord, tailWord_476121, baseEnd_476121] using wordTrace_append hprefix tailTrace_476121
  have hstable : (prefixWord ++ tailWord_476121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476121).length < 2 ^ (prefixWord ++ tailWord_476121).sum := by decide
  have hdescent : baseEnd_476121 < baseStart_476121 := by decide
  rcases family_descends (prefixWord ++ tailWord_476121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476138 : List Nat := [3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_476138 : Nat := 118140960795 + 476138 * 2 ^ 59
def prefixEnd_476138 : Nat := 4983230072969 + 3 ^ 40 * 476138 * 2
def baseEnd_476138 : Nat := 144881571478852350569059

theorem tailTrace_476138 : CollatzResearch.WordTrace tailWord_476138 prefixEnd_476138 144881571478852350569059 := by
  unfold tailWord_476138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341544887260204685365267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11577453032693879160974045 4341544887260204685365267)
  ·
    refine ⟨6512317330890307028047901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341544887260204685365267 6512317330890307028047901)
    ·
      refine ⟨2442118999083865135517963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6512317330890307028047901 2442118999083865135517963)
      ·
        refine ⟨3663178498625797703276945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442118999083865135517963 3663178498625797703276945)
        ·
          refine ⟨2747383873969348277457709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663178498625797703276945 2747383873969348277457709)
          ·
            refine ⟨1030268952738505604046641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2747383873969348277457709 1030268952738505604046641)
            ·
              refine ⟨772701714553879203034981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030268952738505604046641 772701714553879203034981)
              ·
                refine ⟨144881571478852350569059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772701714553879203034981 144881571478852350569059)
                ·
                  rfl

theorem cell19_476138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_476138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476138 prefixEnd_476138 := by exact prefixLift 476138
  have htrace : WordTrace (prefixWord ++ tailWord_476138) baseStart_476138 baseEnd_476138 := by
    simpa [prefixWord, tailWord_476138, baseEnd_476138] using wordTrace_append hprefix tailTrace_476138
  have hstable : (prefixWord ++ tailWord_476138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476138).length < 2 ^ (prefixWord ++ tailWord_476138).sum := by decide
  have hdescent : baseEnd_476138 < baseStart_476138 := by decide
  rcases family_descends (prefixWord ++ tailWord_476138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476195 : List Nat := [1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_476195 : Nat := 118140960795 + 476195 * 2 ^ 59
def prefixEnd_476195 : Nat := 4983230072969 + 3 ^ 40 * 476195 * 2
def baseEnd_476195 : Nat := 144898915714293107302237

theorem tailTrace_476195 : CollatzResearch.WordTrace tailWord_476195 prefixEnd_476195 144898915714293107302237 := by
  unfold tailWord_476195
  simp only [CollatzResearch.WordTrace]
  refine ⟨17368258509834317476286039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11578839006556211650857359 17368258509834317476286039)
  ·
    refine ⟨26052387764751476214429059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17368258509834317476286039 26052387764751476214429059)
    ·
      refine ⟨39078581647127214321643589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26052387764751476214429059 39078581647127214321643589)
      ·
        refine ⟨7327234058836352685308173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39078581647127214321643589 7327234058836352685308173)
        ·
          refine ⟨2747712772063632256990565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7327234058836352685308173 2747712772063632256990565)
          ·
            refine ⟨515196144761931048185731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2747712772063632256990565 515196144761931048185731)
            ·
              refine ⟨772794217142896572278597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515196144761931048185731 772794217142896572278597)
              ·
                refine ⟨144898915714293107302237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772794217142896572278597 144898915714293107302237)
                ·
                  rfl

theorem cell19_476195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_476195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476195 prefixEnd_476195 := by exact prefixLift 476195
  have htrace : WordTrace (prefixWord ++ tailWord_476195) baseStart_476195 baseEnd_476195 := by
    simpa [prefixWord, tailWord_476195, baseEnd_476195] using wordTrace_append hprefix tailTrace_476195
  have hstable : (prefixWord ++ tailWord_476195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476195).length < 2 ^ (prefixWord ++ tailWord_476195).sum := by decide
  have hdescent : baseEnd_476195 < baseStart_476195 := by decide
  rcases family_descends (prefixWord ++ tailWord_476195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476269 : List Nat := [1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_476269 : Nat := 118140960795 + 476269 * 2 ^ 59
def prefixEnd_476269 : Nat := 4983230072969 + 3 ^ 40 * 476269 * 2
def baseEnd_476269 : Nat := 144921432791882861657591

theorem tailTrace_476269 : CollatzResearch.WordTrace tailWord_476269 prefixEnd_476269 144921432791882861657591 := by
  unfold tailWord_476269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370957511566228114479861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11580638341044152076319907 17370957511566228114479861)
  ·
    refine ⟨1628527266709333885732487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17370957511566228114479861 1628527266709333885732487)
    ·
      refine ⟨2442790900064000828598731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628527266709333885732487 2442790900064000828598731)
      ·
        refine ⟨3664186350096001242898097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442790900064000828598731 3664186350096001242898097)
        ·
          refine ⟨2748139762572000932173573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664186350096001242898097 2748139762572000932173573)
          ·
            refine ⟨515276205482250174782545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2748139762572000932173573 515276205482250174782545)
            ·
              refine ⟨386457154111687631086909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515276205482250174782545 386457154111687631086909)
              ·
                refine ⟨144921432791882861657591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386457154111687631086909 144921432791882861657591)
                ·
                  rfl

theorem cell19_476269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_476269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476269 prefixEnd_476269 := by exact prefixLift 476269
  have htrace : WordTrace (prefixWord ++ tailWord_476269) baseStart_476269 baseEnd_476269 := by
    simpa [prefixWord, tailWord_476269, baseEnd_476269] using wordTrace_append hprefix tailTrace_476269
  have hstable : (prefixWord ++ tailWord_476269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476269).length < 2 ^ (prefixWord ++ tailWord_476269).sum := by decide
  have hdescent : baseEnd_476269 < baseStart_476269 := by decide
  rcases family_descends (prefixWord ++ tailWord_476269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476292 : List Nat := [2, 3, 2, 1, 2, 2, 7]
def baseStart_476292 : Nat := 118140960795 + 476292 * 2 ^ 59
def prefixEnd_476292 : Nat := 4983230072969 + 3 ^ 40 * 476292 * 2
def baseEnd_476292 : Nat := 48309477114341874382139

theorem tailTrace_476292 : CollatzResearch.WordTrace tailWord_476292 prefixEnd_476292 48309477114341874382139 := by
  unfold tailWord_476292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685898195241451521283565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11581197593655268695044753 8685898195241451521283565)
  ·
    refine ⟨3257211823215544320481337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8685898195241451521283565 3257211823215544320481337)
    ·
      refine ⟨2442908867411658240361003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3257211823215544320481337 2442908867411658240361003)
      ·
        refine ⟨3664363301117487360541505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442908867411658240361003 3664363301117487360541505)
        ·
          refine ⟨2748272475838115520406129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664363301117487360541505 2748272475838115520406129)
          ·
            refine ⟨2061204356878586640304597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748272475838115520406129 2061204356878586640304597)
            ·
              refine ⟨48309477114341874382139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2061204356878586640304597 48309477114341874382139)
              ·
                rfl

theorem cell19_476292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_476292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476292 prefixEnd_476292 := by exact prefixLift 476292
  have htrace : WordTrace (prefixWord ++ tailWord_476292) baseStart_476292 baseEnd_476292 := by
    simpa [prefixWord, tailWord_476292, baseEnd_476292] using wordTrace_append hprefix tailTrace_476292
  have hstable : (prefixWord ++ tailWord_476292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476292).length < 2 ^ (prefixWord ++ tailWord_476292).sum := by decide
  have hdescent : baseEnd_476292 < baseStart_476292 := by decide
  rcases family_descends (prefixWord ++ tailWord_476292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476311 : List Nat := [1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_476311 : Nat := 118140960795 + 476311 * 2 ^ 59
def prefixEnd_476311 : Nat := 4983230072969 + 3 ^ 40 * 476311 * 2
def baseEnd_476311 : Nat := 144934212754839208724143

theorem tailTrace_476311 : CollatzResearch.WordTrace tailWord_476311 prefixEnd_476311 144934212754839208724143 := by
  unfold tailWord_476311
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372489377414069287508787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11581659584942712858339191 17372489377414069287508787)
  ·
    refine ⟨26058734066121103931263181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17372489377414069287508787 26058734066121103931263181)
    ·
      refine ⟨9772025274795413974223693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26058734066121103931263181 9772025274795413974223693)
      ·
        refine ⟨3664509478048280240333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9772025274795413974223693 3664509478048280240333885)
        ·
          refine ⟨1374191054268105090125207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3664509478048280240333885 1374191054268105090125207)
          ·
            refine ⟨2061286581402157635187811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374191054268105090125207 2061286581402157635187811)
            ·
              refine ⟨3091929872103236452781717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061286581402157635187811 3091929872103236452781717)
              ·
                refine ⟨144934212754839208724143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3091929872103236452781717 144934212754839208724143)
                ·
                  rfl

theorem cell19_476311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_476311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476311 prefixEnd_476311 := by exact prefixLift 476311
  have htrace : WordTrace (prefixWord ++ tailWord_476311) baseStart_476311 baseEnd_476311 := by
    simpa [prefixWord, tailWord_476311, baseEnd_476311] using wordTrace_append hprefix tailTrace_476311
  have hstable : (prefixWord ++ tailWord_476311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476311).length < 2 ^ (prefixWord ++ tailWord_476311).sum := by decide
  have hdescent : baseEnd_476311 < baseStart_476311 := by decide
  rcases family_descends (prefixWord ++ tailWord_476311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476358 : List Nat := [6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_476358 : Nat := 118140960795 + 476358 * 2 ^ 59
def prefixEnd_476358 : Nat := 4983230072969 + 3 ^ 40 * 476358 * 2
def baseEnd_476358 : Nat := 144948514141957025679571

theorem tailTrace_476358 : CollatzResearch.WordTrace tailWord_476358 prefixEnd_476358 144948514141957025679571 := by
  unfold tailWord_476358
  simp only [CollatzResearch.WordTrace]
  refine ⟨542943862757618634827179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11582802405495864209646485 542943862757618634827179)
  ·
    refine ⟨814415794136427952240769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542943862757618634827179 814415794136427952240769)
    ·
      refine ⟨610811845602320964180577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 814415794136427952240769 610811845602320964180577)
      ·
        refine ⟨458108884201740723135433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610811845602320964180577 458108884201740723135433)
        ·
          refine ⟨343581663151305542351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458108884201740723135433 343581663151305542351575)
          ·
            refine ⟨515372494726958313527363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343581663151305542351575 515372494726958313527363)
            ·
              refine ⟨773058742090437470291045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515372494726958313527363 773058742090437470291045)
              ·
                refine ⟨144948514141957025679571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773058742090437470291045 144948514141957025679571)
                ·
                  rfl

theorem cell19_476358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_476358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476358 prefixEnd_476358 := by exact prefixLift 476358
  have htrace : WordTrace (prefixWord ++ tailWord_476358) baseStart_476358 baseEnd_476358 := by
    simpa [prefixWord, tailWord_476358, baseEnd_476358] using wordTrace_append hprefix tailTrace_476358
  have hstable : (prefixWord ++ tailWord_476358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476358).length < 2 ^ (prefixWord ++ tailWord_476358).sum := by decide
  have hdescent : baseEnd_476358 < baseStart_476358 := by decide
  rcases family_descends (prefixWord ++ tailWord_476358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476385 : List Nat := [1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_476385 : Nat := 118140960795 + 476385 * 2 ^ 59
def prefixEnd_476385 : Nat := 4983230072969 + 3 ^ 40 * 476385 * 2
def baseEnd_476385 : Nat := 144956729832428963079497

theorem tailTrace_476385 : CollatzResearch.WordTrace tailWord_476385 prefixEnd_476385 144956729832428963079497 := by
  unfold tailWord_476385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375188379145979925702609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11583458919430653283801739 17375188379145979925702609)
  ·
    refine ⟨13031391284359484944276957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17375188379145979925702609 13031391284359484944276957)
    ·
      refine ⟨4886771731634806854103859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13031391284359484944276957 4886771731634806854103859)
      ·
        refine ⟨7330157597452210281155789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886771731634806854103859 7330157597452210281155789)
        ·
          refine ⟨2748809099044578855433421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7330157597452210281155789 2748809099044578855433421)
          ·
            refine ⟨1030803412141717070787533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2748809099044578855433421 1030803412141717070787533)
            ·
              refine ⟨386551279553143901545325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1030803412141717070787533 386551279553143901545325)
              ·
                refine ⟨144956729832428963079497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386551279553143901545325 144956729832428963079497)
                ·
                  rfl

theorem cell19_476385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_476385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476385 prefixEnd_476385 := by exact prefixLift 476385
  have htrace : WordTrace (prefixWord ++ tailWord_476385) baseStart_476385 baseEnd_476385 := by
    simpa [prefixWord, tailWord_476385, baseEnd_476385] using wordTrace_append hprefix tailTrace_476385
  have hstable : (prefixWord ++ tailWord_476385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476385).length < 2 ^ (prefixWord ++ tailWord_476385).sum := by decide
  have hdescent : baseEnd_476385 < baseStart_476385 := by decide
  rcases family_descends (prefixWord ++ tailWord_476385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476442 : List Nat := [3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_476442 : Nat := 118140960795 + 476442 * 2 ^ 59
def prefixEnd_476442 : Nat := 4983230072969 + 3 ^ 40 * 476442 * 2
def baseEnd_476442 : Nat := 144974074067869719812675

theorem tailTrace_476442 : CollatzResearch.WordTrace tailWord_476442 prefixEnd_476442 144974074067869719812675 := by
  unfold tailWord_476442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344316834984869665131895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11584844893292985773685053 4344316834984869665131895)
  ·
    refine ⟨6516475252477304497697843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344316834984869665131895 6516475252477304497697843)
    ·
      refine ⟨9774712878715956746546765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516475252477304497697843 9774712878715956746546765)
      ·
        refine ⟨3665517329518483779955037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9774712878715956746546765 3665517329518483779955037)
        ·
          refine ⟨1374568998569431417483139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3665517329518483779955037 1374568998569431417483139)
          ·
            refine ⟨2061853497854147126224709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374568998569431417483139 2061853497854147126224709)
            ·
              refine ⟨386597530847652586167133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2061853497854147126224709 386597530847652586167133)
              ·
                refine ⟨144974074067869719812675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386597530847652586167133 144974074067869719812675)
                ·
                  rfl

theorem cell19_476442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_476442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476442 prefixEnd_476442 := by exact prefixLift 476442
  have htrace : WordTrace (prefixWord ++ tailWord_476442) baseStart_476442 baseEnd_476442 := by
    simpa [prefixWord, tailWord_476442, baseEnd_476442] using wordTrace_append hprefix tailTrace_476442
  have hstable : (prefixWord ++ tailWord_476442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476442).length < 2 ^ (prefixWord ++ tailWord_476442).sum := by decide
  have hdescent : baseEnd_476442 < baseStart_476442 := by decide
  rcases family_descends (prefixWord ++ tailWord_476442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476461 : List Nat := [1, 5, 3, 1, 1, 1, 7]
def baseStart_476461 : Nat := 118140960795 + 476461 * 2 ^ 59
def prefixEnd_476461 : Nat := 4983230072969 + 3 ^ 40 * 476461 * 2
def baseEnd_476461 : Nat := 48326618493227768463467

theorem tailTrace_476461 : CollatzResearch.WordTrace tailWord_476461 prefixEnd_476461 48326618493227768463467 := by
  unfold tailWord_476461
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377960326870644905469237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11585306884580429936979491 17377960326870644905469237)
  ·
    refine ⟨1629183780644122959887741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17377960326870644905469237 1629183780644122959887741)
    ·
      refine ⟨610943917741546109957903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1629183780644122959887741 610943917741546109957903)
      ·
        refine ⟨916415876612319164936855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610943917741546109957903 916415876612319164936855)
        ·
          refine ⟨1374623814918478747405283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916415876612319164936855 1374623814918478747405283)
          ·
            refine ⟨2061935722377718121107925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374623814918478747405283 2061935722377718121107925)
            ·
              refine ⟨48326618493227768463467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2061935722377718121107925 48326618493227768463467)
              ·
                rfl

theorem cell19_476461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_476461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476461 prefixEnd_476461 := by exact prefixLift 476461
  have htrace : WordTrace (prefixWord ++ tailWord_476461) baseStart_476461 baseEnd_476461 := by
    simpa [prefixWord, tailWord_476461, baseEnd_476461] using wordTrace_append hprefix tailTrace_476461
  have hstable : (prefixWord ++ tailWord_476461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476461).length < 2 ^ (prefixWord ++ tailWord_476461).sum := by decide
  have hdescent : baseEnd_476461 < baseStart_476461 := by decide
  rcases family_descends (prefixWord ++ tailWord_476461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476501 : List Nat := [1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_476501 : Nat := 118140960795 + 476501 * 2 ^ 59
def prefixEnd_476501 : Nat := 4983230072969 + 3 ^ 40 * 476501 * 2
def baseEnd_476501 : Nat := 144992026872975064501403

theorem tailTrace_476501 : CollatzResearch.WordTrace tailWord_476501 prefixEnd_476501 144992026872975064501403 := by
  unfold tailWord_476501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379419246725731736925357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586279497817154491283571 17379419246725731736925357)
  ·
    refine ⟨6517282217522149401347009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17379419246725731736925357 6517282217522149401347009)
    ·
      refine ⟨4887961663141612051010257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6517282217522149401347009 4887961663141612051010257)
      ·
        refine ⟨3665971247356209038257693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4887961663141612051010257 3665971247356209038257693)
        ·
          refine ⟨1374739217758578389346635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3665971247356209038257693 1374739217758578389346635)
          ·
            refine ⟨2062108826637867584019953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374739217758578389346635 2062108826637867584019953)
            ·
              refine ⟨1546581619978400688014965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062108826637867584019953 1546581619978400688014965)
              ·
                refine ⟨144992026872975064501403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546581619978400688014965 144992026872975064501403)
                ·
                  rfl

theorem cell19_476501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_476501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476501 prefixEnd_476501 := by exact prefixLift 476501
  have htrace : WordTrace (prefixWord ++ tailWord_476501) baseStart_476501 baseEnd_476501 := by
    simpa [prefixWord, tailWord_476501, baseEnd_476501] using wordTrace_append hprefix tailTrace_476501
  have hstable : (prefixWord ++ tailWord_476501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476501).length < 2 ^ (prefixWord ++ tailWord_476501).sum := by decide
  have hdescent : baseEnd_476501 < baseStart_476501 := by decide
  rcases family_descends (prefixWord ++ tailWord_476501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476520 : List Nat := [2, 1, 4, 2, 3, 7]
def baseStart_476520 : Nat := 118140960795 + 476520 * 2 ^ 59
def prefixEnd_476520 : Nat := 4983230072969 + 3 ^ 40 * 476520 * 2
def baseEnd_476520 : Nat := 16110867587198738897681

theorem tailTrace_476520 : CollatzResearch.WordTrace tailWord_476520 prefixEnd_476520 16110867587198738897681 := by
  unfold tailWord_476520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690056116828448990933507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11586741489104598654578009 8690056116828448990933507)
  ·
    refine ⟨13035084175242673486400261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690056116828448990933507 13035084175242673486400261)
    ·
      refine ⟨2444078282858001278700049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13035084175242673486400261 2444078282858001278700049)
      ·
        refine ⟨1833058712143500959025037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444078282858001278700049 1833058712143500959025037)
        ·
          refine ⟨687397017053812859634389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1833058712143500959025037 687397017053812859634389)
          ·
            refine ⟨16110867587198738897681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 687397017053812859634389 16110867587198738897681)
            ·
              rfl

theorem cell19_476520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_476520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476520 prefixEnd_476520 := by exact prefixLift 476520
  have htrace : WordTrace (prefixWord ++ tailWord_476520) baseStart_476520 baseEnd_476520 := by
    simpa [prefixWord, tailWord_476520, baseEnd_476520] using wordTrace_append hprefix tailTrace_476520
  have hstable : (prefixWord ++ tailWord_476520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476520).length < 2 ^ (prefixWord ++ tailWord_476520).sum := by decide
  have hdescent : baseEnd_476520 < baseStart_476520 := by decide
  rcases family_descends (prefixWord ++ tailWord_476520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476579 : List Nat := [1, 1, 1, 4, 1, 3, 8]
def baseStart_476579 : Nat := 118140960795 + 476579 * 2 ^ 59
def prefixEnd_476579 : Nat := 4983230072969 + 3 ^ 40 * 476579 * 2
def baseEnd_476579 : Nat := 48338587029964664922619

theorem tailTrace_476579 : CollatzResearch.WordTrace tailWord_476579 prefixEnd_476579 48338587029964664922619 := by
  unfold tailWord_476579
  simp only [CollatzResearch.WordTrace]
  refine ⟨17382264140443151058264791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11588176093628767372176527 17382264140443151058264791)
  ·
    refine ⟨26073396210664726587397187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17382264140443151058264791 26073396210664726587397187)
    ·
      refine ⟨39110094315997089881095781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26073396210664726587397187 39110094315997089881095781)
      ·
        refine ⟨7333142684249454352705459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39110094315997089881095781 7333142684249454352705459)
        ·
          refine ⟨10999714026374181529058189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333142684249454352705459 10999714026374181529058189)
          ·
            refine ⟨4124892759890318073396821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10999714026374181529058189 4124892759890318073396821)
            ·
              refine ⟨48338587029964664922619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4124892759890318073396821 48338587029964664922619)
              ·
                rfl

theorem cell19_476579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_476579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476579 prefixEnd_476579 := by exact prefixLift 476579
  have htrace : WordTrace (prefixWord ++ tailWord_476579) baseStart_476579 baseEnd_476579 := by
    simpa [prefixWord, tailWord_476579, baseEnd_476579] using wordTrace_append hprefix tailTrace_476579
  have hstable : (prefixWord ++ tailWord_476579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476579).length < 2 ^ (prefixWord ++ tailWord_476579).sum := by decide
  have hdescent : baseEnd_476579 < baseStart_476579 := by decide
  rcases family_descends (prefixWord ++ tailWord_476579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476634 : List Nat := [3, 1, 1, 2, 3, 4, 5]
def baseStart_476634 : Nat := 118140960795 + 476634 * 2 ^ 59
def prefixEnd_476634 : Nat := 4983230072969 + 3 ^ 40 * 476634 * 2
def baseEnd_476634 : Nat := 48344165585223387848495

theorem tailTrace_476634 : CollatzResearch.WordTrace tailWord_476634 prefixEnd_476634 48344165585223387848495 := by
  unfold tailWord_476634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346067538810973862879239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11589513436829263634344637 4346067538810973862879239)
  ·
    refine ⟨6519101308216460794318859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4346067538810973862879239 6519101308216460794318859)
    ·
      refine ⟨9778651962324691191478289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6519101308216460794318859 9778651962324691191478289)
      ·
        refine ⟨7333988971743518393608717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9778651962324691191478289 7333988971743518393608717)
        ·
          refine ⟨2750245864403819397603269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7333988971743518393608717 2750245864403819397603269)
          ·
            refine ⟨515671099575716137050613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2750245864403819397603269 515671099575716137050613)
            ·
              refine ⟨48344165585223387848495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 515671099575716137050613 48344165585223387848495)
              ·
                rfl

theorem cell19_476634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_476634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476634 prefixEnd_476634 := by exact prefixLift 476634
  have htrace : WordTrace (prefixWord ++ tailWord_476634) baseStart_476634 baseEnd_476634 := by
    simpa [prefixWord, tailWord_476634, baseEnd_476634] using wordTrace_append hprefix tailTrace_476634
  have hstable : (prefixWord ++ tailWord_476634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476634).length < 2 ^ (prefixWord ++ tailWord_476634).sum := by decide
  have hdescent : baseEnd_476634 < baseStart_476634 := by decide
  rcases family_descends (prefixWord ++ tailWord_476634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476655 : List Nat := [1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_476655 : Nat := 118140960795 + 476655 * 2 ^ 59
def prefixEnd_476655 : Nat := 4983230072969 + 3 ^ 40 * 476655 * 2
def baseEnd_476655 : Nat := 145038886737148337078761

theorem tailTrace_476655 : CollatzResearch.WordTrace tailWord_476655 prefixEnd_476655 145038886737148337078761 := by
  unfold tailWord_476655
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385036088167816038031419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11590024058778544025354279 17385036088167816038031419)
  ·
    refine ⟨26077554132251724057047129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17385036088167816038031419 26077554132251724057047129)
    ·
      refine ⟨19558165599188793042785347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26077554132251724057047129 19558165599188793042785347)
      ·
        refine ⟨29337248398783189564178021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19558165599188793042785347 29337248398783189564178021)
        ·
          refine ⟨5500734074771848043283379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29337248398783189564178021 5500734074771848043283379)
          ·
            refine ⟨8251101112157772064925069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500734074771848043283379 8251101112157772064925069)
            ·
              refine ⟨3094162917059164524346901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8251101112157772064925069 3094162917059164524346901)
              ·
                refine ⟨145038886737148337078761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3094162917059164524346901 145038886737148337078761)
                ·
                  rfl

theorem cell19_476655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_476655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476655 prefixEnd_476655 := by exact prefixLift 476655
  have htrace : WordTrace (prefixWord ++ tailWord_476655) baseStart_476655 baseEnd_476655 := by
    simpa [prefixWord, tailWord_476655, baseEnd_476655] using wordTrace_append hprefix tailTrace_476655
  have hstable : (prefixWord ++ tailWord_476655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476655).length < 2 ^ (prefixWord ++ tailWord_476655).sum := by decide
  have hdescent : baseEnd_476655 < baseStart_476655 := by decide
  rcases family_descends (prefixWord ++ tailWord_476655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476693 : List Nat := [1, 3, 2, 1, 3, 9]
def baseStart_476693 : Nat := 118140960795 + 476693 * 2 ^ 59
def prefixEnd_476693 : Nat := 4983230072969 + 3 ^ 40 * 476693 * 2
def baseEnd_476693 : Nat := 16116716617863945359357

theorem tailTrace_476693 : CollatzResearch.WordTrace tailWord_476693 prefixEnd_476693 16116716617863945359357 := by
  unfold tailWord_476693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17386422062030148527914733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11590948041353432351943155 17386422062030148527914733)
  ·
    refine ⟨6519908273261305697968025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17386422062030148527914733 6519908273261305697968025)
    ·
      refine ⟨4889931204945979273476019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519908273261305697968025 4889931204945979273476019)
      ·
        refine ⟨7334896807418968910214029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889931204945979273476019 7334896807418968910214029)
        ·
          refine ⟨2750586302782113341330261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7334896807418968910214029 2750586302782113341330261)
          ·
            refine ⟨16116716617863945359357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2750586302782113341330261 16116716617863945359357)
            ·
              rfl

theorem cell19_476693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_476693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476693 prefixEnd_476693 := by exact prefixLift 476693
  have htrace : WordTrace (prefixWord ++ tailWord_476693) baseStart_476693 baseEnd_476693 := by
    simpa [prefixWord, tailWord_476693, baseEnd_476693] using wordTrace_append hprefix tailTrace_476693
  have hstable : (prefixWord ++ tailWord_476693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476693).length < 2 ^ (prefixWord ++ tailWord_476693).sum := by decide
  have hdescent : baseEnd_476693 < baseStart_476693 := by decide
  rcases family_descends (prefixWord ++ tailWord_476693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476702 : List Nat := [4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_476702 : Nat := 118140960795 + 476702 * 2 ^ 59
def prefixEnd_476702 : Nat := 4983230072969 + 3 ^ 40 * 476702 * 2
def baseEnd_476702 : Nat := 145053188124266154034189

theorem tailTrace_476702 : CollatzResearch.WordTrace tailWord_476702 prefixEnd_476702 145053188124266154034189 := by
  unfold tailWord_476702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173343789874692883124045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11591166879331695376661573 2173343789874692883124045)
  ·
    refine ⟨815003921203009831171517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2173343789874692883124045 815003921203009831171517)
    ·
      refine ⟨305626470451128686689319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 815003921203009831171517 305626470451128686689319)
      ·
        refine ⟨458439705676693030033979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305626470451128686689319 458439705676693030033979)
        ·
          refine ⟨687659558515039545050969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458439705676693030033979 687659558515039545050969)
          ·
            refine ⟨515744668886279658788227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687659558515039545050969 515744668886279658788227)
            ·
              refine ⟨773617003329419488182341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515744668886279658788227 773617003329419488182341)
              ·
                refine ⟨145053188124266154034189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773617003329419488182341 145053188124266154034189)
                ·
                  rfl

theorem cell19_476702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_476702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476702 prefixEnd_476702 := by exact prefixLift 476702
  have htrace : WordTrace (prefixWord ++ tailWord_476702) baseStart_476702 baseEnd_476702 := by
    simpa [prefixWord, tailWord_476702, baseEnd_476702] using wordTrace_append hprefix tailTrace_476702
  have hstable : (prefixWord ++ tailWord_476702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476702).length < 2 ^ (prefixWord ++ tailWord_476702).sum := by decide
  have hdescent : baseEnd_476702 < baseStart_476702 := by decide
  rcases family_descends (prefixWord ++ tailWord_476702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476769 : List Nat := [1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_476769 : Nat := 118140960795 + 476769 * 2 ^ 59
def prefixEnd_476769 : Nat := 4983230072969 + 3 ^ 40 * 476769 * 2
def baseEnd_476769 : Nat := 145073575208029850545117

theorem tailTrace_476769 : CollatzResearch.WordTrace tailWord_476769 prefixEnd_476769 145073575208029850545117 := by
  unfold tailWord_476769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17389194009754813507681361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11592796006503209005120907 17389194009754813507681361)
  ·
    refine ⟨13041895507316110130761021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17389194009754813507681361 13041895507316110130761021)
    ·
      refine ⟨4890710815243541299035383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13041895507316110130761021 4890710815243541299035383)
      ·
        refine ⟨7336066222865311948553075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890710815243541299035383 7336066222865311948553075)
        ·
          refine ⟨11004099334297967922829613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336066222865311948553075 11004099334297967922829613)
          ·
            refine ⟨4126537250361737971061105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11004099334297967922829613 4126537250361737971061105)
            ·
              refine ⟨3094902937771303478295829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126537250361737971061105 3094902937771303478295829)
              ·
                refine ⟨145073575208029850545117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3094902937771303478295829 145073575208029850545117)
                ·
                  rfl

theorem cell19_476769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_476769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476769 prefixEnd_476769 := by exact prefixLift 476769
  have htrace : WordTrace (prefixWord ++ tailWord_476769) baseStart_476769 baseEnd_476769 := by
    simpa [prefixWord, tailWord_476769, baseEnd_476769] using wordTrace_append hprefix tailTrace_476769
  have hstable : (prefixWord ++ tailWord_476769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476769).length < 2 ^ (prefixWord ++ tailWord_476769).sum := by decide
  have hdescent : baseEnd_476769 < baseStart_476769 := by decide
  rcases family_descends (prefixWord ++ tailWord_476769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476782 : List Nat := [4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_476782 : Nat := 118140960795 + 476782 * 2 ^ 59
def prefixEnd_476782 : Nat := 4983230072969 + 3 ^ 40 * 476782 * 2
def baseEnd_476782 : Nat := 145077530910849672256193

theorem tailTrace_476782 : CollatzResearch.WordTrace tailWord_476782 prefixEnd_476782 145077530910849672256193 := by
  unfold tailWord_476782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173708519838464590988075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11593112105805144485269733 2173708519838464590988075)
  ·
    refine ⟨3260562779757696886482113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173708519838464590988075 3260562779757696886482113)
    ·
      refine ⟨2445422084818272664861585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3260562779757696886482113 2445422084818272664861585)
      ·
        refine ⟨1834066563613704498646189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445422084818272664861585 1834066563613704498646189)
        ·
          refine ⟨687774961355139186992321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1834066563613704498646189 687774961355139186992321)
          ·
            refine ⟨515831221016354390244241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687774961355139186992321 515831221016354390244241)
            ·
              refine ⟨386873415762265792683181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515831221016354390244241 386873415762265792683181)
              ·
                refine ⟨145077530910849672256193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386873415762265792683181 145077530910849672256193)
                ·
                  rfl

theorem cell19_476782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_476782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476782 prefixEnd_476782 := by exact prefixLift 476782
  have htrace : WordTrace (prefixWord ++ tailWord_476782) baseStart_476782 baseEnd_476782 := by
    simpa [prefixWord, tailWord_476782, baseEnd_476782] using wordTrace_append hprefix tailTrace_476782
  have hstable : (prefixWord ++ tailWord_476782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476782).length < 2 ^ (prefixWord ++ tailWord_476782).sum := by decide
  have hdescent : baseEnd_476782 < baseStart_476782 := by decide
  rcases family_descends (prefixWord ++ tailWord_476782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476784 : List Nat := [2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_476784 : Nat := 118140960795 + 476784 * 2 ^ 59
def prefixEnd_476784 : Nat := 4983230072969 + 3 ^ 40 * 476784 * 2
def baseEnd_476784 : Nat := 145078139480514260211743

theorem tailTrace_476784 : CollatzResearch.WordTrace tailWord_476784 prefixEnd_476784 145078139480514260211743 := by
  unfold tailWord_476784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694870552350235534738703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11593160736466980712984937 8694870552350235534738703)
  ·
    refine ⟨13042305828525353302108055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694870552350235534738703 13042305828525353302108055)
    ·
      refine ⟨19563458742788029953162083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042305828525353302108055 19563458742788029953162083)
      ·
        refine ⟨29345188114182044929743125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563458742788029953162083 29345188114182044929743125)
        ·
          refine ⟨1375555692852283356081709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29345188114182044929743125 1375555692852283356081709)
          ·
            refine ⟨515833384819606258530641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1375555692852283356081709 515833384819606258530641)
            ·
              refine ⟨386875038614704693897981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515833384819606258530641 386875038614704693897981)
              ·
                refine ⟨145078139480514260211743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386875038614704693897981 145078139480514260211743)
                ·
                  rfl

theorem cell19_476784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_476784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476784 prefixEnd_476784 := by exact prefixLift 476784
  have htrace : WordTrace (prefixWord ++ tailWord_476784) baseStart_476784 baseEnd_476784 := by
    simpa [prefixWord, tailWord_476784, baseEnd_476784] using wordTrace_append hprefix tailTrace_476784
  have hstable : (prefixWord ++ tailWord_476784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476784).length < 2 ^ (prefixWord ++ tailWord_476784).sum := by decide
  have hdescent : baseEnd_476784 < baseStart_476784 := by decide
  rcases family_descends (prefixWord ++ tailWord_476784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476786 : List Nat := [3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_476786 : Nat := 118140960795 + 476786 * 2 ^ 59
def prefixEnd_476786 : Nat := 4983230072969 + 3 ^ 40 * 476786 * 2
def baseEnd_476786 : Nat := 145078748050178848167293

theorem tailTrace_476786 : CollatzResearch.WordTrace tailWord_476786 prefixEnd_476786 145078748050178848167293 := by
  unfold tailWord_476786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347453512673306352762553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11593209367128816940700141 4347453512673306352762553)
  ·
    refine ⟨3260590134504979764571915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4347453512673306352762553 3260590134504979764571915)
    ·
      refine ⟨4890885201757469646857873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260590134504979764571915 4890885201757469646857873)
      ·
        refine ⟨3668163901318102235143405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4890885201757469646857873 3668163901318102235143405)
        ·
          refine ⟨1375561462994288338178777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3668163901318102235143405 1375561462994288338178777)
          ·
            refine ⟨1031671097245716253634083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375561462994288338178777 1031671097245716253634083)
            ·
              refine ⟨1547506645868574380451125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031671097245716253634083 1547506645868574380451125)
              ·
                refine ⟨145078748050178848167293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1547506645868574380451125 145078748050178848167293)
                ·
                  rfl

theorem cell19_476786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_476786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476786 prefixEnd_476786 := by exact prefixLift 476786
  have htrace : WordTrace (prefixWord ++ tailWord_476786) baseStart_476786 baseEnd_476786 := by
    simpa [prefixWord, tailWord_476786, baseEnd_476786] using wordTrace_append hprefix tailTrace_476786
  have hstable : (prefixWord ++ tailWord_476786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476786).length < 2 ^ (prefixWord ++ tailWord_476786).sum := by decide
  have hdescent : baseEnd_476786 < baseStart_476786 := by decide
  rcases family_descends (prefixWord ++ tailWord_476786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476807 : List Nat := [1, 1, 4, 2, 1, 3, 7]
def baseStart_476807 : Nat := 118140960795 + 476807 * 2 ^ 59
def prefixEnd_476807 : Nat := 4983230072969 + 3 ^ 40 * 476807 * 2
def baseEnd_476807 : Nat := 48361712677219007233523

theorem tailTrace_476807 : CollatzResearch.WordTrace tailWord_476807 prefixEnd_476807 48361712677219007233523 := by
  unfold tailWord_476807
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390579983617145997564675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11593719989078097331709783 17390579983617145997564675)
  ·
    refine ⟨26085869975425718996347013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17390579983617145997564675 26085869975425718996347013)
    ·
      refine ⟨4891100620392322311815065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26085869975425718996347013 4891100620392322311815065)
      ·
        refine ⟨3668325465294241733861299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891100620392322311815065 3668325465294241733861299)
        ·
          refine ⟨5502488197941362600791949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668325465294241733861299 5502488197941362600791949)
          ·
            refine ⟨2063433074228010975296981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5502488197941362600791949 2063433074228010975296981)
            ·
              refine ⟨48361712677219007233523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2063433074228010975296981 48361712677219007233523)
              ·
                rfl

theorem cell19_476807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_476807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476807 prefixEnd_476807 := by exact prefixLift 476807
  have htrace : WordTrace (prefixWord ++ tailWord_476807) baseStart_476807 baseEnd_476807 := by
    simpa [prefixWord, tailWord_476807, baseEnd_476807] using wordTrace_append hprefix tailTrace_476807
  have hstable : (prefixWord ++ tailWord_476807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476807).length < 2 ^ (prefixWord ++ tailWord_476807).sum := by decide
  have hdescent : baseEnd_476807 < baseStart_476807 := by decide
  rcases family_descends (prefixWord ++ tailWord_476807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476824 : List Nat := [2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_476824 : Nat := 118140960795 + 476824 * 2 ^ 59
def prefixEnd_476824 : Nat := 4983230072969 + 3 ^ 40 * 476824 * 2
def baseEnd_476824 : Nat := 145090310873806019322745

theorem tailTrace_476824 : CollatzResearch.WordTrace tailWord_476824 prefixEnd_476824 145090310873806019322745 := by
  unfold tailWord_476824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695600012277778950466763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11594133349703705267289017 8695600012277778950466763)
  ·
    refine ⟨13043400018416668425700145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8695600012277778950466763 13043400018416668425700145)
    ·
      refine ⟨9782550013812501319275109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043400018416668425700145 9782550013812501319275109)
      ·
        refine ⟨1834228127589843997364083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9782550013812501319275109 1834228127589843997364083)
        ·
          refine ⟨2751342191384765996046125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834228127589843997364083 2751342191384765996046125)
          ·
            refine ⟨1031753321769287248517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2751342191384765996046125 1031753321769287248517297)
            ·
              refine ⟨773814991326965436387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031753321769287248517297 773814991326965436387973)
              ·
                refine ⟨145090310873806019322745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773814991326965436387973 145090310873806019322745)
                ·
                  rfl

theorem cell19_476824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_476824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476824 prefixEnd_476824 := by exact prefixLift 476824
  have htrace : WordTrace (prefixWord ++ tailWord_476824) baseStart_476824 baseEnd_476824 := by
    simpa [prefixWord, tailWord_476824, baseEnd_476824] using wordTrace_append hprefix tailTrace_476824
  have hstable : (prefixWord ++ tailWord_476824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476824).length < 2 ^ (prefixWord ++ tailWord_476824).sum := by decide
  have hdescent : baseEnd_476824 < baseStart_476824 := by decide
  rcases family_descends (prefixWord ++ tailWord_476824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476877 : List Nat := [1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_476877 : Nat := 118140960795 + 476877 * 2 ^ 59
def prefixEnd_476877 : Nat := 4983230072969 + 3 ^ 40 * 476877 * 2
def baseEnd_476877 : Nat := 145106437969917600144823

theorem tailTrace_476877 : CollatzResearch.WordTrace tailWord_476877 prefixEnd_476877 145106437969917600144823 := by
  unfold tailWord_476877
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393133093363547952612885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11595422062242365301741923 17393133093363547952612885)
  ·
    refine ⟨815303113751416310278729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17393133093363547952612885 815303113751416310278729)
    ·
      refine ⟨611477335313562232709047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 815303113751416310278729 611477335313562232709047)
      ·
        refine ⟨917216002970343349063571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611477335313562232709047 917216002970343349063571)
        ·
          refine ⟨1375824004455515023595357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917216002970343349063571 1375824004455515023595357)
          ·
            refine ⟨515934001670818133848259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1375824004455515023595357 515934001670818133848259)
            ·
              refine ⟨773901002506227200772389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515934001670818133848259 773901002506227200772389)
              ·
                refine ⟨145106437969917600144823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773901002506227200772389 145106437969917600144823)
                ·
                  rfl

theorem cell19_476877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_476877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476877 prefixEnd_476877 := by exact prefixLift 476877
  have htrace : WordTrace (prefixWord ++ tailWord_476877) baseStart_476877 baseEnd_476877 := by
    simpa [prefixWord, tailWord_476877, baseEnd_476877] using wordTrace_append hprefix tailTrace_476877
  have hstable : (prefixWord ++ tailWord_476877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476877).length < 2 ^ (prefixWord ++ tailWord_476877).sum := by decide
  have hdescent : baseEnd_476877 < baseStart_476877 := by decide
  rcases family_descends (prefixWord ++ tailWord_476877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476881 : List Nat := [1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_476881 : Nat := 118140960795 + 476881 * 2 ^ 59
def prefixEnd_476881 : Nat := 4983230072969 + 3 ^ 40 * 476881 * 2
def baseEnd_476881 : Nat := 145107655109246776055923

theorem tailTrace_476881 : CollatzResearch.WordTrace tailWord_476881 prefixEnd_476881 145107655109246776055923 := by
  unfold tailWord_476881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393278985349056635758497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11595519323566037757172331 17393278985349056635758497)
  ·
    refine ⟨13044959239011792476818873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17393278985349056635758497 13044959239011792476818873)
    ·
      refine ⟨9783719429258844357614155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13044959239011792476818873 9783719429258844357614155)
      ·
        refine ⟨14675579143888266536421233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9783719429258844357614155 14675579143888266536421233)
        ·
          refine ⟨11006684357916199902315925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14675579143888266536421233 11006684357916199902315925)
          ·
            refine ⟨515938329277321870421059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11006684357916199902315925 515938329277321870421059)
            ·
              refine ⟨773907493915982805631589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515938329277321870421059 773907493915982805631589)
              ·
                refine ⟨145107655109246776055923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773907493915982805631589 145107655109246776055923)
                ·
                  rfl

theorem cell19_476881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_476881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476881 prefixEnd_476881 := by exact prefixLift 476881
  have htrace : WordTrace (prefixWord ++ tailWord_476881) baseStart_476881 baseEnd_476881 := by
    simpa [prefixWord, tailWord_476881, baseEnd_476881] using wordTrace_append hprefix tailTrace_476881
  have hstable : (prefixWord ++ tailWord_476881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476881).length < 2 ^ (prefixWord ++ tailWord_476881).sum := by decide
  have hdescent : baseEnd_476881 < baseStart_476881 := by decide
  rcases family_descends (prefixWord ++ tailWord_476881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476900 : List Nat := [2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_476900 : Nat := 118140960795 + 476900 * 2 ^ 59
def prefixEnd_476900 : Nat := 4983230072969 + 3 ^ 40 * 476900 * 2
def baseEnd_476900 : Nat := 145113436521060361633649

theorem tailTrace_476900 : CollatzResearch.WordTrace tailWord_476900 prefixEnd_476900 145113436521060361633649 := by
  unfold tailWord_476900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696985986140111440350077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11595981314853481920466769 8696985986140111440350077)
  ·
    refine ⟨3261369744802541790131279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8696985986140111440350077 3261369744802541790131279)
    ·
      refine ⟨4892054617203812685196919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261369744802541790131279 4892054617203812685196919)
      ·
        refine ⟨7338081925805719027795379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892054617203812685196919 7338081925805719027795379)
        ·
          refine ⟨11007122888708578541693069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338081925805719027795379 11007122888708578541693069)
          ·
            refine ⟨4127671083265716953134901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11007122888708578541693069 4127671083265716953134901)
            ·
              refine ⟨386969164056160964356397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4127671083265716953134901 386969164056160964356397)
              ·
                refine ⟨145113436521060361633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386969164056160964356397 145113436521060361633649)
                ·
                  rfl

theorem cell19_476900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_476900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476900 prefixEnd_476900 := by exact prefixLift 476900
  have htrace : WordTrace (prefixWord ++ tailWord_476900) baseStart_476900 baseEnd_476900 := by
    simpa [prefixWord, tailWord_476900, baseEnd_476900] using wordTrace_append hprefix tailTrace_476900
  have hstable : (prefixWord ++ tailWord_476900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476900).length < 2 ^ (prefixWord ++ tailWord_476900).sum := by decide
  have hdescent : baseEnd_476900 < baseStart_476900 := by decide
  rcases family_descends (prefixWord ++ tailWord_476900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476959 : List Nat := [1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_476959 : Nat := 118140960795 + 476959 * 2 ^ 59
def prefixEnd_476959 : Nat := 4983230072969 + 3 ^ 40 * 476959 * 2
def baseEnd_476959 : Nat := 145131389326165706322377

theorem tailTrace_476959 : CollatzResearch.WordTrace tailWord_476959 prefixEnd_476959 145131389326165706322377 := by
  unfold tailWord_476959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396123879066475957097931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597415919377650638065287 17396123879066475957097931)
  ·
    refine ⟨26094185818599713935646897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396123879066475957097931 26094185818599713935646897)
    ·
      refine ⟨19570639363949785451735173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26094185818599713935646897 19570639363949785451735173)
      ·
        refine ⟨3669494880740584772200345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19570639363949785451735173 3669494880740584772200345)
        ·
          refine ⟨2752121160555438579150259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669494880740584772200345 2752121160555438579150259)
          ·
            refine ⟨4128181740833157868725389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752121160555438579150259 4128181740833157868725389)
            ·
              refine ⟨1548068152812434200772021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128181740833157868725389 1548068152812434200772021)
              ·
                refine ⟨145131389326165706322377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1548068152812434200772021 145131389326165706322377)
                ·
                  rfl

theorem cell19_476959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_476959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476959 prefixEnd_476959 := by exact prefixLift 476959
  have htrace : WordTrace (prefixWord ++ tailWord_476959) baseStart_476959 baseEnd_476959 := by
    simpa [prefixWord, tailWord_476959, baseEnd_476959] using wordTrace_append hprefix tailTrace_476959
  have hstable : (prefixWord ++ tailWord_476959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476959).length < 2 ^ (prefixWord ++ tailWord_476959).sum := by decide
  have hdescent : baseEnd_476959 < baseStart_476959 := by decide
  rcases family_descends (prefixWord ++ tailWord_476959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476974 : List Nat := [4, 1, 3, 2, 2, 2, 5]
def baseStart_476974 : Nat := 118140960795 + 476974 * 2 ^ 59
def prefixEnd_476974 : Nat := 4983230072969 + 3 ^ 40 * 476974 * 2
def baseEnd_476974 : Nat := 48378651199550038663001

theorem tailTrace_476974 : CollatzResearch.WordTrace tailWord_476974 prefixEnd_476974 48378651199550038663001 := by
  unfold tailWord_476974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174583871751516689861747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11597780649341422345929317 2174583871751516689861747)
  ·
    refine ⟨3261875807627275034792621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174583871751516689861747 3261875807627275034792621)
    ·
      refine ⟨1223203427860228138047233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3261875807627275034792621 1223203427860228138047233)
      ·
        refine ⟨917402570895171103535425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223203427860228138047233 917402570895171103535425)
        ·
          refine ⟨688051928171378327651569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917402570895171103535425 688051928171378327651569)
          ·
            refine ⟨516038946128533745738677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688051928171378327651569 516038946128533745738677)
            ·
              refine ⟨48378651199550038663001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516038946128533745738677 48378651199550038663001)
              ·
                rfl

theorem cell19_476974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_476974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476974 prefixEnd_476974 := by exact prefixLift 476974
  have htrace : WordTrace (prefixWord ++ tailWord_476974) baseStart_476974 baseEnd_476974 := by
    simpa [prefixWord, tailWord_476974, baseEnd_476974] using wordTrace_append hprefix tailTrace_476974
  have hstable : (prefixWord ++ tailWord_476974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476974).length < 2 ^ (prefixWord ++ tailWord_476974).sum := by decide
  have hdescent : baseEnd_476974 < baseStart_476974 := by decide
  rcases family_descends (prefixWord ++ tailWord_476974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476978 : List Nat := [3, 2, 1, 1, 3, 2, 7]
def baseStart_476978 : Nat := 118140960795 + 476978 * 2 ^ 59
def prefixEnd_476978 : Nat := 4983230072969 + 3 ^ 40 * 476978 * 2
def baseEnd_476978 : Nat := 48379056912659763966701

theorem tailTrace_476978 : CollatzResearch.WordTrace tailWord_476978 prefixEnd_476978 48379056912659763966701 := by
  unfold tailWord_476978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349204216499410550509897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11597877910665094801359725 4349204216499410550509897)
  ·
    refine ⟨3261903162374557912882423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4349204216499410550509897 3261903162374557912882423)
    ·
      refine ⟨4892854743561836869323635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261903162374557912882423 4892854743561836869323635)
      ·
        refine ⟨7339282115342755303985453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892854743561836869323635 7339282115342755303985453)
        ·
          refine ⟨2752230793253533238994545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7339282115342755303985453 2752230793253533238994545)
          ·
            refine ⟨2064173094940149929245909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752230793253533238994545 2064173094940149929245909)
            ·
              refine ⟨48379056912659763966701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2064173094940149929245909 48379056912659763966701)
              ·
                rfl

theorem cell19_476978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_476978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476978 prefixEnd_476978 := by exact prefixLift 476978
  have htrace : WordTrace (prefixWord ++ tailWord_476978) baseStart_476978 baseEnd_476978 := by
    simpa [prefixWord, tailWord_476978, baseEnd_476978] using wordTrace_append hprefix tailTrace_476978
  have hstable : (prefixWord ++ tailWord_476978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476978).length < 2 ^ (prefixWord ++ tailWord_476978).sum := by decide
  have hdescent : baseEnd_476978 < baseStart_476978 := by decide
  rcases family_descends (prefixWord ++ tailWord_476978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476997 : List Nat := [1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_476997 : Nat := 118140960795 + 476997 * 2 ^ 59
def prefixEnd_476997 : Nat := 4983230072969 + 3 ^ 40 * 476997 * 2
def baseEnd_476997 : Nat := 145142952149792877477829

theorem tailTrace_476997 : CollatzResearch.WordTrace tailWord_476997 prefixEnd_476997 145142952149792877477829 := by
  unfold tailWord_476997
  simp only [CollatzResearch.WordTrace]
  refine ⟨17397509852928808446981245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11598339901952538964654163 17397509852928808446981245)
  ·
    refine ⟨6524066194848303167617967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17397509852928808446981245 6524066194848303167617967)
    ·
      refine ⟨9786099292272454751426951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6524066194848303167617967 9786099292272454751426951)
      ·
        refine ⟨14679148938408682127140427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9786099292272454751426951 14679148938408682127140427)
        ·
          refine ⟨22018723407613023190710641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679148938408682127140427 22018723407613023190710641)
          ·
            refine ⟨16514042555709767393032981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22018723407613023190710641 16514042555709767393032981)
            ·
              refine ⟨774095744798895346548421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16514042555709767393032981 774095744798895346548421)
              ·
                refine ⟨145142952149792877477829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774095744798895346548421 145142952149792877477829)
                ·
                  rfl

theorem cell19_476997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_476997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_476997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_476997 prefixEnd_476997 := by exact prefixLift 476997
  have htrace : WordTrace (prefixWord ++ tailWord_476997) baseStart_476997 baseEnd_476997 := by
    simpa [prefixWord, tailWord_476997, baseEnd_476997] using wordTrace_append hprefix tailTrace_476997
  have hstable : (prefixWord ++ tailWord_476997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476997).length < 2 ^ (prefixWord ++ tailWord_476997).sum := by decide
  have hdescent : baseEnd_476997 < baseStart_476997 := by decide
  rcases family_descends (prefixWord ++ tailWord_476997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477090 : List Nat := [3, 3, 1, 2, 3, 1, 6]
def baseStart_477090 : Nat := 118140960795 + 477090 * 2 ^ 59
def prefixEnd_477090 : Nat := 4983230072969 + 3 ^ 40 * 477090 * 2
def baseEnd_477090 : Nat := 48390416879732072470303

theorem tailTrace_477090 : CollatzResearch.WordTrace tailWord_477090 prefixEnd_477090 48390416879732072470303 := by
  unfold tailWord_477090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350225460397971332529181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11600601227727923553411149 4350225460397971332529181)
  ·
    refine ⟨1631334547649239249698443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4350225460397971332529181 1631334547649239249698443)
    ·
      refine ⟨2447001821473858874547665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1631334547649239249698443 2447001821473858874547665)
      ·
        refine ⟨1835251366105394155910749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447001821473858874547665 1835251366105394155910749)
        ·
          refine ⟨688219262289522808466531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835251366105394155910749 688219262289522808466531)
          ·
            refine ⟨1032328893434284212699797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688219262289522808466531 1032328893434284212699797)
            ·
              refine ⟨48390416879732072470303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1032328893434284212699797 48390416879732072470303)
              ·
                rfl

theorem cell19_477090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_477090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477090 prefixEnd_477090 := by exact prefixLift 477090
  have htrace : WordTrace (prefixWord ++ tailWord_477090) baseStart_477090 baseEnd_477090 := by
    simpa [prefixWord, tailWord_477090, baseEnd_477090] using wordTrace_append hprefix tailTrace_477090
  have hstable : (prefixWord ++ tailWord_477090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477090).length < 2 ^ (prefixWord ++ tailWord_477090).sum := by decide
  have hdescent : baseEnd_477090 < baseStart_477090 := by decide
  rcases family_descends (prefixWord ++ tailWord_477090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477092 : List Nat := [2, 3, 1, 2, 1, 4, 6]
def baseStart_477092 : Nat := 118140960795 + 477092 * 2 ^ 59
def prefixEnd_477092 : Nat := 4983230072969 + 3 ^ 40 * 477092 * 2
def baseEnd_477092 : Nat := 48390619736286935122153

theorem tailTrace_477092 : CollatzResearch.WordTrace tailWord_477092 prefixEnd_477092 48390619736286935122153 := by
  unfold tailWord_477092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700487393792319835844765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11600649858389759781126353 8700487393792319835844765)
  ·
    refine ⟨3262682772672119938441787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8700487393792319835844765 3262682772672119938441787)
    ·
      refine ⟨4894024159008179907662681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262682772672119938441787 4894024159008179907662681)
      ·
        refine ⟨3670518119256134930747011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894024159008179907662681 3670518119256134930747011)
        ·
          refine ⟨5505777178884202396120517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670518119256134930747011 5505777178884202396120517)
          ·
            refine ⟨1032333221040787949272597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5505777178884202396120517 1032333221040787949272597)
            ·
              refine ⟨48390619736286935122153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1032333221040787949272597 48390619736286935122153)
              ·
                rfl

theorem cell19_477092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_477092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477092 prefixEnd_477092 := by exact prefixLift 477092
  have htrace : WordTrace (prefixWord ++ tailWord_477092) baseStart_477092 baseEnd_477092 := by
    simpa [prefixWord, tailWord_477092, baseEnd_477092] using wordTrace_append hprefix tailTrace_477092
  have hstable : (prefixWord ++ tailWord_477092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477092).length < 2 ^ (prefixWord ++ tailWord_477092).sum := by decide
  have hdescent : baseEnd_477092 < baseStart_477092 := by decide
  rcases family_descends (prefixWord ++ tailWord_477092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477128 : List Nat := [2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_477128 : Nat := 118140960795 + 477128 * 2 ^ 59
def prefixEnd_477128 : Nat := 4983230072969 + 3 ^ 40 * 477128 * 2
def baseEnd_477128 : Nat := 145182813462823388566361

theorem tailTrace_477128 : CollatzResearch.WordTrace tailWord_477128 prefixEnd_477128 145182813462823388566361 := by
  unfold tailWord_477128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701143907727108910000019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11601525210302811880000025 8701143907727108910000019)
  ·
    refine ⟨13051715861590663365000029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701143907727108910000019 13051715861590663365000029)
    ·
      refine ⟨4894393448096498761875011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13051715861590663365000029 4894393448096498761875011)
      ·
        refine ⟨7341590172144748142812517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894393448096498761875011 7341590172144748142812517)
        ·
          refine ⟨1376548157277140276777347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7341590172144748142812517 1376548157277140276777347)
          ·
            refine ⟨2064822235915710415166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376548157277140276777347 2064822235915710415166021)
            ·
              refine ⟨387154169234195702843629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2064822235915710415166021 387154169234195702843629)
              ·
                refine ⟨145182813462823388566361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387154169234195702843629 145182813462823388566361)
                ·
                  rfl

theorem cell19_477128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_477128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477128 prefixEnd_477128 := by exact prefixLift 477128
  have htrace : WordTrace (prefixWord ++ tailWord_477128) baseStart_477128 baseEnd_477128 := by
    simpa [prefixWord, tailWord_477128, baseEnd_477128] using wordTrace_append hprefix tailTrace_477128
  have hstable : (prefixWord ++ tailWord_477128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477128).length < 2 ^ (prefixWord ++ tailWord_477128).sum := by decide
  have hdescent : baseEnd_477128 < baseStart_477128 := by decide
  rcases family_descends (prefixWord ++ tailWord_477128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477166 : List Nat := [4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_477166 : Nat := 118140960795 + 477166 * 2 ^ 59
def prefixEnd_477166 : Nat := 4983230072969 + 3 ^ 40 * 477166 * 2
def baseEnd_477166 : Nat := 145194376286450559721813

theorem tailTrace_477166 : CollatzResearch.WordTrace tailWord_477166 prefixEnd_477166 145194376286450559721813 := by
  unfold tailWord_477166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175459223664568788735419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11602449192877700206588901 2175459223664568788735419)
  ·
    refine ⟨3263188835496853183103129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2175459223664568788735419 3263188835496853183103129)
    ·
      refine ⟨2447391626622639887327347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263188835496853183103129 2447391626622639887327347)
      ·
        refine ⟨3671087439933959830991021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447391626622639887327347 3671087439933959830991021)
        ·
          refine ⟨1376657789975234936621633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3671087439933959830991021 1376657789975234936621633)
          ·
            refine ⟨1032493342481426202466225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376657789975234936621633 1032493342481426202466225)
            ·
              refine ⟨774370006861069651849669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032493342481426202466225 774370006861069651849669)
              ·
                refine ⟨145194376286450559721813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774370006861069651849669 145194376286450559721813)
                ·
                  rfl

theorem cell19_477166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_477166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477166 prefixEnd_477166 := by exact prefixLift 477166
  have htrace : WordTrace (prefixWord ++ tailWord_477166) baseStart_477166 baseEnd_477166 := by
    simpa [prefixWord, tailWord_477166, baseEnd_477166] using wordTrace_append hprefix tailTrace_477166
  have hstable : (prefixWord ++ tailWord_477166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477166).length < 2 ^ (prefixWord ++ tailWord_477166).sum := by decide
  have hdescent : baseEnd_477166 < baseStart_477166 := by decide
  rcases family_descends (prefixWord ++ tailWord_477166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477204 : List Nat := [2, 4, 3, 2, 8]
def baseStart_477204 : Nat := 118140960795 + 477204 * 2 ^ 59
def prefixEnd_477204 : Nat := 4983230072969 + 3 ^ 40 * 477204 * 2
def baseEnd_477204 : Nat := 5377997744817693736195

theorem tailTrace_477204 : CollatzResearch.WordTrace tailWord_477204 prefixEnd_477204 5377997744817693736195 := by
  unfold tailWord_477204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702529881589441399883333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11603373175452588533177777 8702529881589441399883333)
  ·
    refine ⟨1631724352798020262478125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8702529881589441399883333 1631724352798020262478125)
    ·
      refine ⟨611896632299257598429297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1631724352798020262478125 611896632299257598429297)
      ·
        refine ⟨458922474224443198821973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611896632299257598429297 458922474224443198821973)
        ·
          refine ⟨5377997744817693736195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 458922474224443198821973 5377997744817693736195)
          ·
            rfl

theorem cell19_477204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_477204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477204 prefixEnd_477204 := by exact prefixLift 477204
  have htrace : WordTrace (prefixWord ++ tailWord_477204) baseStart_477204 baseEnd_477204 := by
    simpa [prefixWord, tailWord_477204, baseEnd_477204] using wordTrace_append hprefix tailTrace_477204
  have hstable : (prefixWord ++ tailWord_477204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477204).length < 2 ^ (prefixWord ++ tailWord_477204).sum := by decide
  have hdescent : baseEnd_477204 < baseStart_477204 := by decide
  rcases family_descends (prefixWord ++ tailWord_477204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477227 : List Nat := [1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_477227 : Nat := 118140960795 + 477227 * 2 ^ 59
def prefixEnd_477227 : Nat := 4983230072969 + 3 ^ 40 * 477227 * 2
def baseEnd_477227 : Nat := 145212937661220492366091

theorem tailTrace_477227 : CollatzResearch.WordTrace tailWord_477227 prefixEnd_477227 145212937661220492366091 := by
  unfold tailWord_477227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405898642095557727853935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11603932428063705151902623 17405898642095557727853935)
  ·
    refine ⟨26108847963143336591780903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17405898642095557727853935 26108847963143336591780903)
    ·
      refine ⟨39163271944715004887671355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26108847963143336591780903 39163271944715004887671355)
      ·
        refine ⟨58744907917072507331507033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39163271944715004887671355 58744907917072507331507033)
        ·
          refine ⟨44058680937804380498630275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58744907917072507331507033 44058680937804380498630275)
          ·
            refine ⟨66088021406706570747945413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44058680937804380498630275 66088021406706570747945413)
            ·
              refine ⟨12391504013757482015239765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66088021406706570747945413 12391504013757482015239765)
              ·
                refine ⟨145212937661220492366091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12391504013757482015239765 145212937661220492366091)
                ·
                  rfl

theorem cell19_477227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_477227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477227 prefixEnd_477227 := by exact prefixLift 477227
  have htrace : WordTrace (prefixWord ++ tailWord_477227) baseStart_477227 baseEnd_477227 := by
    simpa [prefixWord, tailWord_477227, baseEnd_477227] using wordTrace_append hprefix tailTrace_477227
  have hstable : (prefixWord ++ tailWord_477227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477227).length < 2 ^ (prefixWord ++ tailWord_477227).sum := by decide
  have hdescent : baseEnd_477227 < baseStart_477227 := by decide
  rcases family_descends (prefixWord ++ tailWord_477227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477320 : List Nat := [2, 1, 3, 4, 1, 1, 7]
def baseStart_477320 : Nat := 118140960795 + 477320 * 2 ^ 59
def prefixEnd_477320 : Nat := 4983230072969 + 3 ^ 40 * 477320 * 2
def baseEnd_477320 : Nat := 48413745383541277433057

theorem tailTrace_477320 : CollatzResearch.WordTrace tailWord_477320 prefixEnd_477320 48413745383541277433057 := by
  unfold tailWord_477320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704645315379317305494707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11606193753839089740659609 8704645315379317305494707)
  ·
    refine ⟨13056967973068975958242061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8704645315379317305494707 13056967973068975958242061)
    ·
      refine ⟨4896362989900865984340773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13056967973068975958242061 4896362989900865984340773)
      ·
        refine ⟨918068060606412372063895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4896362989900865984340773 918068060606412372063895)
        ·
          refine ⟨1377102090909618558095843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918068060606412372063895 1377102090909618558095843)
          ·
            refine ⟨2065653136364427837143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377102090909618558095843 2065653136364427837143765)
            ·
              refine ⟨48413745383541277433057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2065653136364427837143765 48413745383541277433057)
              ·
                rfl

theorem cell19_477320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_477320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477320 prefixEnd_477320 := by exact prefixLift 477320
  have htrace : WordTrace (prefixWord ++ tailWord_477320) baseStart_477320 baseEnd_477320 := by
    simpa [prefixWord, tailWord_477320, baseEnd_477320] using wordTrace_append hprefix tailTrace_477320
  have hstable : (prefixWord ++ tailWord_477320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477320).length < 2 ^ (prefixWord ++ tailWord_477320).sum := by decide
  have hdescent : baseEnd_477320 < baseStart_477320 := by decide
  rcases family_descends (prefixWord ++ tailWord_477320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477377 : List Nat := [1, 2, 6, 1, 9]
def baseStart_477377 : Nat := 118140960795 + 477377 * 2 ^ 59
def prefixEnd_477377 : Nat := 4983230072969 + 3 ^ 40 * 477377 * 2
def baseEnd_477377 : Nat := 5379947421706095890087

theorem tailTrace_477377 : CollatzResearch.WordTrace tailWord_477377 prefixEnd_477377 5379947421706095890087 := by
  unfold tailWord_477377
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411369591552133345814385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11607579727701422230542923 17411369591552133345814385)
  ·
    refine ⟨13058527193664100009360789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17411369591552133345814385 13058527193664100009360789)
    ·
      refine ⟨612118462203004687938787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13058527193664100009360789 612118462203004687938787)
      ·
        refine ⟨918177693304507031908181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612118462203004687938787 918177693304507031908181)
        ·
          refine ⟨5379947421706095890087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 918177693304507031908181 5379947421706095890087)
          ·
            rfl

theorem cell19_477377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_477377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477377 prefixEnd_477377 := by exact prefixLift 477377
  have htrace : WordTrace (prefixWord ++ tailWord_477377) baseStart_477377 baseEnd_477377 := by
    simpa [prefixWord, tailWord_477377, baseEnd_477377] using wordTrace_append hprefix tailTrace_477377
  have hstable : (prefixWord ++ tailWord_477377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477377).length < 2 ^ (prefixWord ++ tailWord_477377).sum := by decide
  have hdescent : baseEnd_477377 < baseStart_477377 := by decide
  rcases family_descends (prefixWord ++ tailWord_477377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477394 : List Nat := [3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_477394 : Nat := 118140960795 + 477394 * 2 ^ 59
def prefixEnd_477394 : Nat := 4983230072969 + 3 ^ 40 * 477394 * 2
def baseEnd_477394 : Nat := 145263753228213586654525

theorem tailTrace_477394 : CollatzResearch.WordTrace tailWord_477394 prefixEnd_477394 145263753228213586654525 := by
  unfold tailWord_477394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352997408122636312295809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11607993088327030166122157 4352997408122636312295809)
  ·
    refine ⟨3264748056091977234221857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4352997408122636312295809 3264748056091977234221857)
    ·
      refine ⟨2448561042068982925666393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3264748056091977234221857 2448561042068982925666393)
      ·
        refine ⟨1836420781551737194249795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448561042068982925666393 1836420781551737194249795)
        ·
          refine ⟨2754631172327605791374693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836420781551737194249795 2754631172327605791374693)
          ·
            refine ⟨516493344811426085882755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2754631172327605791374693 516493344811426085882755)
            ·
              refine ⟨774740017217139128824133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516493344811426085882755 774740017217139128824133)
              ·
                refine ⟨145263753228213586654525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774740017217139128824133 145263753228213586654525)
                ·
                  rfl

theorem cell19_477394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_477394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477394 prefixEnd_477394 := by exact prefixLift 477394
  have htrace : WordTrace (prefixWord ++ tailWord_477394) baseStart_477394 baseEnd_477394 := by
    simpa [prefixWord, tailWord_477394, baseEnd_477394] using wordTrace_append hprefix tailTrace_477394
  have hstable : (prefixWord ++ tailWord_477394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477394).length < 2 ^ (prefixWord ++ tailWord_477394).sum := by decide
  have hdescent : baseEnd_477394 < baseStart_477394 := by decide
  rcases family_descends (prefixWord ++ tailWord_477394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477411 : List Nat := [1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_477411 : Nat := 118140960795 + 477411 * 2 ^ 59
def prefixEnd_477411 : Nat := 4983230072969 + 3 ^ 40 * 477411 * 2
def baseEnd_477411 : Nat := 145268926070362584276701

theorem tailTrace_477411 : CollatzResearch.WordTrace tailWord_477411 prefixEnd_477411 145268926070362584276701 := by
  unfold tailWord_477411
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412609673428957152552087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11608406448952638101701391 17412609673428957152552087)
  ·
    refine ⟨26118914510143435728828131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412609673428957152552087 26118914510143435728828131)
    ·
      refine ⟨39178371765215153593242197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118914510143435728828131 39178371765215153593242197)
      ·
        refine ⟨459121544123615081170807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 39178371765215153593242197 459121544123615081170807)
        ·
          refine ⟨688682316185422621756211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459121544123615081170807 688682316185422621756211)
          ·
            refine ⟨1033023474278133932634317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688682316185422621756211 1033023474278133932634317)
            ·
              refine ⟨387383802854300224737869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033023474278133932634317 387383802854300224737869)
              ·
                refine ⟨145268926070362584276701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387383802854300224737869 145268926070362584276701)
                ·
                  rfl

theorem cell19_477411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_477411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477411 prefixEnd_477411 := by exact prefixLift 477411
  have htrace : WordTrace (prefixWord ++ tailWord_477411) baseStart_477411 baseEnd_477411 := by
    simpa [prefixWord, tailWord_477411, baseEnd_477411] using wordTrace_append hprefix tailTrace_477411
  have hstable : (prefixWord ++ tailWord_477411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477411).length < 2 ^ (prefixWord ++ tailWord_477411).sum := by decide
  have hdescent : baseEnd_477411 < baseStart_477411 := by decide
  rcases family_descends (prefixWord ++ tailWord_477411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477413 : List Nat := [1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_477413 : Nat := 118140960795 + 477413 * 2 ^ 59
def prefixEnd_477413 : Nat := 4983230072969 + 3 ^ 40 * 477413 * 2
def baseEnd_477413 : Nat := 145269534640027172232251

theorem tailTrace_477413 : CollatzResearch.WordTrace tailWord_477413 prefixEnd_477413 145269534640027172232251 := by
  unfold tailWord_477413
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412682619421711494124893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11608455079614474329416595 17412682619421711494124893)
  ·
    refine ⟨6529755982283141810296835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17412682619421711494124893 6529755982283141810296835)
    ·
      refine ⟨9794633973424712715445253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529755982283141810296835 9794633973424712715445253)
      ·
        refine ⟨1836493870017133634145985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9794633973424712715445253 1836493870017133634145985)
        ·
          refine ⟨1377370402512850225609489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836493870017133634145985 1377370402512850225609489)
          ·
            refine ⟨1033027801884637669207117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377370402512850225609489 1033027801884637669207117)
            ·
              refine ⟨387385425706739125952669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033027801884637669207117 387385425706739125952669)
              ·
                refine ⟨145269534640027172232251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387385425706739125952669 145269534640027172232251)
                ·
                  rfl

theorem cell19_477413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_477413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477413 prefixEnd_477413 := by exact prefixLift 477413
  have htrace : WordTrace (prefixWord ++ tailWord_477413) baseStart_477413 baseEnd_477413 := by
    simpa [prefixWord, tailWord_477413, baseEnd_477413] using wordTrace_append hprefix tailTrace_477413
  have hstable : (prefixWord ++ tailWord_477413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477413).length < 2 ^ (prefixWord ++ tailWord_477413).sum := by decide
  have hdescent : baseEnd_477413 < baseStart_477413 := by decide
  rcases family_descends (prefixWord ++ tailWord_477413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477472 : List Nat := [2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_477472 : Nat := 118140960795 + 477472 * 2 ^ 59
def prefixEnd_477472 : Nat := 4983230072969 + 3 ^ 40 * 477472 * 2
def baseEnd_477472 : Nat := 145287487445132516920979

theorem tailTrace_477472 : CollatzResearch.WordTrace tailWord_477472 prefixEnd_477472 145287487445132516920979 := by
  unfold tailWord_477472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707417263103982285261335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11609889684138643047015113 8707417263103982285261335)
  ·
    refine ⟨13061125894655973427892003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8707417263103982285261335 13061125894655973427892003)
    ·
      refine ⟨19591688841983960141838005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061125894655973427892003 19591688841983960141838005)
      ·
        refine ⟨1836720828935996263297313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19591688841983960141838005 1836720828935996263297313)
        ·
          refine ⟨1377540621701997197472985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836720828935996263297313 1377540621701997197472985)
          ·
            refine ⟨1033155466276497898104739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377540621701997197472985 1033155466276497898104739)
            ·
              refine ⟨1549733199414746847157109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033155466276497898104739 1549733199414746847157109)
              ·
                refine ⟨145287487445132516920979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1549733199414746847157109 145287487445132516920979)
                ·
                  rfl

theorem cell19_477472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_477472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477472 prefixEnd_477472 := by exact prefixLift 477472
  have htrace : WordTrace (prefixWord ++ tailWord_477472) baseStart_477472 baseEnd_477472 := by
    simpa [prefixWord, tailWord_477472, baseEnd_477472] using wordTrace_append hprefix tailTrace_477472
  have hstable : (prefixWord ++ tailWord_477472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477472).length < 2 ^ (prefixWord ++ tailWord_477472).sum := by decide
  have hdescent : baseEnd_477472 < baseStart_477472 := by decide
  rcases family_descends (prefixWord ++ tailWord_477472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477489 : List Nat := [1, 2, 2, 3, 5, 1, 5]
def baseStart_477489 : Nat := 118140960795 + 477489 * 2 ^ 59
def prefixEnd_477489 : Nat := 4983230072969 + 3 ^ 40 * 477489 * 2
def baseEnd_477489 : Nat := 48430886762427171514385

theorem tailTrace_477489 : CollatzResearch.WordTrace tailWord_477489 prefixEnd_477489 48430886762427171514385 := by
  unfold tailWord_477489
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415454567146376473891521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11610303044764250982594347 17415454567146376473891521)
  ·
    refine ⟨13061590925359782355418641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17415454567146376473891521 13061590925359782355418641)
    ·
      refine ⟨9796193194019836766563981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13061590925359782355418641 9796193194019836766563981)
      ·
        refine ⟨3673572447757438787461493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9796193194019836766563981 3673572447757438787461493)
        ·
          refine ⟨344397416977259886324515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3673572447757438787461493 344397416977259886324515)
          ·
            refine ⟨516596125465889829486773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344397416977259886324515 516596125465889829486773)
            ·
              refine ⟨48430886762427171514385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516596125465889829486773 48430886762427171514385)
              ·
                rfl

theorem cell19_477489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_477489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477489 prefixEnd_477489 := by exact prefixLift 477489
  have htrace : WordTrace (prefixWord ++ tailWord_477489) baseStart_477489 baseEnd_477489 := by
    simpa [prefixWord, tailWord_477489, baseEnd_477489] using wordTrace_append hprefix tailTrace_477489
  have hstable : (prefixWord ++ tailWord_477489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477489).length < 2 ^ (prefixWord ++ tailWord_477489).sum := by decide
  have hdescent : baseEnd_477489 < baseStart_477489 := by decide
  rcases family_descends (prefixWord ++ tailWord_477489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477512 : List Nat := [2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_477512 : Nat := 118140960795 + 477512 * 2 ^ 59
def prefixEnd_477512 : Nat := 4983230072969 + 3 ^ 40 * 477512 * 2
def baseEnd_477512 : Nat := 145299658838424276031981

theorem tailTrace_477512 : CollatzResearch.WordTrace tailWord_477512 prefixEnd_477512 145299658838424276031981 := by
  unfold tailWord_477512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708146723031525700989395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11610862297375367601319193 8708146723031525700989395)
  ·
    refine ⟨13062220084547288551484093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8708146723031525700989395 13062220084547288551484093)
    ·
      refine ⟨4898332531705233206806535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13062220084547288551484093 4898332531705233206806535)
      ·
        refine ⟨7347498797557849810209803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898332531705233206806535 7347498797557849810209803)
        ·
          refine ⟨11021248196336774715314705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347498797557849810209803 11021248196336774715314705)
          ·
            refine ⟨8265936147252581036486029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021248196336774715314705 8265936147252581036486029)
            ·
              refine ⟨3099726055219717888682261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8265936147252581036486029 3099726055219717888682261)
              ·
                refine ⟨145299658838424276031981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3099726055219717888682261 145299658838424276031981)
                ·
                  rfl

theorem cell19_477512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_477512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477512 prefixEnd_477512 := by exact prefixLift 477512
  have htrace : WordTrace (prefixWord ++ tailWord_477512) baseStart_477512 baseEnd_477512 := by
    simpa [prefixWord, tailWord_477512, baseEnd_477512] using wordTrace_append hprefix tailTrace_477512
  have hstable : (prefixWord ++ tailWord_477512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477512).length < 2 ^ (prefixWord ++ tailWord_477512).sum := by decide
  have hdescent : baseEnd_477512 < baseStart_477512 := by decide
  rcases family_descends (prefixWord ++ tailWord_477512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477548 : List Nat := [2, 2, 1, 1, 7, 6]
def baseStart_477548 : Nat := 118140960795 + 477548 * 2 ^ 59
def prefixEnd_477548 : Nat := 4983230072969 + 3 ^ 40 * 477548 * 2
def baseEnd_477548 : Nat := 16145623676931873247987

theorem tailTrace_477548 : CollatzResearch.WordTrace tailWord_477548 prefixEnd_477548 16145623676931873247987 := by
  unfold tailWord_477548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708803236966314775144649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11611737649288419700192865 8708803236966314775144649)
  ·
    refine ⟨6531602427724736081358487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8708803236966314775144649 6531602427724736081358487)
    ·
      refine ⟨9797403641587104122037731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531602427724736081358487 9797403641587104122037731)
      ·
        refine ⟨14696105462380656183056597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9797403641587104122037731 14696105462380656183056597)
        ·
          refine ⟨344439971774546629290389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14696105462380656183056597 344439971774546629290389)
          ·
            refine ⟨16145623676931873247987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 344439971774546629290389 16145623676931873247987)
            ·
              rfl

theorem cell19_477548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_477548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477548 prefixEnd_477548 := by exact prefixLift 477548
  have htrace : WordTrace (prefixWord ++ tailWord_477548) baseStart_477548 baseEnd_477548 := by
    simpa [prefixWord, tailWord_477548, baseEnd_477548] using wordTrace_append hprefix tailTrace_477548
  have hstable : (prefixWord ++ tailWord_477548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477548).length < 2 ^ (prefixWord ++ tailWord_477548).sum := by decide
  have hdescent : baseEnd_477548 < baseStart_477548 := by decide
  rcases family_descends (prefixWord ++ tailWord_477548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477550 : List Nat := [4, 1, 2, 12]
def baseStart_477550 : Nat := 118140960795 + 477550 * 2 ^ 59
def prefixEnd_477550 : Nat := 4983230072969 + 3 ^ 40 * 477550 * 2
def baseEnd_477550 : Nat := 1793965699531499347993

theorem tailTrace_477550 : CollatzResearch.WordTrace tailWord_477550 prefixEnd_477550 1793965699531499347993 := by
  unfold tailWord_477550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177209927490672986482763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11611786279950255927908069 2177209927490672986482763)
  ·
    refine ⟨3265814891236009479724145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177209927490672986482763 3265814891236009479724145)
    ·
      refine ⟨2449361168427007109793109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265814891236009479724145 2449361168427007109793109)
      ·
        refine ⟨1793965699531499347993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2449361168427007109793109 1793965699531499347993)
        ·
          rfl

theorem cell19_477550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 12].length) (baseStart_477550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477550 prefixEnd_477550 := by exact prefixLift 477550
  have htrace : WordTrace (prefixWord ++ tailWord_477550) baseStart_477550 baseEnd_477550 := by
    simpa [prefixWord, tailWord_477550, baseEnd_477550] using wordTrace_append hprefix tailTrace_477550
  have hstable : (prefixWord ++ tailWord_477550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477550).length < 2 ^ (prefixWord ++ tailWord_477550).sum := by decide
  have hdescent : baseEnd_477550 < baseStart_477550 := by decide
  rcases family_descends (prefixWord ++ tailWord_477550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477683 : List Nat := [1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_477683 : Nat := 118140960795 + 477683 * 2 ^ 59
def prefixEnd_477683 : Nat := 4983230072969 + 3 ^ 40 * 477683 * 2
def baseEnd_477683 : Nat := 145351691544746546231515

theorem tailTrace_477683 : CollatzResearch.WordTrace tailWord_477683 prefixEnd_477683 145351691544746546231515 := by
  unfold tailWord_477683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422530328443547606453703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11615020218962365070969135 17422530328443547606453703)
  ·
    refine ⟨26133795492665321409680555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17422530328443547606453703 26133795492665321409680555)
    ·
      refine ⟨39200693238997982114520833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26133795492665321409680555 39200693238997982114520833)
      ·
        refine ⟨29400519929248486585890625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39200693238997982114520833 29400519929248486585890625)
        ·
          refine ⟨22050389946936364939417969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29400519929248486585890625 22050389946936364939417969)
          ·
            refine ⟨16537792460202273704563477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22050389946936364939417969 16537792460202273704563477)
            ·
              refine ⟨775209021571981579901413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16537792460202273704563477 775209021571981579901413)
              ·
                refine ⟨145351691544746546231515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775209021571981579901413 145351691544746546231515)
                ·
                  rfl

theorem cell19_477683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_477683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477683 prefixEnd_477683 := by exact prefixLift 477683
  have htrace : WordTrace (prefixWord ++ tailWord_477683) baseStart_477683 baseEnd_477683 := by
    simpa [prefixWord, tailWord_477683, baseEnd_477683] using wordTrace_append hprefix tailTrace_477683
  have hstable : (prefixWord ++ tailWord_477683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477683).length < 2 ^ (prefixWord ++ tailWord_477683).sum := by decide
  have hdescent : baseEnd_477683 < baseStart_477683 := by decide
  rcases family_descends (prefixWord ++ tailWord_477683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477700 : List Nat := [2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_477700 : Nat := 118140960795 + 477700 * 2 ^ 59
def prefixEnd_477700 : Nat := 4983230072969 + 3 ^ 40 * 477700 * 2
def baseEnd_477700 : Nat := 145356864386895543853691

theorem tailTrace_477700 : CollatzResearch.WordTrace tailWord_477700 prefixEnd_477700 145356864386895543853691 := by
  unfold tailWord_477700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711575184690979754911277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11615433579587973006548369 8711575184690979754911277)
  ·
    refine ⟨3266840694259117408091729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8711575184690979754911277 3266840694259117408091729)
    ·
      refine ⟨2450130520694338056068797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3266840694259117408091729 2450130520694338056068797)
      ·
        refine ⟨918798945260376771025799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2450130520694338056068797 918798945260376771025799)
        ·
          refine ⟨1378198417890565156538699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918798945260376771025799 1378198417890565156538699)
          ·
            refine ⟨2067297626835847734808049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378198417890565156538699 2067297626835847734808049)
            ·
              refine ⟨1550473220126885801106037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067297626835847734808049 1550473220126885801106037)
              ·
                refine ⟨145356864386895543853691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1550473220126885801106037 145356864386895543853691)
                ·
                  rfl

theorem cell19_477700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_477700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477700 prefixEnd_477700 := by exact prefixLift 477700
  have htrace : WordTrace (prefixWord ++ tailWord_477700) baseStart_477700 baseEnd_477700 := by
    simpa [prefixWord, tailWord_477700, baseEnd_477700] using wordTrace_append hprefix tailTrace_477700
  have hstable : (prefixWord ++ tailWord_477700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477700).length < 2 ^ (prefixWord ++ tailWord_477700).sum := by decide
  have hdescent : baseEnd_477700 < baseStart_477700 := by decide
  rcases family_descends (prefixWord ++ tailWord_477700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477719 : List Nat := [1, 1, 3, 6, 1, 7]
def baseStart_477719 : Nat := 118140960795 + 477719 * 2 ^ 59
def prefixEnd_477719 : Nat := 4983230072969 + 3 ^ 40 * 477719 * 2
def baseEnd_477719 : Nat := 16151405088745458825713

theorem tailTrace_477719 : CollatzResearch.WordTrace tailWord_477719 prefixEnd_477719 16151405088745458825713 := by
  unfold tailWord_477719
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423843356313125754764211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11615895570875417169842807 17423843356313125754764211)
  ·
    refine ⟨26135765034469688632146317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17423843356313125754764211 26135765034469688632146317)
    ·
      refine ⟨9800911887926133237054869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26135765034469688632146317 9800911887926133237054869)
      ·
        refine ⟨459417744746537495486947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9800911887926133237054869 459417744746537495486947)
        ·
          refine ⟨689126617119806243230421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459417744746537495486947 689126617119806243230421)
          ·
            refine ⟨16151405088745458825713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 689126617119806243230421 16151405088745458825713)
            ·
              rfl

theorem cell19_477719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_477719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477719 prefixEnd_477719 := by exact prefixLift 477719
  have htrace : WordTrace (prefixWord ++ tailWord_477719) baseStart_477719 baseEnd_477719 := by
    simpa [prefixWord, tailWord_477719, baseEnd_477719] using wordTrace_append hprefix tailTrace_477719
  have hstable : (prefixWord ++ tailWord_477719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477719).length < 2 ^ (prefixWord ++ tailWord_477719).sum := by decide
  have hdescent : baseEnd_477719 < baseStart_477719 := by decide
  rcases family_descends (prefixWord ++ tailWord_477719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477736 : List Nat := [2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_477736 : Nat := 118140960795 + 477736 * 2 ^ 59
def prefixEnd_477736 : Nat := 4983230072969 + 3 ^ 40 * 477736 * 2
def baseEnd_477736 : Nat := 145367818640858127053593

theorem tailTrace_477736 : CollatzResearch.WordTrace tailWord_477736 prefixEnd_477736 145367818640858127053593 := by
  unfold tailWord_477736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712231698625768829066531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616308931501025105422041 8712231698625768829066531)
  ·
    refine ⟨13068347547938653243599797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712231698625768829066531 13068347547938653243599797)
    ·
      refine ⟨1225157582619248741587481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13068347547938653243599797 1225157582619248741587481)
      ·
        refine ⟨918868186964436556190611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225157582619248741587481 918868186964436556190611)
        ·
          refine ⟨1378302280446654834285917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918868186964436556190611 1378302280446654834285917)
          ·
            refine ⟨516863355167495562857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1378302280446654834285917 516863355167495562857219)
            ·
              refine ⟨775295032751243344285829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516863355167495562857219 775295032751243344285829)
              ·
                refine ⟨145367818640858127053593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775295032751243344285829 145367818640858127053593)
                ·
                  rfl

theorem cell19_477736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_477736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477736 prefixEnd_477736 := by exact prefixLift 477736
  have htrace : WordTrace (prefixWord ++ tailWord_477736) baseStart_477736 baseEnd_477736 := by
    simpa [prefixWord, tailWord_477736, baseEnd_477736] using wordTrace_append hprefix tailTrace_477736
  have hstable : (prefixWord ++ tailWord_477736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477736).length < 2 ^ (prefixWord ++ tailWord_477736).sum := by decide
  have hdescent : baseEnd_477736 < baseStart_477736 := by decide
  rcases family_descends (prefixWord ++ tailWord_477736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477738 : List Nat := [3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_477738 : Nat := 118140960795 + 477738 * 2 ^ 59
def prefixEnd_477738 : Nat := 4983230072969 + 3 ^ 40 * 477738 * 2
def baseEnd_477738 : Nat := 145368427210522715009143

theorem tailTrace_477738 : CollatzResearch.WordTrace tailWord_477738 prefixEnd_477738 145368427210522715009143 := by
  unfold tailWord_477738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356134085811072999926467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11616357562162861333137245 4356134085811072999926467)
  ·
    refine ⟨6534201128716609499889701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4356134085811072999926467 6534201128716609499889701)
    ·
      refine ⟨1225162711634364281229319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6534201128716609499889701 1225162711634364281229319)
      ·
        refine ⟨1837744067451546421843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225162711634364281229319 1837744067451546421843979)
        ·
          refine ⟨2756616101177319632765969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837744067451546421843979 2756616101177319632765969)
          ·
            refine ⟨2067462075882989724574477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756616101177319632765969 2067462075882989724574477)
            ·
              refine ⟨775298278456121146715429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067462075882989724574477 775298278456121146715429)
              ·
                refine ⟨145368427210522715009143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775298278456121146715429 145368427210522715009143)
                ·
                  rfl

theorem cell19_477738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_477738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477738 prefixEnd_477738 := by exact prefixLift 477738
  have htrace : WordTrace (prefixWord ++ tailWord_477738) baseStart_477738 baseEnd_477738 := by
    simpa [prefixWord, tailWord_477738, baseEnd_477738] using wordTrace_append hprefix tailTrace_477738
  have hstable : (prefixWord ++ tailWord_477738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477738).length < 2 ^ (prefixWord ++ tailWord_477738).sum := by decide
  have hdescent : baseEnd_477738 < baseStart_477738 := by decide
  rcases family_descends (prefixWord ++ tailWord_477738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477778 : List Nat := [3, 2, 2, 1, 2, 1, 8]
def baseStart_477778 : Nat := 118140960795 + 477778 * 2 ^ 59
def prefixEnd_477778 : Nat := 4983230072969 + 3 ^ 40 * 477778 * 2
def baseEnd_477778 : Nat := 48460199534604824706715

theorem tailTrace_477778 : CollatzResearch.WordTrace tailWord_477778 prefixEnd_477778 48460199534604824706715 := by
  unfold tailWord_477778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356498815774844707790497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11617330175399585887441325 4356498815774844707790497)
  ·
    refine ⟨3267374111831133530842873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4356498815774844707790497 3267374111831133530842873)
    ·
      refine ⟨2450530583873350148132155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3267374111831133530842873 2450530583873350148132155)
      ·
        refine ⟨3675795875810025222198233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450530583873350148132155 3675795875810025222198233)
        ·
          refine ⟨2756846906857518916648675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675795875810025222198233 2756846906857518916648675)
          ·
            refine ⟨4135270360286278374973013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756846906857518916648675 4135270360286278374973013)
            ·
              refine ⟨48460199534604824706715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4135270360286278374973013 48460199534604824706715)
              ·
                rfl

theorem cell19_477778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_477778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477778 prefixEnd_477778 := by exact prefixLift 477778
  have htrace : WordTrace (prefixWord ++ tailWord_477778) baseStart_477778 baseEnd_477778 := by
    simpa [prefixWord, tailWord_477778, baseEnd_477778] using wordTrace_append hprefix tailTrace_477778
  have hstable : (prefixWord ++ tailWord_477778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477778).length < 2 ^ (prefixWord ++ tailWord_477778).sum := by decide
  have hdescent : baseEnd_477778 < baseStart_477778 := by decide
  rcases family_descends (prefixWord ++ tailWord_477778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477810 : List Nat := [3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_477810 : Nat := 118140960795 + 477810 * 2 ^ 59
def prefixEnd_477810 : Nat := 4983230072969 + 3 ^ 40 * 477810 * 2
def baseEnd_477810 : Nat := 145390335718447881408947

theorem tailTrace_477810 : CollatzResearch.WordTrace tailWord_477810 prefixEnd_477810 145390335718447881408947 := by
  unfold tailWord_477810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356790599745862074081721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11618108265988965530884589 4356790599745862074081721)
  ·
    refine ⟨3267592949809396555561291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4356790599745862074081721 3267592949809396555561291)
    ·
      refine ⟨4901389424714094833341937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267592949809396555561291 4901389424714094833341937)
      ·
        refine ⟨3676042068535571125006453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4901389424714094833341937 3676042068535571125006453)
        ·
          refine ⟨344628943925209792969355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3676042068535571125006453 344628943925209792969355)
          ·
            refine ⟨516943415887814689454033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344628943925209792969355 516943415887814689454033)
            ·
              refine ⟨387707561915861017090525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516943415887814689454033 387707561915861017090525)
              ·
                refine ⟨145390335718447881408947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387707561915861017090525 145390335718447881408947)
                ·
                  rfl

theorem cell19_477810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_477810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477810 prefixEnd_477810 := by exact prefixLift 477810
  have htrace : WordTrace (prefixWord ++ tailWord_477810) baseStart_477810 baseEnd_477810 := by
    simpa [prefixWord, tailWord_477810, baseEnd_477810] using wordTrace_append hprefix tailTrace_477810
  have hstable : (prefixWord ++ tailWord_477810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477810).length < 2 ^ (prefixWord ++ tailWord_477810).sum := by decide
  have hdescent : baseEnd_477810 < baseStart_477810 := by decide
  rcases family_descends (prefixWord ++ tailWord_477810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477850 : List Nat := [3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_477850 : Nat := 118140960795 + 477850 * 2 ^ 59
def prefixEnd_477850 : Nat := 4983230072969 + 3 ^ 40 * 477850 * 2
def baseEnd_477850 : Nat := 145402507111739640519949

theorem tailTrace_477850 : CollatzResearch.WordTrace tailWord_477850 prefixEnd_477850 145402507111739640519949 := by
  unfold tailWord_477850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357155329709633781945751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11619080879225690085188669 4357155329709633781945751)
  ·
    refine ⟨6535732994564450672918627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4357155329709633781945751 6535732994564450672918627)
    ·
      refine ⟨9803599491846676009377941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6535732994564450672918627 9803599491846676009377941)
      ·
        refine ⟨459543726180312937939591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9803599491846676009377941 459543726180312937939591)
        ·
          refine ⟨689315589270469406909387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459543726180312937939591 689315589270469406909387)
          ·
            refine ⟨1033973383905704110364081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689315589270469406909387 1033973383905704110364081)
            ·
              refine ⟨775480037929278082773061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033973383905704110364081 775480037929278082773061)
              ·
                refine ⟨145402507111739640519949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775480037929278082773061 145402507111739640519949)
                ·
                  rfl

theorem cell19_477850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_477850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477850 prefixEnd_477850 := by exact prefixLift 477850
  have htrace : WordTrace (prefixWord ++ tailWord_477850) baseStart_477850 baseEnd_477850 := by
    simpa [prefixWord, tailWord_477850, baseEnd_477850] using wordTrace_append hprefix tailTrace_477850
  have hstable : (prefixWord ++ tailWord_477850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477850).length < 2 ^ (prefixWord ++ tailWord_477850).sum := by decide
  have hdescent : baseEnd_477850 < baseStart_477850 := by decide
  rcases family_descends (prefixWord ++ tailWord_477850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477852 : List Nat := [2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_477852 : Nat := 118140960795 + 477852 * 2 ^ 59
def prefixEnd_477852 : Nat := 4983230072969 + 3 ^ 40 * 477852 * 2
def baseEnd_477852 : Nat := 145403115681404228475499

theorem tailTrace_477852 : CollatzResearch.WordTrace tailWord_477852 prefixEnd_477852 145403115681404228475499 := by
  unfold tailWord_477852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714347132415644734677905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11619129509887526312903873 8714347132415644734677905)
  ·
    refine ⟨6535760349311733551008429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8714347132415644734677905 6535760349311733551008429)
    ·
      refine ⟨2450910130991900081628161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6535760349311733551008429 2450910130991900081628161)
      ·
        refine ⟨1838182598243925061221121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450910130991900081628161 1838182598243925061221121)
        ·
          refine ⟨1378636948682943795915841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838182598243925061221121 1378636948682943795915841)
          ·
            refine ⟨1033977711512207846936881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378636948682943795915841 1033977711512207846936881)
            ·
              refine ⟨775483283634155885202661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033977711512207846936881 775483283634155885202661)
              ·
                refine ⟨145403115681404228475499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775483283634155885202661 145403115681404228475499)
                ·
                  rfl

theorem cell19_477852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_477852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477852 prefixEnd_477852 := by exact prefixLift 477852
  have htrace : WordTrace (prefixWord ++ tailWord_477852) baseStart_477852 baseEnd_477852 := by
    simpa [prefixWord, tailWord_477852, baseEnd_477852] using wordTrace_append hprefix tailTrace_477852
  have hstable : (prefixWord ++ tailWord_477852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477852).length < 2 ^ (prefixWord ++ tailWord_477852).sum := by decide
  have hdescent : baseEnd_477852 < baseStart_477852 := by decide
  rcases family_descends (prefixWord ++ tailWord_477852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477890 : List Nat := [3, 5, 1, 10]
def baseStart_477890 : Nat := 118140960795 + 477890 * 2 ^ 59
def prefixEnd_477890 : Nat := 4983230072969 + 3 ^ 40 * 477890 * 2
def baseEnd_477890 : Nat := 1795242944506560489271

theorem tailTrace_477890 : CollatzResearch.WordTrace tailWord_477890 prefixEnd_477890 1795242944506560489271 := by
  unfold tailWord_477890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357520059673405489809781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11620053492462414639492749 4357520059673405489809781)
  ·
    refine ⟨408517505594381764669667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4357520059673405489809781 408517505594381764669667)
    ·
      refine ⟨612776258391572647004501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408517505594381764669667 612776258391572647004501)
      ·
        refine ⟨1795242944506560489271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 612776258391572647004501 1795242944506560489271)
        ·
          rfl

theorem cell19_477890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 10].length) (baseStart_477890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477890 prefixEnd_477890 := by exact prefixLift 477890
  have htrace : WordTrace (prefixWord ++ tailWord_477890) baseStart_477890 baseEnd_477890 := by
    simpa [prefixWord, tailWord_477890, baseEnd_477890] using wordTrace_append hprefix tailTrace_477890
  have hstable : (prefixWord ++ tailWord_477890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477890).length < 2 ^ (prefixWord ++ tailWord_477890).sum := by decide
  have hdescent : baseEnd_477890 < baseStart_477890 := by decide
  rcases family_descends (prefixWord ++ tailWord_477890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477892 : List Nat := [2, 3, 3, 1, 1, 9]
def baseStart_477892 : Nat := 118140960795 + 477892 * 2 ^ 59
def prefixEnd_477892 : Nat := 4983230072969 + 3 ^ 40 * 477892 * 2
def baseEnd_477892 : Nat := 16157254119410665287389

theorem tailTrace_477892 : CollatzResearch.WordTrace tailWord_477892 prefixEnd_477892 16157254119410665287389 := by
  unfold tailWord_477892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715076592343188150405965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11620102123124250867207953 8715076592343188150405965)
  ·
    refine ⟨3268153722128695556402237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8715076592343188150405965 3268153722128695556402237)
    ·
      refine ⟨1225557645798260833650839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3268153722128695556402237 1225557645798260833650839)
      ·
        refine ⟨1838336468697391250476259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225557645798260833650839 1838336468697391250476259)
        ·
          refine ⟨2757504703046086875714389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838336468697391250476259 2757504703046086875714389)
          ·
            refine ⟨16157254119410665287389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2757504703046086875714389 16157254119410665287389)
            ·
              rfl

theorem cell19_477892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_477892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477892 prefixEnd_477892 := by exact prefixLift 477892
  have htrace : WordTrace (prefixWord ++ tailWord_477892) baseStart_477892 baseEnd_477892 := by
    simpa [prefixWord, tailWord_477892, baseEnd_477892] using wordTrace_append hprefix tailTrace_477892
  have hstable : (prefixWord ++ tailWord_477892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477892).length < 2 ^ (prefixWord ++ tailWord_477892).sum := by decide
  have hdescent : baseEnd_477892 < baseStart_477892 := by decide
  rcases family_descends (prefixWord ++ tailWord_477892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477911 : List Nat := [1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_477911 : Nat := 118140960795 + 477911 * 2 ^ 59
def prefixEnd_477911 : Nat := 4983230072969 + 3 ^ 40 * 477911 * 2
def baseEnd_477911 : Nat := 145421068486509573164227

theorem tailTrace_477911 : CollatzResearch.WordTrace tailWord_477911 prefixEnd_477911 145421068486509573164227 := by
  unfold tailWord_477911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430846171617542545753587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11620564114411695030502391 17430846171617542545753587)
  ·
    refine ⟨26146269257426313818630381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17430846171617542545753587 26146269257426313818630381)
    ·
      refine ⟨9804850971534867681986393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26146269257426313818630381 9804850971534867681986393)
      ·
        refine ⟨7353638228651150761489795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9804850971534867681986393 7353638228651150761489795)
        ·
          refine ⟨11030457342976726142234693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353638228651150761489795 11030457342976726142234693)
          ·
            refine ⟨2068210751808136151669005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11030457342976726142234693 2068210751808136151669005)
            ·
              refine ⟨775579031928051056875877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2068210751808136151669005 775579031928051056875877)
              ·
                refine ⟨145421068486509573164227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775579031928051056875877 145421068486509573164227)
                ·
                  rfl

theorem cell19_477911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_477911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477911 prefixEnd_477911 := by exact prefixLift 477911
  have htrace : WordTrace (prefixWord ++ tailWord_477911) baseStart_477911 baseEnd_477911 := by
    simpa [prefixWord, tailWord_477911, baseEnd_477911] using wordTrace_append hprefix tailTrace_477911
  have hstable : (prefixWord ++ tailWord_477911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477911).length < 2 ^ (prefixWord ++ tailWord_477911).sum := by decide
  have hdescent : baseEnd_477911 < baseStart_477911 := by decide
  rcases family_descends (prefixWord ++ tailWord_477911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477981 : List Nat := [1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_477981 : Nat := 118140960795 + 477981 * 2 ^ 59
def prefixEnd_477981 : Nat := 4983230072969 + 3 ^ 40 * 477981 * 2
def baseEnd_477981 : Nat := 145442368424770151608481

theorem tailTrace_477981 : CollatzResearch.WordTrace tailWord_477981 prefixEnd_477981 145442368424770151608481 := by
  unfold tailWord_477981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433399281363944500801797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11622266187575963000534531 17433399281363944500801797)
  ·
    refine ⟨3268762365255739593900337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17433399281363944500801797 3268762365255739593900337)
    ·
      refine ⟨2451571773941804695425253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268762365255739593900337 2451571773941804695425253)
      ·
        refine ⟨459669707614088380392235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2451571773941804695425253 459669707614088380392235)
        ·
          refine ⟨689504561421132570588353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459669707614088380392235 689504561421132570588353)
          ·
            refine ⟨517128421065849427941265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689504561421132570588353 517128421065849427941265)
            ·
              refine ⟨387846315799387070955949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517128421065849427941265 387846315799387070955949)
              ·
                refine ⟨145442368424770151608481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387846315799387070955949 145442368424770151608481)
                ·
                  rfl

theorem cell19_477981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_477981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_477981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_477981 prefixEnd_477981 := by exact prefixLift 477981
  have htrace : WordTrace (prefixWord ++ tailWord_477981) baseStart_477981 baseEnd_477981 := by
    simpa [prefixWord, tailWord_477981, baseEnd_477981] using wordTrace_append hprefix tailTrace_477981
  have hstable : (prefixWord ++ tailWord_477981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477981).length < 2 ^ (prefixWord ++ tailWord_477981).sum := by decide
  have hdescent : baseEnd_477981 < baseStart_477981 := by decide
  rcases family_descends (prefixWord ++ tailWord_477981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478025 : List Nat := [1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_478025 : Nat := 118140960795 + 478025 * 2 ^ 59
def prefixEnd_478025 : Nat := 4983230072969 + 3 ^ 40 * 478025 * 2
def baseEnd_478025 : Nat := 145455756957391086630583

theorem tailTrace_478025 : CollatzResearch.WordTrace tailWord_478025 prefixEnd_478025 145455756957391086630583 := by
  unfold tailWord_478025
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435004093204540015403529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11623336062136360010269019 17435004093204540015403529)
  ·
    refine ⟨13076253069903405011552647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17435004093204540015403529 13076253069903405011552647)
    ·
      refine ⟨19614379604855107517328971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13076253069903405011552647 19614379604855107517328971)
      ·
        refine ⟨29421569407282661275993457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614379604855107517328971 29421569407282661275993457)
        ·
          refine ⟨22066177055461995956995093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29421569407282661275993457 22066177055461995956995093)
          ·
            refine ⟨1034352049474781060484145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22066177055461995956995093 1034352049474781060484145)
            ·
              refine ⟨775764037106085795363109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034352049474781060484145 775764037106085795363109)
              ·
                refine ⟨145455756957391086630583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775764037106085795363109 145455756957391086630583)
                ·
                  rfl

theorem cell19_478025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_478025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478025 prefixEnd_478025 := by exact prefixLift 478025
  have htrace : WordTrace (prefixWord ++ tailWord_478025) baseStart_478025 baseEnd_478025 := by
    simpa [prefixWord, tailWord_478025, baseEnd_478025] using wordTrace_append hprefix tailTrace_478025
  have hstable : (prefixWord ++ tailWord_478025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478025).length < 2 ^ (prefixWord ++ tailWord_478025).sum := by decide
  have hdescent : baseEnd_478025 < baseStart_478025 := by decide
  rcases family_descends (prefixWord ++ tailWord_478025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478065 : List Nat := [1, 2, 2, 2, 1, 11]
def baseStart_478065 : Nat := 118140960795 + 478065 * 2 ^ 59
def prefixEnd_478065 : Nat := 4983230072969 + 3 ^ 40 * 478065 * 2
def baseEnd_478065 : Nat := 16163103150075871749065

theorem tailTrace_478065 : CollatzResearch.WordTrace tailWord_478065 prefixEnd_478065 16163103150075871749065 := by
  unfold tailWord_478065
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436463013059626846859649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11624308675373084564573099 17436463013059626846859649)
  ·
    refine ⟨13077347259794720135144737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17436463013059626846859649 13077347259794720135144737)
    ·
      refine ⟨9808010444846040101358553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13077347259794720135144737 9808010444846040101358553)
      ·
        refine ⟨7356007833634530076018915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9808010444846040101358553 7356007833634530076018915)
        ·
          refine ⟨11034011750451795114028373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356007833634530076018915 11034011750451795114028373)
          ·
            refine ⟨16163103150075871749065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11034011750451795114028373 16163103150075871749065)
            ·
              rfl

theorem cell19_478065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_478065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478065 prefixEnd_478065 := by exact prefixLift 478065
  have htrace : WordTrace (prefixWord ++ tailWord_478065) baseStart_478065 baseEnd_478065 := by
    simpa [prefixWord, tailWord_478065, baseEnd_478065] using wordTrace_append hprefix tailTrace_478065
  have hstable : (prefixWord ++ tailWord_478065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478065).length < 2 ^ (prefixWord ++ tailWord_478065).sum := by decide
  have hdescent : baseEnd_478065 < baseStart_478065 := by decide
  rcases family_descends (prefixWord ++ tailWord_478065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478150 : List Nat := [6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_478150 : Nat := 118140960795 + 478150 * 2 ^ 59
def prefixEnd_478150 : Nat := 4983230072969 + 3 ^ 40 * 478150 * 2
def baseEnd_478150 : Nat := 145493792561427833852465

theorem tailTrace_478150 : CollatzResearch.WordTrace tailWord_478150 prefixEnd_478150 145493792561427833852465 := by
  unfold tailWord_478150
  simp only [CollatzResearch.WordTrace]
  refine ⟨544986350554740198865747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11626375478501124242469269 544986350554740198865747)
  ·
    refine ⟨817479525832110298298621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 544986350554740198865747 817479525832110298298621)
    ·
      refine ⟨306554822187041361861983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 817479525832110298298621 306554822187041361861983)
      ·
        refine ⟨459832233280562042792975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306554822187041361861983 459832233280562042792975)
        ·
          refine ⟨689748349920843064189463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459832233280562042792975 689748349920843064189463)
          ·
            refine ⟨1034622524881264596284195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689748349920843064189463 1034622524881264596284195)
            ·
              refine ⟨1551933787321896894426293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034622524881264596284195 1551933787321896894426293)
              ·
                refine ⟨145493792561427833852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1551933787321896894426293 145493792561427833852465)
                ·
                  rfl

theorem cell19_478150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_478150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478150 prefixEnd_478150 := by exact prefixLift 478150
  have htrace : WordTrace (prefixWord ++ tailWord_478150) baseStart_478150 baseEnd_478150 := by
    simpa [prefixWord, tailWord_478150, baseEnd_478150] using wordTrace_append hprefix tailTrace_478150
  have hstable : (prefixWord ++ tailWord_478150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478150).length < 2 ^ (prefixWord ++ tailWord_478150).sum := by decide
  have hdescent : baseEnd_478150 < baseStart_478150 := by decide
  rcases family_descends (prefixWord ++ tailWord_478150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478158 : List Nat := [4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_478158 : Nat := 118140960795 + 478158 * 2 ^ 59
def prefixEnd_478158 : Nat := 4983230072969 + 3 ^ 40 * 478158 * 2
def baseEnd_478158 : Nat := 145496226840086185674665

theorem tailTrace_478158 : CollatzResearch.WordTrace tailWord_478158 prefixEnd_478158 145496226840086185674665 := by
  unfold tailWord_478158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179981875215337966249391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11626570001148469153330085 2179981875215337966249391)
  ·
    refine ⟨3269972812823006949374087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179981875215337966249391 3269972812823006949374087)
    ·
      refine ⟨4904959219234510424061131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269972812823006949374087 4904959219234510424061131)
      ·
        refine ⟨7357438828851765636091697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904959219234510424061131 7357438828851765636091697)
        ·
          refine ⟨5518079121638824227068773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7357438828851765636091697 5518079121638824227068773)
          ·
            refine ⟨1034639835307279542575395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5518079121638824227068773 1034639835307279542575395)
            ·
              refine ⟨1551959752960919313863093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034639835307279542575395 1551959752960919313863093)
              ·
                refine ⟨145496226840086185674665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1551959752960919313863093 145496226840086185674665)
                ·
                  rfl

theorem cell19_478158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_478158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478158 prefixEnd_478158 := by exact prefixLift 478158
  have htrace : WordTrace (prefixWord ++ tailWord_478158) baseStart_478158 baseEnd_478158 := by
    simpa [prefixWord, tailWord_478158, baseEnd_478158] using wordTrace_append hprefix tailTrace_478158
  have hstable : (prefixWord ++ tailWord_478158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478158).length < 2 ^ (prefixWord ++ tailWord_478158).sum := by decide
  have hdescent : baseEnd_478158 < baseStart_478158 := by decide
  rcases family_descends (prefixWord ++ tailWord_478158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478175 : List Nat := [1, 1, 2, 3, 6, 1, 5]
def baseStart_478175 : Nat := 118140960795 + 478175 * 2 ^ 59
def prefixEnd_478175 : Nat := 4983230072969 + 3 ^ 40 * 478175 * 2
def baseEnd_478175 : Nat := 48500466560745061098947

theorem tailTrace_478175 : CollatzResearch.WordTrace tailWord_478175 prefixEnd_478175 48500466560745061098947 := by
  unfold tailWord_478175
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440475042661115633363979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11626983361774077088909319 17440475042661115633363979)
  ·
    refine ⟨26160712563991673450045969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17440475042661115633363979 26160712563991673450045969)
    ·
      refine ⟨19620534422993755087534477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26160712563991673450045969 19620534422993755087534477)
      ·
        refine ⟨7357700408622658157825429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19620534422993755087534477 7357700408622658157825429)
        ·
          refine ⟨344892206654187101148067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7357700408622658157825429 344892206654187101148067)
          ·
            refine ⟨517338309981280651722101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344892206654187101148067 517338309981280651722101)
            ·
              refine ⟨48500466560745061098947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 517338309981280651722101 48500466560745061098947)
              ·
                rfl

theorem cell19_478175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_478175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478175 prefixEnd_478175 := by exact prefixLift 478175
  have htrace : WordTrace (prefixWord ++ tailWord_478175) baseStart_478175 baseEnd_478175 := by
    simpa [prefixWord, tailWord_478175, baseEnd_478175] using wordTrace_append hprefix tailTrace_478175
  have hstable : (prefixWord ++ tailWord_478175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478175).length < 2 ^ (prefixWord ++ tailWord_478175).sum := by decide
  have hdescent : baseEnd_478175 < baseStart_478175 := by decide
  rcases family_descends (prefixWord ++ tailWord_478175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478236 : List Nat := [2, 2, 3, 1, 11]
def baseStart_478236 : Nat := 118140960795 + 478236 * 2 ^ 59
def prefixEnd_478236 : Nat := 4983230072969 + 3 ^ 40 * 478236 * 2
def baseEnd_478236 : Nat := 5389628187296485775597

theorem tailTrace_478236 : CollatzResearch.WordTrace tailWord_478236 prefixEnd_478236 5389628187296485775597 := by
  unfold tailWord_478236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721349947720061525667281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11628466596960082034223041 8721349947720061525667281)
  ·
    refine ⟨6541012460790046144250461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8721349947720061525667281 6541012460790046144250461)
    ·
      refine ⟨2452879672796267304093923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6541012460790046144250461 2452879672796267304093923)
      ·
        refine ⟨3679319509194400956140885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452879672796267304093923 3679319509194400956140885)
        ·
          refine ⟨5389628187296485775597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3679319509194400956140885 5389628187296485775597)
          ·
            rfl

theorem cell19_478236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_478236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478236 prefixEnd_478236 := by exact prefixLift 478236
  have htrace : WordTrace (prefixWord ++ tailWord_478236) baseStart_478236 baseEnd_478236 := by
    simpa [prefixWord, tailWord_478236, baseEnd_478236] using wordTrace_append hprefix tailTrace_478236
  have hstable : (prefixWord ++ tailWord_478236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478236).length < 2 ^ (prefixWord ++ tailWord_478236).sum := by decide
  have hdescent : baseEnd_478236 < baseStart_478236 := by decide
  rcases family_descends (prefixWord ++ tailWord_478236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478272 : List Nat := [2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_478272 : Nat := 118140960795 + 478272 * 2 ^ 59
def prefixEnd_478272 : Nat := 4983230072969 + 3 ^ 40 * 478272 * 2
def baseEnd_478272 : Nat := 145530915310967699141021

theorem tailTrace_478272 : CollatzResearch.WordTrace tailWord_478272 prefixEnd_478272 145530915310967699141021 := by
  unfold tailWord_478272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722006461654850599822535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11629341948873134133096713 8722006461654850599822535)
  ·
    refine ⟨13083009692482275899733803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8722006461654850599822535 13083009692482275899733803)
    ·
      refine ⟨19624514538723413849600705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13083009692482275899733803 19624514538723413849600705)
      ·
        refine ⟨14718385904042560387200529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19624514538723413849600705 14718385904042560387200529)
        ·
          refine ⟨11038789428031920290400397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14718385904042560387200529 11038789428031920290400397)
          ·
            refine ⟨4139546035511970108900149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11038789428031920290400397 4139546035511970108900149)
            ·
              refine ⟨388082440829247197709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4139546035511970108900149 388082440829247197709389)
              ·
                refine ⟨145530915310967699141021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388082440829247197709389 145530915310967699141021)
                ·
                  rfl

theorem cell19_478272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_478272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478272 prefixEnd_478272 := by exact prefixLift 478272
  have htrace : WordTrace (prefixWord ++ tailWord_478272) baseStart_478272 baseEnd_478272 := by
    simpa [prefixWord, tailWord_478272, baseEnd_478272] using wordTrace_append hprefix tailTrace_478272
  have hstable : (prefixWord ++ tailWord_478272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478272).length < 2 ^ (prefixWord ++ tailWord_478272).sum := by decide
  have hdescent : baseEnd_478272 < baseStart_478272 := by decide
  rcases family_descends (prefixWord ++ tailWord_478272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478293 : List Nat := [1, 3, 2, 2, 1, 2, 8]
def baseStart_478293 : Nat := 118140960795 + 478293 * 2 ^ 59
def prefixEnd_478293 : Nat := 4983230072969 + 3 ^ 40 * 478293 * 2
def baseEnd_478293 : Nat := 48512435097481957558099

theorem tailTrace_478293 : CollatzResearch.WordTrace tailWord_478293 prefixEnd_478293 48512435097481957558099 := by
  unfold tailWord_478293
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444778856233621786159533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11629852570822414524106355 17444778856233621786159533)
  ·
    refine ⟨6541792071087608169809825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17444778856233621786159533 6541792071087608169809825)
    ·
      refine ⟨4906344053315706127357369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6541792071087608169809825 4906344053315706127357369)
      ·
        refine ⟨3679758039986779595518027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4906344053315706127357369 3679758039986779595518027)
        ·
          refine ⟨5519637059980169393277041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679758039986779595518027 5519637059980169393277041)
          ·
            refine ⟨4139727794985127044957781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519637059980169393277041 4139727794985127044957781)
            ·
              refine ⟨48512435097481957558099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4139727794985127044957781 48512435097481957558099)
              ·
                rfl

theorem cell19_478293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_478293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478293 prefixEnd_478293 := by exact prefixLift 478293
  have htrace : WordTrace (prefixWord ++ tailWord_478293) baseStart_478293 baseEnd_478293 := by
    simpa [prefixWord, tailWord_478293, baseEnd_478293] using wordTrace_append hprefix tailTrace_478293
  have hstable : (prefixWord ++ tailWord_478293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478293).length < 2 ^ (prefixWord ++ tailWord_478293).sum := by decide
  have hdescent : baseEnd_478293 < baseStart_478293 := by decide
  rcases family_descends (prefixWord ++ tailWord_478293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478329 : List Nat := [1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_478329 : Nat := 118140960795 + 478329 * 2 ^ 59
def prefixEnd_478329 : Nat := 4983230072969 + 3 ^ 40 * 478329 * 2
def baseEnd_478329 : Nat := 145548259546408455874199

theorem tailTrace_478329 : CollatzResearch.WordTrace tailWord_478329 prefixEnd_478329 145548259546408455874199 := by
  unfold tailWord_478329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446091884103199934470041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11630727922735466622980027 17446091884103199934470041)
  ·
    refine ⟨13084568913077399950852531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17446091884103199934470041 13084568913077399950852531)
    ·
      refine ⟨19626853369616099926278797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13084568913077399950852531 19626853369616099926278797)
      ·
        refine ⟨7360070013606037472354549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19626853369616099926278797 7360070013606037472354549)
        ·
          refine ⟨690006563775566013033239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7360070013606037472354549 690006563775566013033239)
          ·
            refine ⟨1035009845663349019549859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690006563775566013033239 1035009845663349019549859)
            ·
              refine ⟨1552514768495023529324789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035009845663349019549859 1552514768495023529324789)
              ·
                refine ⟨145548259546408455874199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552514768495023529324789 145548259546408455874199)
                ·
                  rfl

theorem cell19_478329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_478329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478329 prefixEnd_478329 := by exact prefixLift 478329
  have htrace : WordTrace (prefixWord ++ tailWord_478329) baseStart_478329 baseEnd_478329 := by
    simpa [prefixWord, tailWord_478329, baseEnd_478329] using wordTrace_append hprefix tailTrace_478329
  have hstable : (prefixWord ++ tailWord_478329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478329).length < 2 ^ (prefixWord ++ tailWord_478329).sum := by decide
  have hdescent : baseEnd_478329 < baseStart_478329 := by decide
  rcases family_descends (prefixWord ++ tailWord_478329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478420 : List Nat := [2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_478420 : Nat := 118140960795 + 478420 * 2 ^ 59
def prefixEnd_478420 : Nat := 4983230072969 + 3 ^ 40 * 478420 * 2
def baseEnd_478420 : Nat := 145575949466147207851729

theorem tailTrace_478420 : CollatzResearch.WordTrace tailWord_478420 prefixEnd_478420 145575949466147207851729 := by
  unfold tailWord_478420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724705463386761238016357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11632940617849014984021809 8724705463386761238016357)
  ·
    refine ⟨1635882274385017732128067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8724705463386761238016357 1635882274385017732128067)
    ·
      refine ⟨2453823411577526598192101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635882274385017732128067 2453823411577526598192101)
      ·
        refine ⟨460091889670786237161019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2453823411577526598192101 460091889670786237161019)
        ·
          refine ⟨690137834506179355741529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460091889670786237161019 690137834506179355741529)
          ·
            refine ⟨517603375879634516806147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690137834506179355741529 517603375879634516806147)
            ·
              refine ⟨776405063819451775209221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517603375879634516806147 776405063819451775209221)
              ·
                refine ⟨145575949466147207851729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776405063819451775209221 145575949466147207851729)
                ·
                  rfl

theorem cell19_478420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_478420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478420 prefixEnd_478420 := by exact prefixLift 478420
  have htrace : WordTrace (prefixWord ++ tailWord_478420) baseStart_478420 baseEnd_478420 := by
    simpa [prefixWord, tailWord_478420, baseEnd_478420] using wordTrace_append hprefix tailTrace_478420
  have hstable : (prefixWord ++ tailWord_478420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478420).length < 2 ^ (prefixWord ++ tailWord_478420).sum := by decide
  have hdescent : baseEnd_478420 < baseStart_478420 := by decide
  rcases family_descends (prefixWord ++ tailWord_478420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478443 : List Nat := [1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_478443 : Nat := 118140960795 + 478443 * 2 ^ 59
def prefixEnd_478443 : Nat := 4983230072969 + 3 ^ 40 * 478443 * 2
def baseEnd_478443 : Nat := 145582948017289969340555

theorem tailTrace_478443 : CollatzResearch.WordTrace tailWord_478443 prefixEnd_478443 145582948017289969340555 := by
  unfold tailWord_478443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450249805690197404119983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11633499870460131602746655 17450249805690197404119983)
  ·
    refine ⟨26175374708535296106179975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17450249805690197404119983 26175374708535296106179975)
    ·
      refine ⟨39263062062802944159269963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26175374708535296106179975 39263062062802944159269963)
      ·
        refine ⟨58894593094204416238904945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39263062062802944159269963 58894593094204416238904945)
        ·
          refine ⟨44170944820653312179178709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58894593094204416238904945 44170944820653312179178709)
          ·
            refine ⟨1035256519234062004199501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44170944820653312179178709 1035256519234062004199501)
            ·
              refine ⟨388221194712773251574813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035256519234062004199501 388221194712773251574813)
              ·
                refine ⟨145582948017289969340555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388221194712773251574813 145582948017289969340555)
                ·
                  rfl

theorem cell19_478443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_478443 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478443 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478443 prefixEnd_478443 := by exact prefixLift 478443
  have htrace : WordTrace (prefixWord ++ tailWord_478443) baseStart_478443 baseEnd_478443 := by
    simpa [prefixWord, tailWord_478443, baseEnd_478443] using wordTrace_append hprefix tailTrace_478443
  have hstable : (prefixWord ++ tailWord_478443).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478443).length < 2 ^ (prefixWord ++ tailWord_478443).sum := by decide
  have hdescent : baseEnd_478443 < baseStart_478443 := by decide
  rcases family_descends (prefixWord ++ tailWord_478443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478462 : List Nat := [4, 2, 2, 1, 1, 3, 6]
def baseStart_478462 : Nat := 118140960795 + 478462 * 2 ^ 59
def prefixEnd_478462 : Nat := 4983230072969 + 3 ^ 40 * 478462 * 2
def baseEnd_478462 : Nat := 48529576476367851639427

theorem tailTrace_478462 : CollatzResearch.WordTrace tailWord_478462 prefixEnd_478462 48529576476367851639427 := by
  unfold tailWord_478462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181367849077670456132705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11633961861747575766041093 2181367849077670456132705)
  ·
    refine ⟨1636025886808252842099529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181367849077670456132705 1636025886808252842099529)
    ·
      refine ⟨1227019415106189631574647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636025886808252842099529 1227019415106189631574647)
      ·
        refine ⟨1840529122659284447361971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227019415106189631574647 1840529122659284447361971)
        ·
          refine ⟨2760793683988926671042957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840529122659284447361971 2760793683988926671042957)
          ·
            refine ⟨1035297631495847501641109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2760793683988926671042957 1035297631495847501641109)
            ·
              refine ⟨48529576476367851639427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1035297631495847501641109 48529576476367851639427)
              ·
                rfl

theorem cell19_478462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_478462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478462 prefixEnd_478462 := by exact prefixLift 478462
  have htrace : WordTrace (prefixWord ++ tailWord_478462) baseStart_478462 baseEnd_478462 := by
    simpa [prefixWord, tailWord_478462, baseEnd_478462] using wordTrace_append hprefix tailTrace_478462
  have hstable : (prefixWord ++ tailWord_478462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478462).length < 2 ^ (prefixWord ++ tailWord_478462).sum := by decide
  have hdescent : baseEnd_478462 < baseStart_478462 := by decide
  rcases family_descends (prefixWord ++ tailWord_478462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478494 : List Nat := [4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_478494 : Nat := 118140960795 + 478494 * 2 ^ 59
def prefixEnd_478494 : Nat := 4983230072969 + 3 ^ 40 * 478494 * 2
def baseEnd_478494 : Nat := 145598466543736962207083

theorem tailTrace_478494 : CollatzResearch.WordTrace tailWord_478494 prefixEnd_478494 145598466543736962207083 := by
  unfold tailWord_478494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181513741063179139278317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11634739952336955409484357 2181513741063179139278317)
  ·
    refine ⟨818067652898692177229369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2181513741063179139278317 818067652898692177229369)
    ·
      refine ⟨613550739674019132922027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818067652898692177229369 613550739674019132922027)
      ·
        refine ⟨920326109511028699383041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613550739674019132922027 920326109511028699383041)
        ·
          refine ⟨690244582133271524537281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920326109511028699383041 690244582133271524537281)
          ·
            refine ⟨517683436599953643402961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690244582133271524537281 517683436599953643402961)
            ·
              refine ⟨388262577449965232552221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517683436599953643402961 388262577449965232552221)
              ·
                refine ⟨145598466543736962207083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388262577449965232552221 145598466543736962207083)
                ·
                  rfl

theorem cell19_478494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_478494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478494 prefixEnd_478494 := by exact prefixLift 478494
  have htrace : WordTrace (prefixWord ++ tailWord_478494) baseStart_478494 baseEnd_478494 := by
    simpa [prefixWord, tailWord_478494, baseEnd_478494] using wordTrace_append hprefix tailTrace_478494
  have hstable : (prefixWord ++ tailWord_478494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478494).length < 2 ^ (prefixWord ++ tailWord_478494).sum := by decide
  have hdescent : baseEnd_478494 < baseStart_478494 := by decide
  rcases family_descends (prefixWord ++ tailWord_478494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478496 : List Nat := [2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_478496 : Nat := 118140960795 + 478496 * 2 ^ 59
def prefixEnd_478496 : Nat := 4983230072969 + 3 ^ 40 * 478496 * 2
def baseEnd_478496 : Nat := 145599075113401550162633

theorem tailTrace_478496 : CollatzResearch.WordTrace tailWord_478496 prefixEnd_478496 145599075113401550162633 := by
  unfold tailWord_478496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726091437249093727899671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11634788582998791637199561 8726091437249093727899671)
  ·
    refine ⟨13089137155873640591849507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726091437249093727899671 13089137155873640591849507)
    ·
      refine ⟨19633705733810460887774261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089137155873640591849507 19633705733810460887774261)
      ·
        refine ⟨1840659912544730708228837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19633705733810460887774261 1840659912544730708228837)
        ·
          refine ⟨345123733602137007792907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1840659912544730708228837 345123733602137007792907)
          ·
            refine ⟨517685600403205511689361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345123733602137007792907 517685600403205511689361)
            ·
              refine ⟨388264200302404133767021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517685600403205511689361 388264200302404133767021)
              ·
                refine ⟨145599075113401550162633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388264200302404133767021 145599075113401550162633)
                ·
                  rfl

theorem cell19_478496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_478496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478496 prefixEnd_478496 := by exact prefixLift 478496
  have htrace : WordTrace (prefixWord ++ tailWord_478496) baseStart_478496 baseEnd_478496 := by
    simpa [prefixWord, tailWord_478496, baseEnd_478496] using wordTrace_append hprefix tailTrace_478496
  have hstable : (prefixWord ++ tailWord_478496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478496).length < 2 ^ (prefixWord ++ tailWord_478496).sum := by decide
  have hdescent : baseEnd_478496 < baseStart_478496 := by decide
  rcases family_descends (prefixWord ++ tailWord_478496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478540 : List Nat := [2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_478540 : Nat := 118140960795 + 478540 * 2 ^ 59
def prefixEnd_478540 : Nat := 4983230072969 + 3 ^ 40 * 478540 * 2
def baseEnd_478540 : Nat := 145612463646022485184735

theorem tailTrace_478540 : CollatzResearch.WordTrace tailWord_478540 prefixEnd_478540 145612463646022485184735 := by
  unfold tailWord_478540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726893843169391485200537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11635858457559188646934049 8726893843169391485200537)
  ·
    refine ⟨6545170382377043613900403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8726893843169391485200537 6545170382377043613900403)
    ·
      refine ⟨9817755573565565420850605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545170382377043613900403 9817755573565565420850605)
      ·
        refine ⟨3681658340087087032818977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9817755573565565420850605 3681658340087087032818977)
        ·
          refine ⟨2761243755065315274614233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3681658340087087032818977 2761243755065315274614233)
          ·
            refine ⟨2070932816298986455960675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761243755065315274614233 2070932816298986455960675)
            ·
              refine ⟨3106399224448479683941013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070932816298986455960675 3106399224448479683941013)
              ·
                refine ⟨145612463646022485184735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3106399224448479683941013 145612463646022485184735)
                ·
                  rfl

theorem cell19_478540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_478540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478540 prefixEnd_478540 := by exact prefixLift 478540
  have htrace : WordTrace (prefixWord ++ tailWord_478540) baseStart_478540 baseEnd_478540 := by
    simpa [prefixWord, tailWord_478540, baseEnd_478540] using wordTrace_append hprefix tailTrace_478540
  have hstable : (prefixWord ++ tailWord_478540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478540).length < 2 ^ (prefixWord ++ tailWord_478540).sum := by decide
  have hdescent : baseEnd_478540 < baseStart_478540 := by decide
  rcases family_descends (prefixWord ++ tailWord_478540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478574 : List Nat := [4, 1, 2, 4, 2, 6]
def baseStart_478574 : Nat := 118140960795 + 478574 * 2 ^ 59
def prefixEnd_478574 : Nat := 4983230072969 + 3 ^ 40 * 478574 * 2
def baseEnd_478574 : Nat := 16180312147813386714343

theorem tailTrace_478574 : CollatzResearch.WordTrace tailWord_478574 prefixEnd_478574 16180312147813386714343 := by
  unfold tailWord_478574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181878471026950847142347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11636685178810404518092517 2181878471026950847142347)
  ·
    refine ⟨3272817706540426270713521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181878471026950847142347 3272817706540426270713521)
    ·
      refine ⟨2454613279905319703035141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272817706540426270713521 2454613279905319703035141)
      ·
        refine ⟨460239989982247444319089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2454613279905319703035141 460239989982247444319089)
        ·
          refine ⟨345179992486685583239317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460239989982247444319089 345179992486685583239317)
          ·
            refine ⟨16180312147813386714343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 345179992486685583239317 16180312147813386714343)
            ·
              rfl

theorem cell19_478574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_478574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478574 prefixEnd_478574 := by exact prefixLift 478574
  have htrace : WordTrace (prefixWord ++ tailWord_478574) baseStart_478574 baseEnd_478574 := by
    simpa [prefixWord, tailWord_478574, baseEnd_478574] using wordTrace_append hprefix tailTrace_478574
  have hstable : (prefixWord ++ tailWord_478574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478574).length < 2 ^ (prefixWord ++ tailWord_478574).sum := by decide
  have hdescent : baseEnd_478574 < baseStart_478574 := by decide
  rcases family_descends (prefixWord ++ tailWord_478574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478593 : List Nat := [1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_478593 : Nat := 118140960795 + 478593 * 2 ^ 59
def prefixEnd_478593 : Nat := 4983230072969 + 3 ^ 40 * 478593 * 2
def baseEnd_478593 : Nat := 145628590742134066006813

theorem tailTrace_478593 : CollatzResearch.WordTrace tailWord_478593 prefixEnd_478593 145628590742134066006813 := by
  unfold tailWord_478593
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455720755146773022080433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637147170097848681386955 17455720755146773022080433)
  ·
    refine ⟨13091790566360079766560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17455720755146773022080433 13091790566360079766560325)
    ·
      refine ⟨2454710731192514956230061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13091790566360079766560325 2454710731192514956230061)
      ·
        refine ⟨920516524197193108586273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454710731192514956230061 920516524197193108586273)
        ·
          refine ⟨690387393147894831439705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920516524197193108586273 690387393147894831439705)
          ·
            refine ⟨517790544860921123579779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690387393147894831439705 517790544860921123579779)
            ·
              refine ⟨776685817291381685369669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517790544860921123579779 776685817291381685369669)
              ·
                refine ⟨145628590742134066006813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776685817291381685369669 145628590742134066006813)
                ·
                  rfl

theorem cell19_478593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_478593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478593 prefixEnd_478593 := by exact prefixLift 478593
  have htrace : WordTrace (prefixWord ++ tailWord_478593) baseStart_478593 baseEnd_478593 := by
    simpa [prefixWord, tailWord_478593, baseEnd_478593] using wordTrace_append hprefix tailTrace_478593
  have hstable : (prefixWord ++ tailWord_478593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478593).length < 2 ^ (prefixWord ++ tailWord_478593).sum := by decide
  have hdescent : baseEnd_478593 < baseStart_478593 := by decide
  rcases family_descends (prefixWord ++ tailWord_478593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478595 : List Nat := [1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_478595 : Nat := 118140960795 + 478595 * 2 ^ 59
def prefixEnd_478595 : Nat := 4983230072969 + 3 ^ 40 * 478595 * 2
def baseEnd_478595 : Nat := 145629199311798653962363

theorem tailTrace_478595 : CollatzResearch.WordTrace tailWord_478595 prefixEnd_478595 145629199311798653962363 := by
  unfold tailWord_478595
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455793701139527363653239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637195800759684909102159 17455793701139527363653239)
  ·
    refine ⟨26183690551709291045479859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455793701139527363653239 26183690551709291045479859)
    ·
      refine ⟨39275535827563936568219789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26183690551709291045479859 39275535827563936568219789)
      ·
        refine ⟨14728325935336476213082421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39275535827563936568219789 14728325935336476213082421)
        ·
          refine ⟨1380780556437794644976477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14728325935336476213082421 1380780556437794644976477)
          ·
            refine ⟨517792708664172991866179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380780556437794644976477 517792708664172991866179)
            ·
              refine ⟨776689062996259487799269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517792708664172991866179 776689062996259487799269)
              ·
                refine ⟨145629199311798653962363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776689062996259487799269 145629199311798653962363)
                ·
                  rfl

theorem cell19_478595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_478595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478595 prefixEnd_478595 := by exact prefixLift 478595
  have htrace : WordTrace (prefixWord ++ tailWord_478595) baseStart_478595 baseEnd_478595 := by
    simpa [prefixWord, tailWord_478595, baseEnd_478595] using wordTrace_append hprefix tailTrace_478595
  have hstable : (prefixWord ++ tailWord_478595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478595).length < 2 ^ (prefixWord ++ tailWord_478595).sum := by decide
  have hdescent : baseEnd_478595 < baseStart_478595 := by decide
  rcases family_descends (prefixWord ++ tailWord_478595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478597 : List Nat := [1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_478597 : Nat := 118140960795 + 478597 * 2 ^ 59
def prefixEnd_478597 : Nat := 4983230072969 + 3 ^ 40 * 478597 * 2
def baseEnd_478597 : Nat := 145629807881463241917913

theorem tailTrace_478597 : CollatzResearch.WordTrace tailWord_478597 prefixEnd_478597 145629807881463241917913 := by
  unfold tailWord_478597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455866647132281705226045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637244431421521136817363 17455866647132281705226045)
  ·
    refine ⟨6545949992674605639459767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17455866647132281705226045 6545949992674605639459767)
    ·
      refine ⟨9818924989011908459189651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545949992674605639459767 9818924989011908459189651)
      ·
        refine ⟨14728387483517862688784477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818924989011908459189651 14728387483517862688784477)
        ·
          refine ⟨5523145306319198508294179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14728387483517862688784477 5523145306319198508294179)
          ·
            refine ⟨8284717959478797762441269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523145306319198508294179 8284717959478797762441269)
            ·
              refine ⟨776692308701137290228869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8284717959478797762441269 776692308701137290228869)
              ·
                refine ⟨145629807881463241917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776692308701137290228869 145629807881463241917913)
                ·
                  rfl

theorem cell19_478597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_478597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478597 prefixEnd_478597 := by exact prefixLift 478597
  have htrace : WordTrace (prefixWord ++ tailWord_478597) baseStart_478597 baseEnd_478597 := by
    simpa [prefixWord, tailWord_478597, baseEnd_478597] using wordTrace_append hprefix tailTrace_478597
  have hstable : (prefixWord ++ tailWord_478597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478597).length < 2 ^ (prefixWord ++ tailWord_478597).sum := by decide
  have hdescent : baseEnd_478597 < baseStart_478597 := by decide
  rcases family_descends (prefixWord ++ tailWord_478597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478610 : List Nat := [3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_478610 : Nat := 118140960795 + 478610 * 2 ^ 59
def prefixEnd_478610 : Nat := 4983230072969 + 3 ^ 40 * 478610 * 2
def baseEnd_478610 : Nat := 145633763584283063628989

theorem tailTrace_478610 : CollatzResearch.WordTrace tailWord_478610 prefixEnd_478610 145633763584283063628989 := by
  unfold tailWord_478610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364085199021296231362321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11637560530723456616966189 4364085199021296231362321)
  ·
    refine ⟨3273063899265972173521741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4364085199021296231362321 3273063899265972173521741)
    ·
      refine ⟨1227398962224739565070653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3273063899265972173521741 1227398962224739565070653)
      ·
        refine ⟨460274610834277336901495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1227398962224739565070653 460274610834277336901495)
        ·
          refine ⟨690411916251416005352243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460274610834277336901495 690411916251416005352243)
          ·
            refine ⟨1035617874377124008028365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690411916251416005352243 1035617874377124008028365)
            ·
              refine ⟨388356702891421503010637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035617874377124008028365 388356702891421503010637)
              ·
                refine ⟨145633763584283063628989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388356702891421503010637 145633763584283063628989)
                ·
                  rfl

theorem cell19_478610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_478610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478610 prefixEnd_478610 := by exact prefixLift 478610
  have htrace : WordTrace (prefixWord ++ tailWord_478610) baseStart_478610 baseEnd_478610 := by
    simpa [prefixWord, tailWord_478610, baseEnd_478610] using wordTrace_append hprefix tailTrace_478610
  have hstable : (prefixWord ++ tailWord_478610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478610).length < 2 ^ (prefixWord ++ tailWord_478610).sum := by decide
  have hdescent : baseEnd_478610 < baseStart_478610 := by decide
  rcases family_descends (prefixWord ++ tailWord_478610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478612 : List Nat := [2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_478612 : Nat := 118140960795 + 478612 * 2 ^ 59
def prefixEnd_478612 : Nat := 4983230072969 + 3 ^ 40 * 478612 * 2
def baseEnd_478612 : Nat := 145634372153947651584539

theorem tailTrace_478612 : CollatzResearch.WordTrace tailWord_478612 prefixEnd_478612 145634372153947651584539 := by
  unfold tailWord_478612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728206871038969633511045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11637609161385292844681393 8728206871038969633511045)
  ·
    refine ⟨1636538788319806806283321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8728206871038969633511045 1636538788319806806283321)
    ·
      refine ⟨1227404091239855104712491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636538788319806806283321 1227404091239855104712491)
      ·
        refine ⟨1841106136859782657068737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227404091239855104712491 1841106136859782657068737)
        ·
          refine ⟨1380829602644836992801553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841106136859782657068737 1380829602644836992801553)
          ·
            refine ⟨1035622201983627744601165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380829602644836992801553 1035622201983627744601165)
            ·
              refine ⟨388358325743860404225437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035622201983627744601165 388358325743860404225437)
              ·
                refine ⟨145634372153947651584539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388358325743860404225437 145634372153947651584539)
                ·
                  rfl

theorem cell19_478612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_478612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478612 prefixEnd_478612 := by exact prefixLift 478612
  have htrace : WordTrace (prefixWord ++ tailWord_478612) baseStart_478612 baseEnd_478612 := by
    simpa [prefixWord, tailWord_478612, baseEnd_478612] using wordTrace_append hprefix tailTrace_478612
  have hstable : (prefixWord ++ tailWord_478612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478612).length < 2 ^ (prefixWord ++ tailWord_478612).sum := by decide
  have hdescent : baseEnd_478612 < baseStart_478612 := by decide
  rcases family_descends (prefixWord ++ tailWord_478612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478654 : List Nat := [4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_478654 : Nat := 118140960795 + 478654 * 2 ^ 59
def prefixEnd_478654 : Nat := 4983230072969 + 3 ^ 40 * 478654 * 2
def baseEnd_478654 : Nat := 145647152116903998651091

theorem tailTrace_478654 : CollatzResearch.WordTrace tailWord_478654 prefixEnd_478654 145647152116903998651091 := by
  unfold tailWord_478654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182243200990722555006377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11638630405283853626700677 2182243200990722555006377)
  ·
    refine ⟨1636682400743041916254783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2182243200990722555006377 1636682400743041916254783)
    ·
      refine ⟨2455023601114562874382175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636682400743041916254783 2455023601114562874382175)
      ·
        refine ⟨3682535401671844311573263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455023601114562874382175 3682535401671844311573263)
        ·
          refine ⟨5523803102507766467359895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682535401671844311573263 5523803102507766467359895)
          ·
            refine ⟨8285704653761649701039843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523803102507766467359895 8285704653761649701039843)
            ·
              refine ⟨12428556980642474551559765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285704653761649701039843 12428556980642474551559765)
              ·
                refine ⟨145647152116903998651091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12428556980642474551559765 145647152116903998651091)
                ·
                  rfl

theorem cell19_478654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_478654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478654 prefixEnd_478654 := by exact prefixLift 478654
  have htrace : WordTrace (prefixWord ++ tailWord_478654) baseStart_478654 baseEnd_478654 := by
    simpa [prefixWord, tailWord_478654, baseEnd_478654] using wordTrace_append hprefix tailTrace_478654
  have hstable : (prefixWord ++ tailWord_478654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478654).length < 2 ^ (prefixWord ++ tailWord_478654).sum := by decide
  have hdescent : baseEnd_478654 < baseStart_478654 := by decide
  rcases family_descends (prefixWord ++ tailWord_478654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478709 : List Nat := [1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_478709 : Nat := 118140960795 + 478709 * 2 ^ 59
def prefixEnd_478709 : Nat := 4983230072969 + 3 ^ 40 * 478709 * 2
def baseEnd_478709 : Nat := 145663887782680167428719

theorem tailTrace_478709 : CollatzResearch.WordTrace tailWord_478709 prefixEnd_478709 145663887782680167428719 := by
  unfold tailWord_478709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459951622726524833303181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11639967748484349888868787 17459951622726524833303181)
  ·
    refine ⟨6547481858522446812488693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17459951622726524833303181 6547481858522446812488693)
    ·
      refine ⟨613826424236479388670815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6547481858522446812488693 613826424236479388670815)
      ·
        refine ⟨920739636354719083006223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613826424236479388670815 920739636354719083006223)
        ·
          refine ⟨1381109454532078624509335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920739636354719083006223 1381109454532078624509335)
          ·
            refine ⟨2071664181798117936764003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381109454532078624509335 2071664181798117936764003)
            ·
              refine ⟨3107496272697176905146005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071664181798117936764003 3107496272697176905146005)
              ·
                refine ⟨145663887782680167428719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107496272697176905146005 145663887782680167428719)
                ·
                  rfl

theorem cell19_478709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_478709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478709 prefixEnd_478709 := by exact prefixLift 478709
  have htrace : WordTrace (prefixWord ++ tailWord_478709) baseStart_478709 baseEnd_478709 := by
    simpa [prefixWord, tailWord_478709, baseEnd_478709] using wordTrace_append hprefix tailTrace_478709
  have hstable : (prefixWord ++ tailWord_478709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478709).length < 2 ^ (prefixWord ++ tailWord_478709).sum := by decide
  have hdescent : baseEnd_478709 < baseStart_478709 := by decide
  rcases family_descends (prefixWord ++ tailWord_478709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478730 : List Nat := [3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_478730 : Nat := 118140960795 + 478730 * 2 ^ 59
def prefixEnd_478730 : Nat := 4983230072969 + 3 ^ 40 * 478730 * 2
def baseEnd_478730 : Nat := 145670277764158340961995

theorem tailTrace_478730 : CollatzResearch.WordTrace tailWord_478730 prefixEnd_478730 145670277764158340961995 := by
  unfold tailWord_478730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365179388912611354954411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11640478370433630279878429 4365179388912611354954411)
  ·
    refine ⟨6547769083368917032431617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365179388912611354954411 6547769083368917032431617)
    ·
      refine ⟨4910826812526687774323713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6547769083368917032431617 4910826812526687774323713)
      ·
        refine ⟨3683120109395015830742785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910826812526687774323713 3683120109395015830742785)
        ·
          refine ⟨2762340082046261873057089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683120109395015830742785 2762340082046261873057089)
          ·
            refine ⟨2071755061534696404792817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762340082046261873057089 2071755061534696404792817)
            ·
              refine ⟨1553816296151022303594613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071755061534696404792817 1553816296151022303594613)
              ·
                refine ⟨145670277764158340961995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553816296151022303594613 145670277764158340961995)
                ·
                  rfl

theorem cell19_478730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_478730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478730 prefixEnd_478730 := by exact prefixLift 478730
  have htrace : WordTrace (prefixWord ++ tailWord_478730) baseStart_478730 baseEnd_478730 := by
    simpa [prefixWord, tailWord_478730, baseEnd_478730] using wordTrace_append hprefix tailTrace_478730
  have hstable : (prefixWord ++ tailWord_478730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478730).length < 2 ^ (prefixWord ++ tailWord_478730).sum := by decide
  have hdescent : baseEnd_478730 < baseStart_478730 := by decide
  rcases family_descends (prefixWord ++ tailWord_478730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478766 : List Nat := [4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_478766 : Nat := 118140960795 + 478766 * 2 ^ 59
def prefixEnd_478766 : Nat := 4983230072969 + 3 ^ 40 * 478766 * 2
def baseEnd_478766 : Nat := 145681232018120924161897

theorem tailTrace_478766 : CollatzResearch.WordTrace tailWord_478766 prefixEnd_478766 145681232018120924161897 := by
  unfold tailWord_478766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182753822940002946016019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11641353722346682378752101 2182753822940002946016019)
  ·
    refine ⟨3274130734410004419024029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182753822940002946016019 3274130734410004419024029)
    ·
      refine ⟨1227799025403751657134011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3274130734410004419024029 1227799025403751657134011)
      ·
        refine ⟨1841698538105627485701017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227799025403751657134011 1841698538105627485701017)
        ·
          refine ⟨1381273903579220614275763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841698538105627485701017 1381273903579220614275763)
          ·
            refine ⟨2071910855368830921413645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381273903579220614275763 2071910855368830921413645)
            ·
              refine ⟨776966570763311595530117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071910855368830921413645 776966570763311595530117)
              ·
                refine ⟨145681232018120924161897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776966570763311595530117 145681232018120924161897)
                ·
                  rfl

theorem cell19_478766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_478766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478766 prefixEnd_478766 := by exact prefixLift 478766
  have htrace : WordTrace (prefixWord ++ tailWord_478766) baseStart_478766 baseEnd_478766 := by
    simpa [prefixWord, tailWord_478766, baseEnd_478766] using wordTrace_append hprefix tailTrace_478766
  have hstable : (prefixWord ++ tailWord_478766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478766).length < 2 ^ (prefixWord ++ tailWord_478766).sum := by decide
  have hdescent : baseEnd_478766 < baseStart_478766 := by decide
  rcases family_descends (prefixWord ++ tailWord_478766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478785 : List Nat := [1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_478785 : Nat := 118140960795 + 478785 * 2 ^ 59
def prefixEnd_478785 : Nat := 4983230072969 + 3 ^ 40 * 478785 * 2
def baseEnd_478785 : Nat := 145687013429934509739623

theorem tailTrace_478785 : CollatzResearch.WordTrace tailWord_478785 prefixEnd_478785 145687013429934509739623 := by
  unfold tailWord_478785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17462723570451189813069809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11641815713634126542046539 17462723570451189813069809)
  ·
    refine ⟨13097042677838392359802357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17462723570451189813069809 13097042677838392359802357)
    ·
      refine ⟨1227847751047349283731471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13097042677838392359802357 1227847751047349283731471)
      ·
        refine ⟨1841771626571023925597207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227847751047349283731471 1841771626571023925597207)
        ·
          refine ⟨2762657439856535888395811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841771626571023925597207 2762657439856535888395811)
          ·
            refine ⟨4143986159784803832593717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762657439856535888395811 4143986159784803832593717)
            ·
              refine ⟨388498702479825359305661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4143986159784803832593717 388498702479825359305661)
              ·
                refine ⟨145687013429934509739623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388498702479825359305661 145687013429934509739623)
                ·
                  rfl

theorem cell19_478785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_478785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478785 prefixEnd_478785 := by exact prefixLift 478785
  have htrace : WordTrace (prefixWord ++ tailWord_478785) baseStart_478785 baseEnd_478785 := by
    simpa [prefixWord, tailWord_478785, baseEnd_478785] using wordTrace_append hprefix tailTrace_478785
  have hstable : (prefixWord ++ tailWord_478785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478785).length < 2 ^ (prefixWord ++ tailWord_478785).sum := by decide
  have hdescent : baseEnd_478785 < baseStart_478785 := by decide
  rcases family_descends (prefixWord ++ tailWord_478785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478914 : List Nat := [3, 5, 1, 2, 2, 6]
def baseStart_478914 : Nat := 118140960795 + 478914 * 2 ^ 59
def prefixEnd_478914 : Nat := 4983230072969 + 3 ^ 40 * 478914 * 2
def baseEnd_478914 : Nat := 16191807352588936985845

theorem tailTrace_478914 : CollatzResearch.WordTrace tailWord_478914 prefixEnd_478914 16191807352588936985845 := by
  unfold tailWord_478914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366857146745961211128949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11644952391322563229677197 4366857146745961211128949)
  ·
    refine ⟨409392857507433863543339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4366857146745961211128949 409392857507433863543339)
    ·
      refine ⟨614089286261150795315009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409392857507433863543339 614089286261150795315009)
      ·
        refine ⟨460566964695863096486257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614089286261150795315009 460566964695863096486257)
        ·
          refine ⟨345425223521897322364693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460566964695863096486257 345425223521897322364693)
          ·
            refine ⟨16191807352588936985845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 345425223521897322364693 16191807352588936985845)
            ·
              rfl

theorem cell19_478914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_478914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478914 prefixEnd_478914 := by exact prefixLift 478914
  have htrace : WordTrace (prefixWord ++ tailWord_478914) baseStart_478914 baseEnd_478914 := by
    simpa [prefixWord, tailWord_478914, baseEnd_478914] using wordTrace_append hprefix tailTrace_478914
  have hstable : (prefixWord ++ tailWord_478914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478914).length < 2 ^ (prefixWord ++ tailWord_478914).sum := by decide
  have hdescent : baseEnd_478914 < baseStart_478914 := by decide
  rcases family_descends (prefixWord ++ tailWord_478914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478922 : List Nat := [3, 1, 2, 1, 12]
def baseStart_478922 : Nat := 118140960795 + 478922 * 2 ^ 59
def prefixEnd_478922 : Nat := 4983230072969 + 3 ^ 40 * 478922 * 2
def baseEnd_478922 : Nat := 5397359275998473507215

theorem tailTrace_478922 : CollatzResearch.WordTrace tailWord_478922 prefixEnd_478922 5397359275998473507215 := by
  unfold tailWord_478922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366930092738715552701755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11645146913969908140538013 4366930092738715552701755)
  ·
    refine ⟨6550395139108073329052633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4366930092738715552701755 6550395139108073329052633)
    ·
      refine ⟨4912796354331054996789475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6550395139108073329052633 4912796354331054996789475)
      ·
        refine ⟨7369194531496582495184213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912796354331054996789475 7369194531496582495184213)
        ·
          refine ⟨5397359275998473507215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7369194531496582495184213 5397359275998473507215)
          ·
            rfl

theorem cell19_478922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_478922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_478922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_478922 prefixEnd_478922 := by exact prefixLift 478922
  have htrace : WordTrace (prefixWord ++ tailWord_478922) baseStart_478922 baseEnd_478922 := by
    simpa [prefixWord, tailWord_478922, baseEnd_478922] using wordTrace_append hprefix tailTrace_478922
  have hstable : (prefixWord ++ tailWord_478922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478922).length < 2 ^ (prefixWord ++ tailWord_478922).sum := by decide
  have hdescent : baseEnd_478922 < baseStart_478922 := by decide
  rcases family_descends (prefixWord ++ tailWord_478922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479013 : List Nat := [1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_479013 : Nat := 118140960795 + 479013 * 2 ^ 59
def prefixEnd_479013 : Nat := 4983230072969 + 3 ^ 40 * 479013 * 2
def baseEnd_479013 : Nat := 145756390371697536672335

theorem tailTrace_479013 : CollatzResearch.WordTrace tailWord_479013 prefixEnd_479013 145756390371697536672335 := by
  unfold tailWord_479013
  simp only [CollatzResearch.WordTrace]
  refine ⟨17471039413625184752369693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11647359609083456501579795 17471039413625184752369693)
  ·
    refine ⟨6551639780109444282138635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17471039413625184752369693 6551639780109444282138635)
    ·
      refine ⟨9827459670164166423207953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551639780109444282138635 9827459670164166423207953)
      ·
        refine ⟨7370594752623124817405965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9827459670164166423207953 7370594752623124817405965)
        ·
          refine ⟨2763973032233671806527237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7370594752623124817405965 2763973032233671806527237)
          ·
            refine ⟨518244943543813463723857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2763973032233671806527237 518244943543813463723857)
            ·
              refine ⟨388683707657860097792893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518244943543813463723857 388683707657860097792893)
              ·
                refine ⟨145756390371697536672335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388683707657860097792893 145756390371697536672335)
                ·
                  rfl

theorem cell19_479013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_479013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479013 prefixEnd_479013 := by exact prefixLift 479013
  have htrace : WordTrace (prefixWord ++ tailWord_479013) baseStart_479013 baseEnd_479013 := by
    simpa [prefixWord, tailWord_479013, baseEnd_479013] using wordTrace_append hprefix tailTrace_479013
  have hstable : (prefixWord ++ tailWord_479013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479013).length < 2 ^ (prefixWord ++ tailWord_479013).sum := by decide
  have hdescent : baseEnd_479013 < baseStart_479013 := by decide
  rcases family_descends (prefixWord ++ tailWord_479013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479034 : List Nat := [3, 1, 1, 1, 5, 3, 5]
def baseStart_479034 : Nat := 118140960795 + 479034 * 2 ^ 59
def prefixEnd_479034 : Nat := 4983230072969 + 3 ^ 40 * 479034 * 2
def baseEnd_479034 : Nat := 48587593451058570068537

theorem tailTrace_479034 : CollatzResearch.WordTrace tailWord_479034 prefixEnd_479034 48587593451058570068537 := by
  unfold tailWord_479034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367951336637276334721039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11647870231032736892589437 4367951336637276334721039)
  ·
    refine ⟨6551927004955914502081559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4367951336637276334721039 6551927004955914502081559)
    ·
      refine ⟨9827890507433871753122339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551927004955914502081559 9827890507433871753122339)
      ·
        refine ⟨14741835761150807629683509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827890507433871753122339 14741835761150807629683509)
        ·
          refine ⟨1382047102607888215282829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14741835761150807629683509 1382047102607888215282829)
          ·
            refine ⟨518267663477958080731061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1382047102607888215282829 518267663477958080731061)
            ·
              refine ⟨48587593451058570068537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 518267663477958080731061 48587593451058570068537)
              ·
                rfl

theorem cell19_479034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_479034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479034 prefixEnd_479034 := by exact prefixLift 479034
  have htrace : WordTrace (prefixWord ++ tailWord_479034) baseStart_479034 baseEnd_479034 := by
    simpa [prefixWord, tailWord_479034, baseEnd_479034] using wordTrace_append hprefix tailTrace_479034
  have hstable : (prefixWord ++ tailWord_479034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479034).length < 2 ^ (prefixWord ++ tailWord_479034).sum := by decide
  have hdescent : baseEnd_479034 < baseStart_479034 := by decide
  rcases family_descends (prefixWord ++ tailWord_479034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479036 : List Nat := [2, 2, 2, 2, 1, 1, 9]
def baseStart_479036 : Nat := 118140960795 + 479036 * 2 ^ 59
def prefixEnd_479036 : Nat := 4983230072969 + 3 ^ 40 * 479036 * 2
def baseEnd_479036 : Nat := 48587796307613432720387

theorem tailTrace_479036 : CollatzResearch.WordTrace tailWord_479036 prefixEnd_479036 48587796307613432720387 := by
  unfold tailWord_479036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735939146270929840228481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11647918861694573120304641 8735939146270929840228481)
  ·
    refine ⟨6551954359703197380171361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8735939146270929840228481 6551954359703197380171361)
    ·
      refine ⟨4913965769777398035128521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6551954359703197380171361 4913965769777398035128521)
      ·
        refine ⟨3685474327333048526346391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913965769777398035128521 3685474327333048526346391)
        ·
          refine ⟨5528211490999572789519587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685474327333048526346391 5528211490999572789519587)
          ·
            refine ⟨8292317236499359184279381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528211490999572789519587 8292317236499359184279381)
            ·
              refine ⟨48587796307613432720387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8292317236499359184279381 48587796307613432720387)
              ·
                rfl

theorem cell19_479036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_479036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479036 prefixEnd_479036 := by exact prefixLift 479036
  have htrace : WordTrace (prefixWord ++ tailWord_479036) baseStart_479036 baseEnd_479036 := by
    simpa [prefixWord, tailWord_479036, baseEnd_479036] using wordTrace_append hprefix tailTrace_479036
  have hstable : (prefixWord ++ tailWord_479036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479036).length < 2 ^ (prefixWord ++ tailWord_479036).sum := by decide
  have hdescent : baseEnd_479036 < baseStart_479036 := by decide
  rcases family_descends (prefixWord ++ tailWord_479036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479222 : List Nat := [5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_479222 : Nat := 118140960795 + 479222 * 2 ^ 59
def prefixEnd_479222 : Nat := 4983230072969 + 3 ^ 40 * 479222 * 2
def baseEnd_479222 : Nat := 145819985901646978027321

theorem tailTrace_479222 : CollatzResearch.WordTrace tailWord_479222 prefixEnd_479222 145819985901646978027321 := by
  unfold tailWord_479222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092416391866750840420495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11652441513245342297818613 1092416391866750840420495)
  ·
    refine ⟨1638624587800126260630743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092416391866750840420495 1638624587800126260630743)
    ·
      refine ⟨2457936881700189390946115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638624587800126260630743 2457936881700189390946115)
      ·
        refine ⟨3686905322550284086419173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457936881700189390946115 3686905322550284086419173)
        ·
          refine ⟨691294747978178266203595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3686905322550284086419173 691294747978178266203595)
          ·
            refine ⟨1036942121967267399305393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691294747978178266203595 1036942121967267399305393)
            ·
              refine ⟨777706591475450549479045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036942121967267399305393 777706591475450549479045)
              ·
                refine ⟨145819985901646978027321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777706591475450549479045 145819985901646978027321)
                ·
                  rfl

theorem cell19_479222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_479222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479222 prefixEnd_479222 := by exact prefixLift 479222
  have htrace : WordTrace (prefixWord ++ tailWord_479222) baseStart_479222 baseEnd_479222 := by
    simpa [prefixWord, tailWord_479222, baseEnd_479222] using wordTrace_append hprefix tailTrace_479222
  have hstable : (prefixWord ++ tailWord_479222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479222).length < 2 ^ (prefixWord ++ tailWord_479222).sum := by decide
  have hdescent : baseEnd_479222 < baseStart_479222 := by decide
  rcases family_descends (prefixWord ++ tailWord_479222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479281 : List Nat := [1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_479281 : Nat := 118140960795 + 479281 * 2 ^ 59
def prefixEnd_479281 : Nat := 4983230072969 + 3 ^ 40 * 479281 * 2
def baseEnd_479281 : Nat := 145837938706752322716049

theorem tailTrace_479281 : CollatzResearch.WordTrace tailWord_479281 prefixEnd_479281 145837938706752322716049 := by
  unfold tailWord_479281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480814176654266523125697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11653876117769511015417131 17480814176654266523125697)
  ·
    refine ⟨13110610632490699892344273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17480814176654266523125697 13110610632490699892344273)
    ·
      refine ⟨9832957974368024919258205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110610632490699892344273 9832957974368024919258205)
      ·
        refine ⟨3687359240388009344721827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9832957974368024919258205 3687359240388009344721827)
        ·
          refine ⟨5531038860582014017082741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687359240388009344721827 5531038860582014017082741)
          ·
            refine ⟨518534893179563814101507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5531038860582014017082741 518534893179563814101507)
            ·
              refine ⟨777802339769345721152261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518534893179563814101507 777802339769345721152261)
              ·
                refine ⟨145837938706752322716049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777802339769345721152261 145837938706752322716049)
                ·
                  rfl

theorem cell19_479281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_479281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479281 prefixEnd_479281 := by exact prefixLift 479281
  have htrace : WordTrace (prefixWord ++ tailWord_479281) baseStart_479281 baseEnd_479281 := by
    simpa [prefixWord, tailWord_479281, baseEnd_479281] using wordTrace_append hprefix tailTrace_479281
  have hstable : (prefixWord ++ tailWord_479281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479281).length < 2 ^ (prefixWord ++ tailWord_479281).sum := by decide
  have hdescent : baseEnd_479281 < baseStart_479281 := by decide
  rcases family_descends (prefixWord ++ tailWord_479281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479283 : List Nat := [1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_479283 : Nat := 118140960795 + 479283 * 2 ^ 59
def prefixEnd_479283 : Nat := 4983230072969 + 3 ^ 40 * 479283 * 2
def baseEnd_479283 : Nat := 145838547276416910671599

theorem tailTrace_479283 : CollatzResearch.WordTrace tailWord_479283 prefixEnd_479283 145838547276416910671599 := by
  unfold tailWord_479283
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480887122647020864698503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11653924748431347243132335 17480887122647020864698503)
  ·
    refine ⟨26221330683970531297047755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480887122647020864698503 26221330683970531297047755)
    ·
      refine ⟨39331996025955796945571633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26221330683970531297047755 39331996025955796945571633)
      ·
        refine ⟨29498997019466847709178725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39331996025955796945571633 29498997019466847709178725)
        ·
          refine ⟨5531061941150033945471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29498997019466847709178725 5531061941150033945471011)
          ·
            refine ⟨8296592911725050918206517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531061941150033945471011 8296592911725050918206517)
            ·
              refine ⟨777805585474223523581861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8296592911725050918206517 777805585474223523581861)
              ·
                refine ⟨145838547276416910671599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777805585474223523581861 145838547276416910671599)
                ·
                  rfl

theorem cell19_479283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_479283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479283 prefixEnd_479283 := by exact prefixLift 479283
  have htrace : WordTrace (prefixWord ++ tailWord_479283) baseStart_479283 baseEnd_479283 := by
    simpa [prefixWord, tailWord_479283, baseEnd_479283] using wordTrace_append hprefix tailTrace_479283
  have hstable : (prefixWord ++ tailWord_479283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479283).length < 2 ^ (prefixWord ++ tailWord_479283).sum := by decide
  have hdescent : baseEnd_479283 < baseStart_479283 := by decide
  rcases family_descends (prefixWord ++ tailWord_479283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479357 : List Nat := [1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_479357 : Nat := 118140960795 + 479357 * 2 ^ 59
def prefixEnd_479357 : Nat := 4983230072969 + 3 ^ 40 * 479357 * 2
def baseEnd_479357 : Nat := 145861064354006665026953

theorem tailTrace_479357 : CollatzResearch.WordTrace tailWord_479357 prefixEnd_479357 145861064354006665026953 := by
  unfold tailWord_479357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483586124378931502892325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11655724082919287668594883 17483586124378931502892325)
  ·
    refine ⟨3278172398321049656792311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17483586124378931502892325 3278172398321049656792311)
    ·
      refine ⟨4917258597481574485188467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278172398321049656792311 4917258597481574485188467)
      ·
        refine ⟨7375887896222361727782701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917258597481574485188467 7375887896222361727782701)
        ·
          refine ⟨2765957961083385647918513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7375887896222361727782701 2765957961083385647918513)
          ·
            refine ⟨2074468470812539235938885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2765957961083385647918513 2074468470812539235938885)
            ·
              refine ⟨388962838277351106738541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2074468470812539235938885 388962838277351106738541)
              ·
                refine ⟨145861064354006665026953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388962838277351106738541 145861064354006665026953)
                ·
                  rfl

theorem cell19_479357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_479357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479357 prefixEnd_479357 := by exact prefixLift 479357
  have htrace : WordTrace (prefixWord ++ tailWord_479357) baseStart_479357 baseEnd_479357 := by
    simpa [prefixWord, tailWord_479357, baseEnd_479357] using wordTrace_append hprefix tailTrace_479357
  have hstable : (prefixWord ++ tailWord_479357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479357).length < 2 ^ (prefixWord ++ tailWord_479357).sum := by decide
  have hdescent : baseEnd_479357 < baseStart_479357 := by decide
  rcases family_descends (prefixWord ++ tailWord_479357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479374 : List Nat := [4, 1, 1, 3, 4, 1, 5]
def baseStart_479374 : Nat := 118140960795 + 479374 * 2 ^ 59
def prefixEnd_479374 : Nat := 4983230072969 + 3 ^ 40 * 479374 * 2
def baseEnd_479374 : Nat := 48622079065385220883043

theorem tailTrace_479374 : CollatzResearch.WordTrace tailWord_479374 prefixEnd_479374 48622079065385220883043 := by
  unfold tailWord_479374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185525770664667925782647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11656137443544895604174117 2185525770664667925782647)
  ·
    refine ⟨3278288655997001888673971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185525770664667925782647 3278288655997001888673971)
    ·
      refine ⟨4917432983995502833010957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278288655997001888673971 4917432983995502833010957)
      ·
        refine ⟨1844037368998313562379109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4917432983995502833010957 1844037368998313562379109)
        ·
          refine ⟨345757006687183792946083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1844037368998313562379109 345757006687183792946083)
          ·
            refine ⟨518635510030775689419125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345757006687183792946083 518635510030775689419125)
            ·
              refine ⟨48622079065385220883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 518635510030775689419125 48622079065385220883043)
              ·
                rfl

theorem cell19_479374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_479374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479374 prefixEnd_479374 := by exact prefixLift 479374
  have htrace : WordTrace (prefixWord ++ tailWord_479374) baseStart_479374 baseEnd_479374 := by
    simpa [prefixWord, tailWord_479374, baseEnd_479374] using wordTrace_append hprefix tailTrace_479374
  have hstable : (prefixWord ++ tailWord_479374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479374).length < 2 ^ (prefixWord ++ tailWord_479374).sum := by decide
  have hdescent : baseEnd_479374 < baseStart_479374 := by decide
  rcases family_descends (prefixWord ++ tailWord_479374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479397 : List Nat := [1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_479397 : Nat := 118140960795 + 479397 * 2 ^ 59
def prefixEnd_479397 : Nat := 4983230072969 + 3 ^ 40 * 479397 * 2
def baseEnd_479397 : Nat := 145873235747298424137955

theorem tailTrace_479397 : CollatzResearch.WordTrace tailWord_479397 prefixEnd_479397 145873235747298424137955 := by
  unfold tailWord_479397
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485045044234018334348445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11656696696156012222898963 17485045044234018334348445)
  ·
    refine ⟨6556891891587756875380667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17485045044234018334348445 6556891891587756875380667)
    ·
      refine ⟨9835337837381635313071001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556891891587756875380667 9835337837381635313071001)
      ·
        refine ⟨7376503378036226484803251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9835337837381635313071001 7376503378036226484803251)
        ·
          refine ⟨11064755067054339727204877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376503378036226484803251 11064755067054339727204877)
          ·
            refine ⟨4149283150145377397701829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11064755067054339727204877 4149283150145377397701829)
            ·
              refine ⟨777990590652258262069093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4149283150145377397701829 777990590652258262069093)
              ·
                refine ⟨145873235747298424137955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777990590652258262069093 145873235747298424137955)
                ·
                  rfl

theorem cell19_479397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_479397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479397 prefixEnd_479397 := by exact prefixLift 479397
  have htrace : WordTrace (prefixWord ++ tailWord_479397) baseStart_479397 baseEnd_479397 := by
    simpa [prefixWord, tailWord_479397, baseEnd_479397] using wordTrace_append hprefix tailTrace_479397
  have hstable : (prefixWord ++ tailWord_479397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479397).length < 2 ^ (prefixWord ++ tailWord_479397).sum := by decide
  have hdescent : baseEnd_479397 < baseStart_479397 := by decide
  rcases family_descends (prefixWord ++ tailWord_479397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479469 : List Nat := [1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_479469 : Nat := 118140960795 + 479469 * 2 ^ 59
def prefixEnd_479469 : Nat := 4983230072969 + 3 ^ 40 * 479469 * 2
def baseEnd_479469 : Nat := 145895144255223590537759

theorem tailTrace_479469 : CollatzResearch.WordTrace tailWord_479469 prefixEnd_479469 145895144255223590537759 := by
  unfold tailWord_479469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487671099973174630969461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11658447399982116420646307 17487671099973174630969461)
  ·
    refine ⟨1639469165622485121653387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17487671099973174630969461 1639469165622485121653387)
    ·
      refine ⟨2459203748433727682480081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639469165622485121653387 2459203748433727682480081)
      ·
        refine ⟨1844402811325295761860061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2459203748433727682480081 1844402811325295761860061)
        ·
          refine ⟨691651054246985910697523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1844402811325295761860061 691651054246985910697523)
          ·
            refine ⟨1037476581370478866046285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691651054246985910697523 1037476581370478866046285)
            ·
              refine ⟨389053718013929574767357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037476581370478866046285 389053718013929574767357)
              ·
                refine ⟨145895144255223590537759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389053718013929574767357 145895144255223590537759)
                ·
                  rfl

theorem cell19_479469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_479469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479469 prefixEnd_479469 := by exact prefixLift 479469
  have htrace : WordTrace (prefixWord ++ tailWord_479469) baseStart_479469 baseEnd_479469 := by
    simpa [prefixWord, tailWord_479469, baseEnd_479469] using wordTrace_append hprefix tailTrace_479469
  have hstable : (prefixWord ++ tailWord_479469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479469).length < 2 ^ (prefixWord ++ tailWord_479469).sum := by decide
  have hdescent : baseEnd_479469 < baseStart_479469 := by decide
  rcases family_descends (prefixWord ++ tailWord_479469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479471 : List Nat := [1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_479471 : Nat := 118140960795 + 479471 * 2 ^ 59
def prefixEnd_479471 : Nat := 4983230072969 + 3 ^ 40 * 479471 * 2
def baseEnd_479471 : Nat := 145895752824888178493309

theorem tailTrace_479471 : CollatzResearch.WordTrace tailWord_479471 prefixEnd_479471 145895752824888178493309 := by
  unfold tailWord_479471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487744045965928972542267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11658496030643952648361511 17487744045965928972542267)
  ·
    refine ⟨26231616068948893458813401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17487744045965928972542267 26231616068948893458813401)
    ·
      refine ⟨19673712051711670094110051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26231616068948893458813401 19673712051711670094110051)
      ·
        refine ⟨29510568077567505141165077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19673712051711670094110051 29510568077567505141165077)
        ·
          refine ⟨1383307878635976803492113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29510568077567505141165077 1383307878635976803492113)
          ·
            refine ⟨1037480908976982602619085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383307878635976803492113 1037480908976982602619085)
            ·
              refine ⟨389055340866368475982157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037480908976982602619085 389055340866368475982157)
              ·
                refine ⟨145895752824888178493309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389055340866368475982157 145895752824888178493309)
                ·
                  rfl

theorem cell19_479471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_479471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479471 prefixEnd_479471 := by exact prefixLift 479471
  have htrace : WordTrace (prefixWord ++ tailWord_479471) baseStart_479471 baseEnd_479471 := by
    simpa [prefixWord, tailWord_479471, baseEnd_479471] using wordTrace_append hprefix tailTrace_479471
  have hstable : (prefixWord ++ tailWord_479471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479471).length < 2 ^ (prefixWord ++ tailWord_479471).sum := by decide
  have hdescent : baseEnd_479471 < baseStart_479471 := by decide
  rcases family_descends (prefixWord ++ tailWord_479471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479490 : List Nat := [3, 4, 1, 1, 2, 2, 6]
def baseStart_479490 : Nat := 118140960795 + 479490 * 2 ^ 59
def prefixEnd_479490 : Nat := 4983230072969 + 3 ^ 40 * 479490 * 2
def baseEnd_479490 : Nat := 48633844745567254690345

theorem tailTrace_479490 : CollatzResearch.WordTrace tailWord_479490 prefixEnd_479490 48633844745567254690345 := by
  unfold tailWord_479490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372109258224273804370981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11658958021931396811655949 4372109258224273804370981)
  ·
    refine ⟨819770485917051338319559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4372109258224273804370981 819770485917051338319559)
    ·
      refine ⟨1229655728875577007479339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819770485917051338319559 1229655728875577007479339)
      ·
        refine ⟨1844483593313365511219009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229655728875577007479339 1844483593313365511219009)
        ·
          refine ⟨1383362694985024133414257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844483593313365511219009 1383362694985024133414257)
          ·
            refine ⟨1037522021238768100060693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383362694985024133414257 1037522021238768100060693)
            ·
              refine ⟨48633844745567254690345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1037522021238768100060693 48633844745567254690345)
              ·
                rfl

theorem cell19_479490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_479490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479490 prefixEnd_479490 := by exact prefixLift 479490
  have htrace : WordTrace (prefixWord ++ tailWord_479490) baseStart_479490 baseEnd_479490 := by
    simpa [prefixWord, tailWord_479490, baseEnd_479490] using wordTrace_append hprefix tailTrace_479490
  have hstable : (prefixWord ++ tailWord_479490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479490).length < 2 ^ (prefixWord ++ tailWord_479490).sum := by decide
  have hdescent : baseEnd_479490 < baseStart_479490 := by decide
  rcases family_descends (prefixWord ++ tailWord_479490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479528 : List Nat := [2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_479528 : Nat := 118140960795 + 479528 * 2 ^ 59
def prefixEnd_479528 : Nat := 4983230072969 + 3 ^ 40 * 479528 * 2
def baseEnd_479528 : Nat := 145913097060328935226487

theorem tailTrace_479528 : CollatzResearch.WordTrace tailWord_479528 prefixEnd_479528 145913097060328935226487 := by
  unfold tailWord_479528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744911503379713853683619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11659882004506285138244825 8744911503379713853683619)
  ·
    refine ⟨13117367255069570780525429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8744911503379713853683619 13117367255069570780525429)
    ·
      refine ⟨1229753180162772260674259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13117367255069570780525429 1229753180162772260674259)
      ·
        refine ⟨1844629770244158391011389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229753180162772260674259 1844629770244158391011389)
        ·
          refine ⟨691736163841559396629271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1844629770244158391011389 691736163841559396629271)
          ·
            refine ⟨1037604245762339094943907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691736163841559396629271 1037604245762339094943907)
            ·
              refine ⟨1556406368643508642415861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037604245762339094943907 1556406368643508642415861)
              ·
                refine ⟨145913097060328935226487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1556406368643508642415861 145913097060328935226487)
                ·
                  rfl

theorem cell19_479528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_479528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479528 prefixEnd_479528 := by exact prefixLift 479528
  have htrace : WordTrace (prefixWord ++ tailWord_479528) baseStart_479528 baseEnd_479528 := by
    simpa [prefixWord, tailWord_479528, baseEnd_479528] using wordTrace_append hprefix tailTrace_479528
  have hstable : (prefixWord ++ tailWord_479528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479528).length < 2 ^ (prefixWord ++ tailWord_479528).sum := by decide
  have hdescent : baseEnd_479528 < baseStart_479528 := by decide
  rcases family_descends (prefixWord ++ tailWord_479528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479568 : List Nat := [2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_479568 : Nat := 118140960795 + 479568 * 2 ^ 59
def prefixEnd_479568 : Nat := 4983230072969 + 3 ^ 40 * 479568 * 2
def baseEnd_479568 : Nat := 145925268453620694337489

theorem tailTrace_479568 : CollatzResearch.WordTrace tailWord_479568 prefixEnd_479568 145925268453620694337489 := by
  unfold tailWord_479568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745640963307257269411679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11660854617743009692548905 8745640963307257269411679)
  ·
    refine ⟨13118461444960885904117519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745640963307257269411679 13118461444960885904117519)
    ·
      refine ⟨19677692167441328856176279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13118461444960885904117519 19677692167441328856176279)
      ·
        refine ⟨29516538251161993284264419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677692167441328856176279 29516538251161993284264419)
        ·
          refine ⟨44274807376742989926396629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29516538251161993284264419 44274807376742989926396629)
          ·
            refine ⟨1037690797892413826399921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44274807376742989926396629 1037690797892413826399921)
            ·
              refine ⟨778268098419310369799941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037690797892413826399921 778268098419310369799941)
              ·
                refine ⟨145925268453620694337489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778268098419310369799941 145925268453620694337489)
                ·
                  rfl

theorem cell19_479568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_479568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479568 prefixEnd_479568 := by exact prefixLift 479568
  have htrace : WordTrace (prefixWord ++ tailWord_479568) baseStart_479568 baseEnd_479568 := by
    simpa [prefixWord, tailWord_479568, baseEnd_479568] using wordTrace_append hprefix tailTrace_479568
  have hstable : (prefixWord ++ tailWord_479568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479568).length < 2 ^ (prefixWord ++ tailWord_479568).sum := by decide
  have hdescent : baseEnd_479568 < baseStart_479568 := by decide
  rcases family_descends (prefixWord ++ tailWord_479568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479625 : List Nat := [1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_479625 : Nat := 118140960795 + 479625 * 2 ^ 59
def prefixEnd_479625 : Nat := 4983230072969 + 3 ^ 40 * 479625 * 2
def baseEnd_479625 : Nat := 145942612689061451070667

theorem tailTrace_479625 : CollatzResearch.WordTrace tailWord_479625 prefixEnd_479625 145942612689061451070667 := by
  unfold tailWord_479625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493360887408013273648329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11662240591605342182432219 17493360887408013273648329)
  ·
    refine ⟨13120020665556009955236247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17493360887408013273648329 13120020665556009955236247)
    ·
      refine ⟨19680030998334014932854371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13120020665556009955236247 19680030998334014932854371)
      ·
        refine ⟨29520046497501022399281557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19680030998334014932854371 29520046497501022399281557)
        ·
          refine ⟨1383752179570360424966323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29520046497501022399281557 1383752179570360424966323)
          ·
            refine ⟨2075628269355540637449485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383752179570360424966323 2075628269355540637449485)
            ·
              refine ⟨778360601008327739043557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2075628269355540637449485 778360601008327739043557)
              ·
                refine ⟨145942612689061451070667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778360601008327739043557 145942612689061451070667)
                ·
                  rfl

theorem cell19_479625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_479625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479625 prefixEnd_479625 := by exact prefixLift 479625
  have htrace : WordTrace (prefixWord ++ tailWord_479625) baseStart_479625 baseEnd_479625 := by
    simpa [prefixWord, tailWord_479625, baseEnd_479625] using wordTrace_append hprefix tailTrace_479625
  have hstable : (prefixWord ++ tailWord_479625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479625).length < 2 ^ (prefixWord ++ tailWord_479625).sum := by decide
  have hdescent : baseEnd_479625 < baseStart_479625 := by decide
  rcases family_descends (prefixWord ++ tailWord_479625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479642 : List Nat := [3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_479642 : Nat := 118140960795 + 479642 * 2 ^ 59
def prefixEnd_479642 : Nat := 4983230072969 + 3 ^ 40 * 479642 * 2
def baseEnd_479642 : Nat := 145947785531210448692843

theorem tailTrace_479642 : CollatzResearch.WordTrace tailWord_479642 prefixEnd_479642 145947785531210448692843 := by
  unfold tailWord_479642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373495232086606294254295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11662653952230950118011453 4373495232086606294254295)
  ·
    refine ⟨6560242848129909441381443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373495232086606294254295 6560242848129909441381443)
    ·
      refine ⟨9840364272194864162072165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560242848129909441381443 9840364272194864162072165)
      ·
        refine ⟨1845068301036537030388531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9840364272194864162072165 1845068301036537030388531)
        ·
          refine ⟨2767602451554805545582797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845068301036537030388531 2767602451554805545582797)
          ·
            refine ⟨1037850919333052079593549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2767602451554805545582797 1037850919333052079593549)
            ·
              refine ⟨389194094749894529847581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037850919333052079593549 389194094749894529847581)
              ·
                refine ⟨145947785531210448692843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389194094749894529847581 145947785531210448692843)
                ·
                  rfl

theorem cell19_479642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_479642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479642 prefixEnd_479642 := by exact prefixLift 479642
  have htrace : WordTrace (prefixWord ++ tailWord_479642) baseStart_479642 baseEnd_479642 := by
    simpa [prefixWord, tailWord_479642, baseEnd_479642] using wordTrace_append hprefix tailTrace_479642
  have hstable : (prefixWord ++ tailWord_479642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479642).length < 2 ^ (prefixWord ++ tailWord_479642).sum := by decide
  have hdescent : baseEnd_479642 < baseStart_479642 := by decide
  rcases family_descends (prefixWord ++ tailWord_479642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479661 : List Nat := [1, 5, 2, 2, 2, 1, 6]
def baseStart_479661 : Nat := 118140960795 + 479661 * 2 ^ 59
def prefixEnd_479661 : Nat := 4983230072969 + 3 ^ 40 * 479661 * 2
def baseEnd_479661 : Nat := 48651188981008011423523

theorem tailTrace_479661 : CollatzResearch.WordTrace tailWord_479661 prefixEnd_479661 48651188981008011423523 := by
  unfold tailWord_479661
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494673915277591421958837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11663115943518394281305891 17494673915277591421958837)
  ·
    refine ⟨1640125679557274195808641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17494673915277591421958837 1640125679557274195808641)
    ·
      refine ⟨1230094259667955646856481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640125679557274195808641 1230094259667955646856481)
      ·
        refine ⟨922570694750966735142361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230094259667955646856481 922570694750966735142361)
        ·
          refine ⟨691928021063225051356771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922570694750966735142361 691928021063225051356771)
          ·
            refine ⟨1037892031594837577035157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691928021063225051356771 1037892031594837577035157)
            ·
              refine ⟨48651188981008011423523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1037892031594837577035157 48651188981008011423523)
              ·
                rfl

theorem cell19_479661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_479661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479661 prefixEnd_479661 := by exact prefixLift 479661
  have htrace : WordTrace (prefixWord ++ tailWord_479661) baseStart_479661 baseEnd_479661 := by
    simpa [prefixWord, tailWord_479661, baseEnd_479661] using wordTrace_append hprefix tailTrace_479661
  have hstable : (prefixWord ++ tailWord_479661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479661).length < 2 ^ (prefixWord ++ tailWord_479661).sum := by decide
  have hdescent : baseEnd_479661 < baseStart_479661 := by decide
  rcases family_descends (prefixWord ++ tailWord_479661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479701 : List Nat := [1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_479701 : Nat := 118140960795 + 479701 * 2 ^ 59
def prefixEnd_479701 : Nat := 4983230072969 + 3 ^ 40 * 479701 * 2
def baseEnd_479701 : Nat := 145965738336315793381571

theorem tailTrace_479701 : CollatzResearch.WordTrace tailWord_479701 prefixEnd_479701 145965738336315793381571 := by
  unfold tailWord_479701
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496132835132678253414957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11664088556755118835609971 17496132835132678253414957)
  ·
    refine ⟨6561049813174754345030609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17496132835132678253414957 6561049813174754345030609)
    ·
      refine ⟨4920787359881065758772957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6561049813174754345030609 4920787359881065758772957)
      ·
        refine ⟨1845295259955399659539859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4920787359881065758772957 1845295259955399659539859)
        ·
          refine ⟨2767942889933099489309789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845295259955399659539859 2767942889933099489309789)
          ·
            refine ⟨1037978583724912308491171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2767942889933099489309789 1037978583724912308491171)
            ·
              refine ⟨1556967875587368462736757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037978583724912308491171 1556967875587368462736757)
              ·
                refine ⟨145965738336315793381571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1556967875587368462736757 145965738336315793381571)
                ·
                  rfl

theorem cell19_479701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_479701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479701 prefixEnd_479701 := by exact prefixLift 479701
  have htrace : WordTrace (prefixWord ++ tailWord_479701) baseStart_479701 baseEnd_479701 := by
    simpa [prefixWord, tailWord_479701, baseEnd_479701] using wordTrace_append hprefix tailTrace_479701
  have hstable : (prefixWord ++ tailWord_479701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479701).length < 2 ^ (prefixWord ++ tailWord_479701).sum := by decide
  have hdescent : baseEnd_479701 < baseStart_479701 := by decide
  rcases family_descends (prefixWord ++ tailWord_479701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479714 : List Nat := [3, 3, 3, 2, 2, 1, 5]
def baseStart_479714 : Nat := 118140960795 + 479714 * 2 ^ 59
def prefixEnd_479714 : Nat := 4983230072969 + 3 ^ 40 * 479714 * 2
def baseEnd_479714 : Nat := 48656564679711871697549

theorem tailTrace_479714 : CollatzResearch.WordTrace tailWord_479714 prefixEnd_479714 48656564679711871697549 := by
  unfold tailWord_479714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374151746021395368409549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11664404656057054315758797 4374151746021395368409549)
  ·
    refine ⟨1640306904758023263153581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4374151746021395368409549 1640306904758023263153581)
    ·
      refine ⟨615115089284258723682593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1640306904758023263153581 615115089284258723682593)
      ·
        refine ⟨461336316963194042761945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615115089284258723682593 461336316963194042761945)
        ·
          refine ⟨346002237722395532071459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461336316963194042761945 346002237722395532071459)
          ·
            refine ⟨519003356583593298107189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346002237722395532071459 519003356583593298107189)
            ·
              refine ⟨48656564679711871697549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519003356583593298107189 48656564679711871697549)
              ·
                rfl

theorem cell19_479714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_479714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479714 prefixEnd_479714 := by exact prefixLift 479714
  have htrace : WordTrace (prefixWord ++ tailWord_479714) baseStart_479714 baseEnd_479714 := by
    simpa [prefixWord, tailWord_479714, baseEnd_479714] using wordTrace_append hprefix tailTrace_479714
  have hstable : (prefixWord ++ tailWord_479714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479714).length < 2 ^ (prefixWord ++ tailWord_479714).sum := by decide
  have hdescent : baseEnd_479714 < baseStart_479714 := by decide
  rcases family_descends (prefixWord ++ tailWord_479714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479720 : List Nat := [2, 1, 4, 1, 1, 5, 5]
def baseStart_479720 : Nat := 118140960795 + 479720 * 2 ^ 59
def prefixEnd_479720 : Nat := 4983230072969 + 3 ^ 40 * 479720 * 2
def baseEnd_479720 : Nat := 48657173249376459653099

theorem tailTrace_479720 : CollatzResearch.WordTrace tailWord_479720 prefixEnd_479720 48657173249376459653099 := by
  unfold tailWord_479720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748412911031922249178307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11664550548042562998904409 8748412911031922249178307)
  ·
    refine ⟨13122619366547883373767461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748412911031922249178307 13122619366547883373767461)
    ·
      refine ⟨2460491131227728132581399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13122619366547883373767461 2460491131227728132581399)
      ·
        refine ⟨3690736696841592198872099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460491131227728132581399 3690736696841592198872099)
        ·
          refine ⟨5536105045262388298308149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690736696841592198872099 5536105045262388298308149)
          ·
            refine ⟨519009847993348902966389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5536105045262388298308149 519009847993348902966389)
            ·
              refine ⟨48657173249376459653099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519009847993348902966389 48657173249376459653099)
              ·
                rfl

theorem cell19_479720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_479720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479720 prefixEnd_479720 := by exact prefixLift 479720
  have htrace : WordTrace (prefixWord ++ tailWord_479720) baseStart_479720 baseEnd_479720 := by
    simpa [prefixWord, tailWord_479720, baseEnd_479720] using wordTrace_append hprefix tailTrace_479720
  have hstable : (prefixWord ++ tailWord_479720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479720).length < 2 ^ (prefixWord ++ tailWord_479720).sum := by decide
  have hdescent : baseEnd_479720 < baseStart_479720 := by decide
  rcases family_descends (prefixWord ++ tailWord_479720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479758 : List Nat := [4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_479758 : Nat := 118140960795 + 479758 * 2 ^ 59
def prefixEnd_479758 : Nat := 4983230072969 + 3 ^ 40 * 479758 * 2
def baseEnd_479758 : Nat := 145983082571756550114749

theorem tailTrace_479758 : CollatzResearch.WordTrace tailWord_479758 prefixEnd_479758 145983082571756550114749 := by
  unfold tailWord_479758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187276474490772123529991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11665474530617451325493285 2187276474490772123529991)
  ·
    refine ⟨3280914711736158185294987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187276474490772123529991 3280914711736158185294987)
    ·
      refine ⟨4921372067604237277942481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280914711736158185294987 4921372067604237277942481)
      ·
        refine ⟨3691029050703177958456861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4921372067604237277942481 3691029050703177958456861)
        ·
          refine ⟨1384135894013691734421323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3691029050703177958456861 1384135894013691734421323)
          ·
            refine ⟨2076203841020537601631985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384135894013691734421323 2076203841020537601631985)
            ·
              refine ⟨1557152880765403201223989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076203841020537601631985 1557152880765403201223989)
              ·
                refine ⟨145983082571756550114749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1557152880765403201223989 145983082571756550114749)
                ·
                  rfl

theorem cell19_479758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_479758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479758 prefixEnd_479758 := by exact prefixLift 479758
  have htrace : WordTrace (prefixWord ++ tailWord_479758) baseStart_479758 baseEnd_479758 := by
    simpa [prefixWord, tailWord_479758, baseEnd_479758] using wordTrace_append hprefix tailTrace_479758
  have hstable : (prefixWord ++ tailWord_479758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479758).length < 2 ^ (prefixWord ++ tailWord_479758).sum := by decide
  have hdescent : baseEnd_479758 < baseStart_479758 := by decide
  rcases family_descends (prefixWord ++ tailWord_479758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479779 : List Nat := [1, 1, 1, 4, 4, 8]
def baseStart_479779 : Nat := 118140960795 + 479779 * 2 ^ 59
def prefixEnd_479779 : Nat := 4983230072969 + 3 ^ 40 * 479779 * 2
def baseEnd_479779 : Nat := 16221052505914969294225

theorem tailTrace_479779 : CollatzResearch.WordTrace tailWord_479779 prefixEnd_479779 16221052505914969294225 := by
  unfold tailWord_479779
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498977728850097574754391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11665985152566731716502927 17498977728850097574754391)
  ·
    refine ⟨26248466593275146362131587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17498977728850097574754391 26248466593275146362131587)
    ·
      refine ⟨39372699889912719543197381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26248466593275146362131587 39372699889912719543197381)
      ·
        refine ⟨7382381229358634914349509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39372699889912719543197381 7382381229358634914349509)
        ·
          refine ⟨1384196480504744046440533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7382381229358634914349509 1384196480504744046440533)
          ·
            refine ⟨16221052505914969294225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1384196480504744046440533 16221052505914969294225)
            ·
              rfl

theorem cell19_479779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_479779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479779 prefixEnd_479779 := by exact prefixLift 479779
  have htrace : WordTrace (prefixWord ++ tailWord_479779) baseStart_479779 baseEnd_479779 := by
    simpa [prefixWord, tailWord_479779, baseEnd_479779] using wordTrace_append hprefix tailTrace_479779
  have hstable : (prefixWord ++ tailWord_479779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479779).length < 2 ^ (prefixWord ++ tailWord_479779).sum := by decide
  have hdescent : baseEnd_479779 < baseStart_479779 := by decide
  rcases family_descends (prefixWord ++ tailWord_479779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479872 : List Nat := [2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_479872 : Nat := 118140960795 + 479872 * 2 ^ 59
def prefixEnd_479872 : Nat := 4983230072969 + 3 ^ 40 * 479872 * 2
def baseEnd_479872 : Nat := 146017771042638063581105

theorem tailTrace_479872 : CollatzResearch.WordTrace tailWord_479872 prefixEnd_479872 146017771042638063581105 := by
  unfold tailWord_479872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751184858756587228944935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11668246478342116305259913 8751184858756587228944935)
  ·
    refine ⟨13126777288134880843417403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8751184858756587228944935 13126777288134880843417403)
    ·
      refine ⟨19690165932202321265126105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13126777288134880843417403 19690165932202321265126105)
      ·
        refine ⟨14767624449151740948844579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19690165932202321265126105 14767624449151740948844579)
        ·
          refine ⟨22151436673727611423266869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767624449151740948844579 22151436673727611423266869)
          ·
            refine ⟨2076697188161963570931269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22151436673727611423266869 2076697188161963570931269)
            ·
              refine ⟨389380722780368169549613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2076697188161963570931269 389380722780368169549613)
              ·
                refine ⟨146017771042638063581105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389380722780368169549613 146017771042638063581105)
                ·
                  rfl

theorem cell19_479872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_479872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479872 prefixEnd_479872 := by exact prefixLift 479872
  have htrace : WordTrace (prefixWord ++ tailWord_479872) baseStart_479872 baseEnd_479872 := by
    simpa [prefixWord, tailWord_479872, baseEnd_479872] using wordTrace_append hprefix tailTrace_479872
  have hstable : (prefixWord ++ tailWord_479872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479872).length < 2 ^ (prefixWord ++ tailWord_479872).sum := by decide
  have hdescent : baseEnd_479872 < baseStart_479872 := by decide
  rcases family_descends (prefixWord ++ tailWord_479872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479950 : List Nat := [4, 1, 1, 1, 3, 9]
def baseStart_479950 : Nat := 118140960795 + 479950 * 2 ^ 59
def prefixEnd_479950 : Nat := 4983230072969 + 3 ^ 40 * 479950 * 2
def baseEnd_479950 : Nat := 16226833917728554871951

theorem tailTrace_479950 : CollatzResearch.WordTrace tailWord_479950 prefixEnd_479950 16226833917728554871951 := by
  unfold tailWord_479950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188151826403824222403663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11670143074153729186152869 2188151826403824222403663)
  ·
    refine ⟨3282227739605736333605495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188151826403824222403663 3282227739605736333605495)
    ·
      refine ⟨4923341609408604500408243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282227739605736333605495 4923341609408604500408243)
      ·
        refine ⟨7385012414112906750612365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923341609408604500408243 7385012414112906750612365)
        ·
          refine ⟨2769379655292340031479637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7385012414112906750612365 2769379655292340031479637)
          ·
            refine ⟨16226833917728554871951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2769379655292340031479637 16226833917728554871951)
            ·
              rfl

theorem cell19_479950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_479950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479950 prefixEnd_479950 := by exact prefixLift 479950
  have htrace : WordTrace (prefixWord ++ tailWord_479950) baseStart_479950 baseEnd_479950 := by
    simpa [prefixWord, tailWord_479950, baseEnd_479950] using wordTrace_append hprefix tailTrace_479950
  have hstable : (prefixWord ++ tailWord_479950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479950).length < 2 ^ (prefixWord ++ tailWord_479950).sum := by decide
  have hdescent : baseEnd_479950 < baseStart_479950 := by decide
  rcases family_descends (prefixWord ++ tailWord_479950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479967 : List Nat := [1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_479967 : Nat := 118140960795 + 479967 * 2 ^ 59
def prefixEnd_479967 : Nat := 4983230072969 + 3 ^ 40 * 479967 * 2
def baseEnd_479967 : Nat := 146046678101705991469735

theorem tailTrace_479967 : CollatzResearch.WordTrace tailWord_479967 prefixEnd_479967 146046678101705991469735 := by
  unfold tailWord_479967
  simp only [CollatzResearch.WordTrace]
  refine ⟨17505834652169005682598155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11670556434779337121732103 17505834652169005682598155)
  ·
    refine ⟨26258751978253508523897233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17505834652169005682598155 26258751978253508523897233)
    ·
      refine ⟨19694063983690131392922925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26258751978253508523897233 19694063983690131392922925)
      ·
        refine ⟨7385273993883799272346097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19694063983690131392922925 7385273993883799272346097)
        ·
          refine ⟨5538955495412849454259573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7385273993883799272346097 5538955495412849454259573)
          ·
            refine ⟨519277077694954636336835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5538955495412849454259573 519277077694954636336835)
            ·
              refine ⟨778915616542431954505253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519277077694954636336835 778915616542431954505253)
              ·
                refine ⟨146046678101705991469735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778915616542431954505253 146046678101705991469735)
                ·
                  rfl

theorem cell19_479967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_479967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_479967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_479967 prefixEnd_479967 := by exact prefixLift 479967
  have htrace : WordTrace (prefixWord ++ tailWord_479967) baseStart_479967 baseEnd_479967 := by
    simpa [prefixWord, tailWord_479967, baseEnd_479967] using wordTrace_append hprefix tailTrace_479967
  have hstable : (prefixWord ++ tailWord_479967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479967).length < 2 ^ (prefixWord ++ tailWord_479967).sum := by decide
  have hdescent : baseEnd_479967 < baseStart_479967 := by decide
  rcases family_descends (prefixWord ++ tailWord_479967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480026 : List Nat := [3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_480026 : Nat := 118140960795 + 480026 * 2 ^ 59
def prefixEnd_480026 : Nat := 4983230072969 + 3 ^ 40 * 480026 * 2
def baseEnd_480026 : Nat := 146064630906811336158463

theorem tailTrace_480026 : CollatzResearch.WordTrace tailWord_480026 prefixEnd_480026 146064630906811336158463 := by
  unfold tailWord_480026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376996639738814689748983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11671991039303505839330621 4376996639738814689748983)
  ·
    refine ⟨6565494959608222034623475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4376996639738814689748983 6565494959608222034623475)
    ·
      refine ⟨9848242439412333051935213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565494959608222034623475 9848242439412333051935213)
      ·
        refine ⟨3693090914779624894475705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9848242439412333051935213 3693090914779624894475705)
        ·
          refine ⟨2769818186084718670856779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693090914779624894475705 2769818186084718670856779)
          ·
            refine ⟨4154727279127078006285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769818186084718670856779 4154727279127078006285169)
            ·
              refine ⟨3116045459345308504713877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154727279127078006285169 3116045459345308504713877)
              ·
                refine ⟨146064630906811336158463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3116045459345308504713877 146064630906811336158463)
                ·
                  rfl

theorem cell19_480026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_480026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480026 prefixEnd_480026 := by exact prefixLift 480026
  have htrace : WordTrace (prefixWord ++ tailWord_480026) baseStart_480026 baseEnd_480026 := by
    simpa [prefixWord, tailWord_480026, baseEnd_480026] using wordTrace_append hprefix tailTrace_480026
  have hstable : (prefixWord ++ tailWord_480026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480026).length < 2 ^ (prefixWord ++ tailWord_480026).sum := by decide
  have hdescent : baseEnd_480026 < baseStart_480026 := by decide
  rcases family_descends (prefixWord ++ tailWord_480026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480081 : List Nat := [1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_480081 : Nat := 118140960795 + 480081 * 2 ^ 59
def prefixEnd_480081 : Nat := 4983230072969 + 3 ^ 40 * 480081 * 2
def baseEnd_480081 : Nat := 146081366572587504936091

theorem tailTrace_480081 : CollatzResearch.WordTrace tailWord_480081 prefixEnd_480081 146081366572587504936091 := by
  unfold tailWord_480081
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509992573756003152248097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673328382504002101498731 17509992573756003152248097)
  ·
    refine ⟨13132494430317002364186073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17509992573756003152248097 13132494430317002364186073)
    ·
      refine ⟨9849370822737751773139555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13132494430317002364186073 9849370822737751773139555)
      ·
        refine ⟨14774056234106627659709333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849370822737751773139555 14774056234106627659709333)
        ·
          refine ⟨692533885973748171548875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14774056234106627659709333 692533885973748171548875)
          ·
            refine ⟨1038800828960622257323313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692533885973748171548875 1038800828960622257323313)
            ·
              refine ⟨779100621720466692992485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038800828960622257323313 779100621720466692992485)
              ·
                refine ⟨146081366572587504936091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779100621720466692992485 146081366572587504936091)
                ·
                  rfl

theorem cell19_480081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_480081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480081 prefixEnd_480081 := by exact prefixLift 480081
  have htrace : WordTrace (prefixWord ++ tailWord_480081) baseStart_480081 baseEnd_480081 := by
    simpa [prefixWord, tailWord_480081, baseEnd_480081] using wordTrace_append hprefix tailTrace_480081
  have hstable : (prefixWord ++ tailWord_480081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480081).length < 2 ^ (prefixWord ++ tailWord_480081).sum := by decide
  have hdescent : baseEnd_480081 < baseStart_480081 := by decide
  rcases family_descends (prefixWord ++ tailWord_480081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480138 : List Nat := [3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_480138 : Nat := 118140960795 + 480138 * 2 ^ 59
def prefixEnd_480138 : Nat := 4983230072969 + 3 ^ 40 * 480138 * 2
def baseEnd_480138 : Nat := 146098710808028261669269

theorem tailTrace_480138 : CollatzResearch.WordTrace tailWord_480138 prefixEnd_480138 146098710808028261669269 := by
  unfold tailWord_480138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378017883637375471768267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11674714356366334591382045 4378017883637375471768267)
  ·
    refine ⟨6567026825456063207652401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378017883637375471768267 6567026825456063207652401)
    ·
      refine ⟨4925270119092047405739301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6567026825456063207652401 4925270119092047405739301)
      ·
        refine ⟨923488147329758888576119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4925270119092047405739301 923488147329758888576119)
        ·
          refine ⟨1385232220994638332864179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923488147329758888576119 1385232220994638332864179)
          ·
            refine ⟨2077848331491957499296269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385232220994638332864179 2077848331491957499296269)
            ·
              refine ⟨779193124309484062236101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077848331491957499296269 779193124309484062236101)
              ·
                refine ⟨146098710808028261669269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779193124309484062236101 146098710808028261669269)
                ·
                  rfl

theorem cell19_480138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_480138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480138 prefixEnd_480138 := by exact prefixLift 480138
  have htrace : WordTrace (prefixWord ++ tailWord_480138) baseStart_480138 baseEnd_480138 := by
    simpa [prefixWord, tailWord_480138, baseEnd_480138] using wordTrace_append hprefix tailTrace_480138
  have hstable : (prefixWord ++ tailWord_480138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480138).length < 2 ^ (prefixWord ++ tailWord_480138).sum := by decide
  have hdescent : baseEnd_480138 < baseStart_480138 := by decide
  rcases family_descends (prefixWord ++ tailWord_480138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480140 : List Nat := [2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_480140 : Nat := 118140960795 + 480140 * 2 ^ 59
def prefixEnd_480140 : Nat := 4983230072969 + 3 ^ 40 * 480140 * 2
def baseEnd_480140 : Nat := 146099319377692849624819

theorem tailTrace_480140 : CollatzResearch.WordTrace tailWord_480140 prefixEnd_480140 146099319377692849624819 := by
  unfold tailWord_480140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756072240271128114322937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11674762987028170819097249 8756072240271128114322937)
  ·
    refine ⟨6567054180203346085742203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8756072240271128114322937 6567054180203346085742203)
    ·
      refine ⟨9850581270305019128613305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567054180203346085742203 9850581270305019128613305)
      ·
        refine ⟨7387935952728764346459979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9850581270305019128613305 7387935952728764346459979)
        ·
          refine ⟨11081903929093146519689969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387935952728764346459979 11081903929093146519689969)
          ·
            refine ⟨8311427946819859889767477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11081903929093146519689969 8311427946819859889767477)
            ·
              refine ⟨779196370014361864665701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8311427946819859889767477 779196370014361864665701)
              ·
                refine ⟨146099319377692849624819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779196370014361864665701 146099319377692849624819)
                ·
                  rfl

theorem cell19_480140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_480140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480140 prefixEnd_480140 := by exact prefixLift 480140
  have htrace : WordTrace (prefixWord ++ tailWord_480140) baseStart_480140 baseEnd_480140 := by
    simpa [prefixWord, tailWord_480140, baseEnd_480140] using wordTrace_append hprefix tailTrace_480140
  have hstable : (prefixWord ++ tailWord_480140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480140).length < 2 ^ (prefixWord ++ tailWord_480140).sum := by decide
  have hdescent : baseEnd_480140 < baseStart_480140 := by decide
  rcases family_descends (prefixWord ++ tailWord_480140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480157 : List Nat := [1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_480157 : Nat := 118140960795 + 480157 * 2 ^ 59
def prefixEnd_480157 : Nat := 4983230072969 + 3 ^ 40 * 480157 * 2
def baseEnd_480157 : Nat := 146104492219841847246995

theorem tailTrace_480157 : CollatzResearch.WordTrace tailWord_480157 prefixEnd_480157 146104492219841847246995 := by
  unfold tailWord_480157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512764521480668132014725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11675176347653778754676483 17512764521480668132014725)
  ·
    refine ⟨3283643347777625274752761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17512764521480668132014725 3283643347777625274752761)
    ·
      refine ⟨2462732510833218956064571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283643347777625274752761 2462732510833218956064571)
      ·
        refine ⟨3694098766249828434096857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462732510833218956064571 3694098766249828434096857)
        ·
          refine ⟨2770574074687371325572643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694098766249828434096857 2770574074687371325572643)
          ·
            refine ⟨4155861112031056988358965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770574074687371325572643 4155861112031056988358965)
            ·
              refine ⟨389611979252911592658653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4155861112031056988358965 389611979252911592658653)
              ·
                refine ⟨146104492219841847246995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389611979252911592658653 146104492219841847246995)
                ·
                  rfl

theorem cell19_480157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_480157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480157 prefixEnd_480157 := by exact prefixLift 480157
  have htrace : WordTrace (prefixWord ++ tailWord_480157) baseStart_480157 baseEnd_480157 := by
    simpa [prefixWord, tailWord_480157, baseEnd_480157] using wordTrace_append hprefix tailTrace_480157
  have hstable : (prefixWord ++ tailWord_480157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480157).length < 2 ^ (prefixWord ++ tailWord_480157).sum := by decide
  have hdescent : baseEnd_480157 < baseStart_480157 := by decide
  rcases family_descends (prefixWord ++ tailWord_480157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480212 : List Nat := [2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_480212 : Nat := 118140960795 + 480212 * 2 ^ 59
def prefixEnd_480212 : Nat := 4983230072969 + 3 ^ 40 * 480212 * 2
def baseEnd_480212 : Nat := 146121227885618016024623

theorem tailTrace_480212 : CollatzResearch.WordTrace tailWord_480212 prefixEnd_480212 146121227885618016024623 := by
  unfold tailWord_480212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757385268140706262633445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11676513690854275016844593 8757385268140706262633445)
  ·
    refine ⟨1642009737776382424243771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8757385268140706262633445 1642009737776382424243771)
    ·
      refine ⟨2463014606664573636365657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642009737776382424243771 2463014606664573636365657)
      ·
        refine ⟨1847260954998430227274243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2463014606664573636365657 1847260954998430227274243)
        ·
          refine ⟨2770891432497645340911365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847260954998430227274243 2770891432497645340911365)
          ·
            refine ⟨519542143593308501420881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2770891432497645340911365 519542143593308501420881)
            ·
              refine ⟨389656607694981376065661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519542143593308501420881 389656607694981376065661)
              ·
                refine ⟨146121227885618016024623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389656607694981376065661 146121227885618016024623)
                ·
                  rfl

theorem cell19_480212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_480212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480212 prefixEnd_480212 := by exact prefixLift 480212
  have htrace : WordTrace (prefixWord ++ tailWord_480212) baseStart_480212 baseEnd_480212 := by
    simpa [prefixWord, tailWord_480212, baseEnd_480212] using wordTrace_append hprefix tailTrace_480212
  have hstable : (prefixWord ++ tailWord_480212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480212).length < 2 ^ (prefixWord ++ tailWord_480212).sum := by decide
  have hdescent : baseEnd_480212 < baseStart_480212 := by decide
  rcases family_descends (prefixWord ++ tailWord_480212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480216 : List Nat := [2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_480216 : Nat := 118140960795 + 480216 * 2 ^ 59
def prefixEnd_480216 : Nat := 4983230072969 + 3 ^ 40 * 480216 * 2
def baseEnd_480216 : Nat := 146122445024947191935723

theorem tailTrace_480216 : CollatzResearch.WordTrace tailWord_480216 prefixEnd_480216 146122445024947191935723 := by
  unfold tailWord_480216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757458214133460604206251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11676610952177947472275001 8757458214133460604206251)
  ·
    refine ⟨13136187321200190906309377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8757458214133460604206251 13136187321200190906309377)
    ·
      refine ⟨9852140490900143179732033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13136187321200190906309377 9852140490900143179732033)
      ·
        refine ⟨7389105368175107384799025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9852140490900143179732033 7389105368175107384799025)
        ·
          refine ⟨5541829026131330538599269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389105368175107384799025 5541829026131330538599269)
          ·
            refine ⟨1039092942399624475987363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5541829026131330538599269 1039092942399624475987363)
            ·
              refine ⟨1558639413599436713981045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039092942399624475987363 1558639413599436713981045)
              ·
                refine ⟨146122445024947191935723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1558639413599436713981045 146122445024947191935723)
                ·
                  rfl

theorem cell19_480216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_480216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480216 prefixEnd_480216 := by exact prefixLift 480216
  have htrace : WordTrace (prefixWord ++ tailWord_480216) baseStart_480216 baseEnd_480216 := by
    simpa [prefixWord, tailWord_480216, baseEnd_480216] using wordTrace_append hprefix tailTrace_480216
  have hstable : (prefixWord ++ tailWord_480216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480216).length < 2 ^ (prefixWord ++ tailWord_480216).sum := by decide
  have hdescent : baseEnd_480216 < baseStart_480216 := by decide
  rcases family_descends (prefixWord ++ tailWord_480216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480292 : List Nat := [2, 3, 1, 4, 1, 8]
def baseStart_480292 : Nat := 118140960795 + 480292 * 2 ^ 59
def prefixEnd_480292 : Nat := 4983230072969 + 3 ^ 40 * 480292 * 2
def baseEnd_480292 : Nat := 16238396741355726027403

theorem tailTrace_480292 : CollatzResearch.WordTrace tailWord_480292 prefixEnd_480292 16238396741355726027403 := by
  unfold tailWord_480292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758844187995793094089565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11678458917327724125452753 8758844187995793094089565)
  ·
    refine ⟨3284566570498422410283587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8758844187995793094089565 3284566570498422410283587)
    ·
      refine ⟨4926849855747633615425381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284566570498422410283587 4926849855747633615425381)
      ·
        refine ⟨923784347952681302892259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4926849855747633615425381 923784347952681302892259)
        ·
          refine ⟨1385676521929021954338389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923784347952681302892259 1385676521929021954338389)
          ·
            refine ⟨16238396741355726027403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1385676521929021954338389 16238396741355726027403)
            ·
              rfl

theorem cell19_480292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_480292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480292 prefixEnd_480292 := by exact prefixLift 480292
  have htrace : WordTrace (prefixWord ++ tailWord_480292) baseStart_480292 baseEnd_480292 := by
    simpa [prefixWord, tailWord_480292, baseEnd_480292] using wordTrace_append hprefix tailTrace_480292
  have hstable : (prefixWord ++ tailWord_480292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480292).length < 2 ^ (prefixWord ++ tailWord_480292).sum := by decide
  have hdescent : baseEnd_480292 < baseStart_480292 := by decide
  rcases family_descends (prefixWord ++ tailWord_480292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480351 : List Nat := [1, 1, 2, 3, 1, 1, 10]
def baseStart_480351 : Nat := 118140960795 + 480351 * 2 ^ 59
def prefixEnd_480351 : Nat := 4983230072969 + 3 ^ 40 * 480351 * 2
def baseEnd_480351 : Nat := 48721174492435626311785

theorem tailTrace_480351 : CollatzResearch.WordTrace tailWord_480351 prefixEnd_480351 48721174492435626311785 := by
  unfold tailWord_480351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519840282777839264576907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11679893521851892843051271 17519840282777839264576907)
  ·
    refine ⟨26279760424166758896865361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17519840282777839264576907 26279760424166758896865361)
    ·
      refine ⟨19709820318125069172649021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26279760424166758896865361 19709820318125069172649021)
      ·
        refine ⟨7391182619296900939743383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19709820318125069172649021 7391182619296900939743383)
        ·
          refine ⟨11086773928945351409615075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391182619296900939743383 11086773928945351409615075)
          ·
            refine ⟨16630160893418027114422613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086773928945351409615075 16630160893418027114422613)
            ·
              refine ⟨48721174492435626311785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16630160893418027114422613 48721174492435626311785)
              ·
                rfl

theorem cell19_480351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_480351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480351 prefixEnd_480351 := by exact prefixLift 480351
  have htrace : WordTrace (prefixWord ++ tailWord_480351) baseStart_480351 baseEnd_480351 := by
    simpa [prefixWord, tailWord_480351, baseEnd_480351] using wordTrace_append hprefix tailTrace_480351
  have hstable : (prefixWord ++ tailWord_480351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480351).length < 2 ^ (prefixWord ++ tailWord_480351).sum := by decide
  have hdescent : baseEnd_480351 < baseStart_480351 := by decide
  rcases family_descends (prefixWord ++ tailWord_480351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480385 : List Nat := [1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_480385 : Nat := 118140960795 + 480385 * 2 ^ 59
def prefixEnd_480385 : Nat := 4983230072969 + 3 ^ 40 * 480385 * 2
def baseEnd_480385 : Nat := 146173869161604874179707

theorem tailTrace_480385 : CollatzResearch.WordTrace tailWord_480385 prefixEnd_480385 146173869161604874179707 := by
  unfold tailWord_480385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521080364654663071314609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11680720243103108714209739 17521080364654663071314609)
  ·
    refine ⟨13140810273490997303485957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17521080364654663071314609 13140810273490997303485957)
    ·
      refine ⟨2463901926279561994403617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13140810273490997303485957 2463901926279561994403617)
      ·
        refine ⟨1847926444709671495802713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2463901926279561994403617 1847926444709671495802713)
        ·
          refine ⟨1385944833532253621852035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847926444709671495802713 1385944833532253621852035)
          ·
            refine ⟨2078917250298380432778053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385944833532253621852035 2078917250298380432778053)
            ·
              refine ⟨389796984430946331145885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2078917250298380432778053 389796984430946331145885)
              ·
                refine ⟨146173869161604874179707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389796984430946331145885 146173869161604874179707)
                ·
                  rfl

theorem cell19_480385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_480385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480385 prefixEnd_480385 := by exact prefixLift 480385
  have htrace : WordTrace (prefixWord ++ tailWord_480385) baseStart_480385 baseEnd_480385 := by
    simpa [prefixWord, tailWord_480385, baseEnd_480385] using wordTrace_append hprefix tailTrace_480385
  have hstable : (prefixWord ++ tailWord_480385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480385).length < 2 ^ (prefixWord ++ tailWord_480385).sum := by decide
  have hdescent : baseEnd_480385 < baseStart_480385 := by decide
  rcases family_descends (prefixWord ++ tailWord_480385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480423 : List Nat := [1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_480423 : Nat := 118140960795 + 480423 * 2 ^ 59
def prefixEnd_480423 : Nat := 4983230072969 + 3 ^ 40 * 480423 * 2
def baseEnd_480423 : Nat := 146185431985232045335159

theorem tailTrace_480423 : CollatzResearch.WordTrace tailWord_480423 prefixEnd_480423 146185431985232045335159 := by
  unfold tailWord_480423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522466338516995561197923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11681644225677997040798615 17522466338516995561197923)
  ·
    refine ⟨26283699507775493341796885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17522466338516995561197923 26283699507775493341796885)
    ·
      refine ⟨1232048414426976250396729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26283699507775493341796885 1232048414426976250396729)
      ·
        refine ⟨924036310820232187797547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232048414426976250396729 924036310820232187797547)
        ·
          refine ⟨1386054466230348281696321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924036310820232187797547 1386054466230348281696321)
          ·
            refine ⟨1039540849672761211272241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386054466230348281696321 1039540849672761211272241)
            ·
              refine ⟨779655637254570908454181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039540849672761211272241 779655637254570908454181)
              ·
                refine ⟨146185431985232045335159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779655637254570908454181 146185431985232045335159)
                ·
                  rfl

theorem cell19_480423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_480423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480423 prefixEnd_480423 := by exact prefixLift 480423
  have htrace : WordTrace (prefixWord ++ tailWord_480423) baseStart_480423 baseEnd_480423 := by
    simpa [prefixWord, tailWord_480423, baseEnd_480423] using wordTrace_append hprefix tailTrace_480423
  have hstable : (prefixWord ++ tailWord_480423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480423).length < 2 ^ (prefixWord ++ tailWord_480423).sum := by decide
  have hdescent : baseEnd_480423 < baseStart_480423 := by decide
  rcases family_descends (prefixWord ++ tailWord_480423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480444 : List Nat := [2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_480444 : Nat := 118140960795 + 480444 * 2 ^ 59
def prefixEnd_480444 : Nat := 4983230072969 + 3 ^ 40 * 480444 * 2
def baseEnd_480444 : Nat := 146191821966710218868435

theorem tailTrace_480444 : CollatzResearch.WordTrace tailWord_480444 prefixEnd_480444 146191821966710218868435 := by
  unfold tailWord_480444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761616135720458073856193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11682154847627277431808257 8761616135720458073856193)
  ·
    refine ⟨6571212101790343555392145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8761616135720458073856193 6571212101790343555392145)
    ·
      refine ⟨4928409076342757666544109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6571212101790343555392145 4928409076342757666544109)
      ·
        refine ⟨1848153403628534124954041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4928409076342757666544109 1848153403628534124954041)
        ·
          refine ⟨1386115052721400593715531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848153403628534124954041 1386115052721400593715531)
          ·
            refine ⟨2079172579082100890573297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386115052721400593715531 2079172579082100890573297)
            ·
              refine ⟨1559379434311575667929973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079172579082100890573297 1559379434311575667929973)
              ·
                refine ⟨146191821966710218868435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1559379434311575667929973 146191821966710218868435)
                ·
                  rfl

theorem cell19_480444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_480444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480444 prefixEnd_480444 := by exact prefixLift 480444
  have htrace : WordTrace (prefixWord ++ tailWord_480444) baseStart_480444 baseEnd_480444 := by
    simpa [prefixWord, tailWord_480444, baseEnd_480444] using wordTrace_append hprefix tailTrace_480444
  have hstable : (prefixWord ++ tailWord_480444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480444).length < 2 ^ (prefixWord ++ tailWord_480444).sum := by decide
  have hdescent : baseEnd_480444 < baseStart_480444 := by decide
  rcases family_descends (prefixWord ++ tailWord_480444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480461 : List Nat := [1, 6, 2, 2, 8]
def baseStart_480461 : Nat := 118140960795 + 480461 * 2 ^ 59
def prefixEnd_480461 : Nat := 4983230072969 + 3 ^ 40 * 480461 * 2
def baseEnd_480461 : Nat := 5414703511439230240393

theorem tailTrace_480461 : CollatzResearch.WordTrace tailWord_480461 prefixEnd_480461 5414703511439230240393 := by
  unfold tailWord_480461
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523852312379328051081237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11682568208252885367387491 17523852312379328051081237)
  ·
    refine ⟨821430577142781002394433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17523852312379328051081237 821430577142781002394433)
    ·
      refine ⟨616072932857085751795825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 821430577142781002394433 616072932857085751795825)
      ·
        refine ⟨462054699642814313846869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616072932857085751795825 462054699642814313846869)
        ·
          refine ⟨5414703511439230240393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 462054699642814313846869 5414703511439230240393)
          ·
            rfl

theorem cell19_480461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_480461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480461 prefixEnd_480461 := by exact prefixLift 480461
  have htrace : WordTrace (prefixWord ++ tailWord_480461) baseStart_480461 baseEnd_480461 := by
    simpa [prefixWord, tailWord_480461, baseEnd_480461] using wordTrace_append hprefix tailTrace_480461
  have hstable : (prefixWord ++ tailWord_480461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480461).length < 2 ^ (prefixWord ++ tailWord_480461).sum := by decide
  have hdescent : baseEnd_480461 < baseStart_480461 := by decide
  rcases family_descends (prefixWord ++ tailWord_480461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480520 : List Nat := [2, 1, 3, 2, 4, 1, 6]
def baseStart_480520 : Nat := 118140960795 + 480520 * 2 ^ 59
def prefixEnd_480520 : Nat := 4983230072969 + 3 ^ 40 * 480520 * 2
def baseEnd_480520 : Nat := 48738315871321520393113

theorem tailTrace_480520 : CollatzResearch.WordTrace tailWord_480520 prefixEnd_480520 48738315871321520393113 := by
  unfold tailWord_480520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763002109582790563739507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11684002812777054084986009 8763002109582790563739507)
  ·
    refine ⟨13144503164374185845609261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763002109582790563739507 13144503164374185845609261)
    ·
      refine ⟨4929188686640319692103473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13144503164374185845609261 4929188686640319692103473)
      ·
        refine ⟨3696891514980239769077605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929188686640319692103473 3696891514980239769077605)
        ·
          refine ⟨693167159058794956702051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3696891514980239769077605 693167159058794956702051)
          ·
            refine ⟨1039750738588192435053077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693167159058794956702051 1039750738588192435053077)
            ·
              refine ⟨48738315871321520393113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1039750738588192435053077 48738315871321520393113)
              ·
                rfl

theorem cell19_480520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_480520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480520 prefixEnd_480520 := by exact prefixLift 480520
  have htrace : WordTrace (prefixWord ++ tailWord_480520) baseStart_480520 baseEnd_480520 := by
    simpa [prefixWord, tailWord_480520, baseEnd_480520] using wordTrace_append hprefix tailTrace_480520
  have hstable : (prefixWord ++ tailWord_480520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480520).length < 2 ^ (prefixWord ++ tailWord_480520).sum := by decide
  have hdescent : baseEnd_480520 < baseStart_480520 := by decide
  rcases family_descends (prefixWord ++ tailWord_480520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480554 : List Nat := [3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_480554 : Nat := 118140960795 + 480554 * 2 ^ 59
def prefixEnd_480554 : Nat := 4983230072969 + 3 ^ 40 * 480554 * 2
def baseEnd_480554 : Nat := 146225293298262556423691

theorem tailTrace_480554 : CollatzResearch.WordTrace tailWord_480554 prefixEnd_480554 146225293298262556423691 := by
  unfold tailWord_480554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381811075260601233554179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11684829534028269956144477 4381811075260601233554179)
  ·
    refine ⟨6572716612890901850331269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4381811075260601233554179 6572716612890901850331269)
    ·
      refine ⟨1232384364917044096937113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6572716612890901850331269 1232384364917044096937113)
      ·
        refine ⟨924288273687783072702835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232384364917044096937113 924288273687783072702835)
        ·
          refine ⟨1386432410531674609054253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924288273687783072702835 1386432410531674609054253)
          ·
            refine ⟨519912153949377978395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1386432410531674609054253 519912153949377978395345)
            ·
              refine ⟨389934115462033483796509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519912153949377978395345 389934115462033483796509)
              ·
                refine ⟨146225293298262556423691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389934115462033483796509 146225293298262556423691)
                ·
                  rfl

theorem cell19_480554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_480554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480554 prefixEnd_480554 := by exact prefixLift 480554
  have htrace : WordTrace (prefixWord ++ tailWord_480554) baseStart_480554 baseEnd_480554 := by
    simpa [prefixWord, tailWord_480554, baseEnd_480554] using wordTrace_append hprefix tailTrace_480554
  have hstable : (prefixWord ++ tailWord_480554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480554).length < 2 ^ (prefixWord ++ tailWord_480554).sum := by decide
  have hdescent : baseEnd_480554 < baseStart_480554 := by decide
  rcases family_descends (prefixWord ++ tailWord_480554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480560 : List Nat := [2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_480560 : Nat := 118140960795 + 480560 * 2 ^ 59
def prefixEnd_480560 : Nat := 4983230072969 + 3 ^ 40 * 480560 * 2
def baseEnd_480560 : Nat := 146227119007256320290341

theorem tailTrace_480560 : CollatzResearch.WordTrace tailWord_480560 prefixEnd_480560 146227119007256320290341 := by
  unfold tailWord_480560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763731569510333979467567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11684975426013778639290089 8763731569510333979467567)
  ·
    refine ⟨13145597354265500969201351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763731569510333979467567 13145597354265500969201351)
    ·
      refine ⟨19718396031398251453802027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145597354265500969201351 19718396031398251453802027)
      ·
        refine ⟨29577594047097377180703041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19718396031398251453802027 29577594047097377180703041)
        ·
          refine ⟨22183195535323032885527281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29577594047097377180703041 22183195535323032885527281)
          ·
            refine ⟨16637396651492274664145461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22183195535323032885527281 16637396651492274664145461)
            ·
              refine ⟨1559755936077400749763637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16637396651492274664145461 1559755936077400749763637)
              ·
                refine ⟨146227119007256320290341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1559755936077400749763637 146227119007256320290341)
                ·
                  rfl

theorem cell19_480560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_480560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480560 prefixEnd_480560 := by exact prefixLift 480560
  have htrace : WordTrace (prefixWord ++ tailWord_480560) baseStart_480560 baseEnd_480560 := by
    simpa [prefixWord, tailWord_480560, baseEnd_480560] using wordTrace_append hprefix tailTrace_480560
  have hstable : (prefixWord ++ tailWord_480560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480560).length < 2 ^ (prefixWord ++ tailWord_480560).sum := by decide
  have hdescent : baseEnd_480560 < baseStart_480560 := by decide
  rcases family_descends (prefixWord ++ tailWord_480560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480573 : List Nat := [1, 4, 1, 5, 2, 1, 5]
def baseStart_480573 : Nat := 118140960795 + 480573 * 2 ^ 59
def prefixEnd_480573 : Nat := 4983230072969 + 3 ^ 40 * 480573 * 2
def baseEnd_480573 : Nat := 48743691570025380667139

theorem tailTrace_480573 : CollatzResearch.WordTrace tailWord_480573 prefixEnd_480573 48743691570025380667139 := by
  unfold tailWord_480573
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527937287973571179158373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11685291525315714119438915 17527937287973571179158373)
  ·
    refine ⟨3286488241495044596092195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17527937287973571179158373 3286488241495044596092195)
    ·
      refine ⟨4929732362242566894138293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286488241495044596092195 4929732362242566894138293)
      ·
        refine ⟨462162408960240646325465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4929732362242566894138293 462162408960240646325465)
        ·
          refine ⟨346621806720180484744099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462162408960240646325465 346621806720180484744099)
          ·
            refine ⟨519932710080270727116149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346621806720180484744099 519932710080270727116149)
            ·
              refine ⟨48743691570025380667139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519932710080270727116149 48743691570025380667139)
              ·
                rfl

theorem cell19_480573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_480573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480573 prefixEnd_480573 := by exact prefixLift 480573
  have htrace : WordTrace (prefixWord ++ tailWord_480573) baseStart_480573 baseEnd_480573 := by
    simpa [prefixWord, tailWord_480573, baseEnd_480573] using wordTrace_append hprefix tailTrace_480573
  have hstable : (prefixWord ++ tailWord_480573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480573).length < 2 ^ (prefixWord ++ tailWord_480573).sum := by decide
  have hdescent : baseEnd_480573 < baseStart_480573 := by decide
  rcases family_descends (prefixWord ++ tailWord_480573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480577 : List Nat := [1, 2, 5, 2, 1, 1, 7]
def baseStart_480577 : Nat := 118140960795 + 480577 * 2 ^ 59
def prefixEnd_480577 : Nat := 4983230072969 + 3 ^ 40 * 480577 * 2
def baseEnd_480577 : Nat := 48744097283135105970839

theorem tailTrace_480577 : CollatzResearch.WordTrace tailWord_480577 prefixEnd_480577 48744097283135105970839 := by
  unfold tailWord_480577
  simp only [CollatzResearch.WordTrace]
  refine ⟨17528083179959079862303985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11685388786639386574869323 17528083179959079862303985)
  ·
    refine ⟨13146062384969309896727989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17528083179959079862303985 13146062384969309896727989)
    ·
      refine ⟨1232443348590872802818249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13146062384969309896727989 1232443348590872802818249)
      ·
        refine ⟨924332511443154602113687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232443348590872802818249 924332511443154602113687)
        ·
          refine ⟨1386498767164731903170531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924332511443154602113687 1386498767164731903170531)
          ·
            refine ⟨2079748150747097854755797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386498767164731903170531 2079748150747097854755797)
            ·
              refine ⟨48744097283135105970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2079748150747097854755797 48744097283135105970839)
              ·
                rfl

theorem cell19_480577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_480577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480577 prefixEnd_480577 := by exact prefixLift 480577
  have htrace : WordTrace (prefixWord ++ tailWord_480577) baseStart_480577 baseEnd_480577 := by
    simpa [prefixWord, tailWord_480577, baseEnd_480577] using wordTrace_append hprefix tailTrace_480577
  have hstable : (prefixWord ++ tailWord_480577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480577).length < 2 ^ (prefixWord ++ tailWord_480577).sum := by decide
  have hdescent : baseEnd_480577 < baseStart_480577 := by decide
  rcases family_descends (prefixWord ++ tailWord_480577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480596 : List Nat := [2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_480596 : Nat := 118140960795 + 480596 * 2 ^ 59
def prefixEnd_480596 : Nat := 4983230072969 + 3 ^ 40 * 480596 * 2
def baseEnd_480596 : Nat := 146238073261218903490243

theorem tailTrace_480596 : CollatzResearch.WordTrace tailWord_480596 prefixEnd_480596 146238073261218903490243 := by
  unfold tailWord_480596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764388083445123053622821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11685850777926830738163761 8764388083445123053622821)
  ·
    refine ⟨1643322765645960572554279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8764388083445123053622821 1643322765645960572554279)
    ·
      refine ⟨2464984148468940858831419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643322765645960572554279 2464984148468940858831419)
      ·
        refine ⟨3697476222703411288247129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464984148468940858831419 3697476222703411288247129)
        ·
          refine ⟨2773107167027558466185347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697476222703411288247129 2773107167027558466185347)
          ·
            refine ⟨4159660750541337699278021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773107167027558466185347 4159660750541337699278021)
            ·
              refine ⟨779936390726500818614629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4159660750541337699278021 779936390726500818614629)
              ·
                refine ⟨146238073261218903490243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779936390726500818614629 146238073261218903490243)
                ·
                  rfl

theorem cell19_480596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_480596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480596 prefixEnd_480596 := by exact prefixLift 480596
  have htrace : WordTrace (prefixWord ++ tailWord_480596) baseStart_480596 baseEnd_480596 := by
    simpa [prefixWord, tailWord_480596, baseEnd_480596] using wordTrace_append hprefix tailTrace_480596
  have hstable : (prefixWord ++ tailWord_480596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480596).length < 2 ^ (prefixWord ++ tailWord_480596).sum := by decide
  have hdescent : baseEnd_480596 < baseStart_480596 := by decide
  rcases family_descends (prefixWord ++ tailWord_480596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480668 : List Nat := [2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_480668 : Nat := 118140960795 + 480668 * 2 ^ 59
def prefixEnd_480668 : Nat := 4983230072969 + 3 ^ 40 * 480668 * 2
def baseEnd_480668 : Nat := 146259981769144069890047

theorem tailTrace_480668 : CollatzResearch.WordTrace tailWord_480668 prefixEnd_480668 146259981769144069890047 := by
  unfold tailWord_480668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765701111314701201933329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687601481752934935911105 8765701111314701201933329)
  ·
    refine ⟨6574275833486025901449997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8765701111314701201933329 6574275833486025901449997)
    ·
      refine ⟨2465353437557259713043749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6574275833486025901449997 2465353437557259713043749)
      ·
        refine ⟨462253769541986196195703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2465353437557259713043749 462253769541986196195703)
        ·
          refine ⟨693380654312979294293555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462253769541986196195703 693380654312979294293555)
          ·
            refine ⟨1040070981469468941440333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693380654312979294293555 1040070981469468941440333)
            ·
              refine ⟨390026618051050853040125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040070981469468941440333 390026618051050853040125)
              ·
                refine ⟨146259981769144069890047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390026618051050853040125 146259981769144069890047)
                ·
                  rfl

theorem cell19_480668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_480668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480668 prefixEnd_480668 := by exact prefixLift 480668
  have htrace : WordTrace (prefixWord ++ tailWord_480668) baseStart_480668 baseEnd_480668 := by
    simpa [prefixWord, tailWord_480668, baseEnd_480668] using wordTrace_append hprefix tailTrace_480668
  have hstable : (prefixWord ++ tailWord_480668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480668).length < 2 ^ (prefixWord ++ tailWord_480668).sum := by decide
  have hdescent : baseEnd_480668 < baseStart_480668 := by decide
  rcases family_descends (prefixWord ++ tailWord_480668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480672 : List Nat := [2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_480672 : Nat := 118140960795 + 480672 * 2 ^ 59
def prefixEnd_480672 : Nat := 4983230072969 + 3 ^ 40 * 480672 * 2
def baseEnd_480672 : Nat := 146261198908473245801147

theorem tailTrace_480672 : CollatzResearch.WordTrace tailWord_480672 prefixEnd_480672 146261198908473245801147 := by
  unfold tailWord_480672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765774057307455543506135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687698743076607391341513 8765774057307455543506135)
  ·
    refine ⟨13148661085961183315259203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765774057307455543506135 13148661085961183315259203)
    ·
      refine ⟨19722991628941774972888805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148661085961183315259203 19722991628941774972888805)
      ·
        refine ⟨3698060930426582807416651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19722991628941774972888805 3698060930426582807416651)
        ·
          refine ⟨5547091395639874211124977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698060930426582807416651 5547091395639874211124977)
          ·
            refine ⟨4160318546729905658343733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547091395639874211124977 4160318546729905658343733)
            ·
              refine ⟨390029863755928655469725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4160318546729905658343733 390029863755928655469725)
              ·
                refine ⟨146261198908473245801147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390029863755928655469725 146261198908473245801147)
                ·
                  rfl

theorem cell19_480672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_480672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480672 prefixEnd_480672 := by exact prefixLift 480672
  have htrace : WordTrace (prefixWord ++ tailWord_480672) baseStart_480672 baseEnd_480672 := by
    simpa [prefixWord, tailWord_480672, baseEnd_480672] using wordTrace_append hprefix tailTrace_480672
  have hstable : (prefixWord ++ tailWord_480672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480672).length < 2 ^ (prefixWord ++ tailWord_480672).sum := by decide
  have hdescent : baseEnd_480672 < baseStart_480672 := by decide
  rcases family_descends (prefixWord ++ tailWord_480672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480712 : List Nat := [2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_480712 : Nat := 118140960795 + 480712 * 2 ^ 59
def prefixEnd_480712 : Nat := 4983230072969 + 3 ^ 40 * 480712 * 2
def baseEnd_480712 : Nat := 146273370301765004912149

theorem tailTrace_480712 : CollatzResearch.WordTrace tailWord_480712 prefixEnd_480712 146273370301765004912149 := by
  unfold tailWord_480712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766503517234998959234195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11688671356313331945645593 8766503517234998959234195)
  ·
    refine ⟨13149755275852498438851293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8766503517234998959234195 13149755275852498438851293)
    ·
      refine ⟨4931158228444686914569235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13149755275852498438851293 4931158228444686914569235)
      ·
        refine ⟨7396737342667030371853853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931158228444686914569235 7396737342667030371853853)
        ·
          refine ⟨2773776503500136389445195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7396737342667030371853853 2773776503500136389445195)
          ·
            refine ⟨4160664755250204584167793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773776503500136389445195 4160664755250204584167793)
            ·
              refine ⟨3120498566437653438125845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160664755250204584167793 3120498566437653438125845)
              ·
                refine ⟨146273370301765004912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3120498566437653438125845 146273370301765004912149)
                ·
                  rfl

theorem cell19_480712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_480712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480712 prefixEnd_480712 := by exact prefixLift 480712
  have htrace : WordTrace (prefixWord ++ tailWord_480712) baseStart_480712 baseEnd_480712 := by
    simpa [prefixWord, tailWord_480712, baseEnd_480712] using wordTrace_append hprefix tailTrace_480712
  have hstable : (prefixWord ++ tailWord_480712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480712).length < 2 ^ (prefixWord ++ tailWord_480712).sum := by decide
  have hdescent : baseEnd_480712 < baseStart_480712 := by decide
  rcases family_descends (prefixWord ++ tailWord_480712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480729 : List Nat := [1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_480729 : Nat := 118140960795 + 480729 * 2 ^ 59
def prefixEnd_480729 : Nat := 4983230072969 + 3 ^ 40 * 480729 * 2
def baseEnd_480729 : Nat := 146278543143914002534325

theorem tailTrace_480729 : CollatzResearch.WordTrace tailWord_480729 prefixEnd_480729 146278543143914002534325 := by
  unfold tailWord_480729
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533627075408409821837241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11689084716938939881224827 17533627075408409821837241)
  ·
    refine ⟨13150220306556307366377931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17533627075408409821837241 13150220306556307366377931)
    ·
      refine ⟨19725330459834461049566897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13150220306556307366377931 19725330459834461049566897)
      ·
        refine ⟨14793997844875845787175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19725330459834461049566897 14793997844875845787175173)
        ·
          refine ⟨2773874595914221085095345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14793997844875845787175173 2773874595914221085095345)
          ·
            refine ⟨2080405946935665813821509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773874595914221085095345 2080405946935665813821509)
            ·
              refine ⟨390076115050437340091533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2080405946935665813821509 390076115050437340091533)
              ·
                refine ⟨146278543143914002534325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390076115050437340091533 146278543143914002534325)
                ·
                  rfl

theorem cell19_480729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_480729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480729 prefixEnd_480729 := by exact prefixLift 480729
  have htrace : WordTrace (prefixWord ++ tailWord_480729) baseStart_480729 baseEnd_480729 := by
    simpa [prefixWord, tailWord_480729, baseEnd_480729] using wordTrace_append hprefix tailTrace_480729
  have hstable : (prefixWord ++ tailWord_480729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480729).length < 2 ^ (prefixWord ++ tailWord_480729).sum := by decide
  have hdescent : baseEnd_480729 < baseStart_480729 := by decide
  rcases family_descends (prefixWord ++ tailWord_480729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480746 : List Nat := [3, 1, 3, 1, 5, 1, 5]
def baseStart_480746 : Nat := 118140960795 + 480746 * 2 ^ 59
def prefixEnd_480746 : Nat := 4983230072969 + 3 ^ 40 * 480746 * 2
def baseEnd_480746 : Nat := 48761238662021000052167

theorem tailTrace_480746 : CollatzResearch.WordTrace tailWord_480746 prefixEnd_480746 48761238662021000052167 := by
  unfold tailWord_480746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383561779086705431301523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11689498077564547816804061 4383561779086705431301523)
  ·
    refine ⟨6575342668630058146952285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383561779086705431301523 6575342668630058146952285)
    ·
      refine ⟨2465753500736271805107107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6575342668630058146952285 2465753500736271805107107)
      ·
        refine ⟨3698630251104407707660661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465753500736271805107107 3698630251104407707660661)
        ·
          refine ⟨346746586041038222593187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3698630251104407707660661 346746586041038222593187)
          ·
            refine ⟨520119879061557333889781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346746586041038222593187 520119879061557333889781)
            ·
              refine ⟨48761238662021000052167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 520119879061557333889781 48761238662021000052167)
              ·
                rfl

theorem cell19_480746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_480746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480746 prefixEnd_480746 := by exact prefixLift 480746
  have htrace : WordTrace (prefixWord ++ tailWord_480746) baseStart_480746 baseEnd_480746 := by
    simpa [prefixWord, tailWord_480746, baseEnd_480746] using wordTrace_append hprefix tailTrace_480746
  have hstable : (prefixWord ++ tailWord_480746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480746).length < 2 ^ (prefixWord ++ tailWord_480746).sum := by decide
  have hdescent : baseEnd_480746 < baseStart_480746 := by decide
  rcases family_descends (prefixWord ++ tailWord_480746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480807 : List Nat := [1, 1, 7, 10]
def baseStart_480807 : Nat := 118140960795 + 480807 * 2 ^ 59
def prefixEnd_480807 : Nat := 4983230072969 + 3 ^ 40 * 480807 * 2
def baseEnd_480807 : Nat := 1806200955072011516059

theorem tailTrace_480807 : CollatzResearch.WordTrace tailWord_480807 prefixEnd_480807 1806200955072011516059 := by
  unfold tailWord_480807
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536471969125829143176675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11690981312750552762117783 17536471969125829143176675)
  ·
    refine ⟨26304707953688743714765013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17536471969125829143176675 26304707953688743714765013)
    ·
      refine ⟨616516592664579930814805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26304707953688743714765013 616516592664579930814805)
      ·
        refine ⟨1806200955072011516059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 616516592664579930814805 1806200955072011516059)
        ·
          rfl

theorem cell19_480807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 10].length) (baseStart_480807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480807 prefixEnd_480807 := by exact prefixLift 480807
  have htrace : WordTrace (prefixWord ++ tailWord_480807) baseStart_480807 baseEnd_480807 := by
    simpa [prefixWord, tailWord_480807, baseEnd_480807] using wordTrace_append hprefix tailTrace_480807
  have hstable : (prefixWord ++ tailWord_480807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480807).length < 2 ^ (prefixWord ++ tailWord_480807).sum := by decide
  have hdescent : baseEnd_480807 < baseStart_480807 := by decide
  rcases family_descends (prefixWord ++ tailWord_480807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480824 : List Nat := [2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_480824 : Nat := 118140960795 + 480824 * 2 ^ 59
def prefixEnd_480824 : Nat := 4983230072969 + 3 ^ 40 * 480824 * 2
def baseEnd_480824 : Nat := 146307450202981930422955

theorem tailTrace_480824 : CollatzResearch.WordTrace tailWord_480824 prefixEnd_480824 146307450202981930422955 := by
  unfold tailWord_480824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768546005032120523272763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11691394673376160697697017 8768546005032120523272763)
  ·
    refine ⟨13152819007548180784909145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8768546005032120523272763 13152819007548180784909145)
    ·
      refine ⟨9864614255661135588681859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152819007548180784909145 9864614255661135588681859)
      ·
        refine ⟨14796921383491703383022789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864614255661135588681859 14796921383491703383022789)
        ·
          refine ⟨2774422759404694384316773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14796921383491703383022789 2774422759404694384316773)
          ·
            refine ⟨520204267388380197059395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2774422759404694384316773 520204267388380197059395)
            ·
              refine ⟨780306401082570295589093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520204267388380197059395 780306401082570295589093)
              ·
                refine ⟨146307450202981930422955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780306401082570295589093 146307450202981930422955)
                ·
                  rfl

theorem cell19_480824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_480824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480824 prefixEnd_480824 := by exact prefixLift 480824
  have htrace : WordTrace (prefixWord ++ tailWord_480824) baseStart_480824 baseEnd_480824 := by
    simpa [prefixWord, tailWord_480824, baseEnd_480824] using wordTrace_append hprefix tailTrace_480824
  have hstable : (prefixWord ++ tailWord_480824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480824).length < 2 ^ (prefixWord ++ tailWord_480824).sum := by decide
  have hdescent : baseEnd_480824 < baseStart_480824 := by decide
  rcases family_descends (prefixWord ++ tailWord_480824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480900 : List Nat := [2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_480900 : Nat := 118140960795 + 480900 * 2 ^ 59
def prefixEnd_480900 : Nat := 4983230072969 + 3 ^ 40 * 480900 * 2
def baseEnd_480900 : Nat := 146330575850236272733859

theorem tailTrace_480900 : CollatzResearch.WordTrace tailWord_480900 prefixEnd_480900 146330575850236272733859 := by
  unfold tailWord_480900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769931978894453013156077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11693242638525937350874769 8769931978894453013156077)
  ·
    refine ⟨3288724492085419879933529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8769931978894453013156077 3288724492085419879933529)
    ·
      refine ⟨2466543369064064909950147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3288724492085419879933529 2466543369064064909950147)
      ·
        refine ⟨3699815053596097364925221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466543369064064909950147 3699815053596097364925221)
        ·
          refine ⟨693715322549268255923479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3699815053596097364925221 693715322549268255923479)
          ·
            refine ⟨1040572983823902383885219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693715322549268255923479 1040572983823902383885219)
            ·
              refine ⟨1560859475735853575827829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040572983823902383885219 1560859475735853575827829)
              ·
                refine ⟨146330575850236272733859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1560859475735853575827829 146330575850236272733859)
                ·
                  rfl

theorem cell19_480900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_480900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480900 prefixEnd_480900 := by exact prefixLift 480900
  have htrace : WordTrace (prefixWord ++ tailWord_480900) baseStart_480900 baseEnd_480900 := by
    simpa [prefixWord, tailWord_480900, baseEnd_480900] using wordTrace_append hprefix tailTrace_480900
  have hstable : (prefixWord ++ tailWord_480900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480900).length < 2 ^ (prefixWord ++ tailWord_480900).sum := by decide
  have hdescent : baseEnd_480900 < baseStart_480900 := by decide
  rcases family_descends (prefixWord ++ tailWord_480900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480978 : List Nat := [3, 2, 2, 2, 2, 8]
def baseStart_480978 : Nat := 118140960795 + 480978 * 2 ^ 59
def prefixEnd_480978 : Nat := 4983230072969 + 3 ^ 40 * 480978 * 2
def baseEnd_480978 : Nat := 16261590007461689222257

theorem tailTrace_480978 : CollatzResearch.WordTrace tailWord_480978 prefixEnd_480978 16261590007461689222257 := by
  unfold tailWord_480978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385677212876581336912897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11695139234337550231767725 4385677212876581336912897)
  ·
    refine ⟨3289257909657436002684673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4385677212876581336912897 3289257909657436002684673)
    ·
      refine ⟨2466943432243077002013505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3289257909657436002684673 2466943432243077002013505)
      ·
        refine ⟨1850207574182307751510129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466943432243077002013505 1850207574182307751510129)
        ·
          refine ⟨1387655680636730813632597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850207574182307751510129 1387655680636730813632597)
          ·
            refine ⟨16261590007461689222257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1387655680636730813632597 16261590007461689222257)
            ·
              rfl

theorem cell19_480978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_480978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480978 prefixEnd_480978 := by exact prefixLift 480978
  have htrace : WordTrace (prefixWord ++ tailWord_480978) baseStart_480978 baseEnd_480978 := by
    simpa [prefixWord, tailWord_480978, baseEnd_480978] using wordTrace_append hprefix tailTrace_480978
  have hstable : (prefixWord ++ tailWord_480978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480978).length < 2 ^ (prefixWord ++ tailWord_480978).sum := by decide
  have hdescent : baseEnd_480978 < baseStart_480978 := by decide
  rcases family_descends (prefixWord ++ tailWord_480978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480993 : List Nat := [1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_480993 : Nat := 118140960795 + 480993 * 2 ^ 59
def prefixEnd_480993 : Nat := 4983230072969 + 3 ^ 40 * 480993 * 2
def baseEnd_480993 : Nat := 146358874339639612666939

theorem tailTrace_480993 : CollatzResearch.WordTrace tailWord_480993 prefixEnd_480993 146358874339639612666939 := by
  unfold tailWord_480993
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543255946451982909447633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695503964301321939631755 17543255946451982909447633)
  ·
    refine ⟨13157441959838987182085725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17543255946451982909447633 13157441959838987182085725)
    ·
      refine ⟨4934040734939620193282147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13157441959838987182085725 4934040734939620193282147)
      ·
        refine ⟨7401061102409430289923221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934040734939620193282147 7401061102409430289923221)
        ·
          refine ⟨346924739175442044840151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7401061102409430289923221 346924739175442044840151)
          ·
            refine ⟨520387108763163067260227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346924739175442044840151 520387108763163067260227)
            ·
              refine ⟨780580663144744600890341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520387108763163067260227 780580663144744600890341)
              ·
                refine ⟨146358874339639612666939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780580663144744600890341 146358874339639612666939)
                ·
                  rfl

theorem cell19_480993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_480993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_480993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_480993 prefixEnd_480993 := by exact prefixLift 480993
  have htrace : WordTrace (prefixWord ++ tailWord_480993) baseStart_480993 baseEnd_480993 := by
    simpa [prefixWord, tailWord_480993, baseEnd_480993] using wordTrace_append hprefix tailTrace_480993
  have hstable : (prefixWord ++ tailWord_480993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480993).length < 2 ^ (prefixWord ++ tailWord_480993).sum := by decide
  have hdescent : baseEnd_480993 < baseStart_480993 := by decide
  rcases family_descends (prefixWord ++ tailWord_480993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481073 : List Nat := [1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_481073 : Nat := 118140960795 + 481073 * 2 ^ 59
def prefixEnd_481073 : Nat := 4983230072969 + 3 ^ 40 * 481073 * 2
def baseEnd_481073 : Nat := 146383217126223130888943

theorem tailTrace_481073 : CollatzResearch.WordTrace tailWord_481073 prefixEnd_481073 146383217126223130888943 := by
  unfold tailWord_481073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17546173786162156572359873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11697449190774771048239915 17546173786162156572359873)
  ·
    refine ⟨13159630339621617429269905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17546173786162156572359873 13159630339621617429269905)
    ·
      refine ⟨9869722754716213071952429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13159630339621617429269905 9869722754716213071952429)
      ·
        refine ⟨3701146033018579901982161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9869722754716213071952429 3701146033018579901982161)
        ·
          refine ⟨2775859524763934926486621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701146033018579901982161 2775859524763934926486621)
          ·
            refine ⟨1040947321786475597432483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2775859524763934926486621 1040947321786475597432483)
            ·
              refine ⟨1561420982679713396148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040947321786475597432483 1561420982679713396148725)
              ·
                refine ⟨146383217126223130888943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561420982679713396148725 146383217126223130888943)
                ·
                  rfl

theorem cell19_481073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_481073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481073 prefixEnd_481073 := by exact prefixLift 481073
  have htrace : WordTrace (prefixWord ++ tailWord_481073) baseStart_481073 baseEnd_481073 := by
    simpa [prefixWord, tailWord_481073, baseEnd_481073] using wordTrace_append hprefix tailTrace_481073
  have hstable : (prefixWord ++ tailWord_481073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481073).length < 2 ^ (prefixWord ++ tailWord_481073).sum := by decide
  have hdescent : baseEnd_481073 < baseStart_481073 := by decide
  rcases family_descends (prefixWord ++ tailWord_481073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481189 : List Nat := [1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_481189 : Nat := 118140960795 + 481189 * 2 ^ 59
def prefixEnd_481189 : Nat := 4983230072969 + 3 ^ 40 * 481189 * 2
def baseEnd_481189 : Nat := 146418514166769232310849

theorem tailTrace_481189 : CollatzResearch.WordTrace tailWord_481189 prefixEnd_481189 146418514166769232310849 := by
  unfold tailWord_481189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550404653741908383582621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11700269769161272255721747 17550404653741908383582621)
  ·
    refine ⟨6581401745153215643843483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17550404653741908383582621 6581401745153215643843483)
    ·
      refine ⟨9872102617729823465765225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581401745153215643843483 9872102617729823465765225)
      ·
        refine ⟨7404076963297367599323919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9872102617729823465765225 7404076963297367599323919)
        ·
          refine ⟨11106115444946051398985879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404076963297367599323919 11106115444946051398985879)
          ·
            refine ⟨16659173167419077098478819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106115444946051398985879 16659173167419077098478819)
            ·
              refine ⟨24988759751128615647718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16659173167419077098478819 24988759751128615647718229)
              ·
                refine ⟨146418514166769232310849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24988759751128615647718229 146418514166769232310849)
                ·
                  rfl

theorem cell19_481189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_481189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481189 prefixEnd_481189 := by exact prefixLift 481189
  have htrace : WordTrace (prefixWord ++ tailWord_481189) baseStart_481189 baseEnd_481189 := by
    simpa [prefixWord, tailWord_481189, baseEnd_481189] using wordTrace_append hprefix tailTrace_481189
  have hstable : (prefixWord ++ tailWord_481189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481189).length < 2 ^ (prefixWord ++ tailWord_481189).sum := by decide
  have hdescent : baseEnd_481189 < baseStart_481189 := by decide
  rcases family_descends (prefixWord ++ tailWord_481189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481208 : List Nat := [2, 1, 2, 1, 2, 3, 8]
def baseStart_481208 : Nat := 118140960795 + 481208 * 2 ^ 59
def prefixEnd_481208 : Nat := 4983230072969 + 3 ^ 40 * 481208 * 2
def baseEnd_481208 : Nat := 48808098526194272629525

theorem tailTrace_481208 : CollatzResearch.WordTrace tailWord_481208 prefixEnd_481208 48808098526194272629525 := by
  unfold tailWord_481208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775548820336537314262139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700731760448716419016185 8775548820336537314262139)
  ·
    refine ⟨13163323230504805971393209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775548820336537314262139 13163323230504805971393209)
    ·
      refine ⟨9872492422878604478544907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13163323230504805971393209 9872492422878604478544907)
      ·
        refine ⟨14808738634317906717817361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9872492422878604478544907 14808738634317906717817361)
        ·
          refine ⟨11106553975738430038363021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14808738634317906717817361 11106553975738430038363021)
          ·
            refine ⟨4164957740901911264386133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11106553975738430038363021 4164957740901911264386133)
            ·
              refine ⟨48808098526194272629525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4164957740901911264386133 48808098526194272629525)
              ·
                rfl

theorem cell19_481208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_481208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481208 prefixEnd_481208 := by exact prefixLift 481208
  have htrace : WordTrace (prefixWord ++ tailWord_481208) baseStart_481208 baseEnd_481208 := by
    simpa [prefixWord, tailWord_481208, baseEnd_481208] using wordTrace_append hprefix tailTrace_481208
  have hstable : (prefixWord ++ tailWord_481208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481208).length < 2 ^ (prefixWord ++ tailWord_481208).sum := by decide
  have hdescent : baseEnd_481208 < baseStart_481208 := by decide
  rcases family_descends (prefixWord ++ tailWord_481208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481227 : List Nat := [1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_481227 : Nat := 118140960795 + 481227 * 2 ^ 59
def prefixEnd_481227 : Nat := 4983230072969 + 3 ^ 40 * 481227 * 2
def baseEnd_481227 : Nat := 146430076990396403466301

theorem tailTrace_481227 : CollatzResearch.WordTrace tailWord_481227 prefixEnd_481227 146430076990396403466301 := by
  unfold tailWord_481227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17551790627604240873465935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11701193751736160582310623 17551790627604240873465935)
  ·
    refine ⟨26327685941406361310198903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17551790627604240873465935 26327685941406361310198903)
    ·
      refine ⟨39491528912109541965298355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327685941406361310198903 39491528912109541965298355)
      ·
        refine ⟨59237293368164312947947533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39491528912109541965298355 59237293368164312947947533)
        ·
          refine ⟨22213985013061617355480325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59237293368164312947947533 22213985013061617355480325)
          ·
            refine ⟨4165122189949053254152561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22213985013061617355480325 4165122189949053254152561)
            ·
              refine ⟨3123841642461789940614421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4165122189949053254152561 3123841642461789940614421)
              ·
                refine ⟨146430076990396403466301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3123841642461789940614421 146430076990396403466301)
                ·
                  rfl

theorem cell19_481227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_481227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481227 prefixEnd_481227 := by exact prefixLift 481227
  have htrace : WordTrace (prefixWord ++ tailWord_481227) baseStart_481227 baseEnd_481227 := by
    simpa [prefixWord, tailWord_481227, baseEnd_481227] using wordTrace_append hprefix tailTrace_481227
  have hstable : (prefixWord ++ tailWord_481227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481227).length < 2 ^ (prefixWord ++ tailWord_481227).sum := by decide
  have hdescent : baseEnd_481227 < baseStart_481227 := by decide
  rcases family_descends (prefixWord ++ tailWord_481227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481238 : List Nat := [5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_481238 : Nat := 118140960795 + 481238 * 2 ^ 59
def prefixEnd_481238 : Nat := 4983230072969 + 3 ^ 40 * 481238 * 2
def baseEnd_481238 : Nat := 146433424123551637221827

theorem tailTrace_481238 : CollatzResearch.WordTrace tailWord_481238 prefixEnd_481238 146433424123551637221827 := by
  unfold tailWord_481238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097011989410274359507273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11701461220376259834744245 1097011989410274359507273)
  ·
    refine ⟨822758992057705769630455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1097011989410274359507273 822758992057705769630455)
    ·
      refine ⟨1234138488086558654445683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822758992057705769630455 1234138488086558654445683)
      ·
        refine ⟨1851207732129837981668525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234138488086558654445683 1851207732129837981668525)
        ·
          refine ⟨694202899548689243125697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1851207732129837981668525 694202899548689243125697)
          ·
            refine ⟨520652174661516932344273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694202899548689243125697 520652174661516932344273)
            ·
              refine ⟨390489130996137699258205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520652174661516932344273 390489130996137699258205)
              ·
                refine ⟨146433424123551637221827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390489130996137699258205 146433424123551637221827)
                ·
                  rfl

theorem cell19_481238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_481238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481238 prefixEnd_481238 := by exact prefixLift 481238
  have htrace : WordTrace (prefixWord ++ tailWord_481238) baseStart_481238 baseEnd_481238 := by
    simpa [prefixWord, tailWord_481238, baseEnd_481238] using wordTrace_append hprefix tailTrace_481238
  have hstable : (prefixWord ++ tailWord_481238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481238).length < 2 ^ (prefixWord ++ tailWord_481238).sum := by decide
  have hdescent : baseEnd_481238 < baseStart_481238 := by decide
  rcases family_descends (prefixWord ++ tailWord_481238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481320 : List Nat := [2, 1, 5, 3, 8]
def baseStart_481320 : Nat := 118140960795 + 481320 * 2 ^ 59
def prefixEnd_481320 : Nat := 4983230072969 + 3 ^ 40 * 481320 * 2
def baseEnd_481320 : Nat := 5424384277029620125903

theorem tailTrace_481320 : CollatzResearch.WordTrace tailWord_481320 prefixEnd_481320 5424384277029620125903 := by
  unfold tailWord_481320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777591308133658878300707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11703455077511545171067609 8777591308133658878300707)
  ·
    refine ⟨13166386962200488317451061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8777591308133658878300707 13166386962200488317451061)
    ·
      refine ⟨1234348777706295779761037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13166386962200488317451061 1234348777706295779761037)
      ·
        refine ⟨462880791639860917410389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1234348777706295779761037 462880791639860917410389)
        ·
          refine ⟨5424384277029620125903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 462880791639860917410389 5424384277029620125903)
          ·
            rfl

theorem cell19_481320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_481320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481320 prefixEnd_481320 := by exact prefixLift 481320
  have htrace : WordTrace (prefixWord ++ tailWord_481320) baseStart_481320 baseEnd_481320 := by
    simpa [prefixWord, tailWord_481320, baseEnd_481320] using wordTrace_append hprefix tailTrace_481320
  have hstable : (prefixWord ++ tailWord_481320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481320).length < 2 ^ (prefixWord ++ tailWord_481320).sum := by decide
  have hdescent : baseEnd_481320 < baseStart_481320 := by decide
  rcases family_descends (prefixWord ++ tailWord_481320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
