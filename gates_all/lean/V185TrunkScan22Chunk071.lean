import V185TrunkScan22Chunk070

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_638113 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 6]
def baseStart_638113 : Nat := 118140960795 + 638113 * 2 ^ 59
def prefixEnd_638113 : Nat := 4983230072969 + 3 ^ 40 * 638113 * 2
def baseEnd_638113 : Nat := 72813040196126025256195

theorem tailTrace_638113 : CollatzResearch.WordTrace tailWord_638113 prefixEnd_638113 72813040196126025256195 := by
  unfold tailWord_638113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23273893137233056869086993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15515928758155371246057995 23273893137233056869086993)
  ·
    refine ⟨17455419852924792651815245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23273893137233056869086993 17455419852924792651815245)
    ·
      refine ⟨6545782444846797244430717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17455419852924792651815245 6545782444846797244430717)
      ·
        refine ⟨2454668416817548966661519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6545782444846797244430717 2454668416817548966661519)
        ·
          refine ⟨3682002625226323449992279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454668416817548966661519 3682002625226323449992279)
          ·
            refine ⟨5523003937839485174988419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682002625226323449992279 5523003937839485174988419)
            ·
              refine ⟨8284505906759227762482629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523003937839485174988419 8284505906759227762482629)
              ·
                refine ⟨1553344857517355205465493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8284505906759227762482629 1553344857517355205465493)
                ·
                  refine ⟨72813040196126025256195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1553344857517355205465493 72813040196126025256195)
                  ·
                    rfl

theorem cell22_638113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_638113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638113 prefixEnd_638113 := by exact prefixLift 638113
  have htrace : WordTrace (prefixWord ++ tailWord_638113) baseStart_638113 baseEnd_638113 := by
    simpa [prefixWord, tailWord_638113, baseEnd_638113] using wordTrace_append hprefix tailTrace_638113
  have hstable : (prefixWord ++ tailWord_638113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638113).length < 2 ^ (prefixWord ++ tailWord_638113).sum := by decide
  have hdescent : baseEnd_638113 < baseStart_638113 := by decide
  rcases family_descends (prefixWord ++ tailWord_638113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638143 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_638143 : Nat := 118140960795 + 638143 * 2 ^ 59
def prefixEnd_638143 : Nat := 4983230072969 + 3 ^ 40 * 638143 * 2
def baseEnd_638143 : Nat := 218449390201467997518493

theorem tailTrace_638143 : CollatzResearch.WordTrace tailWord_638143 prefixEnd_638143 218449390201467997518493 := by
  unfold tailWord_638143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23274987327124371992679083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15516658218082914661786055 23274987327124371992679083)
  ·
    refine ⟨34912480990686557989018625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23274987327124371992679083 34912480990686557989018625)
    ·
      refine ⟨26184360743014918491763969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34912480990686557989018625 26184360743014918491763969)
      ·
        refine ⟨19638270557261188868822977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26184360743014918491763969 19638270557261188868822977)
        ·
          refine ⟨14728702917945891651617233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19638270557261188868822977 14728702917945891651617233)
          ·
            refine ⟨11046527188459418738712925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14728702917945891651617233 11046527188459418738712925)
            ·
              refine ⟨4142447695672282027017347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11046527188459418738712925 4142447695672282027017347)
              ·
                refine ⟨6213671543508423040526021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142447695672282027017347 6213671543508423040526021)
                ·
                  refine ⟨1165063414407829320098629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6213671543508423040526021 1165063414407829320098629)
                  ·
                    refine ⟨218449390201467997518493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165063414407829320098629 218449390201467997518493)
                    ·
                      rfl

theorem cell22_638143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_638143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638143 prefixEnd_638143 := by exact prefixLift 638143
  have htrace : WordTrace (prefixWord ++ tailWord_638143) baseStart_638143 baseEnd_638143 := by
    simpa [prefixWord, tailWord_638143, baseEnd_638143] using wordTrace_append hprefix tailTrace_638143
  have hstable : (prefixWord ++ tailWord_638143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638143).length < 2 ^ (prefixWord ++ tailWord_638143).sum := by decide
  have hdescent : baseEnd_638143 < baseStart_638143 := by decide
  rcases family_descends (prefixWord ++ tailWord_638143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638162 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_638162 : Nat := 118140960795 + 638162 * 2 ^ 59
def prefixEnd_638162 : Nat := 4983230072969 + 3 ^ 40 * 638162 * 2
def baseEnd_638162 : Nat := 218455894289758281293435

theorem tailTrace_638162 : CollatzResearch.WordTrace tailWord_638162 prefixEnd_638162 218455894289758281293435 := by
  unfold tailWord_638162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818920078513884559405185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15517120209370358825080493 5818920078513884559405185)
  ·
    refine ⟨4364190058885413419553889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5818920078513884559405185 4364190058885413419553889)
    ·
      refine ⟨3273142544164060064665417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4364190058885413419553889 3273142544164060064665417)
      ·
        refine ⟨2454856908123045048499063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3273142544164060064665417 2454856908123045048499063)
        ·
          refine ⟨3682285362184567572748595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454856908123045048499063 3682285362184567572748595)
          ·
            refine ⟨5523428043276851359122893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682285362184567572748595 5523428043276851359122893)
            ·
              refine ⟨2071285516228819259671085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5523428043276851359122893 2071285516228819259671085)
              ·
                refine ⟨776732068585807222376657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071285516228819259671085 776732068585807222376657)
                ·
                  refine ⟨582549051439355416782493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 776732068585807222376657 582549051439355416782493)
                  ·
                    refine ⟨218455894289758281293435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582549051439355416782493 218455894289758281293435)
                    ·
                      rfl

theorem cell22_638162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_638162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638162 prefixEnd_638162 := by exact prefixLift 638162
  have htrace : WordTrace (prefixWord ++ tailWord_638162) baseStart_638162 baseEnd_638162 := by
    simpa [prefixWord, tailWord_638162, baseEnd_638162] using wordTrace_append hprefix tailTrace_638162
  have hstable : (prefixWord ++ tailWord_638162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638162).length < 2 ^ (prefixWord ++ tailWord_638162).sum := by decide
  have hdescent : baseEnd_638162 < baseStart_638162 := by decide
  rcases family_descends (prefixWord ++ tailWord_638162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638166 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_638166 : Nat := 118140960795 + 638166 * 2 ^ 59
def prefixEnd_638166 : Nat := 4983230072969 + 3 ^ 40 * 638166 * 2
def baseEnd_638166 : Nat := 218457263571503604193423

theorem tailTrace_638166 : CollatzResearch.WordTrace tailWord_638166 prefixEnd_638166 218457263571503604193423 := by
  unfold tailWord_638166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454739137877565432547897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15517217470694031280510901 1454739137877565432547897)
  ·
    refine ⟨1091054353408174074410923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1454739137877565432547897 1091054353408174074410923)
    ·
      refine ⟨1636581530112261111616385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091054353408174074410923 1636581530112261111616385)
      ·
        refine ⟨1227436147584195833712289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636581530112261111616385 1227436147584195833712289)
        ·
          refine ⟨920577110688146875284217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227436147584195833712289 920577110688146875284217)
          ·
            refine ⟨690432833016110156463163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920577110688146875284217 690432833016110156463163)
            ·
              refine ⟨1035649249524165234694745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690432833016110156463163 1035649249524165234694745)
              ·
                refine ⟨776736937143123926021059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035649249524165234694745 776736937143123926021059)
                ·
                  refine ⟨1165105405714685889031589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776736937143123926021059 1165105405714685889031589)
                  ·
                    refine ⟨218457263571503604193423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165105405714685889031589 218457263571503604193423)
                    ·
                      rfl

theorem cell22_638166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_638166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638166 prefixEnd_638166 := by exact prefixLift 638166
  have htrace : WordTrace (prefixWord ++ tailWord_638166) baseStart_638166 baseEnd_638166 := by
    simpa [prefixWord, tailWord_638166, baseEnd_638166] using wordTrace_append hprefix tailTrace_638166
  have hstable : (prefixWord ++ tailWord_638166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638166).length < 2 ^ (prefixWord ++ tailWord_638166).sum := by decide
  have hdescent : baseEnd_638166 < baseStart_638166 := by decide
  rcases family_descends (prefixWord ++ tailWord_638166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638220 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_638220 : Nat := 118140960795 + 638220 * 2 ^ 59
def prefixEnd_638220 : Nat := 4983230072969 + 3 ^ 40 * 638220 * 2
def baseEnd_638220 : Nat := 72825249625021821114419

theorem tailTrace_638220 : CollatzResearch.WordTrace tailWord_638220 prefixEnd_638220 72825249625021821114419 := by
  unfold tailWord_638220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638897873922707071616057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15518530498563609428821409 11638897873922707071616057)
  ·
    refine ⟨8729173405442030303712043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11638897873922707071616057 8729173405442030303712043)
    ·
      refine ⟨13093760108163045455568065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8729173405442030303712043 13093760108163045455568065)
      ·
        refine ⟨9820320081122284091676049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13093760108163045455568065 9820320081122284091676049)
        ·
          refine ⟨7365240060841713068757037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9820320081122284091676049 7365240060841713068757037)
          ·
            refine ⟨2761965022815642400783889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7365240060841713068757037 2761965022815642400783889)
            ·
              refine ⟨2071473767111731800587917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761965022815642400783889 2071473767111731800587917)
              ·
                refine ⟨776802662666899425220469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071473767111731800587917 776802662666899425220469)
                ·
                  refine ⟨72825249625021821114419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776802662666899425220469 72825249625021821114419)
                  ·
                    rfl

theorem cell22_638220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_638220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638220 prefixEnd_638220 := by exact prefixLift 638220
  have htrace : WordTrace (prefixWord ++ tailWord_638220) baseStart_638220 baseEnd_638220 := by
    simpa [prefixWord, tailWord_638220, baseEnd_638220] using wordTrace_append hprefix tailTrace_638220
  have hstable : (prefixWord ++ tailWord_638220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638220).length < 2 ^ (prefixWord ++ tailWord_638220).sum := by decide
  have hdescent : baseEnd_638220 < baseStart_638220 := by decide
  rcases family_descends (prefixWord ++ tailWord_638220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638263 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_638263 : Nat := 118140960795 + 638263 * 2 ^ 59
def prefixEnd_638263 : Nat := 4983230072969 + 3 ^ 40 * 638263 * 2
def baseEnd_638263 : Nat := 218490468653827684518125

theorem tailTrace_638263 : CollatzResearch.WordTrace tailWord_638263 prefixEnd_638263 218490468653827684518125 := by
  unfold tailWord_638263
  simp only [CollatzResearch.WordTrace]
  refine ⟨23279364086689632487047443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15519576057793088324698295 23279364086689632487047443)
  ·
    refine ⟨34919046130034448730571165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23279364086689632487047443 34919046130034448730571165)
    ·
      refine ⟨13094642298762918273964187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34919046130034448730571165 13094642298762918273964187)
      ·
        refine ⟨19641963448144377410946281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13094642298762918273964187 19641963448144377410946281)
        ·
          refine ⟨14731472586108283058209711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19641963448144377410946281 14731472586108283058209711)
          ·
            refine ⟨22097208879162424587314567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14731472586108283058209711 22097208879162424587314567)
            ·
              refine ⟨33145813318743636880971851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22097208879162424587314567 33145813318743636880971851)
              ·
                refine ⟨49718719978115455321457777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33145813318743636880971851 49718719978115455321457777)
                ·
                  refine ⟨37289039983586591491093333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49718719978115455321457777 37289039983586591491093333)
                  ·
                    refine ⟨218490468653827684518125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37289039983586591491093333 218490468653827684518125)
                    ·
                      rfl

theorem cell22_638263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_638263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638263 prefixEnd_638263 := by exact prefixLift 638263
  have htrace : WordTrace (prefixWord ++ tailWord_638263) baseStart_638263 baseEnd_638263 := by
    simpa [prefixWord, tailWord_638263, baseEnd_638263] using wordTrace_append hprefix tailTrace_638263
  have hstable : (prefixWord ++ tailWord_638263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638263).length < 2 ^ (prefixWord ++ tailWord_638263).sum := by decide
  have hdescent : baseEnd_638263 < baseStart_638263 := by decide
  rcases family_descends (prefixWord ++ tailWord_638263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638295 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_638295 : Nat := 118140960795 + 638295 * 2 ^ 59
def prefixEnd_638295 : Nat := 4983230072969 + 3 ^ 40 * 638295 * 2
def baseEnd_638295 : Nat := 218501422907790267718027

theorem tailTrace_638295 : CollatzResearch.WordTrace tailWord_638295 prefixEnd_638295 218501422907790267718027 := by
  unfold tailWord_638295
  simp only [CollatzResearch.WordTrace]
  refine ⟨23280531222573701952212339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15520354148382467968141559 23280531222573701952212339)
  ·
    refine ⟨34920796833860552928318509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23280531222573701952212339 34920796833860552928318509)
    ·
      refine ⟨13095298812697707348119441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34920796833860552928318509 13095298812697707348119441)
      ·
        refine ⟨9821474109523280511089581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13095298812697707348119441 9821474109523280511089581)
        ·
          refine ⟨3683052791071230191658593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9821474109523280511089581 3683052791071230191658593)
          ·
            refine ⟨2762289593303422643743945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683052791071230191658593 2762289593303422643743945)
            ·
              refine ⟨2071717194977566982807959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762289593303422643743945 2071717194977566982807959)
              ·
                refine ⟨3107575792466350474211939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071717194977566982807959 3107575792466350474211939)
                ·
                  refine ⟨4661363688699525711317909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107575792466350474211939 4661363688699525711317909)
                  ·
                    refine ⟨218501422907790267718027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4661363688699525711317909 218501422907790267718027)
                    ·
                      rfl

theorem cell22_638295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_638295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638295 prefixEnd_638295 := by exact prefixLift 638295
  have htrace : WordTrace (prefixWord ++ tailWord_638295) baseStart_638295 baseEnd_638295 := by
    simpa [prefixWord, tailWord_638295, baseEnd_638295] using wordTrace_append hprefix tailTrace_638295
  have hstable : (prefixWord ++ tailWord_638295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638295).length < 2 ^ (prefixWord ++ tailWord_638295).sum := by decide
  have hdescent : baseEnd_638295 < baseStart_638295 := by decide
  rcases family_descends (prefixWord ++ tailWord_638295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638359 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 1, 3]
def baseStart_638359 : Nat := 118140960795 + 638359 * 2 ^ 59
def prefixEnd_638359 : Nat := 4983230072969 + 3 ^ 40 * 638359 * 2
def baseEnd_638359 : Nat := 218523331415715434117831

theorem tailTrace_638359 : CollatzResearch.WordTrace tailWord_638359 prefixEnd_638359 218523331415715434117831 := by
  unfold tailWord_638359
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282865494341840882542131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15521910329561227255028087 23282865494341840882542131)
  ·
    refine ⟨34924298241512761323813197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23282865494341840882542131 34924298241512761323813197)
    ·
      refine ⟨13096611840567285496429949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34924298241512761323813197 13096611840567285496429949)
      ·
        refine ⟨4911229440212732061161231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13096611840567285496429949 4911229440212732061161231)
        ·
          refine ⟨7366844160319098091741847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911229440212732061161231 7366844160319098091741847)
          ·
            refine ⟨11050266240478647137612771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366844160319098091741847 11050266240478647137612771)
            ·
              refine ⟨16575399360717970706419157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050266240478647137612771 16575399360717970706419157)
              ·
                refine ⟨388485922516827438431699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16575399360717970706419157 388485922516827438431699)
                ·
                  refine ⟨582728883775241157647549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388485922516827438431699 582728883775241157647549)
                  ·
                    refine ⟨218523331415715434117831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582728883775241157647549 218523331415715434117831)
                    ·
                      rfl

theorem cell22_638359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_638359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638359 prefixEnd_638359 := by exact prefixLift 638359
  have htrace : WordTrace (prefixWord ++ tailWord_638359) baseStart_638359 baseEnd_638359 := by
    simpa [prefixWord, tailWord_638359, baseEnd_638359] using wordTrace_append hprefix tailTrace_638359
  have hstable : (prefixWord ++ tailWord_638359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638359).length < 2 ^ (prefixWord ++ tailWord_638359).sum := by decide
  have hdescent : baseEnd_638359 < baseStart_638359 := by decide
  rcases family_descends (prefixWord ++ tailWord_638359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638400 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_638400 : Nat := 118140960795 + 638400 * 2 ^ 59
def prefixEnd_638400 : Nat := 4983230072969 + 3 ^ 40 * 638400 * 2
def baseEnd_638400 : Nat := 72845788851201664614235

theorem tailTrace_638400 : CollatzResearch.WordTrace tailWord_638400 prefixEnd_638400 72845788851201664614235 := by
  unfold tailWord_638400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642180443596652442392327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15522907258128869923189769 11642180443596652442392327)
  ·
    refine ⟨17463270665394978663588491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11642180443596652442392327 17463270665394978663588491)
    ·
      refine ⟨26194905998092467995382737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17463270665394978663588491 26194905998092467995382737)
      ·
        refine ⟨19646179498569350996537053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26194905998092467995382737 19646179498569350996537053)
        ·
          refine ⟨7367317311963506623701395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19646179498569350996537053 7367317311963506623701395)
          ·
            refine ⟨11050975967945259935552093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367317311963506623701395 11050975967945259935552093)
            ·
              refine ⟨4144115987979472475832035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11050975967945259935552093 4144115987979472475832035)
              ·
                refine ⟨6216173981969208713748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144115987979472475832035 6216173981969208713748053)
                ·
                  refine ⟨72845788851201664614235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6216173981969208713748053 72845788851201664614235)
                  ·
                    rfl

theorem cell22_638400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_638400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638400 prefixEnd_638400 := by exact prefixLift 638400
  have htrace : WordTrace (prefixWord ++ tailWord_638400) baseStart_638400 baseEnd_638400 := by
    simpa [prefixWord, tailWord_638400, baseEnd_638400] using wordTrace_append hprefix tailTrace_638400
  have hstable : (prefixWord ++ tailWord_638400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638400).length < 2 ^ (prefixWord ++ tailWord_638400).sum := by decide
  have hdescent : baseEnd_638400 < baseStart_638400 := by decide
  rcases family_descends (prefixWord ++ tailWord_638400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638449 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_638449 : Nat := 118140960795 + 638449 * 2 ^ 59
def prefixEnd_638449 : Nat := 4983230072969 + 3 ^ 40 * 638449 * 2
def baseEnd_638449 : Nat := 218554140254985199367555

theorem tailTrace_638449 : CollatzResearch.WordTrace tailWord_638449 prefixEnd_638449 218554140254985199367555 := by
  unfold tailWord_638449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23286148064015786253318401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15524098709343857502212267 23286148064015786253318401)
  ·
    refine ⟨17464611048011839689988801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23286148064015786253318401 17464611048011839689988801)
    ·
      refine ⟨13098458286008879767491601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17464611048011839689988801 13098458286008879767491601)
      ·
        refine ⟨9823843714506659825618701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13098458286008879767491601 9823843714506659825618701)
        ·
          refine ⟨3683941392939997434607013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9823843714506659825618701 3683941392939997434607013)
          ·
            refine ⟨690739011176249518988815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3683941392939997434607013 690739011176249518988815)
            ·
              refine ⟨1036108516764374278483223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690739011176249518988815 1036108516764374278483223)
              ·
                refine ⟨1554162775146561417724835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036108516764374278483223 1554162775146561417724835)
                ·
                  refine ⟨2331244162719842126587253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554162775146561417724835 2331244162719842126587253)
                  ·
                    refine ⟨218554140254985199367555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331244162719842126587253 218554140254985199367555)
                    ·
                      rfl

theorem cell22_638449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_638449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638449 prefixEnd_638449 := by exact prefixLift 638449
  have htrace : WordTrace (prefixWord ++ tailWord_638449) baseStart_638449 baseEnd_638449 := by
    simpa [prefixWord, tailWord_638449, baseEnd_638449] using wordTrace_append hprefix tailTrace_638449
  have hstable : (prefixWord ++ tailWord_638449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638449).length < 2 ^ (prefixWord ++ tailWord_638449).sum := by decide
  have hdescent : baseEnd_638449 < baseStart_638449 := by decide
  rcases family_descends (prefixWord ++ tailWord_638449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638466 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_638466 : Nat := 118140960795 + 638466 * 2 ^ 59
def prefixEnd_638466 : Nat := 4983230072969 + 3 ^ 40 * 638466 * 2
def baseEnd_638466 : Nat := 218559959702402821692503

theorem tailTrace_638466 : CollatzResearch.WordTrace tailWord_638466 prefixEnd_638466 218559959702402821692503 := by
  unfold tailWord_638466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821692026238549539171813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15524512069969465437791501 5821692026238549539171813)
  ·
    refine ⟨1091567254919728038594715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5821692026238549539171813 1091567254919728038594715)
    ·
      refine ⟨1637350882379592057892073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091567254919728038594715 1637350882379592057892073)
      ·
        refine ⟨1228013161784694043419055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1637350882379592057892073 1228013161784694043419055)
        ·
          refine ⟨1842019742677041065128583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228013161784694043419055 1842019742677041065128583)
          ·
            refine ⟨2763029614015561597692875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842019742677041065128583 2763029614015561597692875)
            ·
              refine ⟨4144544421023342396539313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763029614015561597692875 4144544421023342396539313)
              ·
                refine ⟨3108408315767506797404485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144544421023342396539313 3108408315767506797404485)
                ·
                  refine ⟨582826559206407524513341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3108408315767506797404485 582826559206407524513341)
                  ·
                    refine ⟨218559959702402821692503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582826559206407524513341 218559959702402821692503)
                    ·
                      rfl

theorem cell22_638466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_638466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638466 prefixEnd_638466 := by exact prefixLift 638466
  have htrace : WordTrace (prefixWord ++ tailWord_638466) baseStart_638466 baseEnd_638466 := by
    simpa [prefixWord, tailWord_638466, baseEnd_638466] using wordTrace_append hprefix tailTrace_638466
  have hstable : (prefixWord ++ tailWord_638466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638466).length < 2 ^ (prefixWord ++ tailWord_638466).sum := by decide
  have hdescent : baseEnd_638466 < baseStart_638466 := by decide
  rcases family_descends (prefixWord ++ tailWord_638466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638468 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_638468 : Nat := 118140960795 + 638468 * 2 ^ 59
def prefixEnd_638468 : Nat := 4983230072969 + 3 ^ 40 * 638468 * 2
def baseEnd_638468 : Nat := 72853548114425161047499

theorem tailTrace_638468 : CollatzResearch.WordTrace tailWord_638468 prefixEnd_638468 72853548114425161047499 := by
  unfold tailWord_638468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643420525473476249130029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15524560700631301665506705 11643420525473476249130029)
  ·
    refine ⟨4366282697052553593423761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11643420525473476249130029 4366282697052553593423761)
    ·
      refine ⟨3274712022789415195067821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4366282697052553593423761 3274712022789415195067821)
      ·
        refine ⟨1228017008546030698150433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3274712022789415195067821 1228017008546030698150433)
        ·
          refine ⟨921012756409523023612825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228017008546030698150433 921012756409523023612825)
          ·
            refine ⟨690759567307142267709619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921012756409523023612825 690759567307142267709619)
            ·
              refine ⟨1036139350960713401564429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690759567307142267709619 1036139350960713401564429)
              ·
                refine ⟨388552256610267525586661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036139350960713401564429 388552256610267525586661)
                ·
                  refine ⟨72853548114425161047499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388552256610267525586661 72853548114425161047499)
                  ·
                    rfl

theorem cell22_638468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_638468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638468 prefixEnd_638468 := by exact prefixLift 638468
  have htrace : WordTrace (prefixWord ++ tailWord_638468) baseStart_638468 baseEnd_638468 := by
    simpa [prefixWord, tailWord_638468, baseEnd_638468] using wordTrace_append hprefix tailTrace_638468
  have hstable : (prefixWord ++ tailWord_638468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638468).length < 2 ^ (prefixWord ++ tailWord_638468).sum := by decide
  have hdescent : baseEnd_638468 < baseStart_638468 := by decide
  rcases family_descends (prefixWord ++ tailWord_638468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638492 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_638492 : Nat := 118140960795 + 638492 * 2 ^ 59
def prefixEnd_638492 : Nat := 4983230072969 + 3 ^ 40 * 638492 * 2
def baseEnd_638492 : Nat := 218568860033747420542423

theorem tailTrace_638492 : CollatzResearch.WordTrace tailWord_638492 prefixEnd_638492 218568860033747420542423 := by
  unfold tailWord_638492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643858201430002298566865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15525144268573336398089153 11643858201430002298566865)
  ·
    refine ⟨8732893651072501723925149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11643858201430002298566865 8732893651072501723925149)
    ·
      refine ⟨3274835119152188146471931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8732893651072501723925149 3274835119152188146471931)
      ·
        refine ⟨4912252678728282219707897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274835119152188146471931 4912252678728282219707897)
        ·
          refine ⟨3684189509046211664780923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4912252678728282219707897 3684189509046211664780923)
          ·
            refine ⟨5526284263569317497171385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684189509046211664780923 5526284263569317497171385)
            ·
              refine ⟨4144713197676988122878539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526284263569317497171385 4144713197676988122878539)
              ·
                refine ⟨6217069796515482184317809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144713197676988122878539 6217069796515482184317809)
                ·
                  refine ⟨4662802347386611638238357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6217069796515482184317809 4662802347386611638238357)
                  ·
                    refine ⟨218568860033747420542423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4662802347386611638238357 218568860033747420542423)
                    ·
                      rfl

theorem cell22_638492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_638492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638492 prefixEnd_638492 := by exact prefixLift 638492
  have htrace : WordTrace (prefixWord ++ tailWord_638492) baseStart_638492 baseEnd_638492 := by
    simpa [prefixWord, tailWord_638492, baseEnd_638492] using wordTrace_append hprefix tailTrace_638492
  have hstable : (prefixWord ++ tailWord_638492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638492).length < 2 ^ (prefixWord ++ tailWord_638492).sum := by decide
  have hdescent : baseEnd_638492 < baseStart_638492 := by decide
  rcases family_descends (prefixWord ++ tailWord_638492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638552 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_638552 : Nat := 118140960795 + 638552 * 2 ^ 59
def prefixEnd_638552 : Nat := 4983230072969 + 3 ^ 40 * 638552 * 2
def baseEnd_638552 : Nat := 72863133086642421347413

theorem tailTrace_638552 : CollatzResearch.WordTrace tailWord_638552 prefixEnd_638552 72863133086642421347413 := by
  unfold tailWord_638552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644952391321317422158955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15526603188428423229545273 11644952391321317422158955)
  ·
    refine ⟨17467428586981976133238433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644952391321317422158955 17467428586981976133238433)
    ·
      refine ⟨13100571440236482099928825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17467428586981976133238433 13100571440236482099928825)
      ·
        refine ⟨9825428580177361574946619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13100571440236482099928825 9825428580177361574946619)
        ·
          refine ⟨14738142870266042362419929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825428580177361574946619 14738142870266042362419929)
          ·
            refine ⟨11053607152699531771814947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14738142870266042362419929 11053607152699531771814947)
            ·
              refine ⟨16580410729049297657722421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053607152699531771814947 16580410729049297657722421)
              ·
                refine ⟨1554413505848371655411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16580410729049297657722421 1554413505848371655411477)
                ·
                  refine ⟨72863133086642421347413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1554413505848371655411477 72863133086642421347413)
                  ·
                    rfl

theorem cell22_638552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_638552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638552 prefixEnd_638552 := by exact prefixLift 638552
  have htrace : WordTrace (prefixWord ++ tailWord_638552) baseStart_638552 baseEnd_638552 := by
    simpa [prefixWord, tailWord_638552, baseEnd_638552] using wordTrace_append hprefix tailTrace_638552
  have hstable : (prefixWord ++ tailWord_638552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638552).length < 2 ^ (prefixWord ++ tailWord_638552).sum := by decide
  have hdescent : baseEnd_638552 < baseStart_638552 := by decide
  rcases family_descends (prefixWord ++ tailWord_638552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638597 : List Nat := [1, 3, 1, 1, 4, 1, 11]
def baseStart_638597 : Nat := 118140960795 + 638597 * 2 ^ 59
def prefixEnd_638597 : Nat := 4983230072969 + 3 ^ 40 * 638597 * 2
def baseEnd_638597 : Nat := 8096474210354153580263

theorem tailTrace_638597 : CollatzResearch.WordTrace tailWord_638597 prefixEnd_638597 8096474210354153580263 := by
  unfold tailWord_638597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23291546067479607529706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15527697378319738353137363 23291546067479607529706045)
  ·
    refine ⟨8734329775304852823639767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23291546067479607529706045 8734329775304852823639767)
    ·
      refine ⟨13101494662957279235459651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8734329775304852823639767 13101494662957279235459651)
      ·
        refine ⟨19652241994435918853189477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13101494662957279235459651 19652241994435918853189477)
        ·
          refine ⟨3684795373956734784973027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19652241994435918853189477 3684795373956734784973027)
          ·
            refine ⟨5527193060935102177459541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684795373956734784973027 5527193060935102177459541)
            ·
              refine ⟨8096474210354153580263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5527193060935102177459541 8096474210354153580263)
              ·
                rfl

theorem cell22_638597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 11].length) (baseStart_638597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638597 prefixEnd_638597 := by exact prefixLift 638597
  have htrace : WordTrace (prefixWord ++ tailWord_638597) baseStart_638597 baseEnd_638597 := by
    simpa [prefixWord, tailWord_638597, baseEnd_638597] using wordTrace_append hprefix tailTrace_638597
  have hstable : (prefixWord ++ tailWord_638597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638597).length < 2 ^ (prefixWord ++ tailWord_638597).sum := by decide
  have hdescent : baseEnd_638597 < baseStart_638597 := by decide
  rcases family_descends (prefixWord ++ tailWord_638597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638601 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_638601 : Nat := 118140960795 + 638601 * 2 ^ 59
def prefixEnd_638601 : Nat := 4983230072969 + 3 ^ 40 * 638601 * 2
def baseEnd_638601 : Nat := 218606172961307469567089

theorem tailTrace_638601 : CollatzResearch.WordTrace tailWord_638601 prefixEnd_638601 218606172961307469567089 := by
  unfold tailWord_638601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23291691959465116212851657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15527794639643410808567771 23291691959465116212851657)
  ·
    refine ⟨17468768969598837159638743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23291691959465116212851657 17468768969598837159638743)
    ·
      refine ⟨26203153454398255739458115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17468768969598837159638743 26203153454398255739458115)
      ·
        refine ⟨39304730181597383609187173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26203153454398255739458115 39304730181597383609187173)
        ·
          refine ⟨7369636909049509426722595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39304730181597383609187173 7369636909049509426722595)
          ·
            refine ⟨11054455363574264140083893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7369636909049509426722595 11054455363574264140083893)
            ·
              refine ⟨1036355190335087263132865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11054455363574264140083893 1036355190335087263132865)
              ·
                refine ⟨777266392751315447349649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036355190335087263132865 777266392751315447349649)
                ·
                  refine ⟨582949794563486585512237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777266392751315447349649 582949794563486585512237)
                  ·
                    refine ⟨218606172961307469567089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582949794563486585512237 218606172961307469567089)
                    ·
                      rfl

theorem cell22_638601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_638601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638601 prefixEnd_638601 := by exact prefixLift 638601
  have htrace : WordTrace (prefixWord ++ tailWord_638601) baseStart_638601 baseEnd_638601 := by
    simpa [prefixWord, tailWord_638601, baseEnd_638601] using wordTrace_append hprefix tailTrace_638601
  have hstable : (prefixWord ++ tailWord_638601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638601).length < 2 ^ (prefixWord ++ tailWord_638601).sum := by decide
  have hdescent : baseEnd_638601 < baseStart_638601 := by decide
  rcases family_descends (prefixWord ++ tailWord_638601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638738 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_638738 : Nat := 118140960795 + 638738 * 2 ^ 59
def prefixEnd_638738 : Nat := 4983230072969 + 3 ^ 40 * 638738 * 2
def baseEnd_638738 : Nat := 72884356953694926297223

theorem tailTrace_638738 : CollatzResearch.WordTrace tailWord_638738 prefixEnd_638738 72884356953694926297223 := by
  unfold tailWord_638738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824172189992197152647217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15531125839979192407059245 5824172189992197152647217)
  ·
    refine ⟨4368129142494147864485413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5824172189992197152647217 4368129142494147864485413)
    ·
      refine ⟨819024214217652724591015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4368129142494147864485413 819024214217652724591015)
      ·
        refine ⟨1228536321326479086886523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819024214217652724591015 1228536321326479086886523)
        ·
          refine ⟨1842804481989718630329785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228536321326479086886523 1842804481989718630329785)
          ·
            refine ⟨1382103361492288972747339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842804481989718630329785 1382103361492288972747339)
            ·
              refine ⟨2073155042238433459121009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382103361492288972747339 2073155042238433459121009)
              ·
                refine ⟨1554866281678825094340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073155042238433459121009 1554866281678825094340757)
                ·
                  refine ⟨72884356953694926297223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1554866281678825094340757 72884356953694926297223)
                  ·
                    rfl

theorem cell22_638738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_638738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638738 prefixEnd_638738 := by exact prefixLift 638738
  have htrace : WordTrace (prefixWord ++ tailWord_638738) baseStart_638738 baseEnd_638738 := by
    simpa [prefixWord, tailWord_638738, baseEnd_638738] using wordTrace_append hprefix tailTrace_638738
  have hstable : (prefixWord ++ tailWord_638738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638738).length < 2 ^ (prefixWord ++ tailWord_638738).sum := by decide
  have hdescent : baseEnd_638738 < baseStart_638738 := by decide
  rcases family_descends (prefixWord ++ tailWord_638738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638770 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_638770 : Nat := 118140960795 + 638770 * 2 ^ 59
def prefixEnd_638770 : Nat := 4983230072969 + 3 ^ 40 * 638770 * 2
def baseEnd_638770 : Nat := 218664025115047362091571

theorem tailTrace_638770 : CollatzResearch.WordTrace tailWord_638770 prefixEnd_638770 218664025115047362091571 := by
  unfold tailWord_638770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824463973963214518938441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15531903930568572050502509 5824463973963214518938441)
  ·
    refine ⟨4368347980472410889203831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5824463973963214518938441 4368347980472410889203831)
    ·
      refine ⟨6552521970708616333805747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368347980472410889203831 6552521970708616333805747)
      ·
        refine ⟨9828782956062924500708621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6552521970708616333805747 9828782956062924500708621)
        ·
          refine ⟨3685793608523596687765733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9828782956062924500708621 3685793608523596687765733)
          ·
            refine ⟨691086301598174378956075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3685793608523596687765733 691086301598174378956075)
            ·
              refine ⟨1036629452397261568434113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691086301598174378956075 1036629452397261568434113)
              ·
                refine ⟨777472089297946176325585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036629452397261568434113 777472089297946176325585)
                ·
                  refine ⟨583104066973459632244189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777472089297946176325585 583104066973459632244189)
                  ·
                    refine ⟨218664025115047362091571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583104066973459632244189 218664025115047362091571)
                    ·
                      rfl

theorem cell22_638770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_638770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638770 prefixEnd_638770 := by exact prefixLift 638770
  have htrace : WordTrace (prefixWord ++ tailWord_638770) baseStart_638770 baseEnd_638770 := by
    simpa [prefixWord, tailWord_638770, baseEnd_638770] using wordTrace_append hprefix tailTrace_638770
  have hstable : (prefixWord ++ tailWord_638770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638770).length < 2 ^ (prefixWord ++ tailWord_638770).sum := by decide
  have hdescent : baseEnd_638770 < baseStart_638770 := by decide
  rcases family_descends (prefixWord ++ tailWord_638770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638815 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 1, 3]
def baseStart_638815 : Nat := 118140960795 + 638815 * 2 ^ 59
def prefixEnd_638815 : Nat := 4983230072969 + 3 ^ 40 * 638815 * 2
def baseEnd_638815 : Nat := 218679429534682244716433

theorem tailTrace_638815 : CollatzResearch.WordTrace tailWord_638815 prefixEnd_638815 218679429534682244716433 := by
  unfold tailWord_638815
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299497180689830761141899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15532998120459887174094599 23299497180689830761141899)
  ·
    refine ⟨34949245771034746141712849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23299497180689830761141899 34949245771034746141712849)
    ·
      refine ⟨26211934328276059606284637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34949245771034746141712849 26211934328276059606284637)
      ·
        refine ⟨9829475373103522352356739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26211934328276059606284637 9829475373103522352356739)
        ·
          refine ⟨14744213059655283528535109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829475373103522352356739 14744213059655283528535109)
          ·
            refine ⟨2764539948685365661600333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14744213059655283528535109 2764539948685365661600333)
            ·
              refine ⟨1036702480757012123100125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2764539948685365661600333 1036702480757012123100125)
              ·
                refine ⟨388763430283879546162547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036702480757012123100125 388763430283879546162547)
                ·
                  refine ⟨583145145425819319243821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388763430283879546162547 583145145425819319243821)
                  ·
                    refine ⟨218679429534682244716433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583145145425819319243821 218679429534682244716433)
                    ·
                      rfl

theorem cell22_638815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_638815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638815 prefixEnd_638815 := by exact prefixLift 638815
  have htrace : WordTrace (prefixWord ++ tailWord_638815) baseStart_638815 baseEnd_638815 := by
    simpa [prefixWord, tailWord_638815, baseEnd_638815] using wordTrace_append hprefix tailTrace_638815
  have hstable : (prefixWord ++ tailWord_638815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638815).length < 2 ^ (prefixWord ++ tailWord_638815).sum := by decide
  have hdescent : baseEnd_638815 < baseStart_638815 := by decide
  rcases family_descends (prefixWord ++ tailWord_638815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638841 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_638841 : Nat := 118140960795 + 638841 * 2 ^ 59
def prefixEnd_638841 : Nat := 4983230072969 + 3 ^ 40 * 638841 * 2
def baseEnd_638841 : Nat := 218688329866026843566353

theorem tailTrace_638841 : CollatzResearch.WordTrace tailWord_638841 prefixEnd_638841 218688329866026843566353 := by
  unfold tailWord_638841
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300445478595637201588377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15533630319063758134392251 23300445478595637201588377)
  ·
    refine ⟨17475334108946727901191283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23300445478595637201588377 17475334108946727901191283)
    ·
      refine ⟨26213001163420091851786925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17475334108946727901191283 26213001163420091851786925)
      ·
        refine ⟨9829875436282534444420097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26213001163420091851786925 9829875436282534444420097)
        ·
          refine ⟨7372406577211900833315073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9829875436282534444420097 7372406577211900833315073)
          ·
            refine ⟨5529304932908925624986305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7372406577211900833315073 5529304932908925624986305)
            ·
              refine ⟨4146978699681694218739729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5529304932908925624986305 4146978699681694218739729)
              ·
                refine ⟨3110234024761270664054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146978699681694218739729 3110234024761270664054797)
                ·
                  refine ⟨1166337759285476499020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3110234024761270664054797 1166337759285476499020549)
                  ·
                    refine ⟨218688329866026843566353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166337759285476499020549 218688329866026843566353)
                    ·
                      rfl

theorem cell22_638841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_638841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638841 prefixEnd_638841 := by exact prefixLift 638841
  have htrace : WordTrace (prefixWord ++ tailWord_638841) baseStart_638841 baseEnd_638841 := by
    simpa [prefixWord, tailWord_638841, baseEnd_638841] using wordTrace_append hprefix tailTrace_638841
  have hstable : (prefixWord ++ tailWord_638841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638841).length < 2 ^ (prefixWord ++ tailWord_638841).sum := by decide
  have hdescent : baseEnd_638841 < baseStart_638841 := by decide
  rcases family_descends (prefixWord ++ tailWord_638841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638871 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_638871 : Nat := 118140960795 + 638871 * 2 ^ 59
def prefixEnd_638871 : Nat := 4983230072969 + 3 ^ 40 * 638871 * 2
def baseEnd_638871 : Nat := 218698599479116765316261

theorem tailTrace_638871 : CollatzResearch.WordTrace tailWord_638871 prefixEnd_638871 218698599479116765316261 := by
  unfold tailWord_638871
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301539668486952325180467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15534359778991301550120311 23301539668486952325180467)
  ·
    refine ⟨34952309502730428487770701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23301539668486952325180467 34952309502730428487770701)
    ·
      refine ⟨13107116063523910682914013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34952309502730428487770701 13107116063523910682914013)
      ·
        refine ⟨4915168523821466506092755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13107116063523910682914013 4915168523821466506092755)
        ·
          refine ⟨7372752785732199759139133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915168523821466506092755 7372752785732199759139133)
          ·
            refine ⟨2764782294649574909677175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7372752785732199759139133 2764782294649574909677175)
            ·
              refine ⟨4147173441974362364515763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764782294649574909677175 4147173441974362364515763)
              ·
                refine ⟨6220760162961543546773645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147173441974362364515763 6220760162961543546773645)
                ·
                  refine ⟨2332785061110578830040117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6220760162961543546773645 2332785061110578830040117)
                  ·
                    refine ⟨218698599479116765316261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2332785061110578830040117 218698599479116765316261)
                    ·
                      rfl

theorem cell22_638871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_638871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638871 prefixEnd_638871 := by exact prefixLift 638871
  have htrace : WordTrace (prefixWord ++ tailWord_638871) baseStart_638871 baseEnd_638871 := by
    simpa [prefixWord, tailWord_638871, baseEnd_638871] using wordTrace_append hprefix tailTrace_638871
  have hstable : (prefixWord ++ tailWord_638871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638871).length < 2 ^ (prefixWord ++ tailWord_638871).sum := by decide
  have hdescent : baseEnd_638871 < baseStart_638871 := by decide
  rcases family_descends (prefixWord ++ tailWord_638871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638920 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_638920 : Nat := 118140960795 + 638920 * 2 ^ 59
def prefixEnd_638920 : Nat := 4983230072969 + 3 ^ 40 * 638920 * 2
def baseEnd_638920 : Nat := 218715373180496970841111

theorem tailTrace_638920 : CollatzResearch.WordTrace tailWord_638920 prefixEnd_638920 218715373180496970841111 := by
  unfold tailWord_638920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651663422654716846857107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15535551230206289129142809 11651663422654716846857107)
  ·
    refine ⟨17477495133982075270285661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651663422654716846857107 17477495133982075270285661)
    ·
      refine ⟨6554060675243278226357123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17477495133982075270285661 6554060675243278226357123)
      ·
        refine ⟨9831091012864917339535685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554060675243278226357123 9831091012864917339535685)
        ·
          refine ⟨1843329564912172001162941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9831091012864917339535685 1843329564912172001162941)
          ·
            refine ⟨691248586842064500436103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1843329564912172001162941 691248586842064500436103)
            ·
              refine ⟨1036872880263096750654155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691248586842064500436103 1036872880263096750654155)
              ·
                refine ⟨1555309320394645125981233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036872880263096750654155 1555309320394645125981233)
                ·
                  refine ⟨1166481990295983844485925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555309320394645125981233 1166481990295983844485925)
                  ·
                    refine ⟨218715373180496970841111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166481990295983844485925 218715373180496970841111)
                    ·
                      rfl

theorem cell22_638920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_638920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638920 prefixEnd_638920 := by exact prefixLift 638920
  have htrace : WordTrace (prefixWord ++ tailWord_638920) baseStart_638920 baseEnd_638920 := by
    simpa [prefixWord, tailWord_638920, baseEnd_638920] using wordTrace_append hprefix tailTrace_638920
  have hstable : (prefixWord ++ tailWord_638920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638920).length < 2 ^ (prefixWord ++ tailWord_638920).sum := by decide
  have hdescent : baseEnd_638920 < baseStart_638920 := by decide
  rcases family_descends (prefixWord ++ tailWord_638920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639023 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 6, 3]
def baseStart_639023 : Nat := 118140960795 + 639023 * 2 ^ 59
def prefixEnd_639023 : Nat := 4983230072969 + 3 ^ 40 * 639023 * 2
def baseEnd_639023 : Nat := 218750632185439035515795

theorem tailTrace_639023 : CollatzResearch.WordTrace tailWord_639023 prefixEnd_639023 218750632185439035515795 := by
  unfold tailWord_639023
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307083563936282284713723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15538055709290854856475815 23307083563936282284713723)
  ·
    refine ⟨34960625345904423427070585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23307083563936282284713723 34960625345904423427070585)
    ·
      refine ⟨26220469009428317570302939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34960625345904423427070585 26220469009428317570302939)
      ·
        refine ⟨39330703514142476355454409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26220469009428317570302939 39330703514142476355454409)
        ·
          refine ⟨29498027635606857266590807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39330703514142476355454409 29498027635606857266590807)
          ·
            refine ⟨44247041453410285899886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29498027635606857266590807 44247041453410285899886211)
            ·
              refine ⟨66370562180115428849829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44247041453410285899886211 66370562180115428849829317)
              ·
                refine ⟨12444480408771642909342997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66370562180115428849829317 12444480408771642909342997)
                ·
                  refine ⟨583335019161170761375453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12444480408771642909342997 583335019161170761375453)
                  ·
                    refine ⟨218750632185439035515795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583335019161170761375453 218750632185439035515795)
                    ·
                      rfl

theorem cell22_639023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_639023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639023 prefixEnd_639023 := by exact prefixLift 639023
  have htrace : WordTrace (prefixWord ++ tailWord_639023) baseStart_639023 baseEnd_639023 := by
    simpa [prefixWord, tailWord_639023, baseEnd_639023] using wordTrace_append hprefix tailTrace_639023
  have hstable : (prefixWord ++ tailWord_639023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639023).length < 2 ^ (prefixWord ++ tailWord_639023).sum := by decide
  have hdescent : baseEnd_639023 < baseStart_639023 := by decide
  rcases family_descends (prefixWord ++ tailWord_639023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639113 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_639113 : Nat := 118140960795 + 639113 * 2 ^ 59
def prefixEnd_639113 : Nat := 4983230072969 + 3 ^ 40 * 639113 * 2
def baseEnd_639113 : Nat := 218781441024708800765519

theorem tailTrace_639113 : CollatzResearch.WordTrace tailWord_639113 prefixEnd_639113 218781441024708800765519 := by
  unfold tailWord_639113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23310366133610227655489993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15540244089073485103659995 23310366133610227655489993)
  ·
    refine ⟨17482774600207670741617495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23310366133610227655489993 17482774600207670741617495)
    ·
      refine ⟨26224161900311506112426243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17482774600207670741617495 26224161900311506112426243)
      ·
        refine ⟨39336242850467259168639365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26224161900311506112426243 39336242850467259168639365)
        ·
          refine ⟨7375545534462611094119881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39336242850467259168639365 7375545534462611094119881)
          ·
            refine ⟨5531659150846958320589911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7375545534462611094119881 5531659150846958320589911)
            ·
              refine ⟨8297488726270437480884867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531659150846958320589911 8297488726270437480884867)
              ·
                refine ⟨12446233089405656221327301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297488726270437480884867 12446233089405656221327301)
                ·
                  refine ⟨2333668704263560541498869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12446233089405656221327301 2333668704263560541498869)
                  ·
                    refine ⟨218781441024708800765519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2333668704263560541498869 218781441024708800765519)
                    ·
                      rfl

theorem cell22_639113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_639113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639113 prefixEnd_639113 := by exact prefixLift 639113
  have htrace : WordTrace (prefixWord ++ tailWord_639113) baseStart_639113 baseEnd_639113 := by
    simpa [prefixWord, tailWord_639113, baseEnd_639113] using wordTrace_append hprefix tailTrace_639113
  have hstable : (prefixWord ++ tailWord_639113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639113).length < 2 ^ (prefixWord ++ tailWord_639113).sum := by decide
  have hdescent : baseEnd_639113 < baseStart_639113 := by decide
  rcases family_descends (prefixWord ++ tailWord_639113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639132 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_639132 : Nat := 118140960795 + 639132 * 2 ^ 59
def prefixEnd_639132 : Nat := 4983230072969 + 3 ^ 40 * 639132 * 2
def baseEnd_639132 : Nat := 72929315037666361513487

theorem tailTrace_639132 : CollatzResearch.WordTrace tailWord_639132 prefixEnd_639132 72929315037666361513487 := by
  unfold tailWord_639132
  simp only [CollatzResearch.WordTrace]
  refine ⟨11655529560270696950215825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15540706080360929266954433 11655529560270696950215825)
  ·
    refine ⟨8741647170203022712661869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11655529560270696950215825 8741647170203022712661869)
    ·
      refine ⟨3278117688826133517248201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8741647170203022712661869 3278117688826133517248201)
      ·
        refine ⟨2458588266619600137936151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3278117688826133517248201 2458588266619600137936151)
        ·
          refine ⟨3687882399929400206904227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458588266619600137936151 3687882399929400206904227)
          ·
            refine ⟨5531823599894100310356341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687882399929400206904227 5531823599894100310356341)
            ·
              refine ⟨518608462490071904095907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5531823599894100310356341 518608462490071904095907)
              ·
                refine ⟨777912693735107856143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518608462490071904095907 777912693735107856143861)
                ·
                  refine ⟨72929315037666361513487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 777912693735107856143861 72929315037666361513487)
                  ·
                    rfl

theorem cell22_639132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_639132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639132 prefixEnd_639132 := by exact prefixLift 639132
  have htrace : WordTrace (prefixWord ++ tailWord_639132) baseStart_639132 baseEnd_639132 := by
    simpa [prefixWord, tailWord_639132, baseEnd_639132] using wordTrace_append hprefix tailTrace_639132
  have hstable : (prefixWord ++ tailWord_639132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639132).length < 2 ^ (prefixWord ++ tailWord_639132).sum := by decide
  have hdescent : baseEnd_639132 < baseStart_639132 := by decide
  rcases family_descends (prefixWord ++ tailWord_639132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639153 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_639153 : Nat := 118140960795 + 639153 * 2 ^ 59
def prefixEnd_639153 : Nat := 4983230072969 + 3 ^ 40 * 639153 * 2
def baseEnd_639153 : Nat := 218795133842162029765397

theorem tailTrace_639153 : CollatzResearch.WordTrace tailWord_639153 prefixEnd_639153 218795133842162029765397 := by
  unfold tailWord_639153
  simp only [CollatzResearch.WordTrace]
  refine ⟨23311825053465314486946113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15541216702310209657964075 23311825053465314486946113)
  ·
    refine ⟨17483868790098985865209585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23311825053465314486946113 17483868790098985865209585)
    ·
      refine ⟨13112901592574239398907189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17483868790098985865209585 13112901592574239398907189)
      ·
        refine ⟨1229334524303834943647549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13112901592574239398907189 1229334524303834943647549)
        ·
          refine ⟨461000446613938103867831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1229334524303834943647549 461000446613938103867831)
          ·
            refine ⟨691500669920907155801747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461000446613938103867831 691500669920907155801747)
            ·
              refine ⟨1037251004881360733702621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691500669920907155801747 1037251004881360733702621)
              ·
                refine ⟨388969126830510275138483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1037251004881360733702621 388969126830510275138483)
                ·
                  refine ⟨583453690245765412707725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388969126830510275138483 583453690245765412707725)
                  ·
                    refine ⟨218795133842162029765397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583453690245765412707725 218795133842162029765397)
                    ·
                      rfl

theorem cell22_639153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_639153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639153 prefixEnd_639153 := by exact prefixLift 639153
  have htrace : WordTrace (prefixWord ++ tailWord_639153) baseStart_639153 baseEnd_639153 := by
    simpa [prefixWord, tailWord_639153, baseEnd_639153] using wordTrace_append hprefix tailTrace_639153
  have hstable : (prefixWord ++ tailWord_639153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639153).length < 2 ^ (prefixWord ++ tailWord_639153).sum := by decide
  have hdescent : baseEnd_639153 < baseStart_639153 := by decide
  rcases family_descends (prefixWord ++ tailWord_639153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639170 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_639170 : Nat := 118140960795 + 639170 * 2 ^ 59
def prefixEnd_639170 : Nat := 4983230072969 + 3 ^ 40 * 639170 * 2
def baseEnd_639170 : Nat := 218800953289579652090345

theorem tailTrace_639170 : CollatzResearch.WordTrace tailWord_639170 prefixEnd_639170 218800953289579652090345 := by
  unfold tailWord_639170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828111273600931597578741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15541630062935817593543309 5828111273600931597578741)
  ·
    refine ⟨546385431900087337273007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5828111273600931597578741 546385431900087337273007)
    ·
      refine ⟨819578147850131005909511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546385431900087337273007 819578147850131005909511)
      ·
        refine ⟨1229367221775196508864267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819578147850131005909511 1229367221775196508864267)
        ·
          refine ⟨1844050832662794763296401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229367221775196508864267 1844050832662794763296401)
          ·
            refine ⟨1383038124497096072472301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844050832662794763296401 1383038124497096072472301)
            ·
              refine ⟨518639296686411027177113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383038124497096072472301 518639296686411027177113)
              ·
                refine ⟨388979472514808270382835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518639296686411027177113 388979472514808270382835)
                ·
                  refine ⟨583469208772212405574253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388979472514808270382835 583469208772212405574253)
                  ·
                    refine ⟨218800953289579652090345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583469208772212405574253 218800953289579652090345)
                    ·
                      rfl

theorem cell22_639170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_639170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639170 prefixEnd_639170 := by exact prefixLift 639170
  have htrace : WordTrace (prefixWord ++ tailWord_639170) baseStart_639170 baseEnd_639170 := by
    simpa [prefixWord, tailWord_639170, baseEnd_639170] using wordTrace_append hprefix tailTrace_639170
  have hstable : (prefixWord ++ tailWord_639170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639170).length < 2 ^ (prefixWord ++ tailWord_639170).sum := by decide
  have hdescent : baseEnd_639170 < baseStart_639170 := by decide
  rcases family_descends (prefixWord ++ tailWord_639170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639205 : List Nat := [1, 3, 1, 4, 2, 1, 2, 8]
def baseStart_639205 : Nat := 118140960795 + 639205 * 2 ^ 59
def prefixEnd_639205 : Nat := 4983230072969 + 3 ^ 40 * 639205 * 2
def baseEnd_639205 : Nat := 24312548278316803051693

theorem tailTrace_639205 : CollatzResearch.WordTrace tailWord_639205 prefixEnd_639205 24312548278316803051693 := by
  unfold tailWord_639205
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313721649276927367839069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15542481099517951578559379 23313721649276927367839069)
  ·
    refine ⟨8742645618478847762939651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23313721649276927367839069 8742645618478847762939651)
    ·
      refine ⟨13113968427718271644409477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742645618478847762939651 13113968427718271644409477)
      ·
        refine ⟨2458869080197175933326777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13113968427718271644409477 2458869080197175933326777)
        ·
          refine ⟨1844151810147881949995083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458869080197175933326777 1844151810147881949995083)
          ·
            refine ⟨2766227715221822924992625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844151810147881949995083 2766227715221822924992625)
            ·
              refine ⟨2074670786416367193744469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766227715221822924992625 2074670786416367193744469)
              ·
                refine ⟨24312548278316803051693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2074670786416367193744469 24312548278316803051693)
                ·
                  rfl

theorem cell22_639205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 8].length) (baseStart_639205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639205 prefixEnd_639205 := by exact prefixLift 639205
  have htrace : WordTrace (prefixWord ++ tailWord_639205) baseStart_639205 baseEnd_639205 := by
    simpa [prefixWord, tailWord_639205, baseEnd_639205] using wordTrace_append hprefix tailTrace_639205
  have hstable : (prefixWord ++ tailWord_639205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639205).length < 2 ^ (prefixWord ++ tailWord_639205).sum := by decide
  have hdescent : baseEnd_639205 < baseStart_639205 := by decide
  rcases family_descends (prefixWord ++ tailWord_639205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639207 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_639207 : Nat := 118140960795 + 639207 * 2 ^ 59
def prefixEnd_639207 : Nat := 4983230072969 + 3 ^ 40 * 639207 * 2
def baseEnd_639207 : Nat := 218813619145723888915231

theorem tailTrace_639207 : CollatzResearch.WordTrace tailWord_639207 prefixEnd_639207 218813619145723888915231 := by
  unfold tailWord_639207
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313794595269681709411875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15542529730179787806274583 23313794595269681709411875)
  ·
    refine ⟨34970691892904522564117813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23313794595269681709411875 34970691892904522564117813)
    ·
      refine ⟨3278502364959798990386045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34970691892904522564117813 3278502364959798990386045)
      ·
        refine ⟨1229438386859924621394767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278502364959798990386045 1229438386859924621394767)
        ·
          refine ⟨1844157580289886932092151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229438386859924621394767 1844157580289886932092151)
          ·
            refine ⟨2766236370434830398138227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844157580289886932092151 2766236370434830398138227)
            ·
              refine ⟨4149354555652245597207341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766236370434830398138227 4149354555652245597207341)
              ·
                refine ⟨1556007958369592098952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149354555652245597207341 1556007958369592098952753)
                ·
                  refine ⟨1167005968777194074214565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556007958369592098952753 1167005968777194074214565)
                  ·
                    refine ⟨218813619145723888915231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167005968777194074214565 218813619145723888915231)
                    ·
                      rfl

theorem cell22_639207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_639207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639207 prefixEnd_639207 := by exact prefixLift 639207
  have htrace : WordTrace (prefixWord ++ tailWord_639207) baseStart_639207 baseEnd_639207 := by
    simpa [prefixWord, tailWord_639207, baseEnd_639207] using wordTrace_append hprefix tailTrace_639207
  have hstable : (prefixWord ++ tailWord_639207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639207).length < 2 ^ (prefixWord ++ tailWord_639207).sum := by decide
  have hdescent : baseEnd_639207 < baseStart_639207 := by decide
  rcases family_descends (prefixWord ++ tailWord_639207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639239 : List Nat := [1, 1, 4, 5, 1, 2, 1, 7]
def baseStart_639239 : Nat := 118140960795 + 639239 * 2 ^ 59
def prefixEnd_639239 : Nat := 4983230072969 + 3 ^ 40 * 639239 * 2
def baseEnd_639239 : Nat := 24313841488854052457237

theorem tailTrace_639239 : CollatzResearch.WordTrace tailWord_639239 prefixEnd_639239 24313841488854052457237 := by
  unfold tailWord_639239
  simp only [CollatzResearch.WordTrace]
  refine ⟨23314961731153751174576771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15543307820769167449717847 23314961731153751174576771)
  ·
    refine ⟨34972442596730626761865157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23314961731153751174576771 34972442596730626761865157)
    ·
      refine ⟨6557332986886992517849717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34972442596730626761865157 6557332986886992517849717)
      ·
        refine ⟨614749967520655548548411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6557332986886992517849717 614749967520655548548411)
        ·
          refine ⟨922124951280983322822617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614749967520655548548411 922124951280983322822617)
          ·
            refine ⟨691593713460737492116963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922124951280983322822617 691593713460737492116963)
            ·
              refine ⟨1037390570191106238175445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691593713460737492116963 1037390570191106238175445)
              ·
                refine ⟨24313841488854052457237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1037390570191106238175445 24313841488854052457237)
                ·
                  rfl

theorem cell22_639239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 7].length) (baseStart_639239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639239 prefixEnd_639239 := by exact prefixLift 639239
  have htrace : WordTrace (prefixWord ++ tailWord_639239) baseStart_639239 baseEnd_639239 := by
    simpa [prefixWord, tailWord_639239, baseEnd_639239] using wordTrace_append hprefix tailTrace_639239
  have hstable : (prefixWord ++ tailWord_639239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639239).length < 2 ^ (prefixWord ++ tailWord_639239).sum := by decide
  have hdescent : baseEnd_639239 < baseStart_639239 := by decide
  rcases family_descends (prefixWord ++ tailWord_639239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_639280 : Nat := 118140960795 + 639280 * 2 ^ 59
def prefixEnd_639280 : Nat := 4983230072969 + 3 ^ 40 * 639280 * 2
def baseEnd_639280 : Nat := 218838608537576031840007

theorem tailTrace_639280 : CollatzResearch.WordTrace tailWord_639280 prefixEnd_639280 218838608537576031840007 := by
  unfold tailWord_639280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658228562002607588409647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15544304749336810117879529 11658228562002607588409647)
  ·
    refine ⟨17487342843003911382614471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11658228562002607588409647 17487342843003911382614471)
    ·
      refine ⟨26231014264505867073921707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17487342843003911382614471 26231014264505867073921707)
      ·
        refine ⟨39346521396758800610882561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26231014264505867073921707 39346521396758800610882561)
        ·
          refine ⟨29509891047569100458161921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39346521396758800610882561 29509891047569100458161921)
          ·
            refine ⟨22132418285676825343621441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29509891047569100458161921 22132418285676825343621441)
            ·
              refine ⟨16599313714257619007716081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22132418285676825343621441 16599313714257619007716081)
              ·
                refine ⟨12449485285693214255787061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16599313714257619007716081 12449485285693214255787061)
                ·
                  refine ⟨1167139245533738836480037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12449485285693214255787061 1167139245533738836480037)
                  ·
                    refine ⟨218838608537576031840007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167139245533738836480037 218838608537576031840007)
                    ·
                      rfl

theorem cell22_639280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_639280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639280 prefixEnd_639280 := by exact prefixLift 639280
  have htrace : WordTrace (prefixWord ++ tailWord_639280) baseStart_639280 baseEnd_639280 := by
    simpa [prefixWord, tailWord_639280, baseEnd_639280] using wordTrace_append hprefix tailTrace_639280
  have hstable : (prefixWord ++ tailWord_639280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639280).length < 2 ^ (prefixWord ++ tailWord_639280).sum := by decide
  have hdescent : baseEnd_639280 < baseStart_639280 := by decide
  rcases family_descends (prefixWord ++ tailWord_639280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639284 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_639284 : Nat := 118140960795 + 639284 * 2 ^ 59
def prefixEnd_639284 : Nat := 4983230072969 + 3 ^ 40 * 639284 * 2
def baseEnd_639284 : Nat := 72946659273107118246665

theorem tailTrace_639284 : CollatzResearch.WordTrace tailWord_639284 prefixEnd_639284 72946659273107118246665 := by
  unfold tailWord_639284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658301507995361929982453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15544402010660482573309937 11658301507995361929982453)
  ·
    refine ⟨1092965766374565180935855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11658301507995361929982453 1092965766374565180935855)
    ·
      refine ⟨1639448649561847771403783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092965766374565180935855 1639448649561847771403783)
      ·
        refine ⟨2459172974342771657105675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639448649561847771403783 2459172974342771657105675)
        ·
          refine ⟨3688759461514157485658513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459172974342771657105675 3688759461514157485658513)
          ·
            refine ⟨2766569596135618114243885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688759461514157485658513 2766569596135618114243885)
            ·
              refine ⟨1037463598550856792841457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2766569596135618114243885 1037463598550856792841457)
              ·
                refine ⟨778097698913142594631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037463598550856792841457 778097698913142594631093)
                ·
                  refine ⟨72946659273107118246665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 778097698913142594631093 72946659273107118246665)
                  ·
                    rfl

theorem cell22_639284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_639284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639284 prefixEnd_639284 := by exact prefixLift 639284
  have htrace : WordTrace (prefixWord ++ tailWord_639284) baseStart_639284 baseEnd_639284 := by
    simpa [prefixWord, tailWord_639284, baseEnd_639284] using wordTrace_append hprefix tailTrace_639284
  have hstable : (prefixWord ++ tailWord_639284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639284).length < 2 ^ (prefixWord ++ tailWord_639284).sum := by decide
  have hdescent : baseEnd_639284 < baseStart_639284 := by decide
  rcases family_descends (prefixWord ++ tailWord_639284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639327 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 4, 3]
def baseStart_639327 : Nat := 118140960795 + 639327 * 2 ^ 59
def prefixEnd_639327 : Nat := 4983230072969 + 3 ^ 40 * 639327 * 2
def baseEnd_639327 : Nat := 218854697598083575914863

theorem tailTrace_639327 : CollatzResearch.WordTrace tailWord_639327 prefixEnd_639327 218854697598083575914863 := by
  unfold tailWord_639327
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318171354834942203780235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15545447569889961469186823 23318171354834942203780235)
  ·
    refine ⟨34977257032252413305670353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23318171354834942203780235 34977257032252413305670353)
    ·
      refine ⟨26232942774189309979252765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34977257032252413305670353 26232942774189309979252765)
      ·
        refine ⟨9837353540320991242219787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26232942774189309979252765 9837353540320991242219787)
        ·
          refine ⟨14756030310481486863329681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9837353540320991242219787 14756030310481486863329681)
          ·
            refine ⟨11067022732861115147497261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14756030310481486863329681 11067022732861115147497261)
            ·
              refine ⟨4150133524822918180311473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11067022732861115147497261 4150133524822918180311473)
              ·
                refine ⟨3112600143617188635233605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150133524822918180311473 3112600143617188635233605)
                ·
                  refine ⟨583612526928222869106301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3112600143617188635233605 583612526928222869106301)
                  ·
                    refine ⟨218854697598083575914863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583612526928222869106301 218854697598083575914863)
                    ·
                      rfl

theorem cell22_639327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_639327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639327 prefixEnd_639327 := by exact prefixLift 639327
  have htrace : WordTrace (prefixWord ++ tailWord_639327) baseStart_639327 baseEnd_639327 := by
    simpa [prefixWord, tailWord_639327, baseEnd_639327] using wordTrace_append hprefix tailTrace_639327
  have hstable : (prefixWord ++ tailWord_639327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639327).length < 2 ^ (prefixWord ++ tailWord_639327).sum := by decide
  have hdescent : baseEnd_639327 < baseStart_639327 := by decide
  rcases family_descends (prefixWord ++ tailWord_639327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639346 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_639346 : Nat := 118140960795 + 639346 * 2 ^ 59
def prefixEnd_639346 : Nat := 4983230072969 + 3 ^ 40 * 639346 * 2
def baseEnd_639346 : Nat := 72953733895457953229935

theorem tailTrace_639346 : CollatzResearch.WordTrace tailWord_639346 prefixEnd_639346 72953733895457953229935 := by
  unfold tailWord_639346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829716085441527112180473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15545909561177405632481261 5829716085441527112180473)
  ·
    refine ⟨4372287064081145334135355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5829716085441527112180473 4372287064081145334135355)
    ·
      refine ⟨6558430596121718001203033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372287064081145334135355 6558430596121718001203033)
      ·
        refine ⟨4918822947091288500902275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6558430596121718001203033 4918822947091288500902275)
        ·
          refine ⟨7378234420636932751353413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4918822947091288500902275 7378234420636932751353413)
          ·
            refine ⟨1383418953869424890878765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7378234420636932751353413 1383418953869424890878765)
            ·
              refine ⟨518782107701034334079537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383418953869424890878765 518782107701034334079537)
              ·
                refine ⟨389086580775775750559653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518782107701034334079537 389086580775775750559653)
                ·
                  refine ⟨72953733895457953229935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389086580775775750559653 72953733895457953229935)
                  ·
                    rfl

theorem cell22_639346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_639346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639346 prefixEnd_639346 := by exact prefixLift 639346
  have htrace : WordTrace (prefixWord ++ tailWord_639346) baseStart_639346 baseEnd_639346 := by
    simpa [prefixWord, tailWord_639346, baseEnd_639346] using wordTrace_append hprefix tailTrace_639346
  have hstable : (prefixWord ++ tailWord_639346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639346).length < 2 ^ (prefixWord ++ tailWord_639346).sum := by decide
  have hdescent : baseEnd_639346 < baseStart_639346 := by decide
  rcases family_descends (prefixWord ++ tailWord_639346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639357 : List Nat := [1, 4, 1, 1, 2, 4, 2, 7]
def baseStart_639357 : Nat := 118140960795 + 639357 * 2 ^ 59
def prefixEnd_639357 : Nat := 4983230072969 + 3 ^ 40 * 639357 * 2
def baseEnd_639357 : Nat := 24318329690130388629419

theorem tailTrace_639357 : CollatzResearch.WordTrace tailWord_639357 prefixEnd_639357 24318329690130388629419 := by
  unfold tailWord_639357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23319265544726257327372325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15546177029817504884914883 23319265544726257327372325)
  ·
    refine ⟨4372362289636173248882311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23319265544726257327372325 4372362289636173248882311)
    ·
      refine ⟨6558543434454259873323467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372362289636173248882311 6558543434454259873323467)
      ·
        refine ⟨9837815151681389809985201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558543434454259873323467 9837815151681389809985201)
        ·
          refine ⟨7378361363761042357488901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9837815151681389809985201 7378361363761042357488901)
          ·
            refine ⟨1383442755705195442029169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7378361363761042357488901 1383442755705195442029169)
            ·
              refine ⟨1037582066778896581521877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383442755705195442029169 1037582066778896581521877)
              ·
                refine ⟨24318329690130388629419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1037582066778896581521877 24318329690130388629419)
                ·
                  rfl

theorem cell22_639357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 7].length) (baseStart_639357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639357 prefixEnd_639357 := by exact prefixLift 639357
  have htrace : WordTrace (prefixWord ++ tailWord_639357) baseStart_639357 baseEnd_639357 := by
    simpa [prefixWord, tailWord_639357, baseEnd_639357] using wordTrace_append hprefix tailTrace_639357
  have hstable : (prefixWord ++ tailWord_639357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639357).length < 2 ^ (prefixWord ++ tailWord_639357).sum := by decide
  have hdescent : baseEnd_639357 < baseStart_639357 := by decide
  rcases family_descends (prefixWord ++ tailWord_639357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639361 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_639361 : Nat := 118140960795 + 639361 * 2 ^ 59
def prefixEnd_639361 : Nat := 4983230072969 + 3 ^ 40 * 639361 * 2
def baseEnd_639361 : Nat := 218866336492918820564759

theorem tailTrace_639361 : CollatzResearch.WordTrace tailWord_639361 prefixEnd_639361 218866336492918820564759 := by
  unfold tailWord_639361
  simp only [CollatzResearch.WordTrace]
  refine ⟨23319411436711766010517937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15546274291141177340345291 23319411436711766010517937)
  ·
    refine ⟨17489558577533824507888453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23319411436711766010517937 17489558577533824507888453)
    ·
      refine ⟨3279292233287592095229085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17489558577533824507888453 3279292233287592095229085)
      ·
        refine ⟨1229734587482847035710907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3279292233287592095229085 1229734587482847035710907)
        ·
          refine ⟨1844601881224270553566361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229734587482847035710907 1844601881224270553566361)
          ·
            refine ⟨1383451410918202915174771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844601881224270553566361 1383451410918202915174771)
            ·
              refine ⟨2075177116377304372762157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383451410918202915174771 2075177116377304372762157)
              ·
                refine ⟨778191418641489139785809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2075177116377304372762157 778191418641489139785809)
                ·
                  refine ⟨583643563981116854839357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778191418641489139785809 583643563981116854839357)
                  ·
                    refine ⟨218866336492918820564759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583643563981116854839357 218866336492918820564759)
                    ·
                      rfl

theorem cell22_639361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_639361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639361 prefixEnd_639361 := by exact prefixLift 639361
  have htrace : WordTrace (prefixWord ++ tailWord_639361) baseStart_639361 baseEnd_639361 := by
    simpa [prefixWord, tailWord_639361, baseEnd_639361] using wordTrace_append hprefix tailTrace_639361
  have hstable : (prefixWord ++ tailWord_639361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639361).length < 2 ^ (prefixWord ++ tailWord_639361).sum := by decide
  have hdescent : baseEnd_639361 < baseStart_639361 := by decide
  rcases family_descends (prefixWord ++ tailWord_639361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639382 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_639382 : Nat := 118140960795 + 639382 * 2 ^ 59
def prefixEnd_639382 : Nat := 4983230072969 + 3 ^ 40 * 639382 * 2
def baseEnd_639382 : Nat := 218873525222081765789695

theorem tailTrace_639382 : CollatzResearch.WordTrace tailWord_639382 prefixEnd_639382 218873525222081765789695 := by
  unfold tailWord_639382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1457511085602230412314525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15546784913090457731354933 1457511085602230412314525)
  ·
    refine ⟨546566657100836404617947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1457511085602230412314525 546566657100836404617947)
    ·
      refine ⟨819849985651254606926921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546566657100836404617947 819849985651254606926921)
      ·
        refine ⟨614887489238440955195191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819849985651254606926921 614887489238440955195191)
        ·
          refine ⟨922331233857661432792787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614887489238440955195191 922331233857661432792787)
          ·
            refine ⟨1383496850786492149189181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922331233857661432792787 1383496850786492149189181)
            ·
              refine ⟨518811319044934555945943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383496850786492149189181 518811319044934555945943)
              ·
                refine ⟨778216978567401833918915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518811319044934555945943 778216978567401833918915)
                ·
                  refine ⟨1167325467851102750878373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778216978567401833918915 1167325467851102750878373)
                  ·
                    refine ⟨218873525222081765789695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167325467851102750878373 218873525222081765789695)
                    ·
                      rfl

theorem cell22_639382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_639382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639382 prefixEnd_639382 := by exact prefixLift 639382
  have htrace : WordTrace (prefixWord ++ tailWord_639382) baseStart_639382 baseEnd_639382 := by
    simpa [prefixWord, tailWord_639382, baseEnd_639382] using wordTrace_append hprefix tailTrace_639382
  have hstable : (prefixWord ++ tailWord_639382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639382).length < 2 ^ (prefixWord ++ tailWord_639382).sum := by decide
  have hdescent : baseEnd_639382 < baseStart_639382 := by decide
  rcases family_descends (prefixWord ++ tailWord_639382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639417 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_639417 : Nat := 118140960795 + 639417 * 2 ^ 59
def prefixEnd_639417 : Nat := 4983230072969 + 3 ^ 40 * 639417 * 2
def baseEnd_639417 : Nat := 218885506437353341164587

theorem tailTrace_639417 : CollatzResearch.WordTrace tailWord_639417 prefixEnd_639417 218885506437353341164587 := by
  unfold tailWord_639417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321453924508887574556505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15547635949672591716371003 23321453924508887574556505)
  ·
    refine ⟨17491090443381665680917379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23321453924508887574556505 17491090443381665680917379)
    ·
      refine ⟨26236635665072498521376069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17491090443381665680917379 26236635665072498521376069)
      ·
        refine ⟨4919369187201093472758013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26236635665072498521376069 4919369187201093472758013)
        ·
          refine ⟨1844763445200410052284255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4919369187201093472758013 1844763445200410052284255)
          ·
            refine ⟨2767145167800615078426383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844763445200410052284255 2767145167800615078426383)
            ·
              refine ⟨4150717751700922617639575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767145167800615078426383 4150717751700922617639575)
              ·
                refine ⟨6226076627551383926459363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150717751700922617639575 6226076627551383926459363)
                ·
                  refine ⟨9339114941327075889689045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226076627551383926459363 9339114941327075889689045)
                  ·
                    refine ⟨218885506437353341164587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9339114941327075889689045 218885506437353341164587)
                    ·
                      rfl

theorem cell22_639417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_639417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639417 prefixEnd_639417 := by exact prefixLift 639417
  have htrace : WordTrace (prefixWord ++ tailWord_639417) baseStart_639417 baseEnd_639417 := by
    simpa [prefixWord, tailWord_639417, baseEnd_639417] using wordTrace_append hprefix tailTrace_639417
  have hstable : (prefixWord ++ tailWord_639417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639417).length < 2 ^ (prefixWord ++ tailWord_639417).sum := by decide
  have hdescent : baseEnd_639417 < baseStart_639417 := by decide
  rcases family_descends (prefixWord ++ tailWord_639417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639449 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_639449 : Nat := 118140960795 + 639449 * 2 ^ 59
def prefixEnd_639449 : Nat := 4983230072969 + 3 ^ 40 * 639449 * 2
def baseEnd_639449 : Nat := 218896460691315924364489

theorem tailTrace_639449 : CollatzResearch.WordTrace tailWord_639449 prefixEnd_639449 218896460691315924364489 := by
  unfold tailWord_639449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23322621060392957039721401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15548414040261971359814267 23322621060392957039721401)
  ·
    refine ⟨17491965795294717779791051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23322621060392957039721401 17491965795294717779791051)
    ·
      refine ⟨26237948692942076669686577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17491965795294717779791051 26237948692942076669686577)
      ·
        refine ⟨19678461519706557502264933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26237948692942076669686577 19678461519706557502264933)
        ·
          refine ⟨3689711534944979531674675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19678461519706557502264933 3689711534944979531674675)
          ·
            refine ⟨5534567302417469297512013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689711534944979531674675 5534567302417469297512013)
            ·
              refine ⟨2075462738406550986567005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5534567302417469297512013 2075462738406550986567005)
              ·
                refine ⟨778298526902456619962627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2075462738406550986567005 778298526902456619962627)
                ·
                  refine ⟨1167447790353684929943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778298526902456619962627 1167447790353684929943941)
                  ·
                    refine ⟨218896460691315924364489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167447790353684929943941 218896460691315924364489)
                    ·
                      rfl

theorem cell22_639449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_639449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639449 prefixEnd_639449 := by exact prefixLift 639449
  have htrace : WordTrace (prefixWord ++ tailWord_639449) baseStart_639449 baseEnd_639449 := by
    simpa [prefixWord, tailWord_639449, baseEnd_639449] using wordTrace_append hprefix tailTrace_639449
  have hstable : (prefixWord ++ tailWord_639449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639449).length < 2 ^ (prefixWord ++ tailWord_639449).sum := by decide
  have hdescent : baseEnd_639449 < baseStart_639449 := by decide
  rcases family_descends (prefixWord ++ tailWord_639449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639464 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_639464 : Nat := 118140960795 + 639464 * 2 ^ 59
def prefixEnd_639464 : Nat := 4983230072969 + 3 ^ 40 * 639464 * 2
def baseEnd_639464 : Nat := 72967198499286961746481

theorem tailTrace_639464 : CollatzResearch.WordTrace tailWord_639464 prefixEnd_639464 72967198499286961746481 := by
  unfold tailWord_639464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661584077669307300758723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15548778770225743067678297 11661584077669307300758723)
  ·
    refine ⟨17492376116503960951138085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11661584077669307300758723 17492376116503960951138085)
    ·
      refine ⟨3279820521844492678338391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17492376116503960951138085 3279820521844492678338391)
      ·
        refine ⟨4919730782766739017507587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3279820521844492678338391 4919730782766739017507587)
        ·
          refine ⟨7379596174150108526261381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919730782766739017507587 7379596174150108526261381)
          ·
            refine ⟨1383674282653145348674009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7379596174150108526261381 1383674282653145348674009)
            ·
              refine ⟨1037755711989859011505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383674282653145348674009 1037755711989859011505507)
              ·
                refine ⟨1556633567984788517258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037755711989859011505507 1556633567984788517258261)
                ·
                  refine ⟨72967198499286961746481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1556633567984788517258261 72967198499286961746481)
                  ·
                    rfl

theorem cell22_639464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_639464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639464 prefixEnd_639464 := by exact prefixLift 639464
  have htrace : WordTrace (prefixWord ++ tailWord_639464) baseStart_639464 baseEnd_639464 := by
    simpa [prefixWord, tailWord_639464, baseEnd_639464] using wordTrace_append hprefix tailTrace_639464
  have hstable : (prefixWord ++ tailWord_639464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639464).length < 2 ^ (prefixWord ++ tailWord_639464).sum := by decide
  have hdescent : baseEnd_639464 < baseStart_639464 := by decide
  rcases family_descends (prefixWord ++ tailWord_639464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639530 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_639530 : Nat := 118140960795 + 639530 * 2 ^ 59
def prefixEnd_639530 : Nat := 4983230072969 + 3 ^ 40 * 639530 * 2
def baseEnd_639530 : Nat := 218924188646658713089241

theorem tailTrace_639530 : CollatzResearch.WordTrace tailWord_639530 prefixEnd_639530 218924188646658713089241 := by
  unfold tailWord_639530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831393843274876968355011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15550383582066338582280029 5831393843274876968355011)
  ·
    refine ⟨8747090764912315452532517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5831393843274876968355011 8747090764912315452532517)
    ·
      refine ⟨1640079518421059147349847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8747090764912315452532517 1640079518421059147349847)
      ·
        refine ⟨2460119277631588721024771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640079518421059147349847 2460119277631588721024771)
        ·
          refine ⟨3690178916447383081537157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460119277631588721024771 3690178916447383081537157)
          ·
            refine ⟨691908546833884327788217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3690178916447383081537157 691908546833884327788217)
            ·
              refine ⟨518931410125413245841163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691908546833884327788217 518931410125413245841163)
              ·
                refine ⟨778397115188119868761745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518931410125413245841163 778397115188119868761745)
                ·
                  refine ⟨583797836391089901571309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778397115188119868761745 583797836391089901571309)
                  ·
                    refine ⟨218924188646658713089241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583797836391089901571309 218924188646658713089241)
                    ·
                      rfl

theorem cell22_639530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_639530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639530 prefixEnd_639530 := by exact prefixLift 639530
  have htrace : WordTrace (prefixWord ++ tailWord_639530) baseStart_639530 baseEnd_639530 := by
    simpa [prefixWord, tailWord_639530, baseEnd_639530] using wordTrace_append hprefix tailTrace_639530
  have hstable : (prefixWord ++ tailWord_639530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639530).length < 2 ^ (prefixWord ++ tailWord_639530).sum := by decide
  have hdescent : baseEnd_639530 < baseStart_639530 := by decide
  rcases family_descends (prefixWord ++ tailWord_639530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639584 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_639584 : Nat := 118140960795 + 639584 * 2 ^ 59
def prefixEnd_639584 : Nat := 4983230072969 + 3 ^ 40 * 639584 * 2
def baseEnd_639584 : Nat := 218942673950220572239075

theorem tailTrace_639584 : CollatzResearch.WordTrace tailWord_639584 prefixEnd_639584 218942673950220572239075 := by
  unfold tailWord_639584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11663772457451937547942903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15551696609935916730590537 11663772457451937547942903)
  ·
    refine ⟨17495658686177906321914355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11663772457451937547942903 17495658686177906321914355)
    ·
      refine ⟨26243488029266859482871533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17495658686177906321914355 26243488029266859482871533)
      ·
        refine ⟨9841308010975072306076825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26243488029266859482871533 9841308010975072306076825)
        ·
          refine ⟨7380981008231304229557619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9841308010975072306076825 7380981008231304229557619)
          ·
            refine ⟨11071471512346956344336429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7380981008231304229557619 11071471512346956344336429)
            ·
              refine ⟨4151801817130108629126161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11071471512346956344336429 4151801817130108629126161)
              ·
                refine ⟨3113851362847581471844621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151801817130108629126161 3113851362847581471844621)
                ·
                  refine ⟨1167694261067843051941733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3113851362847581471844621 1167694261067843051941733)
                  ·
                    refine ⟨218942673950220572239075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167694261067843051941733 218942673950220572239075)
                    ·
                      rfl

theorem cell22_639584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_639584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639584 prefixEnd_639584 := by exact prefixLift 639584
  have htrace : WordTrace (prefixWord ++ tailWord_639584) baseStart_639584 baseEnd_639584 := by
    simpa [prefixWord, tailWord_639584, baseEnd_639584] using wordTrace_append hprefix tailTrace_639584
  have hstable : (prefixWord ++ tailWord_639584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639584).length < 2 ^ (prefixWord ++ tailWord_639584).sum := by decide
  have hdescent : baseEnd_639584 < baseStart_639584 := by decide
  rcases family_descends (prefixWord ++ tailWord_639584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639616 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_639616 : Nat := 118140960795 + 639616 * 2 ^ 59
def prefixEnd_639616 : Nat := 4983230072969 + 3 ^ 40 * 639616 * 2
def baseEnd_639616 : Nat := 72984542734727718479659

theorem tailTrace_639616 : CollatzResearch.WordTrace tailWord_639616 prefixEnd_639616 72984542734727718479659 := by
  unfold tailWord_639616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11664356025393972280525351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15552474700525296374033801 11664356025393972280525351)
  ·
    refine ⟨17496534038090958420788027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11664356025393972280525351 17496534038090958420788027)
    ·
      refine ⟨26244801057136437631182041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17496534038090958420788027 26244801057136437631182041)
      ·
        refine ⟨19683600792852328223386531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26244801057136437631182041 19683600792852328223386531)
        ·
          refine ⟨29525401189278492335079797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19683600792852328223386531 29525401189278492335079797)
          ·
            refine ⟨2768006361494858656413731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29525401189278492335079797 2768006361494858656413731)
            ·
              refine ⟨4152009542242287984620597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768006361494858656413731 4152009542242287984620597)
              ·
                refine ⟨389250894585214498558181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4152009542242287984620597 389250894585214498558181)
                ·
                  refine ⟨72984542734727718479659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389250894585214498558181 72984542734727718479659)
                  ·
                    rfl

theorem cell22_639616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_639616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639616 prefixEnd_639616 := by exact prefixLift 639616
  have htrace : WordTrace (prefixWord ++ tailWord_639616) baseStart_639616 baseEnd_639616 := by
    simpa [prefixWord, tailWord_639616, baseEnd_639616] using wordTrace_append hprefix tailTrace_639616
  have hstable : (prefixWord ++ tailWord_639616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639616).length < 2 ^ (prefixWord ++ tailWord_639616).sum := by decide
  have hdescent : baseEnd_639616 < baseStart_639616 := by decide
  rcases family_descends (prefixWord ++ tailWord_639616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639646 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_639646 : Nat := 118140960795 + 639646 * 2 ^ 59
def prefixEnd_639646 : Nat := 4983230072969 + 3 ^ 40 * 639646 * 2
def baseEnd_639646 : Nat := 218963897817273077188885

theorem tailTrace_639646 : CollatzResearch.WordTrace tailWord_639646 prefixEnd_639646 218963897817273077188885 := by
  unfold tailWord_639646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916225780084907460580349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15553204160452839789761861 2916225780084907460580349)
  ·
    refine ⟨1093584667531840297717631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2916225780084907460580349 1093584667531840297717631)
    ·
      refine ⟨1640377001297760446576447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093584667531840297717631 1640377001297760446576447)
      ·
        refine ⟨2460565501946640669864671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640377001297760446576447 2460565501946640669864671)
        ·
          refine ⟨3690848252919961004797007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460565501946640669864671 3690848252919961004797007)
          ·
            refine ⟨5536272379379941507195511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690848252919961004797007 5536272379379941507195511)
            ·
              refine ⟨8304408569069912260793267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5536272379379941507195511 8304408569069912260793267)
              ·
                refine ⟨12456612853604868391189901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304408569069912260793267 12456612853604868391189901)
                ·
                  refine ⟨4671229820101825646696213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12456612853604868391189901 4671229820101825646696213)
                  ·
                    refine ⟨218963897817273077188885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4671229820101825646696213 218963897817273077188885)
                    ·
                      rfl

theorem cell22_639646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_639646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639646 prefixEnd_639646 := by exact prefixLift 639646
  have htrace : WordTrace (prefixWord ++ tailWord_639646) baseStart_639646 baseEnd_639646 := by
    simpa [prefixWord, tailWord_639646, baseEnd_639646] using wordTrace_append hprefix tailTrace_639646
  have hstable : (prefixWord ++ tailWord_639646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639646).length < 2 ^ (prefixWord ++ tailWord_639646).sum := by decide
  have hdescent : baseEnd_639646 < baseStart_639646 := by decide
  rcases family_descends (prefixWord ++ tailWord_639646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639648 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_639648 : Nat := 118140960795 + 639648 * 2 ^ 59
def prefixEnd_639648 : Nat := 4983230072969 + 3 ^ 40 * 639648 * 2
def baseEnd_639648 : Nat := 218964582458145738638879

theorem tailTrace_639648 : CollatzResearch.WordTrace tailWord_639648 prefixEnd_639648 218964582458145738638879 := by
  unfold tailWord_639648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11664939593336007013107799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15553252791114676017477065 11664939593336007013107799)
  ·
    refine ⟨17497409390004010519661699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11664939593336007013107799 17497409390004010519661699)
    ·
      refine ⟨26246114085006015779492549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17497409390004010519661699 26246114085006015779492549)
      ·
        refine ⟨4921146390938627958654853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26246114085006015779492549 4921146390938627958654853)
        ·
          refine ⟨922714948300992742247785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4921146390938627958654853 922714948300992742247785)
          ·
            refine ⟨692036211225744556685839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922714948300992742247785 692036211225744556685839)
            ·
              refine ⟨1038054316838616835028759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692036211225744556685839 1038054316838616835028759)
              ·
                refine ⟨1557081475257925252543139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038054316838616835028759 1557081475257925252543139)
                ·
                  refine ⟨2335622212886887878814709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557081475257925252543139 2335622212886887878814709)
                  ·
                    refine ⟨218964582458145738638879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2335622212886887878814709 218964582458145738638879)
                    ·
                      rfl

theorem cell22_639648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_639648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639648 prefixEnd_639648 := by exact prefixLift 639648
  have htrace : WordTrace (prefixWord ++ tailWord_639648) baseStart_639648 baseEnd_639648 := by
    simpa [prefixWord, tailWord_639648, baseEnd_639648] using wordTrace_append hprefix tailTrace_639648
  have hstable : (prefixWord ++ tailWord_639648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639648).length < 2 ^ (prefixWord ++ tailWord_639648).sum := by decide
  have hdescent : baseEnd_639648 < baseStart_639648 := by decide
  rcases family_descends (prefixWord ++ tailWord_639648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639661 : List Nat := [1, 5, 2, 1, 1, 3, 1, 8]
def baseStart_639661 : Nat := 118140960795 + 639661 * 2 ^ 59
def prefixEnd_639661 : Nat := 4983230072969 + 3 ^ 40 * 639661 * 2
def baseEnd_639661 : Nat := 24329892513757559784871

theorem tailTrace_639661 : CollatzResearch.WordTrace tailWord_639661 prefixEnd_639661 24329892513757559784871 := by
  unfold tailWord_639661
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330353335624917246438837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553568890416611497625891 23330353335624917246438837)
  ·
    refine ⟨2187220625214835991853641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23330353335624917246438837 2187220625214835991853641)
    ·
      refine ⟨1640415468911126993890231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187220625214835991853641 1640415468911126993890231)
      ·
        refine ⟨2460623203366690490835347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640415468911126993890231 2460623203366690490835347)
        ·
          refine ⟨3690934805050035736253021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460623203366690490835347 3690934805050035736253021)
          ·
            refine ⟨1384100551893763401094883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3690934805050035736253021 1384100551893763401094883)
            ·
              refine ⟨2076150827840645101642325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384100551893763401094883 2076150827840645101642325)
              ·
                refine ⟨24329892513757559784871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2076150827840645101642325 24329892513757559784871)
                ·
                  rfl

theorem cell22_639661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 8].length) (baseStart_639661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639661 prefixEnd_639661 := by exact prefixLift 639661
  have htrace : WordTrace (prefixWord ++ tailWord_639661) baseStart_639661 baseEnd_639661 := by
    simpa [prefixWord, tailWord_639661, baseEnd_639661] using wordTrace_append hprefix tailTrace_639661
  have hstable : (prefixWord ++ tailWord_639661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639661).length < 2 ^ (prefixWord ++ tailWord_639661).sum := by decide
  have hdescent : baseEnd_639661 < baseStart_639661 := by decide
  rcases family_descends (prefixWord ++ tailWord_639661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639706 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_639706 : Nat := 118140960795 + 639706 * 2 ^ 59
def prefixEnd_639706 : Nat := 4983230072969 + 3 ^ 40 * 639706 * 2
def baseEnd_639706 : Nat := 72994812347817640229567

theorem tailTrace_639706 : CollatzResearch.WordTrace tailWord_639706 prefixEnd_639706 72994812347817640229567 := by
  unfold tailWord_639706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832998655115472482956743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15554663080307926621217981 5832998655115472482956743)
  ·
    refine ⟨8749497982673208724435115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5832998655115472482956743 8749497982673208724435115)
    ·
      refine ⟨13124246974009813086652673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8749497982673208724435115 13124246974009813086652673)
      ·
        refine ⟨9843185230507359814989505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13124246974009813086652673 9843185230507359814989505)
        ·
          refine ⟨7382388922880519861242129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9843185230507359814989505 7382388922880519861242129)
          ·
            refine ⟨5536791692160389895931597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382388922880519861242129 5536791692160389895931597)
            ·
              refine ⟨2076296884560146210974349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5536791692160389895931597 2076296884560146210974349)
              ·
                refine ⟨778611331710054829115381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2076296884560146210974349 778611331710054829115381)
                ·
                  refine ⟨72994812347817640229567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 778611331710054829115381 72994812347817640229567)
                  ·
                    rfl

theorem cell22_639706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_639706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639706 prefixEnd_639706 := by exact prefixLift 639706
  have htrace : WordTrace (prefixWord ++ tailWord_639706) baseStart_639706 baseEnd_639706 := by
    simpa [prefixWord, tailWord_639706, baseEnd_639706] using wordTrace_append hprefix tailTrace_639706
  have hstable : (prefixWord ++ tailWord_639706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639706).length < 2 ^ (prefixWord ++ tailWord_639706).sum := by decide
  have hdescent : baseEnd_639706 < baseStart_639706 := by decide
  rcases family_descends (prefixWord ++ tailWord_639706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639781 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_639781 : Nat := 118140960795 + 639781 * 2 ^ 59
def prefixEnd_639781 : Nat := 4983230072969 + 3 ^ 40 * 639781 * 2
def baseEnd_639781 : Nat := 219010111076177725063471

theorem tailTrace_639781 : CollatzResearch.WordTrace tailWord_639781 prefixEnd_639781 219010111076177725063471 := by
  unfold tailWord_639781
  simp only [CollatzResearch.WordTrace]
  refine ⟨23334730095190177740807197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15556486730126785160538131 23334730095190177740807197)
  ·
    refine ⟨8750523785696316652802699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23334730095190177740807197 8750523785696316652802699)
    ·
      refine ⟨13125785678544474979204049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8750523785696316652802699 13125785678544474979204049)
      ·
        refine ⟨9844339258908356234403037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13125785678544474979204049 9844339258908356234403037)
        ·
          refine ⟨3691627222090633587901139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9844339258908356234403037 3691627222090633587901139)
          ·
            refine ⟨5537440833135950381851709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691627222090633587901139 5537440833135950381851709)
            ·
              refine ⟨2076540312425981393194391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537440833135950381851709 2076540312425981393194391)
              ·
                refine ⟨3114810468638972089791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076540312425981393194391 3114810468638972089791587)
                ·
                  refine ⟨4672215702958458134687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114810468638972089791587 4672215702958458134687381)
                  ·
                    refine ⟨219010111076177725063471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4672215702958458134687381 219010111076177725063471)
                    ·
                      rfl

theorem cell22_639781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_639781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639781 prefixEnd_639781 := by exact prefixLift 639781
  have htrace : WordTrace (prefixWord ++ tailWord_639781) baseStart_639781 baseEnd_639781 := by
    simpa [prefixWord, tailWord_639781, baseEnd_639781] using wordTrace_append hprefix tailTrace_639781
  have hstable : (prefixWord ++ tailWord_639781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639781).length < 2 ^ (prefixWord ++ tailWord_639781).sum := by decide
  have hdescent : baseEnd_639781 < baseStart_639781 := by decide
  rcases family_descends (prefixWord ++ tailWord_639781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639856 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_639856 : Nat := 118140960795 + 639856 * 2 ^ 59
def prefixEnd_639856 : Nat := 4983230072969 + 3 ^ 40 * 639856 * 2
def baseEnd_639856 : Nat := 219035785108902529438241

theorem tailTrace_639856 : CollatzResearch.WordTrace tailWord_639856 prefixEnd_639856 219035785108902529438241 := by
  unfold tailWord_639856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668732784959232774893711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15558310379945643699858281 11668732784959232774893711)
  ·
    refine ⟨17503099177438849162340567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11668732784959232774893711 17503099177438849162340567)
    ·
      refine ⟨26254648766158273743510851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17503099177438849162340567 26254648766158273743510851)
      ·
        refine ⟨39381973149237410615266277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26254648766158273743510851 39381973149237410615266277)
        ·
          refine ⟨7384119965482014490362427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39381973149237410615266277 7384119965482014490362427)
          ·
            refine ⟨11076179948223021735543641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7384119965482014490362427 11076179948223021735543641)
            ·
              refine ⟨8307134961167266301657731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11076179948223021735543641 8307134961167266301657731)
              ·
                refine ⟨12460702441750899452486597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307134961167266301657731 12460702441750899452486597)
                ·
                  refine ⟨2336381707828293647341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12460702441750899452486597 2336381707828293647341237)
                  ·
                    refine ⟨219035785108902529438241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2336381707828293647341237 219035785108902529438241)
                    ·
                      rfl

theorem cell22_639856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_639856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639856 prefixEnd_639856 := by exact prefixLift 639856
  have htrace : WordTrace (prefixWord ++ tailWord_639856) baseStart_639856 baseEnd_639856 := by
    simpa [prefixWord, tailWord_639856, baseEnd_639856] using wordTrace_append hprefix tailTrace_639856
  have hstable : (prefixWord ++ tailWord_639856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639856).length < 2 ^ (prefixWord ++ tailWord_639856).sum := by decide
  have hdescent : baseEnd_639856 < baseStart_639856 := by decide
  rcases family_descends (prefixWord ++ tailWord_639856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639862 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_639862 : Nat := 118140960795 + 639862 * 2 ^ 59
def prefixEnd_639862 : Nat := 4983230072969 + 3 ^ 40 * 639862 * 2
def baseEnd_639862 : Nat := 219037839031520513788223

theorem tailTrace_639862 : CollatzResearch.WordTrace tailWord_639862 prefixEnd_639862 219037839031520513788223 := by
  unfold tailWord_639862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458605275493545535906615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15558456271931152383003893 1458605275493545535906615)
  ·
    refine ⟨2187907913240318303859923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458605275493545535906615 2187907913240318303859923)
    ·
      refine ⟨3281861869860477455789885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187907913240318303859923 3281861869860477455789885)
      ·
        refine ⟨1230698201197679045921207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3281861869860477455789885 1230698201197679045921207)
        ·
          refine ⟨1846047301796518568881811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230698201197679045921207 1846047301796518568881811)
          ·
            refine ⟨2769070952694777853322717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846047301796518568881811 2769070952694777853322717)
            ·
              refine ⟨1038401607260541694996019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769070952694777853322717 1038401607260541694996019)
              ·
                refine ⟨1557602410890812542494029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038401607260541694996019 1557602410890812542494029)
                ·
                  refine ⟨584100904084054703435261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1557602410890812542494029 584100904084054703435261)
                  ·
                    refine ⟨219037839031520513788223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584100904084054703435261 219037839031520513788223)
                    ·
                      rfl

theorem cell22_639862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_639862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639862 prefixEnd_639862 := by exact prefixLift 639862
  have htrace : WordTrace (prefixWord ++ tailWord_639862) baseStart_639862 baseEnd_639862 := by
    simpa [prefixWord, tailWord_639862, baseEnd_639862] using wordTrace_append hprefix tailTrace_639862
  have hstable : (prefixWord ++ tailWord_639862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639862).length < 2 ^ (prefixWord ++ tailWord_639862).sum := by decide
  have hdescent : baseEnd_639862 < baseStart_639862 := by decide
  rcases family_descends (prefixWord ++ tailWord_639862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639950 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_639950 : Nat := 118140960795 + 639950 * 2 ^ 59
def prefixEnd_639950 : Nat := 4983230072969 + 3 ^ 40 * 639950 * 2
def baseEnd_639950 : Nat := 219067963229917617587953

theorem tailTrace_639950 : CollatzResearch.WordTrace tailWord_639950 prefixEnd_639950 219067963229917617587953 := by
  unfold tailWord_639950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917611753947239950463663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15560596021051946402472869 2917611753947239950463663)
  ·
    refine ⟨4376417630920859925695495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917611753947239950463663 4376417630920859925695495)
    ·
      refine ⟨6564626446381289888543243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376417630920859925695495 6564626446381289888543243)
      ·
        refine ⟨9846939669571934832814865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564626446381289888543243 9846939669571934832814865)
        ·
          refine ⟨7385204752178951124611149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9846939669571934832814865 7385204752178951124611149)
          ·
            refine ⟨2769451782067106671729181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7385204752178951124611149 2769451782067106671729181)
            ·
              refine ⟨1038544418275165001898443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769451782067106671729181 1038544418275165001898443)
              ·
                refine ⟨1557816627412747502847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038544418275165001898443 1557816627412747502847665)
                ·
                  refine ⟨1168362470559560627135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557816627412747502847665 1168362470559560627135749)
                  ·
                    refine ⟨219067963229917617587953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168362470559560627135749 219067963229917617587953)
                    ·
                      rfl

theorem cell22_639950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_639950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639950 prefixEnd_639950 := by exact prefixLift 639950
  have htrace : WordTrace (prefixWord ++ tailWord_639950) baseStart_639950 baseEnd_639950 := by
    simpa [prefixWord, tailWord_639950, baseEnd_639950] using wordTrace_append hprefix tailTrace_639950
  have hstable : (prefixWord ++ tailWord_639950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639950).length < 2 ^ (prefixWord ++ tailWord_639950).sum := by decide
  have hdescent : baseEnd_639950 < baseStart_639950 := by decide
  rcases family_descends (prefixWord ++ tailWord_639950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639986 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_639986 : Nat := 118140960795 + 639986 * 2 ^ 59
def prefixEnd_639986 : Nat := 4983230072969 + 3 ^ 40 * 639986 * 2
def baseEnd_639986 : Nat := 219080286765625523687843

theorem tailTrace_639986 : CollatzResearch.WordTrace tailWord_639986 prefixEnd_639986 219080286765625523687843 := by
  unfold tailWord_639986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835551764861874438004953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15561471372964998501346541 5835551764861874438004953)
  ·
    refine ⟨4376663823646405828503715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835551764861874438004953 4376663823646405828503715)
    ·
      refine ⟨6564995735469608742755573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376663823646405828503715 6564995735469608742755573)
      ·
        refine ⟨615468350200275819633335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6564995735469608742755573 615468350200275819633335)
        ·
          refine ⟨923202525300413729450003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615468350200275819633335 923202525300413729450003)
          ·
            refine ⟨1384803787950620594175005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923202525300413729450003 1384803787950620594175005)
            ·
              refine ⟨519301420481482722815627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1384803787950620594175005 519301420481482722815627)
              ·
                refine ⟨778952130722224084223441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519301420481482722815627 778952130722224084223441)
                ·
                  refine ⟨584214098041668063167581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778952130722224084223441 584214098041668063167581)
                  ·
                    refine ⟨219080286765625523687843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584214098041668063167581 219080286765625523687843)
                    ·
                      rfl

theorem cell22_639986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_639986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_639986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_639986 prefixEnd_639986 := by exact prefixLift 639986
  have htrace : WordTrace (prefixWord ++ tailWord_639986) baseStart_639986 baseEnd_639986 := by
    simpa [prefixWord, tailWord_639986, baseEnd_639986] using wordTrace_append hprefix tailTrace_639986
  have hstable : (prefixWord ++ tailWord_639986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639986).length < 2 ^ (prefixWord ++ tailWord_639986).sum := by decide
  have hdescent : baseEnd_639986 < baseStart_639986 := by decide
  rcases family_descends (prefixWord ++ tailWord_639986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640014 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_640014 : Nat := 118140960795 + 640014 * 2 ^ 59
def prefixEnd_640014 : Nat := 4983230072969 + 3 ^ 40 * 640014 * 2
def baseEnd_640014 : Nat := 219089871737842783987757

theorem tailTrace_640014 : CollatzResearch.WordTrace tailWord_640014 prefixEnd_640014 219089871737842783987757 := by
  unfold tailWord_640014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917903537918257316754887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15562152202230705689359397 2917903537918257316754887)
  ·
    refine ⟨4376855306877385975132331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917903537918257316754887 4376855306877385975132331)
    ·
      refine ⟨6565282960316078962698497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376855306877385975132331 6565282960316078962698497)
      ·
        refine ⟨4923962220237059222023873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565282960316078962698497 4923962220237059222023873)
        ·
          refine ⟨3692971665177794416517905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923962220237059222023873 3692971665177794416517905)
          ·
            refine ⟨2769728748883345812388429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692971665177794416517905 2769728748883345812388429)
            ·
              refine ⟨1038648280831254679645661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769728748883345812388429 1038648280831254679645661)
              ·
                refine ⟨389493105311720504867123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038648280831254679645661 389493105311720504867123)
                ·
                  refine ⟨584239657967580757300685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389493105311720504867123 584239657967580757300685)
                  ·
                    refine ⟨219089871737842783987757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584239657967580757300685 219089871737842783987757)
                    ·
                      rfl

theorem cell22_640014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_640014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640014 prefixEnd_640014 := by exact prefixLift 640014
  have htrace : WordTrace (prefixWord ++ tailWord_640014) baseStart_640014 baseEnd_640014 := by
    simpa [prefixWord, tailWord_640014, baseEnd_640014] using wordTrace_append hprefix tailTrace_640014
  have hstable : (prefixWord ++ tailWord_640014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640014).length < 2 ^ (prefixWord ++ tailWord_640014).sum := by decide
  have hdescent : baseEnd_640014 < baseStart_640014 := by decide
  rcases family_descends (prefixWord ++ tailWord_640014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640057 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_640057 : Nat := 118140960795 + 640057 * 2 ^ 59
def prefixEnd_640057 : Nat := 4983230072969 + 3 ^ 40 * 640057 * 2
def baseEnd_640057 : Nat := 219104591516605005162625

theorem tailTrace_640057 : CollatzResearch.WordTrace tailWord_640057 prefixEnd_640057 219104591516605005162625 := by
  unfold tailWord_640057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23344796642190276877854425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15563197761460184585236283 23344796642190276877854425)
  ·
    refine ⟨17508597481642707658390819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23344796642190276877854425 17508597481642707658390819)
    ·
      refine ⟨26262896222464061487586229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17508597481642707658390819 26262896222464061487586229)
      ·
        refine ⟨2462146520856005764461209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26262896222464061487586229 2462146520856005764461209)
        ·
          refine ⟨1846609890642004323345907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462146520856005764461209 1846609890642004323345907)
          ·
            refine ⟨2769914835963006485018861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846609890642004323345907 2769914835963006485018861)
            ·
              refine ⟨1038718063486127431882073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769914835963006485018861 1038718063486127431882073)
              ·
                refine ⟨779038547614595573911555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038718063486127431882073 779038547614595573911555)
                ·
                  refine ⟨1168557821421893360867333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779038547614595573911555 1168557821421893360867333)
                  ·
                    refine ⟨219104591516605005162625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168557821421893360867333 219104591516605005162625)
                    ·
                      rfl

theorem cell22_640057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_640057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640057 prefixEnd_640057 := by exact prefixLift 640057
  have htrace : WordTrace (prefixWord ++ tailWord_640057) baseStart_640057 baseEnd_640057 := by
    simpa [prefixWord, tailWord_640057, baseEnd_640057] using wordTrace_append hprefix tailTrace_640057
  have hstable : (prefixWord ++ tailWord_640057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640057).length < 2 ^ (prefixWord ++ tailWord_640057).sum := by decide
  have hdescent : baseEnd_640057 < baseStart_640057 := by decide
  rcases family_descends (prefixWord ++ tailWord_640057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640085 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_640085 : Nat := 118140960795 + 640085 * 2 ^ 59
def prefixEnd_640085 : Nat := 4983230072969 + 3 ^ 40 * 640085 * 2
def baseEnd_640085 : Nat := 219114176488822265462539

theorem tailTrace_640085 : CollatzResearch.WordTrace tailWord_640085 prefixEnd_640085 219114176488822265462539 := by
  unfold tailWord_640085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23345817886088837659873709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15563878590725891773249139 23345817886088837659873709)
  ·
    refine ⟨8754681707283314122452641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23345817886088837659873709 8754681707283314122452641)
    ·
      refine ⟨6566011280462485591839481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8754681707283314122452641 6566011280462485591839481)
      ·
        refine ⟨4924508460346864193879611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566011280462485591839481 4924508460346864193879611)
        ·
          refine ⟨7386762690520296290819417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924508460346864193879611 7386762690520296290819417)
          ·
            refine ⟨5540072017890222218114563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7386762690520296290819417 5540072017890222218114563)
            ·
              refine ⟨8310108026835333327171845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540072017890222218114563 8310108026835333327171845)
              ·
                refine ⟨1558145255031624998844721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8310108026835333327171845 1558145255031624998844721)
                ·
                  refine ⟨1168608941273718749133541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558145255031624998844721 1168608941273718749133541)
                  ·
                    refine ⟨219114176488822265462539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168608941273718749133541 219114176488822265462539)
                    ·
                      rfl

theorem cell22_640085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_640085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640085 prefixEnd_640085 := by exact prefixLift 640085
  have htrace : WordTrace (prefixWord ++ tailWord_640085) baseStart_640085 baseEnd_640085 := by
    simpa [prefixWord, tailWord_640085, baseEnd_640085] using wordTrace_append hprefix tailTrace_640085
  have hstable : (prefixWord ++ tailWord_640085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640085).length < 2 ^ (prefixWord ++ tailWord_640085).sum := by decide
  have hdescent : baseEnd_640085 < baseStart_640085 := by decide
  rcases family_descends (prefixWord ++ tailWord_640085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640104 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_640104 : Nat := 118140960795 + 640104 * 2 ^ 59
def prefixEnd_640104 : Nat := 4983230072969 + 3 ^ 40 * 640104 * 2
def baseEnd_640104 : Nat := 219120680577112549237481

theorem tailTrace_640104 : CollatzResearch.WordTrace tailWord_640104 prefixEnd_640104 219120680577112549237481 := by
  unfold tailWord_640104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673255436510001952407683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15564340582013335936543577 11673255436510001952407683)
  ·
    refine ⟨17509883154765002928611525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11673255436510001952407683 17509883154765002928611525)
    ·
      refine ⟨3283103091518438049114661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17509883154765002928611525 3283103091518438049114661)
      ·
        refine ⟨615581829659707134208999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3283103091518438049114661 615581829659707134208999)
        ·
          refine ⟨923372744489560701313499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615581829659707134208999 923372744489560701313499)
          ·
            refine ⟨1385059116734341051970249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923372744489560701313499 1385059116734341051970249)
            ·
              refine ⟨1038794337550755788977687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385059116734341051970249 1038794337550755788977687)
              ·
                refine ⟨1558191506326133683466531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038794337550755788977687 1558191506326133683466531)
                ·
                  refine ⟨2337287259489200525199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558191506326133683466531 2337287259489200525199797)
                  ·
                    refine ⟨219120680577112549237481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2337287259489200525199797 219120680577112549237481)
                    ·
                      rfl

theorem cell22_640104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_640104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640104 prefixEnd_640104 := by exact prefixLift 640104
  have htrace : WordTrace (prefixWord ++ tailWord_640104) baseStart_640104 baseEnd_640104 := by
    simpa [prefixWord, tailWord_640104, baseEnd_640104] using wordTrace_append hprefix tailTrace_640104
  have hstable : (prefixWord ++ tailWord_640104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640104).length < 2 ^ (prefixWord ++ tailWord_640104).sum := by decide
  have hdescent : baseEnd_640104 < baseStart_640104 := by decide
  rcases family_descends (prefixWord ++ tailWord_640104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640160 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_640160 : Nat := 118140960795 + 640160 * 2 ^ 59
def prefixEnd_640160 : Nat := 4983230072969 + 3 ^ 40 * 640160 * 2
def baseEnd_640160 : Nat := 219139850521547069837309

theorem tailTrace_640160 : CollatzResearch.WordTrace tailWord_640160 prefixEnd_640160 219139850521547069837309 := by
  unfold tailWord_640160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674276680408562734426967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15565702240544750312569289 11674276680408562734426967)
  ·
    refine ⟨17511415020612844101640451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674276680408562734426967 17511415020612844101640451)
    ·
      refine ⟨26267122530919266152460677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17511415020612844101640451 26267122530919266152460677)
      ·
        refine ⟨4925085474547362403586377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26267122530919266152460677 4925085474547362403586377)
        ·
          refine ⟨3693814105910521802689783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925085474547362403586377 3693814105910521802689783)
          ·
            refine ⟨5540721158865782704034675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693814105910521802689783 5540721158865782704034675)
            ·
              refine ⟨8311081738298674056052013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540721158865782704034675 8311081738298674056052013)
              ·
                refine ⟨3116655651862002771019505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8311081738298674056052013 3116655651862002771019505)
                ·
                  refine ⟨2337491738896502078264629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116655651862002771019505 2337491738896502078264629)
                  ·
                    refine ⟨219139850521547069837309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2337491738896502078264629 219139850521547069837309)
                    ·
                      rfl

theorem cell22_640160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_640160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640160 prefixEnd_640160 := by exact prefixLift 640160
  have htrace : WordTrace (prefixWord ++ tailWord_640160) baseStart_640160 baseEnd_640160 := by
    simpa [prefixWord, tailWord_640160, baseEnd_640160] using wordTrace_append hprefix tailTrace_640160
  have hstable : (prefixWord ++ tailWord_640160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640160).length < 2 ^ (prefixWord ++ tailWord_640160).sum := by decide
  have hdescent : baseEnd_640160 < baseStart_640160 := by decide
  rcases family_descends (prefixWord ++ tailWord_640160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640175 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_640175 : Nat := 118140960795 + 640175 * 2 ^ 59
def prefixEnd_640175 : Nat := 4983230072969 + 3 ^ 40 * 640175 * 2
def baseEnd_640175 : Nat := 219144985328092030712263

theorem tailTrace_640175 : CollatzResearch.WordTrace tailWord_640175 prefixEnd_640175 219144985328092030712263 := by
  unfold tailWord_640175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23349100455762783030649979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15566066970508522020433319 23349100455762783030649979)
  ·
    refine ⟨35023650683644174545974969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23349100455762783030649979 35023650683644174545974969)
    ·
      refine ⟨26267738012733130909481227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35023650683644174545974969 26267738012733130909481227)
      ·
        refine ⟨39401607019099696364221841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26267738012733130909481227 39401607019099696364221841)
        ·
          refine ⟨29551205264324772273166381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39401607019099696364221841 29551205264324772273166381)
          ·
            refine ⟨11081701974121789602437393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29551205264324772273166381 11081701974121789602437393)
            ·
              refine ⟨8311276480591342201828045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11081701974121789602437393 8311276480591342201828045)
              ·
                refine ⟨3116728680221753325685517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8311276480591342201828045 3116728680221753325685517)
                ·
                  refine ⟨1168773255083157497132069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3116728680221753325685517 1168773255083157497132069)
                  ·
                    refine ⟨219144985328092030712263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168773255083157497132069 219144985328092030712263)
                    ·
                      rfl

theorem cell22_640175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_640175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640175 prefixEnd_640175 := by exact prefixLift 640175
  have htrace : WordTrace (prefixWord ++ tailWord_640175) baseStart_640175 baseEnd_640175 := by
    simpa [prefixWord, tailWord_640175, baseEnd_640175] using wordTrace_append hprefix tailTrace_640175
  have hstable : (prefixWord ++ tailWord_640175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640175).length < 2 ^ (prefixWord ++ tailWord_640175).sum := by decide
  have hdescent : baseEnd_640175 < baseStart_640175 := by decide
  rcases family_descends (prefixWord ++ tailWord_640175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640235 : List Nat := [1, 1, 1, 1, 2, 6, 2, 8]
def baseStart_640235 : Nat := 118140960795 + 640235 * 2 ^ 59
def prefixEnd_640235 : Nat := 4983230072969 + 3 ^ 40 * 640235 * 2
def baseEnd_640235 : Nat := 24351724950474652690231

theorem tailTrace_640235 : CollatzResearch.WordTrace tailWord_640235 prefixEnd_640235 24351724950474652690231 := by
  unfold tailWord_640235
  simp only [CollatzResearch.WordTrace]
  refine ⟨23351288835545413277834159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15567525890363608851889439 23351288835545413277834159)
  ·
    refine ⟨35026933253318119916751239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23351288835545413277834159 35026933253318119916751239)
    ·
      refine ⟨52540399879977179875126859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35026933253318119916751239 52540399879977179875126859)
      ·
        refine ⟨78810599819965769812690289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52540399879977179875126859 78810599819965769812690289)
        ·
          refine ⟨59107949864974327359517717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78810599819965769812690289 59107949864974327359517717)
          ·
            refine ⟨2770685149920671594977393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59107949864974327359517717 2770685149920671594977393)
            ·
              refine ⟨2078013862440503696233045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770685149920671594977393 2078013862440503696233045)
              ·
                refine ⟨24351724950474652690231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2078013862440503696233045 24351724950474652690231)
                ·
                  rfl

theorem cell22_640235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_640235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640235 prefixEnd_640235 := by exact prefixLift 640235
  have htrace : WordTrace (prefixWord ++ tailWord_640235) baseStart_640235 baseEnd_640235 := by
    simpa [prefixWord, tailWord_640235, baseEnd_640235] using wordTrace_append hprefix tailTrace_640235
  have hstable : (prefixWord ++ tailWord_640235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640235).length < 2 ^ (prefixWord ++ tailWord_640235).sum := by decide
  have hdescent : baseEnd_640235 < baseStart_640235 := by decide
  rcases family_descends (prefixWord ++ tailWord_640235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640252 : List Nat := [2, 2, 2, 1, 6, 9]
def baseStart_640252 : Nat := 118140960795 + 640252 * 2 ^ 59
def prefixEnd_640252 : Nat := 4983230072969 + 3 ^ 40 * 640252 * 2
def baseEnd_640252 : Nat := 2705819061749253043667

theorem tailTrace_640252 : CollatzResearch.WordTrace tailWord_640252 prefixEnd_640252 2705819061749253043667 := by
  unfold tailWord_640252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675954438241912590601505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15567939250989216787468673 11675954438241912590601505)
  ·
    refine ⟨8756965828681434442951129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11675954438241912590601505 8756965828681434442951129)
    ·
      refine ⟨6567724371511075832213347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8756965828681434442951129 6567724371511075832213347)
      ·
        refine ⟨9851586557266613748320021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567724371511075832213347 9851586557266613748320021)
        ·
          refine ⟨461793119871872519452501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9851586557266613748320021 461793119871872519452501)
          ·
            refine ⟨2705819061749253043667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 461793119871872519452501 2705819061749253043667)
            ·
              rfl

theorem cell22_640252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 9].length) (baseStart_640252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640252 prefixEnd_640252 := by exact prefixLift 640252
  have htrace : WordTrace (prefixWord ++ tailWord_640252) baseStart_640252 baseEnd_640252 := by
    simpa [prefixWord, tailWord_640252, baseEnd_640252] using wordTrace_append hprefix tailTrace_640252
  have hstable : (prefixWord ++ tailWord_640252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640252).length < 2 ^ (prefixWord ++ tailWord_640252).sum := by decide
  have hdescent : baseEnd_640252 < baseStart_640252 := by decide
  rcases family_descends (prefixWord ++ tailWord_640252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640254 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_640254 : Nat := 118140960795 + 640254 * 2 ^ 59
def prefixEnd_640254 : Nat := 4983230072969 + 3 ^ 40 * 640254 * 2
def baseEnd_640254 : Nat := 219172028642562157987021

theorem tailTrace_640254 : CollatzResearch.WordTrace tailWord_640254 prefixEnd_640254 219172028642562157987021 := by
  unfold tailWord_640254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918997727809572440346977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15567987881651053015183877 2918997727809572440346977)
  ·
    refine ⟨2189248295857179330260233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2918997727809572440346977 2189248295857179330260233)
    ·
      refine ⟨1641936221892884497695175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189248295857179330260233 1641936221892884497695175)
      ·
        refine ⟨2462904332839326746542763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641936221892884497695175 2462904332839326746542763)
        ·
          refine ⟨3694356499258990119814145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462904332839326746542763 3694356499258990119814145)
          ·
            refine ⟨2770767374444242589860609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3694356499258990119814145 2770767374444242589860609)
            ·
              refine ⟨2078075530833181942395457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770767374444242589860609 2078075530833181942395457)
              ·
                refine ⟨1558556648124886456796593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078075530833181942395457 1558556648124886456796593)
                ·
                  refine ⟨1168917486093664842597445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558556648124886456796593 1168917486093664842597445)
                  ·
                    refine ⟨219172028642562157987021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168917486093664842597445 219172028642562157987021)
                    ·
                      rfl

theorem cell22_640254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_640254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640254 prefixEnd_640254 := by exact prefixLift 640254
  have htrace : WordTrace (prefixWord ++ tailWord_640254) baseStart_640254 baseEnd_640254 := by
    simpa [prefixWord, tailWord_640254, baseEnd_640254] using wordTrace_append hprefix tailTrace_640254
  have hstable : (prefixWord ++ tailWord_640254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640254).length < 2 ^ (prefixWord ++ tailWord_640254).sum := by decide
  have hdescent : baseEnd_640254 < baseStart_640254 := by decide
  rcases family_descends (prefixWord ++ tailWord_640254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640265 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_640265 : Nat := 118140960795 + 640265 * 2 ^ 59
def prefixEnd_640265 : Nat := 4983230072969 + 3 ^ 40 * 640265 * 2
def baseEnd_640265 : Nat := 219175794167361795961987

theorem tailTrace_640265 : CollatzResearch.WordTrace tailWord_640265 prefixEnd_640265 219175794167361795961987 := by
  unfold tailWord_640265
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352383025436728401426249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15568255350291152267617499 23352383025436728401426249)
  ·
    refine ⟨17514287269077546301069687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23352383025436728401426249 17514287269077546301069687)
    ·
      refine ⟨26271430903616319451604531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17514287269077546301069687 26271430903616319451604531)
      ·
        refine ⟨39407146355424479177406797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26271430903616319451604531 39407146355424479177406797)
        ·
          refine ⟨14777679883284179691527549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39407146355424479177406797 14777679883284179691527549)
          ·
            refine ⟨5541629956231567384322831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14777679883284179691527549 5541629956231567384322831)
            ·
              refine ⟨8312444934347351076484247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541629956231567384322831 8312444934347351076484247)
              ·
                refine ⟨12468667401521026614726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312444934347351076484247 12468667401521026614726371)
                ·
                  refine ⟨18703001102281539922089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12468667401521026614726371 18703001102281539922089557)
                  ·
                    refine ⟨219175794167361795961987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18703001102281539922089557 219175794167361795961987)
                    ·
                      rfl

theorem cell22_640265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_640265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640265 prefixEnd_640265 := by exact prefixLift 640265
  have htrace : WordTrace (prefixWord ++ tailWord_640265) baseStart_640265 baseEnd_640265 := by
    simpa [prefixWord, tailWord_640265, baseEnd_640265] using wordTrace_append hprefix tailTrace_640265
  have hstable : (prefixWord ++ tailWord_640265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640265).length < 2 ^ (prefixWord ++ tailWord_640265).sum := by decide
  have hdescent : baseEnd_640265 < baseStart_640265 := by decide
  rcases family_descends (prefixWord ++ tailWord_640265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640344 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_640344 : Nat := 118140960795 + 640344 * 2 ^ 59
def prefixEnd_640344 : Nat := 4983230072969 + 3 ^ 40 * 640344 * 2
def baseEnd_640344 : Nat := 219202837481831923236745

theorem tailTrace_640344 : CollatzResearch.WordTrace tailWord_640344 prefixEnd_640344 219202837481831923236745 := by
  unfold tailWord_640344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677632196075262446776043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15570176261433683262368057 11677632196075262446776043)
  ·
    refine ⟨17516448294112893670164065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11677632196075262446776043 17516448294112893670164065)
    ·
      refine ⟨13137336220584670252623049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17516448294112893670164065 13137336220584670252623049)
      ·
        refine ⟨9853002165438502689467287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13137336220584670252623049 9853002165438502689467287)
        ·
          refine ⟨14779503248157754034200931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853002165438502689467287 14779503248157754034200931)
          ·
            refine ⟨22169254872236631051301397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14779503248157754034200931 22169254872236631051301397)
            ·
              refine ⟨1039183822136092080529753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22169254872236631051301397 1039183822136092080529753)
              ·
                refine ⟨779387866602069060397315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039183822136092080529753 779387866602069060397315)
                ·
                  refine ⟨1169081799903103590595973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779387866602069060397315 1169081799903103590595973)
                  ·
                    refine ⟨219202837481831923236745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169081799903103590595973 219202837481831923236745)
                    ·
                      rfl

theorem cell22_640344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_640344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640344 prefixEnd_640344 := by exact prefixLift 640344
  have htrace : WordTrace (prefixWord ++ tailWord_640344) baseStart_640344 baseEnd_640344 := by
    simpa [prefixWord, tailWord_640344, baseEnd_640344] using wordTrace_append hprefix tailTrace_640344
  have hstable : (prefixWord ++ tailWord_640344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640344).length < 2 ^ (prefixWord ++ tailWord_640344).sum := by decide
  have hdescent : baseEnd_640344 < baseStart_640344 := by decide
  rcases family_descends (prefixWord ++ tailWord_640344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640357 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_640357 : Nat := 118140960795 + 640357 * 2 ^ 59
def prefixEnd_640357 : Nat := 4983230072969 + 3 ^ 40 * 640357 * 2
def baseEnd_640357 : Nat := 219207287647504222661705

theorem tailTrace_640357 : CollatzResearch.WordTrace tailWord_640357 prefixEnd_640357 219207287647504222661705 := by
  unfold tailWord_640357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355738541103428113775325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15570492360735618742516883 23355738541103428113775325)
  ·
    refine ⟨8758401952913785542665747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23355738541103428113775325 8758401952913785542665747)
    ·
      refine ⟨13137602929370678313998621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758401952913785542665747 13137602929370678313998621)
      ·
        refine ⟨4926601098514004367749483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13137602929370678313998621 4926601098514004367749483)
        ·
          refine ⟨7389901647771006551624225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926601098514004367749483 7389901647771006551624225)
          ·
            refine ⟨5542426235828254913718169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7389901647771006551624225 5542426235828254913718169)
            ·
              refine ⟨4156819676871191185288627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542426235828254913718169 4156819676871191185288627)
              ·
                refine ⟨6235229515306786777932941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156819676871191185288627 6235229515306786777932941)
                ·
                  refine ⟨2338211068240045041724853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6235229515306786777932941 2338211068240045041724853)
                  ·
                    refine ⟨219207287647504222661705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2338211068240045041724853 219207287647504222661705)
                    ·
                      rfl

theorem cell22_640357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_640357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640357 prefixEnd_640357 := by exact prefixLift 640357
  have htrace : WordTrace (prefixWord ++ tailWord_640357) baseStart_640357 baseEnd_640357 := by
    simpa [prefixWord, tailWord_640357, baseEnd_640357] using wordTrace_append hprefix tailTrace_640357
  have hstable : (prefixWord ++ tailWord_640357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640357).length < 2 ^ (prefixWord ++ tailWord_640357).sum := by decide
  have hdescent : baseEnd_640357 < baseStart_640357 := by decide
  rcases family_descends (prefixWord ++ tailWord_640357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640382 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_640382 : Nat := 118140960795 + 640382 * 2 ^ 59
def prefixEnd_640382 : Nat := 4983230072969 + 3 ^ 40 * 640382 * 2
def baseEnd_640382 : Nat := 73071948552804163595543

theorem tailTrace_640382 : CollatzResearch.WordTrace tailWord_640382 prefixEnd_640382 73071948552804163595543 := by
  unfold tailWord_640382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919581295751607172929425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15571100244008571588956933 2919581295751607172929425)
  ·
    refine ⟨2189685971813705379697069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2919581295751607172929425 2189685971813705379697069)
    ·
      refine ⟨821132239430139517386401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2189685971813705379697069 821132239430139517386401)
      ·
        refine ⟨615849179572604638039801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821132239430139517386401 615849179572604638039801)
        ·
          refine ⟨461886884679453478529851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615849179572604638039801 461886884679453478529851)
          ·
            refine ⟨692830327019180217794777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461886884679453478529851 692830327019180217794777)
            ·
              refine ⟨519622745264385163346083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692830327019180217794777 519622745264385163346083)
              ·
                refine ⟨779434117896577745019125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519622745264385163346083 779434117896577745019125)
                ·
                  refine ⟨73071948552804163595543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779434117896577745019125 73071948552804163595543)
                  ·
                    rfl

theorem cell22_640382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_640382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640382 prefixEnd_640382 := by exact prefixLift 640382
  have htrace : WordTrace (prefixWord ++ tailWord_640382) baseStart_640382 baseEnd_640382 := by
    simpa [prefixWord, tailWord_640382, baseEnd_640382] using wordTrace_append hprefix tailTrace_640382
  have hstable : (prefixWord ++ tailWord_640382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640382).length < 2 ^ (prefixWord ++ tailWord_640382).sum := by decide
  have hdescent : baseEnd_640382 < baseStart_640382 := by decide
  rcases family_descends (prefixWord ++ tailWord_640382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640387 : List Nat := [1, 1, 1, 3, 5, 1, 1, 9]
def baseStart_640387 : Nat := 118140960795 + 640387 * 2 ^ 59
def prefixEnd_640387 : Nat := 4983230072969 + 3 ^ 40 * 640387 * 2
def baseEnd_640387 : Nat := 24357506362288238267957

theorem tailTrace_640387 : CollatzResearch.WordTrace tailWord_640387 prefixEnd_640387 24357506362288238267957 := by
  unfold tailWord_640387
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356832730994743237367415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15571221820663162158244943 23356832730994743237367415)
  ·
    refine ⟨35035249096492114856051123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23356832730994743237367415 35035249096492114856051123)
    ·
      refine ⟨52552873644738172284076685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35035249096492114856051123 52552873644738172284076685)
      ·
        refine ⟨19707327616776814606528757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52552873644738172284076685 19707327616776814606528757)
        ·
          refine ⟨1847561964072826369362071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19707327616776814606528757 1847561964072826369362071)
          ·
            refine ⟨2771342946109239554043107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847561964072826369362071 2771342946109239554043107)
            ·
              refine ⟨4157014419163859331064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771342946109239554043107 4157014419163859331064661)
              ·
                refine ⟨24357506362288238267957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4157014419163859331064661 24357506362288238267957)
                ·
                  rfl

theorem cell22_640387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_640387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640387 prefixEnd_640387 := by exact prefixLift 640387
  have htrace : WordTrace (prefixWord ++ tailWord_640387) baseStart_640387 baseEnd_640387 := by
    simpa [prefixWord, tailWord_640387, baseEnd_640387] using wordTrace_append hprefix tailTrace_640387
  have hstable : (prefixWord ++ tailWord_640387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640387).length < 2 ^ (prefixWord ++ tailWord_640387).sum := by decide
  have hdescent : baseEnd_640387 < baseStart_640387 := by decide
  rcases family_descends (prefixWord ++ tailWord_640387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640391 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 2, 3]
def baseStart_640391 : Nat := 118140960795 + 640391 * 2 ^ 59
def prefixEnd_640391 : Nat := 4983230072969 + 3 ^ 40 * 640391 * 2
def baseEnd_640391 : Nat := 219218926542339467311601

theorem tailTrace_640391 : CollatzResearch.WordTrace tailWord_640391 prefixEnd_640391 219218926542339467311601 := by
  unfold tailWord_640391
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356978622980251920513027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15571319081986834613675351 23356978622980251920513027)
  ·
    refine ⟨35035467934470377880769541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23356978622980251920513027 35035467934470377880769541)
    ·
      refine ⟨6569150237713195852644289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35035467934470377880769541 6569150237713195852644289)
      ·
        refine ⟨4926862678284896889483217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569150237713195852644289 4926862678284896889483217)
        ·
          refine ⟨3695147008713672667112413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926862678284896889483217 3695147008713672667112413)
          ·
            refine ⟨1385680128267627250167155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3695147008713672667112413 1385680128267627250167155)
            ·
              refine ⟨2078520192401440875250733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385680128267627250167155 2078520192401440875250733)
              ·
                refine ⟨779445072150540328219025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2078520192401440875250733 779445072150540328219025)
                ·
                  refine ⟨584583804112905246164269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779445072150540328219025 584583804112905246164269)
                  ·
                    refine ⟨219218926542339467311601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584583804112905246164269 219218926542339467311601)
                    ·
                      rfl

theorem cell22_640391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_640391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640391 prefixEnd_640391 := by exact prefixLift 640391
  have htrace : WordTrace (prefixWord ++ tailWord_640391) baseStart_640391 baseEnd_640391 := by
    simpa [prefixWord, tailWord_640391, baseEnd_640391] using wordTrace_append hprefix tailTrace_640391
  have hstable : (prefixWord ++ tailWord_640391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640391).length < 2 ^ (prefixWord ++ tailWord_640391).sum := by decide
  have hdescent : baseEnd_640391 < baseStart_640391 := by decide
  rcases family_descends (prefixWord ++ tailWord_640391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640404 : List Nat := [2, 4, 2, 1, 2, 1, 2, 8]
def baseStart_640404 : Nat := 118140960795 + 640404 * 2 ^ 59
def prefixEnd_640404 : Nat := 4983230072969 + 3 ^ 40 * 640404 * 2
def baseEnd_640404 : Nat := 24358152967556862970729

theorem tailTrace_640404 : CollatzResearch.WordTrace tailWord_640404 prefixEnd_640404 24358152967556862970729 := by
  unfold tailWord_640404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678726385966577570368133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15571635181288770093824177 11678726385966577570368133)
  ·
    refine ⟨2189761197368733294444025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11678726385966577570368133 2189761197368733294444025)
    ·
      refine ⟨1642320898026549970833019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189761197368733294444025 1642320898026549970833019)
      ·
        refine ⟨2463481347039824956249529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642320898026549970833019 2463481347039824956249529)
        ·
          refine ⟨1847611010279868717187147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463481347039824956249529 1847611010279868717187147)
          ·
            refine ⟨2771416515419803075780721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847611010279868717187147 2771416515419803075780721)
            ·
              refine ⟨2078562386564852306835541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771416515419803075780721 2078562386564852306835541)
              ·
                refine ⟨24358152967556862970729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2078562386564852306835541 24358152967556862970729)
                ·
                  rfl

theorem cell22_640404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_640404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640404 prefixEnd_640404 := by exact prefixLift 640404
  have htrace : WordTrace (prefixWord ++ tailWord_640404) baseStart_640404 baseEnd_640404 := by
    simpa [prefixWord, tailWord_640404, baseEnd_640404] using wordTrace_append hprefix tailTrace_640404
  have hstable : (prefixWord ++ tailWord_640404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640404).length < 2 ^ (prefixWord ++ tailWord_640404).sum := by decide
  have hdescent : baseEnd_640404 < baseStart_640404 := by decide
  rcases family_descends (prefixWord ++ tailWord_640404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640470 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_640470 : Nat := 118140960795 + 640470 * 2 ^ 59
def prefixEnd_640470 : Nat := 4983230072969 + 3 ^ 40 * 640470 * 2
def baseEnd_640470 : Nat := 219245969856809594586359

theorem tailTrace_640470 : CollatzResearch.WordTrace tailWord_640470 prefixEnd_640470 219245969856809594586359 := by
  unfold tailWord_640470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459991249355878025789929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15573239993129365608425909 1459991249355878025789929)
  ·
    refine ⟨1094993437016908519342447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1459991249355878025789929 1094993437016908519342447)
    ·
      refine ⟨1642490155525362779013671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094993437016908519342447 1642490155525362779013671)
      ·
        refine ⟨2463735233288044168520507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642490155525362779013671 2463735233288044168520507)
        ·
          refine ⟨3695602849932066252780761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463735233288044168520507 3695602849932066252780761)
          ·
            refine ⟨2771702137449049689585571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695602849932066252780761 2771702137449049689585571)
            ·
              refine ⟨4157553206173574534378357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771702137449049689585571 4157553206173574534378357)
              ·
                refine ⟨389770613078772612597971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4157553206173574534378357 389770613078772612597971)
                ·
                  refine ⟨584655919618158918896957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389770613078772612597971 584655919618158918896957)
                  ·
                    refine ⟨219245969856809594586359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584655919618158918896957 219245969856809594586359)
                    ·
                      rfl

theorem cell22_640470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_640470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640470 prefixEnd_640470 := by exact prefixLift 640470
  have htrace : WordTrace (prefixWord ++ tailWord_640470) baseStart_640470 baseEnd_640470 := by
    simpa [prefixWord, tailWord_640470, baseEnd_640470] using wordTrace_append hprefix tailTrace_640470
  have hstable : (prefixWord ++ tailWord_640470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640470).length < 2 ^ (prefixWord ++ tailWord_640470).sum := by decide
  have hdescent : baseEnd_640470 < baseStart_640470 := by decide
  rcases family_descends (prefixWord ++ tailWord_640470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640513 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_640513 : Nat := 118140960795 + 640513 * 2 ^ 59
def prefixEnd_640513 : Nat := 4983230072969 + 3 ^ 40 * 640513 * 2
def baseEnd_640513 : Nat := 219260689635571815761227

theorem tailTrace_640513 : CollatzResearch.WordTrace tailWord_640513 prefixEnd_640513 219260689635571815761227 := by
  unfold tailWord_640513
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361428328538266756454193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15574285552358844504302795 23361428328538266756454193)
  ·
    refine ⟨17521071246403700067340645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23361428328538266756454193 17521071246403700067340645)
    ·
      refine ⟨3285200858700693762626371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17521071246403700067340645 3285200858700693762626371)
      ·
        refine ⟨4927801288051040643939557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285200858700693762626371 4927801288051040643939557)
        ·
          refine ⟨923962741509570120738667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4927801288051040643939557 923962741509570120738667)
          ·
            refine ⟨1385944112264355181108001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923962741509570120738667 1385944112264355181108001)
            ·
              refine ⟨1039458084198266385831001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385944112264355181108001 1039458084198266385831001)
              ·
                refine ⟨779593563148699789373251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039458084198266385831001 779593563148699789373251)
                ·
                  refine ⟨1169390344723049684059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779593563148699789373251 1169390344723049684059877)
                  ·
                    refine ⟨219260689635571815761227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169390344723049684059877 219260689635571815761227)
                    ·
                      rfl

theorem cell22_640513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_640513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640513 prefixEnd_640513 := by exact prefixLift 640513
  have htrace : WordTrace (prefixWord ++ tailWord_640513) baseStart_640513 baseEnd_640513 := by
    simpa [prefixWord, tailWord_640513, baseEnd_640513] using wordTrace_append hprefix tailTrace_640513
  have hstable : (prefixWord ++ tailWord_640513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640513).length < 2 ^ (prefixWord ++ tailWord_640513).sum := by decide
  have hdescent : baseEnd_640513 < baseStart_640513 := by decide
  rcases family_descends (prefixWord ++ tailWord_640513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640541 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_640541 : Nat := 118140960795 + 640541 * 2 ^ 59
def prefixEnd_640541 : Nat := 4983230072969 + 3 ^ 40 * 640541 * 2
def baseEnd_640541 : Nat := 219270274607789076061141

theorem tailTrace_640541 : CollatzResearch.WordTrace tailWord_640541 prefixEnd_640541 219270274607789076061141 := by
  unfold tailWord_640541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23362449572436827538473477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15574966381624551692315651 23362449572436827538473477)
  ·
    refine ⟨4380459294831905163463777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23362449572436827538473477 4380459294831905163463777)
    ·
      refine ⟨3285344471123928872597833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380459294831905163463777 3285344471123928872597833)
      ·
        refine ⟨2464008353342946654448375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285344471123928872597833 2464008353342946654448375)
        ·
          refine ⟨3696012530014419981672563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464008353342946654448375 3696012530014419981672563)
          ·
            refine ⟨5544018795021629972508845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696012530014419981672563 5544018795021629972508845)
            ·
              refine ⟨2079007048133111239690817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5544018795021629972508845 2079007048133111239690817)
              ·
                refine ⟨1559255286099833429768113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079007048133111239690817 1559255286099833429768113)
                ·
                  refine ⟨1169441464574875072326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559255286099833429768113 1169441464574875072326085)
                  ·
                    refine ⟨219270274607789076061141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169441464574875072326085 219270274607789076061141)
                    ·
                      rfl

theorem cell22_640541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_640541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640541 prefixEnd_640541 := by exact prefixLift 640541
  have htrace : WordTrace (prefixWord ++ tailWord_640541) baseStart_640541 baseEnd_640541 := by
    simpa [prefixWord, tailWord_640541, baseEnd_640541] using wordTrace_append hprefix tailTrace_640541
  have hstable : (prefixWord ++ tailWord_640541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640541).length < 2 ^ (prefixWord ++ tailWord_640541).sum := by decide
  have hdescent : baseEnd_640541 < baseStart_640541 := by decide
  rcases family_descends (prefixWord ++ tailWord_640541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640616 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_640616 : Nat := 118140960795 + 640616 * 2 ^ 59
def prefixEnd_640616 : Nat := 4983230072969 + 3 ^ 40 * 640616 * 2
def baseEnd_640616 : Nat := 219295948640513880435911

theorem tailTrace_640616 : CollatzResearch.WordTrace tailWord_640616 prefixEnd_640616 219295948640513880435911 := by
  unfold tailWord_640616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682592523582557673726851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15576790031443410231635801 11682592523582557673726851)
  ·
    refine ⟨17523888785373836510590277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11682592523582557673726851 17523888785373836510590277)
    ·
      refine ⟨3285729147257594345735677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17523888785373836510590277 3285729147257594345735677)
      ·
        refine ⟨1232148430221597879650879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3285729147257594345735677 1232148430221597879650879)
        ·
          refine ⟨1848222645332396819476319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232148430221597879650879 1848222645332396819476319)
          ·
            refine ⟨2772333967998595229214479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848222645332396819476319 2772333967998595229214479)
            ·
              refine ⟨4158500951997892843821719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772333967998595229214479 4158500951997892843821719)
              ·
                refine ⟨6237751427996839265732579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158500951997892843821719 6237751427996839265732579)
                ·
                  refine ⟨9356627141995258898598869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237751427996839265732579 9356627141995258898598869)
                  ·
                    refine ⟨219295948640513880435911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9356627141995258898598869 219295948640513880435911)
                    ·
                      rfl

theorem cell22_640616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_640616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640616 prefixEnd_640616 := by exact prefixLift 640616
  have htrace : WordTrace (prefixWord ++ tailWord_640616) baseStart_640616 baseEnd_640616 := by
    simpa [prefixWord, tailWord_640616, baseEnd_640616] using wordTrace_append hprefix tailTrace_640616
  have hstable : (prefixWord ++ tailWord_640616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640616).length < 2 ^ (prefixWord ++ tailWord_640616).sum := by decide
  have hdescent : baseEnd_640616 < baseStart_640616 := by decide
  rcases family_descends (prefixWord ++ tailWord_640616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640631 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 1, 4]
def baseStart_640631 : Nat := 118140960795 + 640631 * 2 ^ 59
def prefixEnd_640631 : Nat := 4983230072969 + 3 ^ 40 * 640631 * 2
def baseEnd_640631 : Nat := 219301083447058841310865

theorem tailTrace_640631 : CollatzResearch.WordTrace tailWord_640631 prefixEnd_640631 219301083447058841310865 := by
  unfold tailWord_640631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365732142110772909249747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15577154761407181939499831 23365732142110772909249747)
  ·
    refine ⟨35048598213166159363874621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23365732142110772909249747 35048598213166159363874621)
    ·
      refine ⟨13143224329937309761452983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35048598213166159363874621 13143224329937309761452983)
      ·
        refine ⟨19714836494905964642179475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143224329937309761452983 19714836494905964642179475)
        ·
          refine ⟨29572254742358946963269213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19714836494905964642179475 29572254742358946963269213)
          ·
            refine ⟨11089595528384605111225955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29572254742358946963269213 11089595528384605111225955)
            ·
              refine ⟨16634393292576907666838933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11089595528384605111225955 16634393292576907666838933)
              ·
                refine ⟨779737185589542546883075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16634393292576907666838933 779737185589542546883075)
                ·
                  refine ⟨1169605778384313820324613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779737185589542546883075 1169605778384313820324613)
                  ·
                    refine ⟨219301083447058841310865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169605778384313820324613 219301083447058841310865)
                    ·
                      rfl

theorem cell22_640631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_640631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640631 prefixEnd_640631 := by exact prefixLift 640631
  have htrace : WordTrace (prefixWord ++ tailWord_640631) baseStart_640631 baseEnd_640631 := by
    simpa [prefixWord, tailWord_640631, baseEnd_640631] using wordTrace_append hprefix tailTrace_640631
  have hstable : (prefixWord ++ tailWord_640631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640631).length < 2 ^ (prefixWord ++ tailWord_640631).sum := by decide
  have hdescent : baseEnd_640631 < baseStart_640631 := by decide
  rcases family_descends (prefixWord ++ tailWord_640631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640659 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_640659 : Nat := 118140960795 + 640659 * 2 ^ 59
def prefixEnd_640659 : Nat := 4983230072969 + 3 ^ 40 * 640659 * 2
def baseEnd_640659 : Nat := 219310668419276101610779

theorem tailTrace_640659 : CollatzResearch.WordTrace tailWord_640659 prefixEnd_640659 219310668419276101610779 := by
  unfold tailWord_640659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366753386009333691269031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15577835590672889127512687 23366753386009333691269031)
  ·
    refine ⟨35050130079014000536903547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23366753386009333691269031 35050130079014000536903547)
    ·
      refine ⟨52575195118521000805355321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35050130079014000536903547 52575195118521000805355321)
      ·
        refine ⟨39431396338890750604016491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52575195118521000805355321 39431396338890750604016491)
        ·
          refine ⟨59147094508336125906024737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39431396338890750604016491 59147094508336125906024737)
          ·
            refine ⟨44360320881252094429518553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59147094508336125906024737 44360320881252094429518553)
            ·
              refine ⟨33270240660939070822138915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44360320881252094429518553 33270240660939070822138915)
              ·
                refine ⟨49905360991408606233208373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33270240660939070822138915 49905360991408606233208373)
                ·
                  refine ⟨4678627592944556834363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49905360991408606233208373 4678627592944556834363285)
                  ·
                    refine ⟨219310668419276101610779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4678627592944556834363285 219310668419276101610779)
                    ·
                      rfl

theorem cell22_640659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_640659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640659 prefixEnd_640659 := by exact prefixLift 640659
  have htrace : WordTrace (prefixWord ++ tailWord_640659) baseStart_640659 baseEnd_640659 := by
    simpa [prefixWord, tailWord_640659, baseEnd_640659] using wordTrace_append hprefix tailTrace_640659
  have hstable : (prefixWord ++ tailWord_640659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640659).length < 2 ^ (prefixWord ++ tailWord_640659).sum := by decide
  have hdescent : baseEnd_640659 < baseStart_640659 := by decide
  rcases family_descends (prefixWord ++ tailWord_640659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640663 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 4]
def baseStart_640663 : Nat := 118140960795 + 640663 * 2 ^ 59
def prefixEnd_640663 : Nat := 4983230072969 + 3 ^ 40 * 640663 * 2
def baseEnd_640663 : Nat := 73104012567007141503589

theorem tailTrace_640663 : CollatzResearch.WordTrace tailWord_640663 prefixEnd_640663 73104012567007141503589 := by
  unfold tailWord_640663
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366899277994842374414643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15577932851996561582943095 23366899277994842374414643)
  ·
    refine ⟨35050348916992263561621965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23366899277994842374414643 35050348916992263561621965)
    ·
      refine ⟨13143880843872098835608237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35050348916992263561621965 13143880843872098835608237)
      ·
        refine ⟨4928955316452037063353089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13143880843872098835608237 4928955316452037063353089)
        ·
          refine ⟨3696716487339027797514817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928955316452037063353089 3696716487339027797514817)
          ·
            refine ⟨2772537365504270848136113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696716487339027797514817 2772537365504270848136113)
            ·
              refine ⟨2079403024128203136102085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772537365504270848136113 2079403024128203136102085)
              ·
                refine ⟨389888067024038088019141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2079403024128203136102085 389888067024038088019141)
                ·
                  refine ⟨73104012567007141503589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389888067024038088019141 73104012567007141503589)
                  ·
                    rfl

theorem cell22_640663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 4].length) (baseStart_640663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640663 prefixEnd_640663 := by exact prefixLift 640663
  have htrace : WordTrace (prefixWord ++ tailWord_640663) baseStart_640663 baseEnd_640663 := by
    simpa [prefixWord, tailWord_640663, baseEnd_640663] using wordTrace_append hprefix tailTrace_640663
  have hstable : (prefixWord ++ tailWord_640663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640663).length < 2 ^ (prefixWord ++ tailWord_640663).sum := by decide
  have hdescent : baseEnd_640663 < baseStart_640663 := by decide
  rcases family_descends (prefixWord ++ tailWord_640663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640676 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_640676 : Nat := 118140960795 + 640676 * 2 ^ 59
def prefixEnd_640676 : Nat := 4983230072969 + 3 ^ 40 * 640676 * 2
def baseEnd_640676 : Nat := 219316487866693723935727

theorem tailTrace_640676 : CollatzResearch.WordTrace tailWord_640676 prefixEnd_640676 219316487866693723935727 := by
  unfold tailWord_640676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683686713473872797318941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15578248951298497063091921 11683686713473872797318941)
  ·
    refine ⟨4381382517552702298994603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11683686713473872797318941 4381382517552702298994603)
    ·
      refine ⟨6572073776329053448491905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381382517552702298994603 6572073776329053448491905)
      ·
        refine ⟨4929055332246790086368929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6572073776329053448491905 4929055332246790086368929)
        ·
          refine ⟨3696791499185092564776697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929055332246790086368929 3696791499185092564776697)
          ·
            refine ⟨2772593624388819423582523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696791499185092564776697 2772593624388819423582523)
            ·
              refine ⟨4158890436583229135373785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772593624388819423582523 4158890436583229135373785)
              ·
                refine ⟨3119167827437421851530339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158890436583229135373785 3119167827437421851530339)
                ·
                  refine ⟨4678751741156132777295509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119167827437421851530339 4678751741156132777295509)
                  ·
                    refine ⟨219316487866693723935727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4678751741156132777295509 219316487866693723935727)
                    ·
                      rfl

theorem cell22_640676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_640676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640676 prefixEnd_640676 := by exact prefixLift 640676
  have htrace : WordTrace (prefixWord ++ tailWord_640676) baseStart_640676 baseEnd_640676 := by
    simpa [prefixWord, tailWord_640676, baseEnd_640676] using wordTrace_append hprefix tailTrace_640676
  have hstable : (prefixWord ++ tailWord_640676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640676).length < 2 ^ (prefixWord ++ tailWord_640676).sum := by decide
  have hdescent : baseEnd_640676 < baseStart_640676 := by decide
  rcases family_descends (prefixWord ++ tailWord_640676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640770 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_640770 : Nat := 118140960795 + 640770 * 2 ^ 59
def prefixEnd_640770 : Nat := 4983230072969 + 3 ^ 40 * 640770 * 2
def baseEnd_640770 : Nat := 73116221995902937361813

theorem tailTrace_640770 : CollatzResearch.WordTrace tailWord_640770 prefixEnd_640770 73116221995902937361813 := by
  unfold tailWord_640770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842700472151799912139941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15580534592404799765706509 5842700472151799912139941)
  ·
    refine ⟨1095506338528462483526239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5842700472151799912139941 1095506338528462483526239)
    ·
      refine ⟨1643259507792693725289359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095506338528462483526239 1643259507792693725289359)
      ·
        refine ⟨2464889261689040587934039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643259507792693725289359 2464889261689040587934039)
        ·
          refine ⟨3697333892533560881901059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464889261689040587934039 3697333892533560881901059)
          ·
            refine ⟨5546000838800341322851589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697333892533560881901059 5546000838800341322851589)
            ·
              refine ⟨1039875157275063998034673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5546000838800341322851589 1039875157275063998034673)
              ·
                refine ⟨779906367956297998526005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039875157275063998034673 779906367956297998526005)
                ·
                  refine ⟨73116221995902937361813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779906367956297998526005 73116221995902937361813)
                  ·
                    rfl

theorem cell22_640770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_640770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640770 prefixEnd_640770 := by exact prefixLift 640770
  have htrace : WordTrace (prefixWord ++ tailWord_640770) baseStart_640770 baseEnd_640770 := by
    simpa [prefixWord, tailWord_640770, baseEnd_640770] using wordTrace_append hprefix tailTrace_640770
  have hstable : (prefixWord ++ tailWord_640770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640770).length < 2 ^ (prefixWord ++ tailWord_640770).sum := by decide
  have hdescent : baseEnd_640770 < baseStart_640770 := by decide
  rcases family_descends (prefixWord ++ tailWord_640770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640817 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_640817 : Nat := 118140960795 + 640817 * 2 ^ 59
def prefixEnd_640817 : Nat := 4983230072969 + 3 ^ 40 * 640817 * 2
def baseEnd_640817 : Nat := 219364755048216356160295

theorem tailTrace_640817 : CollatzResearch.WordTrace tailWord_640817 prefixEnd_640817 219364755048216356160295 := by
  unfold tailWord_640817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372516119436926675520705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15581677412957951117013803 23372516119436926675520705)
  ·
    refine ⟨17529387089577695006640529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23372516119436926675520705 17529387089577695006640529)
    ·
      refine ⟨13147040317183271254980397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17529387089577695006640529 13147040317183271254980397)
      ·
        refine ⟨4930140118943726720617649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13147040317183271254980397 4930140118943726720617649)
        ·
          refine ⟨3697605089207795040463237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930140118943726720617649 3697605089207795040463237)
          ·
            refine ⟨693300954226461570086857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3697605089207795040463237 693300954226461570086857)
            ·
              refine ⟨519975715669846177565143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693300954226461570086857 519975715669846177565143)
              ·
                refine ⟨779963573504769266347715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519975715669846177565143 779963573504769266347715)
                ·
                  refine ⟨1169945360257153899521573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779963573504769266347715 1169945360257153899521573)
                  ·
                    refine ⟨219364755048216356160295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169945360257153899521573 219364755048216356160295)
                    ·
                      rfl

theorem cell22_640817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_640817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640817 prefixEnd_640817 := by exact prefixLift 640817
  have htrace : WordTrace (prefixWord ++ tailWord_640817) baseStart_640817 baseEnd_640817 := by
    simpa [prefixWord, tailWord_640817, baseEnd_640817] using wordTrace_append hprefix tailTrace_640817
  have hstable : (prefixWord ++ tailWord_640817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640817).length < 2 ^ (prefixWord ++ tailWord_640817).sum := by decide
  have hdescent : baseEnd_640817 < baseStart_640817 := by decide
  rcases family_descends (prefixWord ++ tailWord_640817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640828 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_640828 : Nat := 118140960795 + 640828 * 2 ^ 59
def prefixEnd_640828 : Nat := 4983230072969 + 3 ^ 40 * 640828 * 2
def baseEnd_640828 : Nat := 219368520573015994135261

theorem tailTrace_640828 : CollatzResearch.WordTrace tailWord_640828 prefixEnd_640828 219368520573015994135261 := by
  unfold tailWord_640828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686458661198537777085569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15581944881598050369447425 11686458661198537777085569)
  ·
    refine ⟨8764843995898903332814177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11686458661198537777085569 8764843995898903332814177)
    ·
      refine ⟨6573632996924177499610633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8764843995898903332814177 6573632996924177499610633)
      ·
        refine ⟨4930224747693133124707975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6573632996924177499610633 4930224747693133124707975)
        ·
          refine ⟨7395337121539699687061963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930224747693133124707975 7395337121539699687061963)
          ·
            refine ⟨11093005682309549530592945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395337121539699687061963 11093005682309549530592945)
            ·
              refine ⟨8319754261732162147944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11093005682309549530592945 8319754261732162147944709)
              ·
                refine ⟨1559953924074780402739633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8319754261732162147944709 1559953924074780402739633)
                ·
                  refine ⟨1169965443056085302054725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559953924074780402739633 1169965443056085302054725)
                  ·
                    refine ⟨219368520573015994135261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169965443056085302054725 219368520573015994135261)
                    ·
                      rfl

theorem cell22_640828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_640828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640828 prefixEnd_640828 := by exact prefixLift 640828
  have htrace : WordTrace (prefixWord ++ tailWord_640828) baseStart_640828 baseEnd_640828 := by
    simpa [prefixWord, tailWord_640828, baseEnd_640828] using wordTrace_append hprefix tailTrace_640828
  have hstable : (prefixWord ++ tailWord_640828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640828).length < 2 ^ (prefixWord ++ tailWord_640828).sum := by decide
  have hdescent : baseEnd_640828 < baseStart_640828 := by decide
  rcases family_descends (prefixWord ++ tailWord_640828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640845 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_640845 : Nat := 118140960795 + 640845 * 2 ^ 59
def prefixEnd_640845 : Nat := 4983230072969 + 3 ^ 40 * 640845 * 2
def baseEnd_640845 : Nat := 219374340020433616460209

theorem tailTrace_640845 : CollatzResearch.WordTrace tailWord_640845 prefixEnd_640845 219374340020433616460209 := by
  unfold tailWord_640845
  simp only [CollatzResearch.WordTrace]
  refine ⟨23373537363335487457539989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15582358242223658305026659 23373537363335487457539989)
  ·
    refine ⟨1095634563906350974572187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23373537363335487457539989 1095634563906350974572187)
    ·
      refine ⟨1643451845859526461858281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095634563906350974572187 1643451845859526461858281)
      ·
        refine ⟨1232588884394644846393711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643451845859526461858281 1232588884394644846393711)
        ·
          refine ⟨1848883326591967269590567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232588884394644846393711 1848883326591967269590567)
          ·
            refine ⟨2773324989887950904385851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848883326591967269590567 2773324989887950904385851)
            ·
              refine ⟨4159987484831926356578777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773324989887950904385851 4159987484831926356578777)
              ·
                refine ⟨3119990613623944767434083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159987484831926356578777 3119990613623944767434083)
                ·
                  refine ⟨4679985920435917151151125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119990613623944767434083 4679985920435917151151125)
                  ·
                    refine ⟨219374340020433616460209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4679985920435917151151125 219374340020433616460209)
                    ·
                      rfl

theorem cell22_640845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_640845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640845 prefixEnd_640845 := by exact prefixLift 640845
  have htrace : WordTrace (prefixWord ++ tailWord_640845) baseStart_640845 baseEnd_640845 := by
    simpa [prefixWord, tailWord_640845, baseEnd_640845] using wordTrace_append hprefix tailTrace_640845
  have hstable : (prefixWord ++ tailWord_640845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640845).length < 2 ^ (prefixWord ++ tailWord_640845).sum := by decide
  have hdescent : baseEnd_640845 < baseStart_640845 := by decide
  rcases family_descends (prefixWord ++ tailWord_640845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640860 : List Nat := [2, 2, 4, 2, 2, 1, 1, 8]
def baseStart_640860 : Nat := 118140960795 + 640860 * 2 ^ 59
def prefixEnd_640860 : Nat := 4983230072969 + 3 ^ 40 * 640860 * 2
def baseEnd_640860 : Nat := 24375497202997619703907

theorem tailTrace_640860 : CollatzResearch.WordTrace tailWord_640860 prefixEnd_640860 24375497202997619703907 := by
  unfold tailWord_640860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687042229140572509668017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15582722972187430012890689 11687042229140572509668017)
  ·
    refine ⟨8765281671855429382251013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11687042229140572509668017 8765281671855429382251013)
    ·
      refine ⟨1643490313472893009172065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8765281671855429382251013 1643490313472893009172065)
      ·
        refine ⟨1232617735104669756879049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643490313472893009172065 1232617735104669756879049)
        ·
          refine ⟨924463301328502317659287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232617735104669756879049 924463301328502317659287)
          ·
            refine ⟨1386694951992753476488931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924463301328502317659287 1386694951992753476488931)
            ·
              refine ⟨2080042427989130214733397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386694951992753476488931 2080042427989130214733397)
              ·
                refine ⟨24375497202997619703907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2080042427989130214733397 24375497202997619703907)
                ·
                  rfl

theorem cell22_640860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_640860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640860 prefixEnd_640860 := by exact prefixLift 640860
  have htrace : WordTrace (prefixWord ++ tailWord_640860) baseStart_640860 baseEnd_640860 := by
    simpa [prefixWord, tailWord_640860, baseEnd_640860] using wordTrace_append hprefix tailTrace_640860
  have hstable : (prefixWord ++ tailWord_640860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640860).length < 2 ^ (prefixWord ++ tailWord_640860).sum := by decide
  have hdescent : baseEnd_640860 < baseStart_640860 := by decide
  rcases family_descends (prefixWord ++ tailWord_640860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640980 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_640980 : Nat := 118140960795 + 640980 * 2 ^ 59
def prefixEnd_640980 : Nat := 4983230072969 + 3 ^ 40 * 640980 * 2
def baseEnd_640980 : Nat := 219420553279338264334795

theorem tailTrace_640980 : CollatzResearch.WordTrace tailWord_640980 prefixEnd_640980 219420553279338264334795 := by
  unfold tailWord_640980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689230608923202756852197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15585640811897603675802929 11689230608923202756852197)
  ·
    refine ⟨2191730739173100516909787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11689230608923202756852197 2191730739173100516909787)
    ·
      refine ⟨3287596108759650775364681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191730739173100516909787 3287596108759650775364681)
      ·
        refine ⟨2465697081569738081523511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3287596108759650775364681 2465697081569738081523511)
        ·
          refine ⟨3698545622354607122285267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465697081569738081523511 3698545622354607122285267)
          ·
            refine ⟨5547818433531910683427901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698545622354607122285267 5547818433531910683427901)
            ·
              refine ⟨2080431912574466506285463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547818433531910683427901 2080431912574466506285463)
              ·
                refine ⟨3120647868861699759428195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080431912574466506285463 3120647868861699759428195)
                ·
                  refine ⟨4680971803292549639142293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120647868861699759428195 4680971803292549639142293)
                  ·
                    refine ⟨219420553279338264334795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4680971803292549639142293 219420553279338264334795)
                    ·
                      rfl

theorem cell22_640980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_640980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640980 prefixEnd_640980 := by exact prefixLift 640980
  have htrace : WordTrace (prefixWord ++ tailWord_640980) baseStart_640980 baseEnd_640980 := by
    simpa [prefixWord, tailWord_640980, baseEnd_640980] using wordTrace_append hprefix tailTrace_640980
  have hstable : (prefixWord ++ tailWord_640980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640980).length < 2 ^ (prefixWord ++ tailWord_640980).sum := by decide
  have hdescent : baseEnd_640980 < baseStart_640980 := by decide
  rcases family_descends (prefixWord ++ tailWord_640980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640986 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_640986 : Nat := 118140960795 + 640986 * 2 ^ 59
def prefixEnd_640986 : Nat := 4983230072969 + 3 ^ 40 * 640986 * 2
def baseEnd_640986 : Nat := 219422607201956248684777

theorem tailTrace_640986 : CollatzResearch.WordTrace tailWord_640986 prefixEnd_640986 219422607201956248684777 := by
  unfold tailWord_640986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844670013956167134605703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15585786703883112358948541 5844670013956167134605703)
  ·
    refine ⟨8767005020934250701908555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5844670013956167134605703 8767005020934250701908555)
    ·
      refine ⟨13150507531401376052862833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8767005020934250701908555 13150507531401376052862833)
      ·
        refine ⟨9862880648551032039647125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13150507531401376052862833 9862880648551032039647125)
        ·
          refine ⟨462322530400829626858459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9862880648551032039647125 462322530400829626858459)
          ·
            refine ⟨693483795601244440287689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462322530400829626858459 693483795601244440287689)
            ·
              refine ⟨520112846700933330215767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693483795601244440287689 520112846700933330215767)
              ·
                refine ⟨780169270051399995323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520112846700933330215767 780169270051399995323651)
                ·
                  refine ⟨1170253905077099992985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780169270051399995323651 1170253905077099992985477)
                  ·
                    refine ⟨219422607201956248684777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170253905077099992985477 219422607201956248684777)
                    ·
                      rfl

theorem cell22_640986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_640986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_640986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_640986 prefixEnd_640986 := by exact prefixLift 640986
  have htrace : WordTrace (prefixWord ++ tailWord_640986) baseStart_640986 baseEnd_640986 := by
    simpa [prefixWord, tailWord_640986, baseEnd_640986] using wordTrace_append hprefix tailTrace_640986
  have hstable : (prefixWord ++ tailWord_640986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640986).length < 2 ^ (prefixWord ++ tailWord_640986).sum := by decide
  have hdescent : baseEnd_640986 < baseStart_640986 := by decide
  rcases family_descends (prefixWord ++ tailWord_640986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641008 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_641008 : Nat := 118140960795 + 641008 * 2 ^ 59
def prefixEnd_641008 : Nat := 4983230072969 + 3 ^ 40 * 641008 * 2
def baseEnd_641008 : Nat := 219430138251555524634709

theorem tailTrace_641008 : CollatzResearch.WordTrace tailWord_641008 prefixEnd_641008 219430138251555524634709 := by
  unfold tailWord_641008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689741230872483147861839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15586321641163310863815785 11689741230872483147861839)
  ·
    refine ⟨17534611846308724721792759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11689741230872483147861839 17534611846308724721792759)
    ·
      refine ⟨26301917769463087082689139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17534611846308724721792759 26301917769463087082689139)
      ·
        refine ⟨39452876654194630624033709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26301917769463087082689139 39452876654194630624033709)
        ·
          refine ⟨14794828745322986484012641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39452876654194630624033709 14794828745322986484012641)
          ·
            refine ⟨11096121558992239863009481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14794828745322986484012641 11096121558992239863009481)
            ·
              refine ⟨8322091169244179897257111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11096121558992239863009481 8322091169244179897257111)
              ·
                refine ⟨12483136753866269845885667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322091169244179897257111 12483136753866269845885667)
                ·
                  refine ⟨18724705130799404768828501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12483136753866269845885667 18724705130799404768828501)
                  ·
                    refine ⟨219430138251555524634709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18724705130799404768828501 219430138251555524634709)
                    ·
                      rfl

theorem cell22_641008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_641008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641008 prefixEnd_641008 := by exact prefixLift 641008
  have htrace : WordTrace (prefixWord ++ tailWord_641008) baseStart_641008 baseEnd_641008 := by
    simpa [prefixWord, tailWord_641008, baseEnd_641008] using wordTrace_append hprefix tailTrace_641008
  have hstable : (prefixWord ++ tailWord_641008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641008).length < 2 ^ (prefixWord ++ tailWord_641008).sum := by decide
  have hdescent : baseEnd_641008 < baseStart_641008 := by decide
  rcases family_descends (prefixWord ++ tailWord_641008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641061 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_641061 : Nat := 118140960795 + 641061 * 2 ^ 59
def prefixEnd_641061 : Nat := 4983230072969 + 3 ^ 40 * 641061 * 2
def baseEnd_641061 : Nat := 219448281234681053059547

theorem tailTrace_641061 : CollatzResearch.WordTrace tailWord_641061 prefixEnd_641061 219448281234681053059547 := by
  unfold tailWord_641061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23381415530552956347403037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15587610353701970898268691 23381415530552956347403037)
  ·
    refine ⟨8768030823957358630276139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23381415530552956347403037 8768030823957358630276139)
    ·
      refine ⟨13152046235936037945414209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8768030823957358630276139 13152046235936037945414209)
      ·
        refine ⟨9864034676952028459060657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13152046235936037945414209 9864034676952028459060657)
        ·
          refine ⟨7398026007714021344295493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9864034676952028459060657 7398026007714021344295493)
          ·
            refine ⟨1387129876446379002055405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7398026007714021344295493 1387129876446379002055405)
            ·
              refine ⟨520173703667392125770777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1387129876446379002055405 520173703667392125770777)
              ·
                refine ⟨390130277750544094328083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520173703667392125770777 390130277750544094328083)
                ·
                  refine ⟨585195416625816141492125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390130277750544094328083 585195416625816141492125)
                  ·
                    refine ⟨219448281234681053059547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 585195416625816141492125 219448281234681053059547)
                    ·
                      rfl

theorem cell22_641061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_641061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641061 prefixEnd_641061 := by exact prefixLift 641061
  have htrace : WordTrace (prefixWord ++ tailWord_641061) baseStart_641061 baseEnd_641061 := by
    simpa [prefixWord, tailWord_641061, baseEnd_641061] using wordTrace_append hprefix tailTrace_641061
  have hstable : (prefixWord ++ tailWord_641061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641061).length < 2 ^ (prefixWord ++ tailWord_641061).sum := by decide
  have hdescent : baseEnd_641061 < baseStart_641061 := by decide
  rcases family_descends (prefixWord ++ tailWord_641061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641074 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_641074 : Nat := 118140960795 + 641074 * 2 ^ 59
def prefixEnd_641074 : Nat := 4983230072969 + 3 ^ 40 * 641074 * 2
def baseEnd_641074 : Nat := 73150910466784450828169

theorem tailTrace_641074 : CollatzResearch.WordTrace tailWord_641074 prefixEnd_641074 73150910466784450828169 := by
  unfold tailWord_641074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845472419876464891906569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15587926453003906378417517 5845472419876464891906569)
  ·
    refine ⟨4384104314907348668929927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5845472419876464891906569 4384104314907348668929927)
    ·
      refine ⟨6576156472361023003394891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384104314907348668929927 6576156472361023003394891)
      ·
        refine ⟨9864234708541534505092337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576156472361023003394891 9864234708541534505092337)
        ·
          refine ⟨7398176031406150878819253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9864234708541534505092337 7398176031406150878819253)
          ·
            refine ⟨693579002944326644889305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7398176031406150878819253 693579002944326644889305)
            ·
              refine ⟨520184252208244983666979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693579002944326644889305 520184252208244983666979)
              ·
                refine ⟨780276378312367475500469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520184252208244983666979 780276378312367475500469)
                ·
                  refine ⟨73150910466784450828169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 780276378312367475500469 73150910466784450828169)
                  ·
                    rfl

theorem cell22_641074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_641074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641074 prefixEnd_641074 := by exact prefixLift 641074
  have htrace : WordTrace (prefixWord ++ tailWord_641074) baseStart_641074 baseEnd_641074 := by
    simpa [prefixWord, tailWord_641074, baseEnd_641074] using wordTrace_append hprefix tailTrace_641074
  have hstable : (prefixWord ++ tailWord_641074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641074).length < 2 ^ (prefixWord ++ tailWord_641074).sum := by decide
  have hdescent : baseEnd_641074 < baseStart_641074 := by decide
  rcases family_descends (prefixWord ++ tailWord_641074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641085 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 8]
def baseStart_641085 : Nat := 118140960795 + 641085 * 2 ^ 59
def prefixEnd_641085 : Nat := 4983230072969 + 3 ^ 40 * 641085 * 2
def baseEnd_641085 : Nat := 73152165641717663486491

theorem tailTrace_641085 : CollatzResearch.WordTrace tailWord_641085 prefixEnd_641085 73152165641717663486491 := by
  unfold tailWord_641085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382290882466008446276709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15588193921644005630851139 23382290882466008446276709)
  ·
    refine ⟨4384179540462376583676883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23382290882466008446276709 4384179540462376583676883)
    ·
      refine ⟨6576269310693564875515325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384179540462376583676883 6576269310693564875515325)
      ·
        refine ⟨2466100991510086828318247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6576269310693564875515325 2466100991510086828318247)
        ·
          refine ⟨3699151487265130242477371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466100991510086828318247 3699151487265130242477371)
          ·
            refine ⟨5548727230897695363716057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699151487265130242477371 5548727230897695363716057)
            ·
              refine ⟨4161545423173271522787043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548727230897695363716057 4161545423173271522787043)
              ·
                refine ⟨6242318134759907284180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161545423173271522787043 6242318134759907284180565)
                ·
                  refine ⟨73152165641717663486491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6242318134759907284180565 73152165641717663486491)
                  ·
                    rfl

theorem cell22_641085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_641085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641085 prefixEnd_641085 := by exact prefixLift 641085
  have htrace : WordTrace (prefixWord ++ tailWord_641085) baseStart_641085 baseEnd_641085 := by
    simpa [prefixWord, tailWord_641085, baseEnd_641085] using wordTrace_append hprefix tailTrace_641085
  have hstable : (prefixWord ++ tailWord_641085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641085).length < 2 ^ (prefixWord ++ tailWord_641085).sum := by decide
  have hdescent : baseEnd_641085 < baseStart_641085 := by decide
  rcases family_descends (prefixWord ++ tailWord_641085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641087 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 1, 4]
def baseStart_641087 : Nat := 118140960795 + 641087 * 2 ^ 59
def prefixEnd_641087 : Nat := 4983230072969 + 3 ^ 40 * 641087 * 2
def baseEnd_641087 : Nat := 219457181566025651909467

theorem tailTrace_641087 : CollatzResearch.WordTrace tailWord_641087 prefixEnd_641087 219457181566025651909467 := by
  unfold tailWord_641087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382363828458762787849515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15588242552305841858566343 23382363828458762787849515)
  ·
    refine ⟨35073545742688144181774273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23382363828458762787849515 35073545742688144181774273)
    ·
      refine ⟨26305159307016108136330705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35073545742688144181774273 26305159307016108136330705)
      ·
        refine ⟨19728869480262081102248029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26305159307016108136330705 19728869480262081102248029)
        ·
          refine ⟨7398326055098280413343011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19728869480262081102248029 7398326055098280413343011)
          ·
            refine ⟨11097489082647420620014517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398326055098280413343011 11097489082647420620014517)
            ·
              refine ⟨1040389601498195683126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11097489082647420620014517 1040389601498195683126361)
              ·
                refine ⟨780292201123646762344771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040389601498195683126361 780292201123646762344771)
                ·
                  refine ⟨1170438301685470143517157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780292201123646762344771 1170438301685470143517157)
                  ·
                    refine ⟨219457181566025651909467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170438301685470143517157 219457181566025651909467)
                    ·
                      rfl

theorem cell22_641087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_641087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641087 prefixEnd_641087 := by exact prefixLift 641087
  have htrace : WordTrace (prefixWord ++ tailWord_641087) baseStart_641087 baseEnd_641087 := by
    simpa [prefixWord, tailWord_641087, baseEnd_641087] using wordTrace_append hprefix tailTrace_641087
  have hstable : (prefixWord ++ tailWord_641087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641087).length < 2 ^ (prefixWord ++ tailWord_641087).sum := by decide
  have hdescent : baseEnd_641087 < baseStart_641087 := by decide
  rcases family_descends (prefixWord ++ tailWord_641087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641100 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_641100 : Nat := 118140960795 + 641100 * 2 ^ 59
def prefixEnd_641100 : Nat := 4983230072969 + 3 ^ 40 * 641100 * 2
def baseEnd_641100 : Nat := 219461631731697951334427

theorem tailTrace_641100 : CollatzResearch.WordTrace tailWord_641100 prefixEnd_641100 219461631731697951334427 := by
  unfold tailWord_641100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691418988705833004036377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15588558651607777338715169 11691418988705833004036377)
  ·
    refine ⟨8768564241529374753027283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11691418988705833004036377 8768564241529374753027283)
    ·
      refine ⟨13152846362294062129540925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8768564241529374753027283 13152846362294062129540925)
      ·
        refine ⟨4932317385860273298577847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13152846362294062129540925 4932317385860273298577847)
        ·
          refine ⟨7398476078790409947866771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932317385860273298577847 7398476078790409947866771)
          ·
            refine ⟨11097714118185614921800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398476078790409947866771 11097714118185614921800157)
            ·
              refine ⟨4161642794319605595675059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11097714118185614921800157 4161642794319605595675059)
              ·
                refine ⟨6242464191479408393512589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161642794319605595675059 6242464191479408393512589)
                ·
                  refine ⟨2340924071804778147567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242464191479408393512589 2340924071804778147567221)
                  ·
                    refine ⟨219461631731697951334427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2340924071804778147567221 219461631731697951334427)
                    ·
                      rfl

theorem cell22_641100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_641100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641100 prefixEnd_641100 := by exact prefixLift 641100
  have htrace : WordTrace (prefixWord ++ tailWord_641100) baseStart_641100 baseEnd_641100 := by
    simpa [prefixWord, tailWord_641100, baseEnd_641100] using wordTrace_append hprefix tailTrace_641100
  have hstable : (prefixWord ++ tailWord_641100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641100).length < 2 ^ (prefixWord ++ tailWord_641100).sum := by decide
  have hdescent : baseEnd_641100 < baseStart_641100 := by decide
  rcases family_descends (prefixWord ++ tailWord_641100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641134 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_641134 : Nat := 118140960795 + 641134 * 2 ^ 59
def prefixEnd_641134 : Nat := 4983230072969 + 3 ^ 40 * 641134 * 2
def baseEnd_641134 : Nat := 219473270626533195984323

theorem tailTrace_641134 : CollatzResearch.WordTrace tailWord_641134 prefixEnd_641134 219473270626533195984323 := by
  unfold tailWord_641134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923009757411061226851307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15589385372858993209873637 2923009757411061226851307)
  ·
    refine ⟨4384514636116591840276961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923009757411061226851307 4384514636116591840276961)
    ·
      refine ⟨3288385977087443880207721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4384514636116591840276961 3288385977087443880207721)
      ·
        refine ⟨2466289482815582910155791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288385977087443880207721 2466289482815582910155791)
        ·
          refine ⟨3699434224223374365233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466289482815582910155791 3699434224223374365233687)
          ·
            refine ⟨5549151336335061547850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699434224223374365233687 5549151336335061547850531)
            ·
              refine ⟨8323727004502592321775797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549151336335061547850531 8323727004502592321775797)
              ·
                refine ⟨780349406672118030166481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8323727004502592321775797 780349406672118030166481)
                ·
                  refine ⟨585262055004088522624861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780349406672118030166481 585262055004088522624861)
                  ·
                    refine ⟨219473270626533195984323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 585262055004088522624861 219473270626533195984323)
                    ·
                      rfl

theorem cell22_641134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_641134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641134 prefixEnd_641134 := by exact prefixLift 641134
  have htrace : WordTrace (prefixWord ++ tailWord_641134) baseStart_641134 baseEnd_641134 := by
    simpa [prefixWord, tailWord_641134, baseEnd_641134] using wordTrace_append hprefix tailTrace_641134
  have hstable : (prefixWord ++ tailWord_641134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641134).length < 2 ^ (prefixWord ++ tailWord_641134).sum := by decide
  have hdescent : baseEnd_641134 < baseStart_641134 := by decide
  rcases family_descends (prefixWord ++ tailWord_641134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641149 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_641149 : Nat := 118140960795 + 641149 * 2 ^ 59
def prefixEnd_641149 : Nat := 4983230072969 + 3 ^ 40 * 641149 * 2
def baseEnd_641149 : Nat := 219478405433078156859277

theorem tailTrace_641149 : CollatzResearch.WordTrace tailWord_641149 prefixEnd_641149 219478405433078156859277 := by
  unfold tailWord_641149
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384625154234147376606501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15589750102822764917737667 23384625154234147376606501)
  ·
    refine ⟨4384617216418902633113719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23384625154234147376606501 4384617216418902633113719)
    ·
      refine ⟨6576925824628353949670579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384617216418902633113719 6576925824628353949670579)
      ·
        refine ⟨9865388736942530924505869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576925824628353949670579 9865388736942530924505869)
        ·
          refine ⟨3699520776353449096689701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9865388736942530924505869 3699520776353449096689701)
          ·
            refine ⟨693660145566271705629319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3699520776353449096689701 693660145566271705629319)
            ·
              refine ⟨1040490218349407558443979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693660145566271705629319 1040490218349407558443979)
              ·
                refine ⟨1560735327524111337665969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040490218349407558443979 1560735327524111337665969)
                ·
                  refine ⟨1170551495643083503249477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560735327524111337665969 1170551495643083503249477)
                  ·
                    refine ⟨219478405433078156859277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170551495643083503249477 219478405433078156859277)
                    ·
                      rfl

theorem cell22_641149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_641149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641149 prefixEnd_641149 := by exact prefixLift 641149
  have htrace : WordTrace (prefixWord ++ tailWord_641149) baseStart_641149 baseEnd_641149 := by
    simpa [prefixWord, tailWord_641149, baseEnd_641149] using wordTrace_append hprefix tailTrace_641149
  have hstable : (prefixWord ++ tailWord_641149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641149).length < 2 ^ (prefixWord ++ tailWord_641149).sum := by decide
  have hdescent : baseEnd_641149 < baseStart_641149 := by decide
  rcases family_descends (prefixWord ++ tailWord_641149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641179 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 1, 3]
def baseStart_641179 : Nat := 118140960795 + 641179 * 2 ^ 59
def prefixEnd_641179 : Nat := 4983230072969 + 3 ^ 40 * 641179 * 2
def baseEnd_641179 : Nat := 219488675046168078609185

theorem tailTrace_641179 : CollatzResearch.WordTrace tailWord_641179 prefixEnd_641179 219488675046168078609185 := by
  unfold tailWord_641179
  simp only [CollatzResearch.WordTrace]
  refine ⟨23385719344125462500198591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15590479562750308333465727 23385719344125462500198591)
  ·
    refine ⟨35078579016188193750297887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23385719344125462500198591 35078579016188193750297887)
    ·
      refine ⟨52617868524282290625446831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35078579016188193750297887 52617868524282290625446831)
      ·
        refine ⟨78926802786423435938170247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52617868524282290625446831 78926802786423435938170247)
        ·
          refine ⟨118390204179635153907255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78926802786423435938170247 118390204179635153907255371)
          ·
            refine ⟨177585306269452730860883057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118390204179635153907255371 177585306269452730860883057)
            ·
              refine ⟨133188979702089548145662293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177585306269452730860883057 133188979702089548145662293)
              ·
                refine ⟨390202088970965473082995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 133188979702089548145662293 390202088970965473082995)
                ·
                  refine ⟨585303133456448209624493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390202088970965473082995 585303133456448209624493)
                  ·
                    refine ⟨219488675046168078609185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 585303133456448209624493 219488675046168078609185)
                    ·
                      rfl

theorem cell22_641179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 3].length) (baseStart_641179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641179 prefixEnd_641179 := by exact prefixLift 641179
  have htrace : WordTrace (prefixWord ++ tailWord_641179) baseStart_641179 baseEnd_641179 := by
    simpa [prefixWord, tailWord_641179, baseEnd_641179] using wordTrace_append hprefix tailTrace_641179
  have hstable : (prefixWord ++ tailWord_641179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641179).length < 2 ^ (prefixWord ++ tailWord_641179).sum := by decide
  have hdescent : baseEnd_641179 < baseStart_641179 := by decide
  rcases family_descends (prefixWord ++ tailWord_641179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641198 : List Nat := [4, 1, 4, 2, 1, 2, 2, 6]
def baseStart_641198 : Nat := 118140960795 + 641198 * 2 ^ 59
def prefixEnd_641198 : Nat := 4983230072969 + 3 ^ 40 * 641198 * 2
def baseEnd_641198 : Nat := 24388353237162040264903

theorem tailTrace_641198 : CollatzResearch.WordTrace tailWord_641198 prefixEnd_641198 24388353237162040264903 := by
  unfold tailWord_641198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923301541382078593142531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15590941554037752496760165 2923301541382078593142531)
  ·
    refine ⟨4384952312073117889713797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923301541382078593142531 4384952312073117889713797)
    ·
      refine ⟨822178558513709604321337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4384952312073117889713797 822178558513709604321337)
      ·
        refine ⟨616633918885282203241003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822178558513709604321337 616633918885282203241003)
        ·
          refine ⟨924950878327923304861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616633918885282203241003 924950878327923304861505)
          ·
            refine ⟨693713158745942478646129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924950878327923304861505 693713158745942478646129)
            ·
              refine ⟨520284869059456858984597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693713158745942478646129 520284869059456858984597)
              ·
                refine ⟨24388353237162040264903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 520284869059456858984597 24388353237162040264903)
                ·
                  rfl

theorem cell22_641198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_641198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641198 prefixEnd_641198 := by exact prefixLift 641198
  have htrace : WordTrace (prefixWord ++ tailWord_641198) baseStart_641198 baseEnd_641198 := by
    simpa [prefixWord, tailWord_641198, baseEnd_641198] using wordTrace_append hprefix tailTrace_641198
  have hstable : (prefixWord ++ tailWord_641198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641198).length < 2 ^ (prefixWord ++ tailWord_641198).sum := by decide
  have hdescent : baseEnd_641198 < baseStart_641198 := by decide
  rcases family_descends (prefixWord ++ tailWord_641198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641235 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_641235 : Nat := 118140960795 + 641235 * 2 ^ 59
def prefixEnd_641235 : Nat := 4983230072969 + 3 ^ 40 * 641235 * 2
def baseEnd_641235 : Nat := 219507844990602599209013

theorem tailTrace_641235 : CollatzResearch.WordTrace tailWord_641235 prefixEnd_641235 219507844990602599209013 := by
  unfold tailWord_641235
  simp only [CollatzResearch.WordTrace]
  refine ⟨23387761831922584064237159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15591841221281722709491439 23387761831922584064237159)
  ·
    refine ⟨35081642747883876096355739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23387761831922584064237159 35081642747883876096355739)
    ·
      refine ⟨52622464121825814144533609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35081642747883876096355739 52622464121825814144533609)
      ·
        refine ⟨39466848091369360608400207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52622464121825814144533609 39466848091369360608400207)
        ·
          refine ⟨59200272137054040912600311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39466848091369360608400207 59200272137054040912600311)
          ·
            refine ⟨88800408205581061368900467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59200272137054040912600311 88800408205581061368900467)
            ·
              refine ⟨133200612308371592053350701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88800408205581061368900467 133200612308371592053350701)
              ·
                refine ⟨49950229615639347020006513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133200612308371592053350701 49950229615639347020006513)
                ·
                  refine ⟨37462672211729510265004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49950229615639347020006513 37462672211729510265004885)
                  ·
                    refine ⟨219507844990602599209013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37462672211729510265004885 219507844990602599209013)
                    ·
                      rfl

theorem cell22_641235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_641235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641235 prefixEnd_641235 := by exact prefixLift 641235
  have htrace : WordTrace (prefixWord ++ tailWord_641235) baseStart_641235 baseEnd_641235 := by
    simpa [prefixWord, tailWord_641235, baseEnd_641235] using wordTrace_append hprefix tailTrace_641235
  have hstable : (prefixWord ++ tailWord_641235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641235).length < 2 ^ (prefixWord ++ tailWord_641235).sum := by decide
  have hdescent : baseEnd_641235 < baseStart_641235 := by decide
  rcases family_descends (prefixWord ++ tailWord_641235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641252 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_641252 : Nat := 118140960795 + 641252 * 2 ^ 59
def prefixEnd_641252 : Nat := 4983230072969 + 3 ^ 40 * 641252 * 2
def baseEnd_641252 : Nat := 219513664438020221533961

theorem tailTrace_641252 : CollatzResearch.WordTrace tailWord_641252 prefixEnd_641252 219513664438020221533961 := by
  unfold tailWord_641252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694190936430497983803005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15592254581907330645070673 11694190936430497983803005)
  ·
    refine ⟨4385321601161436743926127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11694190936430497983803005 4385321601161436743926127)
    ·
      refine ⟨6577982401742155115889191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385321601161436743926127 6577982401742155115889191)
      ·
        refine ⟨9866973602613232673833787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577982401742155115889191 9866973602613232673833787)
        ·
          refine ⟨14800460403919849010750681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866973602613232673833787 14800460403919849010750681)
          ·
            refine ⟨11100345302939886758063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14800460403919849010750681 11100345302939886758063011)
            ·
              refine ⟨16650517954409830137094517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11100345302939886758063011 16650517954409830137094517)
              ·
                refine ⟨1560986058225921575352611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16650517954409830137094517 1560986058225921575352611)
                ·
                  refine ⟨2341479087338882363028917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560986058225921575352611 2341479087338882363028917)
                  ·
                    refine ⟨219513664438020221533961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2341479087338882363028917 219513664438020221533961)
                    ·
                      rfl

theorem cell22_641252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_641252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641252 prefixEnd_641252 := by exact prefixLift 641252
  have htrace : WordTrace (prefixWord ++ tailWord_641252) baseStart_641252 baseEnd_641252 := by
    simpa [prefixWord, tailWord_641252, baseEnd_641252] using wordTrace_append hprefix tailTrace_641252
  have hstable : (prefixWord ++ tailWord_641252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641252).length < 2 ^ (prefixWord ++ tailWord_641252).sum := by decide
  have hdescent : baseEnd_641252 < baseStart_641252 := by decide
  rcases family_descends (prefixWord ++ tailWord_641252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641256 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_641256 : Nat := 118140960795 + 641256 * 2 ^ 59
def prefixEnd_641256 : Nat := 4983230072969 + 3 ^ 40 * 641256 * 2
def baseEnd_641256 : Nat := 219515033719765544433949

theorem tailTrace_641256 : CollatzResearch.WordTrace tailWord_641256 prefixEnd_641256 219515033719765544433949 := by
  unfold tailWord_641256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694263882423252325375811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15592351843231003100501081 11694263882423252325375811)
  ·
    refine ⟨17541395823634878488063717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694263882423252325375811 17541395823634878488063717)
    ·
      refine ⟨3289011716931539716511947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17541395823634878488063717 3289011716931539716511947)
      ·
        refine ⟨4933517575397309574767921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289011716931539716511947 4933517575397309574767921)
        ·
          refine ⟨3700138181547982181075941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4933517575397309574767921 3700138181547982181075941)
          ·
            refine ⟨693775909040246658951739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3700138181547982181075941 693775909040246658951739)
            ·
              refine ⟨1040663863560369988427609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693775909040246658951739 1040663863560369988427609)
              ·
                refine ⟨780497897670277491320707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040663863560369988427609 780497897670277491320707)
                ·
                  refine ⟨1170746846505416236981061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780497897670277491320707 1170746846505416236981061)
                  ·
                    refine ⟨219515033719765544433949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170746846505416236981061 219515033719765544433949)
                    ·
                      rfl

theorem cell22_641256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_641256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641256 prefixEnd_641256 := by exact prefixLift 641256
  have htrace : WordTrace (prefixWord ++ tailWord_641256) baseStart_641256 baseEnd_641256 := by
    simpa [prefixWord, tailWord_641256, baseEnd_641256] using wordTrace_append hprefix tailTrace_641256
  have hstable : (prefixWord ++ tailWord_641256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641256).length < 2 ^ (prefixWord ++ tailWord_641256).sum := by decide
  have hdescent : baseEnd_641256 < baseStart_641256 := by decide
  rcases family_descends (prefixWord ++ tailWord_641256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641288 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_641288 : Nat := 118140960795 + 641288 * 2 ^ 59
def prefixEnd_641288 : Nat := 4983230072969 + 3 ^ 40 * 641288 * 2
def baseEnd_641288 : Nat := 73175329324576042544617

theorem tailTrace_641288 : CollatzResearch.WordTrace tailWord_641288 prefixEnd_641288 73175329324576042544617 := by
  unfold tailWord_641288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694847450365287057958259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15593129933820382743944345 11694847450365287057958259)
  ·
    refine ⟨17542271175547930586937389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694847450365287057958259 17542271175547930586937389)
    ·
      refine ⟨6578351690830473970101521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17542271175547930586937389 6578351690830473970101521)
      ·
        refine ⟨4933763768122855477576141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6578351690830473970101521 4933763768122855477576141)
        ·
          refine ⟨1850161413046070804091053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4933763768122855477576141 1850161413046070804091053)
          ·
            refine ⟨693810529892276551534145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1850161413046070804091053 693810529892276551534145)
            ·
              refine ⟨520357897419207413650609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693810529892276551534145 520357897419207413650609)
              ·
                refine ⟨390268423064405560237957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520357897419207413650609 390268423064405560237957)
                ·
                  refine ⟨73175329324576042544617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390268423064405560237957 73175329324576042544617)
                  ·
                    rfl

theorem cell22_641288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_641288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641288 prefixEnd_641288 := by exact prefixLift 641288
  have htrace : WordTrace (prefixWord ++ tailWord_641288) baseStart_641288 baseEnd_641288 := by
    simpa [prefixWord, tailWord_641288, baseEnd_641288] using wordTrace_append hprefix tailTrace_641288
  have hstable : (prefixWord ++ tailWord_641288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641288).length < 2 ^ (prefixWord ++ tailWord_641288).sum := by decide
  have hdescent : baseEnd_641288 < baseStart_641288 := by decide
  rcases family_descends (prefixWord ++ tailWord_641288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641361 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 5]
def baseStart_641361 : Nat := 118140960795 + 641361 * 2 ^ 59
def prefixEnd_641361 : Nat := 4983230072969 + 3 ^ 40 * 641361 * 2
def baseEnd_641361 : Nat := 73183659121860090186209

theorem tailTrace_641361 : CollatzResearch.WordTrace tailWord_641361 prefixEnd_641361 73183659121860090186209 := by
  unfold tailWord_641361
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392357429466107583323937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15594904952977405055549291 23392357429466107583323937)
  ·
    refine ⟨17544268072099580687492953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23392357429466107583323937 17544268072099580687492953)
    ·
      refine ⟨13158201054074685515619715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17544268072099580687492953 13158201054074685515619715)
      ·
        refine ⟨19737301581112028273429573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13158201054074685515619715 19737301581112028273429573)
        ·
          refine ⟨3700744046458505301268045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19737301581112028273429573 3700744046458505301268045)
          ·
            refine ⟨1387779017421939487975517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3700744046458505301268045 1387779017421939487975517)
            ·
              refine ⟨520417131533227307990819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1387779017421939487975517 520417131533227307990819)
              ·
                refine ⟨780625697299840961986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520417131533227307990819 780625697299840961986229)
                ·
                  refine ⟨73183659121860090186209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 780625697299840961986229 73183659121860090186209)
                  ·
                    rfl

theorem cell22_641361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_641361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641361 prefixEnd_641361 := by exact prefixLift 641361
  have htrace : WordTrace (prefixWord ++ tailWord_641361) baseStart_641361 baseEnd_641361 := by
    simpa [prefixWord, tailWord_641361, baseEnd_641361] using wordTrace_append hprefix tailTrace_641361
  have hstable : (prefixWord ++ tailWord_641361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641361).length < 2 ^ (prefixWord ++ tailWord_641361).sum := by decide
  have hdescent : baseEnd_641361 < baseStart_641361 := by decide
  rcases family_descends (prefixWord ++ tailWord_641361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641434 : List Nat := [3, 1, 1, 4, 1, 2, 2, 8]
def baseStart_641434 : Nat := 118140960795 + 641434 * 2 ^ 59
def prefixEnd_641434 : Nat := 4983230072969 + 3 ^ 40 * 641434 * 2
def baseEnd_641434 : Nat := 24397329639714712609267

theorem tailTrace_641434 : CollatzResearch.WordTrace tailWord_641434 prefixEnd_641434 24397329639714712609267 := by
  unfold tailWord_641434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5848754989550410262682839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15596679972134427367154237 5848754989550410262682839)
  ·
    refine ⟨8773132484325615394024259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5848754989550410262682839 8773132484325615394024259)
    ·
      refine ⟨13159698726488423091036389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8773132484325615394024259 13159698726488423091036389)
      ·
        refine ⟨2467443511216579329569323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13159698726488423091036389 2467443511216579329569323)
        ·
          refine ⟨3701165266824868994353985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467443511216579329569323 3701165266824868994353985)
          ·
            refine ⟨2775873950118651745765489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701165266824868994353985 2775873950118651745765489)
            ·
              refine ⟨2081905462588988809324117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2775873950118651745765489 2081905462588988809324117)
              ·
                refine ⟨24397329639714712609267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2081905462588988809324117 24397329639714712609267)
                ·
                  rfl

theorem cell22_641434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_641434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641434 prefixEnd_641434 := by exact prefixLift 641434
  have htrace : WordTrace (prefixWord ++ tailWord_641434) baseStart_641434 baseEnd_641434 := by
    simpa [prefixWord, tailWord_641434, baseEnd_641434] using wordTrace_append hprefix tailTrace_641434
  have hstable : (prefixWord ++ tailWord_641434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641434).length < 2 ^ (prefixWord ++ tailWord_641434).sum := by decide
  have hdescent : baseEnd_641434 < baseStart_641434 := by decide
  rcases family_descends (prefixWord ++ tailWord_641434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641438 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_641438 : Nat := 118140960795 + 641438 * 2 ^ 59
def prefixEnd_641438 : Nat := 4983230072969 + 3 ^ 40 * 641438 * 2
def baseEnd_641438 : Nat := 219577336039177736383391

theorem tailTrace_641438 : CollatzResearch.WordTrace tailWord_641438 prefixEnd_641438 219577336039177736383391 := by
  unfold tailWord_641438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924395731273393716734621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15596777233458099822584645 2924395731273393716734621)
  ·
    refine ⟨1096648399227522643775483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2924395731273393716734621 1096648399227522643775483)
    ·
      refine ⟨1644972598841283965663225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096648399227522643775483 1644972598841283965663225)
      ·
        refine ⟨1233729449130962974247419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1644972598841283965663225 1233729449130962974247419)
        ·
          refine ⟨1850594173696444461371129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233729449130962974247419 1850594173696444461371129)
          ·
            refine ⟨1387945630272333346028347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850594173696444461371129 1387945630272333346028347)
            ·
              refine ⟨2081918445408500019042521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387945630272333346028347 2081918445408500019042521)
              ·
                refine ⟨1561438834056375014281891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081918445408500019042521 1561438834056375014281891)
                ·
                  refine ⟨2342158251084562521422837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561438834056375014281891 2342158251084562521422837)
                  ·
                    refine ⟨219577336039177736383391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2342158251084562521422837 219577336039177736383391)
                    ·
                      rfl

theorem cell22_641438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_641438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641438 prefixEnd_641438 := by exact prefixLift 641438
  have htrace : WordTrace (prefixWord ++ tailWord_641438) baseStart_641438 baseEnd_641438 := by
    simpa [prefixWord, tailWord_641438, baseEnd_641438] using wordTrace_append hprefix tailTrace_641438
  have hstable : (prefixWord ++ tailWord_641438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641438).length < 2 ^ (prefixWord ++ tailWord_641438).sum := by decide
  have hdescent : baseEnd_641438 < baseStart_641438 := by decide
  rcases family_descends (prefixWord ++ tailWord_641438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641571 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_641571 : Nat := 118140960795 + 641571 * 2 ^ 59
def prefixEnd_641571 : Nat := 4983230072969 + 3 ^ 40 * 641571 * 2
def baseEnd_641571 : Nat := 219622864657209722807983

theorem tailTrace_641571 : CollatzResearch.WordTrace tailWord_641571 prefixEnd_641571 219622864657209722807983 := by
  unfold tailWord_641571
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400016758705313448468567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15600011172470208965645711 23400016758705313448468567)
  ·
    refine ⟨35100025138057970172702851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23400016758705313448468567 35100025138057970172702851)
    ·
      refine ⟨52650037707086955259054277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35100025138057970172702851 52650037707086955259054277)
      ·
        refine ⟨9871882070078804111072677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52650037707086955259054277 9871882070078804111072677)
        ·
          refine ⟨1850977888139775770826127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9871882070078804111072677 1850977888139775770826127)
          ·
            refine ⟨2776466832209663656239191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850977888139775770826127 2776466832209663656239191)
            ·
              refine ⟨4164700248314495484358787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776466832209663656239191 4164700248314495484358787)
              ·
                refine ⟨6247050372471743226538181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164700248314495484358787 6247050372471743226538181)
                ·
                  refine ⟨1171321944838451854975909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6247050372471743226538181 1171321944838451854975909)
                  ·
                    refine ⟨219622864657209722807983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171321944838451854975909 219622864657209722807983)
                    ·
                      rfl

theorem cell22_641571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_641571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641571 prefixEnd_641571 := by exact prefixLift 641571
  have htrace : WordTrace (prefixWord ++ tailWord_641571) baseStart_641571 baseEnd_641571 := by
    simpa [prefixWord, tailWord_641571, baseEnd_641571] using wordTrace_append hprefix tailTrace_641571
  have hstable : (prefixWord ++ tailWord_641571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641571).length < 2 ^ (prefixWord ++ tailWord_641571).sum := by decide
  have hdescent : baseEnd_641571 < baseStart_641571 := by decide
  rcases family_descends (prefixWord ++ tailWord_641571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641581 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 5]
def baseStart_641581 : Nat := 118140960795 + 641581 * 2 ^ 59
def prefixEnd_641581 : Nat := 4983230072969 + 3 ^ 40 * 641581 * 2
def baseEnd_641581 : Nat := 73208762620524343352651

theorem tailTrace_641581 : CollatzResearch.WordTrace tailWord_641581 prefixEnd_641581 73208762620524343352651 := by
  unfold tailWord_641581
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400381488669085156332597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15600254325779390104221731 23400381488669085156332597)
  ·
    refine ⟨2193785764562726733406181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23400381488669085156332597 2193785764562726733406181)
    ·
      refine ⟨411334830855511262513659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2193785764562726733406181 411334830855511262513659)
      ·
        refine ⟨617002246283266893770489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411334830855511262513659 617002246283266893770489)
        ·
          refine ⟨462751684712450170327867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617002246283266893770489 462751684712450170327867)
          ·
            refine ⟨694127527068675255491801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462751684712450170327867 694127527068675255491801)
            ·
              refine ⟨520595645301506441618851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694127527068675255491801 520595645301506441618851)
              ·
                refine ⟨780893467952259662428277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520595645301506441618851 780893467952259662428277)
                ·
                  refine ⟨73208762620524343352651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 780893467952259662428277 73208762620524343352651)
                  ·
                    rfl

theorem cell22_641581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_641581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641581 prefixEnd_641581 := by exact prefixLift 641581
  have htrace : WordTrace (prefixWord ++ tailWord_641581) baseStart_641581 baseEnd_641581 := by
    simpa [prefixWord, tailWord_641581, baseEnd_641581] using wordTrace_append hprefix tailTrace_641581
  have hstable : (prefixWord ++ tailWord_641581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641581).length < 2 ^ (prefixWord ++ tailWord_641581).sum := by decide
  have hdescent : baseEnd_641581 < baseStart_641581 := by decide
  rcases family_descends (prefixWord ++ tailWord_641581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641635 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 1, 3]
def baseStart_641635 : Nat := 118140960795 + 641635 * 2 ^ 59
def prefixEnd_641635 : Nat := 4983230072969 + 3 ^ 40 * 641635 * 2
def baseEnd_641635 : Nat := 219644773165134889207787

theorem tailTrace_641635 : CollatzResearch.WordTrace tailWord_641635 prefixEnd_641635 219644773165134889207787 := by
  unfold tailWord_641635
  simp only [CollatzResearch.WordTrace]
  refine ⟨23402351030473452378798359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15601567353648968252532239 23402351030473452378798359)
  ·
    refine ⟨35103526545710178568197539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23402351030473452378798359 35103526545710178568197539)
    ·
      refine ⟨52655289818565267852296309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35103526545710178568197539 52655289818565267852296309)
      ·
        refine ⟨4936433420490493861152779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52655289818565267852296309 4936433420490493861152779)
        ·
          refine ⟨7404650130735740791729169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4936433420490493861152779 7404650130735740791729169)
          ·
            refine ⟨5553487598051805593796877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7404650130735740791729169 5553487598051805593796877)
            ·
              refine ⟨2082557849269427097673829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5553487598051805593796877 2082557849269427097673829)
              ·
                refine ⟨390479596738017580813843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2082557849269427097673829 390479596738017580813843)
                ·
                  refine ⟨585719395107026371220765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390479596738017580813843 585719395107026371220765)
                  ·
                    refine ⟨219644773165134889207787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 585719395107026371220765 219644773165134889207787)
                    ·
                      rfl

theorem cell22_641635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 3].length) (baseStart_641635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641635 prefixEnd_641635 := by exact prefixLift 641635
  have htrace : WordTrace (prefixWord ++ tailWord_641635) baseStart_641635 baseEnd_641635 := by
    simpa [prefixWord, tailWord_641635, baseEnd_641635] using wordTrace_append hprefix tailTrace_641635
  have hstable : (prefixWord ++ tailWord_641635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641635).length < 2 ^ (prefixWord ++ tailWord_641635).sum := by decide
  have hdescent : baseEnd_641635 < baseStart_641635 := by decide
  rcases family_descends (prefixWord ++ tailWord_641635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641710 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_641710 : Nat := 118140960795 + 641710 * 2 ^ 59
def prefixEnd_641710 : Nat := 4983230072969 + 3 ^ 40 * 641710 * 2
def baseEnd_641710 : Nat := 73223482399286564527519

theorem tailTrace_641710 : CollatzResearch.WordTrace tailWord_641710 prefixEnd_641710 73223482399286564527519 := by
  unfold tailWord_641710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925635813150217523472323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15603391003467826791852389 2925635813150217523472323)
  ·
    refine ⟨4388453719725326285208485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2925635813150217523472323 4388453719725326285208485)
    ·
      refine ⟨822835072448498678476591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4388453719725326285208485 822835072448498678476591)
      ·
        refine ⟨1234252608672748017714887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822835072448498678476591 1234252608672748017714887)
        ·
          refine ⟨1851378913009122026572331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234252608672748017714887 1851378913009122026572331)
          ·
            refine ⟨2777068369513683039858497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851378913009122026572331 2777068369513683039858497)
            ·
              refine ⟨2082801277135262279893873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777068369513683039858497 2082801277135262279893873)
              ·
                refine ⟨1562100957851446709920405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082801277135262279893873 1562100957851446709920405)
                ·
                  refine ⟨73223482399286564527519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1562100957851446709920405 73223482399286564527519)
                  ·
                    rfl

theorem cell22_641710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_641710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641710 prefixEnd_641710 := by exact prefixLift 641710
  have htrace : WordTrace (prefixWord ++ tailWord_641710) baseStart_641710 baseEnd_641710 := by
    simpa [prefixWord, tailWord_641710, baseEnd_641710] using wordTrace_append hprefix tailTrace_641710
  have hstable : (prefixWord ++ tailWord_641710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641710).length < 2 ^ (prefixWord ++ tailWord_641710).sum := by decide
  have hdescent : baseEnd_641710 < baseStart_641710 := by decide
  rcases family_descends (prefixWord ++ tailWord_641710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641738 : List Nat := [3, 1, 2, 1, 4, 3, 8]
def baseStart_641738 : Nat := 118140960795 + 641738 * 2 ^ 59
def prefixEnd_641738 : Nat := 4983230072969 + 3 ^ 40 * 641738 * 2
def baseEnd_641738 : Nat := 8136297487780627921573

theorem tailTrace_641738 : CollatzResearch.WordTrace tailWord_641738 prefixEnd_641738 8136297487780627921573 := by
  unfold tailWord_641738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851526937275075242449467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15604071832733533979865245 5851526937275075242449467)
  ·
    refine ⟨8777290405912612863674201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5851526937275075242449467 8777290405912612863674201)
    ·
      refine ⟨6582967804434459647755651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8777290405912612863674201 6582967804434459647755651)
      ·
        refine ⟨9874451706651689471633477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582967804434459647755651 9874451706651689471633477)
        ·
          refine ⟨1851459694997191775931277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9874451706651689471633477 1851459694997191775931277)
          ·
            refine ⟨694297385623946915974229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1851459694997191775931277 694297385623946915974229)
            ·
              refine ⟨8136297487780627921573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 694297385623946915974229 8136297487780627921573)
              ·
                rfl

theorem cell22_641738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 8].length) (baseStart_641738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641738 prefixEnd_641738 := by exact prefixLift 641738
  have htrace : WordTrace (prefixWord ++ tailWord_641738) baseStart_641738 baseEnd_641738 := by
    simpa [prefixWord, tailWord_641738, baseEnd_641738] using wordTrace_append hprefix tailTrace_641738
  have hstable : (prefixWord ++ tailWord_641738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641738).length < 2 ^ (prefixWord ++ tailWord_641738).sum := by decide
  have hdescent : baseEnd_641738 < baseStart_641738 := by decide
  rcases family_descends (prefixWord ++ tailWord_641738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641740 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_641740 : Nat := 118140960795 + 641740 * 2 ^ 59
def prefixEnd_641740 : Nat := 4983230072969 + 3 ^ 40 * 641740 * 2
def baseEnd_641740 : Nat := 219680716810949615332465

theorem tailTrace_641740 : CollatzResearch.WordTrace tailWord_641740 prefixEnd_641740 219680716810949615332465 := by
  unfold tailWord_641740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703090347546527655685337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15604120463395370207580449 11703090347546527655685337)
  ·
    refine ⟨8777317760659895741764003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11703090347546527655685337 8777317760659895741764003)
    ·
      refine ⟨13165976640989843612646005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777317760659895741764003 13165976640989843612646005)
      ·
        refine ⟨1234310310092797838685563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13165976640989843612646005 1234310310092797838685563)
        ·
          refine ⟨1851465465139196758028345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234310310092797838685563 1851465465139196758028345)
          ·
            refine ⟨1388599098854397568521259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851465465139196758028345 1388599098854397568521259)
            ·
              refine ⟨2082898648281596352781889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388599098854397568521259 2082898648281596352781889)
              ·
                refine ⟨1562173986211197264586417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082898648281596352781889 1562173986211197264586417)
                ·
                  refine ⟨1171630489658397948439813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562173986211197264586417 1171630489658397948439813)
                  ·
                    refine ⟨219680716810949615332465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171630489658397948439813 219680716810949615332465)
                    ·
                      rfl

theorem cell22_641740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_641740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641740 prefixEnd_641740 := by exact prefixLift 641740
  have htrace : WordTrace (prefixWord ++ tailWord_641740) baseStart_641740 baseEnd_641740 := by
    simpa [prefixWord, tailWord_641740, baseEnd_641740] using wordTrace_append hprefix tailTrace_641740
  have hstable : (prefixWord ++ tailWord_641740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641740).length < 2 ^ (prefixWord ++ tailWord_641740).sum := by decide
  have hdescent : baseEnd_641740 < baseStart_641740 := by decide
  rcases family_descends (prefixWord ++ tailWord_641740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641800 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_641800 : Nat := 118140960795 + 641800 * 2 ^ 59
def prefixEnd_641800 : Nat := 4983230072969 + 3 ^ 40 * 641800 * 2
def baseEnd_641800 : Nat := 73233752012376486277427

theorem tailTrace_641800 : CollatzResearch.WordTrace tailWord_641800 prefixEnd_641800 73233752012376486277427 := by
  unfold tailWord_641800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704184537437842779277427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15605579383250457039036569 11704184537437842779277427)
  ·
    refine ⟨17556276806156764168916141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704184537437842779277427 17556276806156764168916141)
    ·
      refine ⟨6583603802308786563343553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17556276806156764168916141 6583603802308786563343553)
      ·
        refine ⟨4937702851731589922507665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6583603802308786563343553 4937702851731589922507665)
        ·
          refine ⟨3703277138798692441880749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937702851731589922507665 3703277138798692441880749)
          ·
            refine ⟨1388728927049509665705281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3703277138798692441880749 1388728927049509665705281)
            ·
              refine ⟨1041546695287132249278961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388728927049509665705281 1041546695287132249278961)
              ·
                refine ⟨781160021465349186959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041546695287132249278961 781160021465349186959221)
                ·
                  refine ⟨73233752012376486277427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 781160021465349186959221 73233752012376486277427)
                  ·
                    rfl

theorem cell22_641800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_641800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641800 prefixEnd_641800 := by exact prefixLift 641800
  have htrace : WordTrace (prefixWord ++ tailWord_641800) baseStart_641800 baseEnd_641800 := by
    simpa [prefixWord, tailWord_641800, baseEnd_641800] using wordTrace_append hprefix tailTrace_641800
  have hstable : (prefixWord ++ tailWord_641800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641800).length < 2 ^ (prefixWord ++ tailWord_641800).sum := by decide
  have hdescent : baseEnd_641800 < baseStart_641800 := by decide
  rcases family_descends (prefixWord ++ tailWord_641800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641813 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_641813 : Nat := 118140960795 + 641813 * 2 ^ 59
def prefixEnd_641813 : Nat := 4983230072969 + 3 ^ 40 * 641813 * 2
def baseEnd_641813 : Nat := 219705706202801758257241

theorem tailTrace_641813 : CollatzResearch.WordTrace tailWord_641813 prefixEnd_641813 219705706202801758257241 := by
  unfold tailWord_641813
  simp only [CollatzResearch.WordTrace]
  refine ⟨23408843223828588778778093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15605895482552392519185395 23408843223828588778778093)
  ·
    refine ⟨8778316208935720792041785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23408843223828588778778093 8778316208935720792041785)
    ·
      refine ⟨6583737156701790594031339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8778316208935720792041785 6583737156701790594031339)
      ·
        refine ⟨9875605735052685891047009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583737156701790594031339 9875605735052685891047009)
        ·
          refine ⟨7406704301289514418285257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9875605735052685891047009 7406704301289514418285257)
          ·
            refine ⟨5555028225967135813713943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406704301289514418285257 5555028225967135813713943)
            ·
              refine ⟨8332542338950703720570915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555028225967135813713943 8332542338950703720570915)
              ·
                refine ⟨12498813508426055580856373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332542338950703720570915 12498813508426055580856373)
                ·
                  refine ⟨1171763766414942710705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12498813508426055580856373 1171763766414942710705285)
                  ·
                    refine ⟨219705706202801758257241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171763766414942710705285 219705706202801758257241)
                    ·
                      rfl

theorem cell22_641813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_641813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641813 prefixEnd_641813 := by exact prefixLift 641813
  have htrace : WordTrace (prefixWord ++ tailWord_641813) baseStart_641813 baseEnd_641813 := by
    simpa [prefixWord, tailWord_641813, baseEnd_641813] using wordTrace_append hprefix tailTrace_641813
  have hstable : (prefixWord ++ tailWord_641813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641813).length < 2 ^ (prefixWord ++ tailWord_641813).sum := by decide
  have hdescent : baseEnd_641813 < baseStart_641813 := by decide
  rcases family_descends (prefixWord ++ tailWord_641813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641815 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_641815 : Nat := 118140960795 + 641815 * 2 ^ 59
def prefixEnd_641815 : Nat := 4983230072969 + 3 ^ 40 * 641815 * 2
def baseEnd_641815 : Nat := 219706390843674419707235

theorem tailTrace_641815 : CollatzResearch.WordTrace tailWord_641815 prefixEnd_641815 219706390843674419707235 := by
  unfold tailWord_641815
  simp only [CollatzResearch.WordTrace]
  refine ⟨23408916169821343120350899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15605944113214228746900599 23408916169821343120350899)
  ·
    refine ⟨35113374254732014680526349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23408916169821343120350899 35113374254732014680526349)
    ·
      refine ⟨13167515345524505505197381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35113374254732014680526349 13167515345524505505197381)
      ·
        refine ⟨2468909127285844782224509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13167515345524505505197381 2468909127285844782224509)
        ·
          refine ⟨925840922732191793334191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2468909127285844782224509 925840922732191793334191)
          ·
            refine ⟨1388761384098287690001287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925840922732191793334191 1388761384098287690001287)
            ·
              refine ⟨2083142076147431535001931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388761384098287690001287 2083142076147431535001931)
              ·
                refine ⟨3124713114221147302502897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083142076147431535001931 3124713114221147302502897)
                ·
                  refine ⟨2343534835665860476877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124713114221147302502897 2343534835665860476877173)
                  ·
                    refine ⟨219706390843674419707235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343534835665860476877173 219706390843674419707235)
                    ·
                      rfl

theorem cell22_641815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_641815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641815 prefixEnd_641815 := by exact prefixLift 641815
  have htrace : WordTrace (prefixWord ++ tailWord_641815) baseStart_641815 baseEnd_641815 := by
    simpa [prefixWord, tailWord_641815, baseEnd_641815] using wordTrace_append hprefix tailTrace_641815
  have hstable : (prefixWord ++ tailWord_641815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641815).length < 2 ^ (prefixWord ++ tailWord_641815).sum := by decide
  have hdescent : baseEnd_641815 < baseStart_641815 := by decide
  rcases family_descends (prefixWord ++ tailWord_641815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641888 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_641888 : Nat := 118140960795 + 641888 * 2 ^ 59
def prefixEnd_641888 : Nat := 4983230072969 + 3 ^ 40 * 641888 * 2
def baseEnd_641888 : Nat := 219731380235526562632011

theorem tailTrace_641888 : CollatzResearch.WordTrace tailWord_641888 prefixEnd_641888 219731380235526562632011 := by
  unfold tailWord_641888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705789349278438293879159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15607719132371251058505545 11705789349278438293879159)
  ·
    refine ⟨17558684023917657440818739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11705789349278438293879159 17558684023917657440818739)
    ·
      refine ⟨26338026035876486161228109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17558684023917657440818739 26338026035876486161228109)
      ·
        refine ⟨9876759763453682310460541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26338026035876486161228109 9876759763453682310460541)
        ·
          refine ⟨3703784911295130866422703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9876759763453682310460541 3703784911295130866422703)
          ·
            refine ⟨5555677366942696299634055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703784911295130866422703 5555677366942696299634055)
            ·
              refine ⟨8333516050414044449451083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555677366942696299634055 8333516050414044449451083)
              ·
                refine ⟨12500274075621066674176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8333516050414044449451083 12500274075621066674176625)
                ·
                  refine ⟨9375205556715800005632469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500274075621066674176625 9375205556715800005632469)
                  ·
                    refine ⟨219731380235526562632011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9375205556715800005632469 219731380235526562632011)
                    ·
                      rfl

theorem cell22_641888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_641888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641888 prefixEnd_641888 := by exact prefixLift 641888
  have htrace : WordTrace (prefixWord ++ tailWord_641888) baseStart_641888 baseEnd_641888 := by
    simpa [prefixWord, tailWord_641888, baseEnd_641888] using wordTrace_append hprefix tailTrace_641888
  have hstable : (prefixWord ++ tailWord_641888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641888).length < 2 ^ (prefixWord ++ tailWord_641888).sum := by decide
  have hdescent : baseEnd_641888 < baseStart_641888 := by decide
  rcases family_descends (prefixWord ++ tailWord_641888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641963 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 8]
def baseStart_641963 : Nat := 118140960795 + 641963 * 2 ^ 59
def prefixEnd_641963 : Nat := 4983230072969 + 3 ^ 40 * 641963 * 2
def baseEnd_641963 : Nat := 73252351422750455668927

theorem tailTrace_641963 : CollatzResearch.WordTrace tailWord_641963 prefixEnd_641963 73252351422750455668927 := by
  unfold tailWord_641963
  simp only [CollatzResearch.WordTrace]
  refine ⟨23414314173285164396738543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15609542782190109597825695 23414314173285164396738543)
  ·
    refine ⟨35121471259927746595107815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23414314173285164396738543 35121471259927746595107815)
    ·
      refine ⟨52682206889891619892661723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35121471259927746595107815 52682206889891619892661723)
      ·
        refine ⟨79023310334837429838992585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52682206889891619892661723 79023310334837429838992585)
        ·
          refine ⟨59267482751128072379244439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79023310334837429838992585 59267482751128072379244439)
          ·
            refine ⟨88901224126692108568866659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59267482751128072379244439 88901224126692108568866659)
            ·
              refine ⟨133351836190038162853299989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88901224126692108568866659 133351836190038162853299989)
              ·
                refine ⟨6250867321408038883748437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 133351836190038162853299989 6250867321408038883748437)
                ·
                  refine ⟨73252351422750455668927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6250867321408038883748437 73252351422750455668927)
                  ·
                    rfl

theorem cell22_641963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_641963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641963 prefixEnd_641963 := by exact prefixLift 641963
  have htrace : WordTrace (prefixWord ++ tailWord_641963) baseStart_641963 baseEnd_641963 := by
    simpa [prefixWord, tailWord_641963, baseEnd_641963] using wordTrace_append hprefix tailTrace_641963
  have hstable : (prefixWord ++ tailWord_641963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641963).length < 2 ^ (prefixWord ++ tailWord_641963).sum := by decide
  have hdescent : baseEnd_641963 < baseStart_641963 := by decide
  rcases family_descends (prefixWord ++ tailWord_641963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641990 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_641990 : Nat := 118140960795 + 641990 * 2 ^ 59
def prefixEnd_641990 : Nat := 4983230072969 + 3 ^ 40 * 641990 * 2
def baseEnd_641990 : Nat := 219766296920032296581699

theorem tailTrace_641990 : CollatzResearch.WordTrace tailWord_641990 prefixEnd_641990 219766296920032296581699 := by
  unfold tailWord_641990
  simp only [CollatzResearch.WordTrace]
  refine ⟨731728092005854625249107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15610199296124898671980949 731728092005854625249107)
  ·
    refine ⟨1097592138008781937873661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 731728092005854625249107 1097592138008781937873661)
    ·
      refine ⟨411597051753293226702623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1097592138008781937873661 411597051753293226702623)
      ·
        refine ⟨617395577629939840053935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411597051753293226702623 617395577629939840053935)
        ·
          refine ⟨926093366444909760080903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617395577629939840053935 926093366444909760080903)
          ·
            refine ⟨1389140049667364640121355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926093366444909760080903 1389140049667364640121355)
            ·
              refine ⟨2083710074501046960182033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389140049667364640121355 2083710074501046960182033)
              ·
                refine ⟨1562782555875785220136525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083710074501046960182033 1562782555875785220136525)
                ·
                  refine ⟨586043458453419457551197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1562782555875785220136525 586043458453419457551197)
                  ·
                    refine ⟨219766296920032296581699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586043458453419457551197 219766296920032296581699)
                    ·
                      rfl

theorem cell22_641990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_641990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641990 prefixEnd_641990 := by exact prefixLift 641990
  have htrace : WordTrace (prefixWord ++ tailWord_641990) baseStart_641990 baseEnd_641990 := by
    simpa [prefixWord, tailWord_641990, baseEnd_641990] using wordTrace_append hprefix tailTrace_641990
  have hstable : (prefixWord ++ tailWord_641990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641990).length < 2 ^ (prefixWord ++ tailWord_641990).sum := by decide
  have hdescent : baseEnd_641990 < baseStart_641990 := by decide
  rcases family_descends (prefixWord ++ tailWord_641990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641995 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_641995 : Nat := 118140960795 + 641995 * 2 ^ 59
def prefixEnd_641995 : Nat := 4983230072969 + 3 ^ 40 * 641995 * 2
def baseEnd_641995 : Nat := 219768008522213950206683

theorem tailTrace_641995 : CollatzResearch.WordTrace tailWord_641995 prefixEnd_641995 219768008522213950206683 := by
  unfold tailWord_641995
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415481309169233861903439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15610320872779489241268959 23415481309169233861903439)
  ·
    refine ⟨35123221963753850792855159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23415481309169233861903439 35123221963753850792855159)
    ·
      refine ⟨52684832945630776189282739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35123221963753850792855159 52684832945630776189282739)
      ·
        refine ⟨79027249418446164283924109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52684832945630776189282739 79027249418446164283924109)
        ·
          refine ⟨29635218531917311606471541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79027249418446164283924109 29635218531917311606471541)
          ·
            refine ⟨2778301737367247963106707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29635218531917311606471541 2778301737367247963106707)
            ·
              refine ⟨4167452606050871944660061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778301737367247963106707 4167452606050871944660061)
              ·
                refine ⟨1562794727269076979247523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167452606050871944660061 1562794727269076979247523)
                ·
                  refine ⟨2344192090903615468871285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562794727269076979247523 2344192090903615468871285)
                  ·
                    refine ⟨219768008522213950206683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344192090903615468871285 219768008522213950206683)
                    ·
                      rfl

theorem cell22_641995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_641995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_641995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_641995 prefixEnd_641995 := by exact prefixLift 641995
  have htrace : WordTrace (prefixWord ++ tailWord_641995) baseStart_641995 baseEnd_641995 := by
    simpa [prefixWord, tailWord_641995, baseEnd_641995] using wordTrace_append hprefix tailTrace_641995
  have hstable : (prefixWord ++ tailWord_641995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641995).length < 2 ^ (prefixWord ++ tailWord_641995).sum := by decide
  have hdescent : baseEnd_641995 < baseStart_641995 := by decide
  rcases family_descends (prefixWord ++ tailWord_641995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642046 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_642046 : Nat := 118140960795 + 642046 * 2 ^ 59
def prefixEnd_642046 : Nat := 4983230072969 + 3 ^ 40 * 642046 * 2
def baseEnd_642046 : Nat := 219785466864466817181527

theorem tailTrace_642046 : CollatzResearch.WordTrace tailWord_642046 prefixEnd_642046 219785466864466817181527 := by
  unfold tailWord_642046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927167678998058696501249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15611560954656313048006661 2927167678998058696501249)
  ·
    refine ⟨2195375759248544022375937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927167678998058696501249 2195375759248544022375937)
    ·
      refine ⟨1646531819436408016781953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195375759248544022375937 1646531819436408016781953)
      ·
        refine ⟨1234898864577306012586465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646531819436408016781953 1234898864577306012586465)
        ·
          refine ⟨926174148432979509439849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234898864577306012586465 926174148432979509439849)
          ·
            refine ⟨694630611324734632079887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926174148432979509439849 694630611324734632079887)
            ·
              refine ⟨1041945916987101948119831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694630611324734632079887 1041945916987101948119831)
              ·
                refine ⟨1562918875480652922179747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041945916987101948119831 1562918875480652922179747)
                ·
                  refine ⟨2344378313220979383269621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562918875480652922179747 2344378313220979383269621)
                  ·
                    refine ⟨219785466864466817181527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344378313220979383269621 219785466864466817181527)
                    ·
                      rfl

theorem cell22_642046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_642046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642046 prefixEnd_642046 := by exact prefixLift 642046
  have htrace : WordTrace (prefixWord ++ tailWord_642046) baseStart_642046 baseEnd_642046 := by
    simpa [prefixWord, tailWord_642046, baseEnd_642046] using wordTrace_append hprefix tailTrace_642046
  have hstable : (prefixWord ++ tailWord_642046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642046).length < 2 ^ (prefixWord ++ tailWord_642046).sum := by decide
  have hdescent : baseEnd_642046 < baseStart_642046 := by decide
  rcases family_descends (prefixWord ++ tailWord_642046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642091 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 1, 3]
def baseStart_642091 : Nat := 118140960795 + 642091 * 2 ^ 59
def prefixEnd_642091 : Nat := 4983230072969 + 3 ^ 40 * 642091 * 2
def baseEnd_642091 : Nat := 219800871284101699806389

theorem tailTrace_642091 : CollatzResearch.WordTrace tailWord_642091 prefixEnd_642091 219800871284101699806389 := by
  unfold tailWord_642091
  simp only [CollatzResearch.WordTrace]
  refine ⟨23418982716821442257398127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15612655144547628171598751 23418982716821442257398127)
  ·
    refine ⟨35128474075232163386097191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23418982716821442257398127 35128474075232163386097191)
    ·
      refine ⟨52692711112848245079145787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35128474075232163386097191 52692711112848245079145787)
      ·
        refine ⟨79039066669272367618718681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52692711112848245079145787 79039066669272367618718681)
        ·
          refine ⟨59279300001954275714039011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79039066669272367618718681 59279300001954275714039011)
          ·
            refine ⟨88918950002931413571058517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59279300001954275714039011 88918950002931413571058517)
            ·
              refine ⟨521009472673426251392921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 88918950002931413571058517 521009472673426251392921)
              ·
                refine ⟨390757104505069688544691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521009472673426251392921 390757104505069688544691)
                ·
                  refine ⟨586135656757604532817037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390757104505069688544691 586135656757604532817037)
                  ·
                    refine ⟨219800871284101699806389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586135656757604532817037 219800871284101699806389)
                    ·
                      rfl

theorem cell22_642091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 3].length) (baseStart_642091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642091 prefixEnd_642091 := by exact prefixLift 642091
  have htrace : WordTrace (prefixWord ++ tailWord_642091) baseStart_642091 baseEnd_642091 := by
    simpa [prefixWord, tailWord_642091, baseEnd_642091] using wordTrace_append hprefix tailTrace_642091
  have hstable : (prefixWord ++ tailWord_642091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642091).length < 2 ^ (prefixWord ++ tailWord_642091).sum := by decide
  have hdescent : baseEnd_642091 < baseStart_642091 := by decide
  rcases family_descends (prefixWord ++ tailWord_642091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642104 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_642104 : Nat := 118140960795 + 642104 * 2 ^ 59
def prefixEnd_642104 : Nat := 4983230072969 + 3 ^ 40 * 642104 * 2
def baseEnd_642104 : Nat := 73268440483257999743783

theorem tailTrace_642104 : CollatzResearch.WordTrace tailWord_642104 prefixEnd_642104 73268440483257999743783 := by
  unfold tailWord_642104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709728432887172738810683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15612971243849563651747577 11709728432887172738810683)
  ·
    refine ⟨17564592649330759108216025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11709728432887172738810683 17564592649330759108216025)
    ·
      refine ⟨13173444486998069331162019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17564592649330759108216025 13173444486998069331162019)
      ·
        refine ⟨19760166730497103996743029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13173444486998069331162019 19760166730497103996743029)
        ·
          refine ⟨1852515630984103499694659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19760166730497103996743029 1852515630984103499694659)
          ·
            refine ⟨2778773446476155249541989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852515630984103499694659 2778773446476155249541989)
            ·
              refine ⟨521020021214279109289123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2778773446476155249541989 521020021214279109289123)
              ·
                refine ⟨781530031821418663933685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521020021214279109289123 781530031821418663933685)
                ·
                  refine ⟨73268440483257999743783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 781530031821418663933685 73268440483257999743783)
                  ·
                    rfl

theorem cell22_642104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_642104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642104 prefixEnd_642104 := by exact prefixLift 642104
  have htrace : WordTrace (prefixWord ++ tailWord_642104) baseStart_642104 baseEnd_642104 := by
    simpa [prefixWord, tailWord_642104, baseEnd_642104] using wordTrace_append hprefix tailTrace_642104
  have hstable : (prefixWord ++ tailWord_642104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642104).length < 2 ^ (prefixWord ++ tailWord_642104).sum := by decide
  have hdescent : baseEnd_642104 < baseStart_642104 := by decide
  rcases family_descends (prefixWord ++ tailWord_642104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642115 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 8]
def baseStart_642115 : Nat := 118140960795 + 642115 * 2 ^ 59
def prefixEnd_642115 : Nat := 4983230072969 + 3 ^ 40 * 642115 * 2
def baseEnd_642115 : Nat := 73269695658191212402105

theorem tailTrace_642115 : CollatzResearch.WordTrace tailWord_642115 prefixEnd_642115 73269695658191212402105 := by
  unfold tailWord_642115
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419858068734494356271799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15613238712489662904181199 23419858068734494356271799)
  ·
    refine ⟨35129787103101741534407699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23419858068734494356271799 35129787103101741534407699)
    ·
      refine ⟨52694680654652612301611549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35129787103101741534407699 52694680654652612301611549)
      ·
        refine ⟨19760505245494729613104331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52694680654652612301611549 19760505245494729613104331)
        ·
          refine ⟨29640757868242094419656497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19760505245494729613104331 29640757868242094419656497)
          ·
            refine ⟨22230568401181570814742373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29640757868242094419656497 22230568401181570814742373)
            ·
              refine ⟨4168231575221544527764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22230568401181570814742373 4168231575221544527764195)
              ·
                refine ⟨6252347362832316791646293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168231575221544527764195 6252347362832316791646293)
                ·
                  refine ⟨73269695658191212402105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6252347362832316791646293 73269695658191212402105)
                  ·
                    rfl

theorem cell22_642115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_642115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642115 prefixEnd_642115 := by exact prefixLift 642115
  have htrace : WordTrace (prefixWord ++ tailWord_642115) baseStart_642115 baseEnd_642115 := by
    simpa [prefixWord, tailWord_642115, baseEnd_642115] using wordTrace_append hprefix tailTrace_642115
  have hstable : (prefixWord ++ tailWord_642115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642115).length < 2 ^ (prefixWord ++ tailWord_642115).sum := by decide
  have hdescent : baseEnd_642115 < baseStart_642115 := by decide
  rcases family_descends (prefixWord ++ tailWord_642115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642142 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_642142 : Nat := 118140960795 + 642142 * 2 ^ 59
def prefixEnd_642142 : Nat := 4983230072969 + 3 ^ 40 * 642142 * 2
def baseEnd_642142 : Nat := 219818329626354566781233

theorem tailTrace_642142 : CollatzResearch.WordTrace tailWord_642142 prefixEnd_642142 219818329626354566781233 := by
  unfold tailWord_642142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927605354954584745938085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15613895226424451978336453 2927605354954584745938085)
  ·
    refine ⟨548926004053984639863391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2927605354954584745938085 548926004053984639863391)
    ·
      refine ⟨823389006080976959795087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548926004053984639863391 823389006080976959795087)
      ·
        refine ⟨1235083509121465439692631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823389006080976959795087 1235083509121465439692631)
        ·
          refine ⟨1852625263682198159538947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235083509121465439692631 1852625263682198159538947)
          ·
            refine ⟨2778937895523297239308421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852625263682198159538947 2778937895523297239308421)
            ·
              refine ⟨521050855410618232370329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2778937895523297239308421 521050855410618232370329)
              ·
                refine ⟨390788141557963674277747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521050855410618232370329 390788141557963674277747)
                ·
                  refine ⟨586182212336945511416621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390788141557963674277747 586182212336945511416621)
                  ·
                    refine ⟨219818329626354566781233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586182212336945511416621 219818329626354566781233)
                    ·
                      rfl

theorem cell22_642142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_642142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642142 prefixEnd_642142 := by exact prefixLift 642142
  have htrace : WordTrace (prefixWord ++ tailWord_642142) baseStart_642142 baseEnd_642142 := by
    simpa [prefixWord, tailWord_642142, baseEnd_642142] using wordTrace_append hprefix tailTrace_642142
  have hstable : (prefixWord ++ tailWord_642142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642142).length < 2 ^ (prefixWord ++ tailWord_642142).sum := by decide
  have hdescent : baseEnd_642142 < baseStart_642142 := by decide
  rcases family_descends (prefixWord ++ tailWord_642142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642149 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 4]
def baseStart_642149 : Nat := 118140960795 + 642149 * 2 ^ 59
def prefixEnd_642149 : Nat := 4983230072969 + 3 ^ 40 * 642149 * 2
def baseEnd_642149 : Nat := 73273575289802960618737

theorem tailTrace_642149 : CollatzResearch.WordTrace tailWord_642149 prefixEnd_642149 73273575289802960618737 := by
  unfold tailWord_642149
  simp only [CollatzResearch.WordTrace]
  refine ⟨23421098150611318163009501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15614065433740878775339667 23421098150611318163009501)
  ·
    refine ⟨8782911806479244311128563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23421098150611318163009501 8782911806479244311128563)
    ·
      refine ⟨13174367709718866466692845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8782911806479244311128563 13174367709718866466692845)
      ·
        refine ⟨4940387891144574925009817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13174367709718866466692845 4940387891144574925009817)
        ·
          refine ⟨3705290918358431193757363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940387891144574925009817 3705290918358431193757363)
          ·
            refine ⟨5557936377537646790636045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705290918358431193757363 5557936377537646790636045)
            ·
              refine ⟨2084226141576617546488517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5557936377537646790636045 2084226141576617546488517)
              ·
                refine ⟨390792401545615789966597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2084226141576617546488517 390792401545615789966597)
                ·
                  refine ⟨73273575289802960618737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390792401545615789966597 73273575289802960618737)
                  ·
                    rfl

theorem cell22_642149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_642149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642149 prefixEnd_642149 := by exact prefixLift 642149
  have htrace : WordTrace (prefixWord ++ tailWord_642149) baseStart_642149 baseEnd_642149 := by
    simpa [prefixWord, tailWord_642149, baseEnd_642149] using wordTrace_append hprefix tailTrace_642149
  have hstable : (prefixWord ++ tailWord_642149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642149).length < 2 ^ (prefixWord ++ tailWord_642149).sum := by decide
  have hdescent : baseEnd_642149 < baseStart_642149 := by decide
  rcases family_descends (prefixWord ++ tailWord_642149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642162 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_642162 : Nat := 118140960795 + 642162 * 2 ^ 59
def prefixEnd_642162 : Nat := 4983230072969 + 3 ^ 40 * 642162 * 2
def baseEnd_642162 : Nat := 219825176035081181281171

theorem tailTrace_642162 : CollatzResearch.WordTrace tailWord_642162 prefixEnd_642162 219825176035081181281171 := by
  unfold tailWord_642162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855393074891055345808185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15614381533042814255488493 5855393074891055345808185)
  ·
    refine ⟨4391544806168291509356139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5855393074891055345808185 4391544806168291509356139)
    ·
      refine ⟨6587317209252437264034209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391544806168291509356139 6587317209252437264034209)
      ·
        refine ⟨4940487906939327948025657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587317209252437264034209 4940487906939327948025657)
        ·
          refine ⟨3705365930204495961019243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940487906939327948025657 3705365930204495961019243)
          ·
            refine ⟨5558048895306743941528865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705365930204495961019243 5558048895306743941528865)
            ·
              refine ⟨4168536671480057956146649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558048895306743941528865 4168536671480057956146649)
              ·
                refine ⟨3126402503610043467109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168536671480057956146649 3126402503610043467109987)
                ·
                  refine ⟨4689603755415065200664981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126402503610043467109987 4689603755415065200664981)
                  ·
                    refine ⟨219825176035081181281171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4689603755415065200664981 219825176035081181281171)
                    ·
                      rfl

theorem cell22_642162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_642162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642162 prefixEnd_642162 := by exact prefixLift 642162
  have htrace : WordTrace (prefixWord ++ tailWord_642162) baseStart_642162 baseEnd_642162 := by
    simpa [prefixWord, tailWord_642162, baseEnd_642162] using wordTrace_append hprefix tailTrace_642162
  have hstable : (prefixWord ++ tailWord_642162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642162).length < 2 ^ (prefixWord ++ tailWord_642162).sum := by decide
  have hdescent : baseEnd_642162 < baseStart_642162 := by decide
  rcases family_descends (prefixWord ++ tailWord_642162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642237 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_642237 : Nat := 118140960795 + 642237 * 2 ^ 59
def prefixEnd_642237 : Nat := 4983230072969 + 3 ^ 40 * 642237 * 2
def baseEnd_642237 : Nat := 219850850067805985655941

theorem tailTrace_642237 : CollatzResearch.WordTrace tailWord_642237 prefixEnd_642237 219850850067805985655941 := by
  unfold tailWord_642237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23424307774292509192212965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15616205182861672794808643 23424307774292509192212965)
  ·
    refine ⟨4392057707679845473539931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23424307774292509192212965 4392057707679845473539931)
    ·
      refine ⟨6588086561519768210309897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392057707679845473539931 6588086561519768210309897)
      ·
        refine ⟨4941064921139826157732423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6588086561519768210309897 4941064921139826157732423)
        ·
          refine ⟨7411597381709739236598635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941064921139826157732423 7411597381709739236598635)
          ·
            refine ⟨11117396072564608854897953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411597381709739236598635 11117396072564608854897953)
            ·
              refine ⟨8338047054423456641173465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11117396072564608854897953 8338047054423456641173465)
              ·
                refine ⟨6253535290817592480880099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8338047054423456641173465 6253535290817592480880099)
                ·
                  refine ⟨9380302936226388721320149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6253535290817592480880099 9380302936226388721320149)
                  ·
                    refine ⟨219850850067805985655941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9380302936226388721320149 219850850067805985655941)
                    ·
                      rfl

theorem cell22_642237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_642237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642237 prefixEnd_642237 := by exact prefixLift 642237
  have htrace : WordTrace (prefixWord ++ tailWord_642237) baseStart_642237 baseEnd_642237 := by
    simpa [prefixWord, tailWord_642237, baseEnd_642237] using wordTrace_append hprefix tailTrace_642237
  have hstable : (prefixWord ++ tailWord_642237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642237).length < 2 ^ (prefixWord ++ tailWord_642237).sum := by decide
  have hdescent : baseEnd_642237 < baseStart_642237 := by decide
  rcases family_descends (prefixWord ++ tailWord_642237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642260 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_642260 : Nat := 118140960795 + 642260 * 2 ^ 59
def prefixEnd_642260 : Nat := 4983230072969 + 3 ^ 40 * 642260 * 2
def baseEnd_642260 : Nat := 219858723437841592330871

theorem tailTrace_642260 : CollatzResearch.WordTrace tailWord_642260 prefixEnd_642260 219858723437841592330871 := by
  unfold tailWord_642260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712573326604592060150117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15616764435472789413533489 11712573326604592060150117)
  ·
    refine ⟨2196107498738361011278147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11712573326604592060150117 2196107498738361011278147)
    ·
      refine ⟨3294161248107541516917221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196107498738361011278147 3294161248107541516917221)
      ·
        refine ⟨617655234020164034421979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3294161248107541516917221 617655234020164034421979)
        ·
          refine ⟨926482851030246051632969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617655234020164034421979 926482851030246051632969)
          ·
            refine ⟨694862138272684538724727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926482851030246051632969 694862138272684538724727)
            ·
              refine ⟨1042293207409026808087091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694862138272684538724727 1042293207409026808087091)
              ·
                refine ⟨1563439811113540212130637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042293207409026808087091 1563439811113540212130637)
                ·
                  refine ⟨586289929167577579548989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1563439811113540212130637 586289929167577579548989)
                  ·
                    refine ⟨219858723437841592330871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586289929167577579548989 219858723437841592330871)
                    ·
                      rfl

theorem cell22_642260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_642260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642260 prefixEnd_642260 := by exact prefixLift 642260
  have htrace : WordTrace (prefixWord ++ tailWord_642260) baseStart_642260 baseEnd_642260 := by
    simpa [prefixWord, tailWord_642260, baseEnd_642260] using wordTrace_append hprefix tailTrace_642260
  have hstable : (prefixWord ++ tailWord_642260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642260).length < 2 ^ (prefixWord ++ tailWord_642260).sum := by decide
  have hdescent : baseEnd_642260 < baseStart_642260 := by decide
  rcases family_descends (prefixWord ++ tailWord_642260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642286 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_642286 : Nat := 118140960795 + 642286 * 2 ^ 59
def prefixEnd_642286 : Nat := 4983230072969 + 3 ^ 40 * 642286 * 2
def baseEnd_642286 : Nat := 219867623769186191180791

theorem tailTrace_642286 : CollatzResearch.WordTrace tailWord_642286 prefixEnd_642286 219867623769186191180791 := by
  unfold tailWord_642286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928261868889373820093339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15617396634076660373831141 2928261868889373820093339)
  ·
    refine ⟨4392392803334060730140009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928261868889373820093339 4392392803334060730140009)
    ·
      refine ⟨3294294602500545547605007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4392392803334060730140009 3294294602500545547605007)
      ·
        refine ⟨4941441903750818321407511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294294602500545547605007 4941441903750818321407511)
        ·
          refine ⟨7412162855626227482111267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941441903750818321407511 7412162855626227482111267)
          ·
            refine ⟨11118244283439341223166901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412162855626227482111267 11118244283439341223166901)
            ·
              refine ⟨1042335401572438239671897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11118244283439341223166901 1042335401572438239671897)
              ·
                refine ⟨781751551179328679753923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042335401572438239671897 781751551179328679753923)
                ·
                  refine ⟨1172627326768993019630885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781751551179328679753923 1172627326768993019630885)
                  ·
                    refine ⟨219867623769186191180791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1172627326768993019630885 219867623769186191180791)
                    ·
                      rfl

theorem cell22_642286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_642286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642286 prefixEnd_642286 := by exact prefixLift 642286
  have htrace : WordTrace (prefixWord ++ tailWord_642286) baseStart_642286 baseEnd_642286 := by
    simpa [prefixWord, tailWord_642286, baseEnd_642286] using wordTrace_append hprefix tailTrace_642286
  have hstable : (prefixWord ++ tailWord_642286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642286).length < 2 ^ (prefixWord ++ tailWord_642286).sum := by decide
  have hdescent : baseEnd_642286 < baseStart_642286 := by decide
  rcases family_descends (prefixWord ++ tailWord_642286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642312 : List Nat := [2, 1, 3, 2, 14]
def baseStart_642312 : Nat := 118140960795 + 642312 * 2 ^ 59
def prefixEnd_642312 : Nat := 4983230072969 + 3 ^ 40 * 642312 * 2
def baseEnd_642312 : Nat := 904841662965147284077

theorem tailTrace_642312 : CollatzResearch.WordTrace tailWord_642312 prefixEnd_642312 904841662965147284077 := by
  unfold tailWord_642312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713521624510398500596595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15618028832680531334128793 11713521624510398500596595)
  ·
    refine ⟨17570282436765597750894893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11713521624510398500596595 17570282436765597750894893)
    ·
      refine ⟨6588855913787099156585585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17570282436765597750894893 6588855913787099156585585)
      ·
        refine ⟨4941641935340324367439189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6588855913787099156585585 4941641935340324367439189)
        ·
          refine ⟨904841662965147284077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 4941641935340324367439189 904841662965147284077)
          ·
            rfl

theorem cell22_642312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 14].length) (baseStart_642312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642312 prefixEnd_642312 := by exact prefixLift 642312
  have htrace : WordTrace (prefixWord ++ tailWord_642312) baseStart_642312 baseEnd_642312 := by
    simpa [prefixWord, tailWord_642312, baseEnd_642312] using wordTrace_append hprefix tailTrace_642312
  have hstable : (prefixWord ++ tailWord_642312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642312).length < 2 ^ (prefixWord ++ tailWord_642312).sum := by decide
  have hdescent : baseEnd_642312 < baseStart_642312 := by decide
  rcases family_descends (prefixWord ++ tailWord_642312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642316 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_642316 : Nat := 118140960795 + 642316 * 2 ^ 59
def prefixEnd_642316 : Nat := 4983230072969 + 3 ^ 40 * 642316 * 2
def baseEnd_642316 : Nat := 219877893382276112930699

theorem tailTrace_642316 : CollatzResearch.WordTrace tailWord_642316 prefixEnd_642316 219877893382276112930699 := by
  unfold tailWord_642316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713594570503152842169401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15618126094004203789559201 11713594570503152842169401)
  ·
    refine ⟨8785195927877364631627051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11713594570503152842169401 8785195927877364631627051)
    ·
      refine ⟨13177793891816046947440577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785195927877364631627051 13177793891816046947440577)
      ·
        refine ⟨9883345418862035210580433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13177793891816046947440577 9883345418862035210580433)
        ·
          refine ⟨7412509064146526407935325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9883345418862035210580433 7412509064146526407935325)
          ·
            refine ⟨2779690899054947402975747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7412509064146526407935325 2779690899054947402975747)
            ·
              refine ⟨4169536348582421104463621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779690899054947402975747 4169536348582421104463621)
              ·
                refine ⟨781788065359203957086929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4169536348582421104463621 781788065359203957086929)
                ·
                  refine ⟨586341049019402967815197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781788065359203957086929 586341049019402967815197)
                  ·
                    refine ⟨219877893382276112930699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586341049019402967815197 219877893382276112930699)
                    ·
                      rfl

theorem cell22_642316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_642316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642316 prefixEnd_642316 := by exact prefixLift 642316
  have htrace : WordTrace (prefixWord ++ tailWord_642316) baseStart_642316 baseEnd_642316 := by
    simpa [prefixWord, tailWord_642316, baseEnd_642316] using wordTrace_append hprefix tailTrace_642316
  have hstable : (prefixWord ++ tailWord_642316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642316).length < 2 ^ (prefixWord ++ tailWord_642316).sum := by decide
  have hdescent : baseEnd_642316 < baseStart_642316 := by decide
  rcases family_descends (prefixWord ++ tailWord_642316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642318 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_642318 : Nat := 118140960795 + 642318 * 2 ^ 59
def prefixEnd_642318 : Nat := 4983230072969 + 3 ^ 40 * 642318 * 2
def baseEnd_642318 : Nat := 73292859341049591460231

theorem tailTrace_642318 : CollatzResearch.WordTrace tailWord_642318 prefixEnd_642318 73292859341049591460231 := by
  unfold tailWord_642318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928407760874882503238951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15618174724666040017274405 2928407760874882503238951)
  ·
    refine ⟨4392611641312323754858427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928407760874882503238951 4392611641312323754858427)
    ·
      refine ⟨6588917461968485632287641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392611641312323754858427 6588917461968485632287641)
      ·
        refine ⟨4941688096476364224215731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6588917461968485632287641 4941688096476364224215731)
        ·
          refine ⟨7412532144714546336323597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941688096476364224215731 7412532144714546336323597)
          ·
            refine ⟨2779699554267954876121349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7412532144714546336323597 2779699554267954876121349)
            ·
              refine ⟨521193666425241539272753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2779699554267954876121349 521193666425241539272753)
              ·
                refine ⟨390895249818931154454565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521193666425241539272753 390895249818931154454565)
                ·
                  refine ⟨73292859341049591460231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390895249818931154454565 73292859341049591460231)
                  ·
                    rfl

theorem cell22_642318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_642318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642318 prefixEnd_642318 := by exact prefixLift 642318
  have htrace : WordTrace (prefixWord ++ tailWord_642318) baseStart_642318 baseEnd_642318 := by
    simpa [prefixWord, tailWord_642318, baseEnd_642318] using wordTrace_append hprefix tailTrace_642318
  have hstable : (prefixWord ++ tailWord_642318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642318).length < 2 ^ (prefixWord ++ tailWord_642318).sum := by decide
  have hdescent : baseEnd_642318 < baseStart_642318 := by decide
  rcases family_descends (prefixWord ++ tailWord_642318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642333 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_642333 : Nat := 118140960795 + 642333 * 2 ^ 59
def prefixEnd_642333 : Nat := 4983230072969 + 3 ^ 40 * 642333 * 2
def baseEnd_642333 : Nat := 219883712829693735255647

theorem tailTrace_642333 : CollatzResearch.WordTrace tailWord_642333 prefixEnd_642333 219883712829693735255647 := by
  unfold tailWord_642333
  simp only [CollatzResearch.WordTrace]
  refine ⟨23427809181944717587707653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15618539454629811725138435 23427809181944717587707653)
  ·
    refine ⟨4392714221614634547695185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23427809181944717587707653 4392714221614634547695185)
    ·
      refine ⟨3294535666210975910771389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4392714221614634547695185 3294535666210975910771389)
      ·
        refine ⟨1235450874829115966539271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3294535666210975910771389 1235450874829115966539271)
        ·
          refine ⟨1853176312243673949808907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235450874829115966539271 1853176312243673949808907)
          ·
            refine ⟨2779764468365510924713361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853176312243673949808907 2779764468365510924713361)
            ·
              refine ⟨2084823351274133193535021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779764468365510924713361 2084823351274133193535021)
              ·
                refine ⟨781808756727799947575633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2084823351274133193535021 781808756727799947575633)
                ·
                  refine ⟨586356567545849960681725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781808756727799947575633 586356567545849960681725)
                  ·
                    refine ⟨219883712829693735255647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586356567545849960681725 219883712829693735255647)
                    ·
                      rfl

theorem cell22_642333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_642333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642333 prefixEnd_642333 := by exact prefixLift 642333
  have htrace : WordTrace (prefixWord ++ tailWord_642333) baseStart_642333 baseEnd_642333 := by
    simpa [prefixWord, tailWord_642333, baseEnd_642333] using wordTrace_append hprefix tailTrace_642333
  have hstable : (prefixWord ++ tailWord_642333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642333).length < 2 ^ (prefixWord ++ tailWord_642333).sum := by decide
  have hdescent : baseEnd_642333 < baseStart_642333 := by decide
  rcases family_descends (prefixWord ++ tailWord_642333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642397 : List Nat := [1, 4, 5, 1, 1, 2, 2, 6]
def baseStart_642397 : Nat := 118140960795 + 642397 * 2 ^ 59
def prefixEnd_642397 : Nat := 4983230072969 + 3 ^ 40 * 642397 * 2
def baseEnd_642397 : Nat := 24433957926402100183939

theorem tailTrace_642397 : CollatzResearch.WordTrace tailWord_642397 prefixEnd_642397 24433957926402100183939 := by
  unfold tailWord_642397
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430143453712856518037445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15620095635808571012024963 23430143453712856518037445)
  ·
    refine ⟨4393151897571160597132021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23430143453712856518037445 4393151897571160597132021)
    ·
      refine ⟨411857990397296305981127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4393151897571160597132021 411857990397296305981127)
      ·
        refine ⟨617786985595944458971691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411857990397296305981127 617786985595944458971691)
        ·
          refine ⟨926680478393916688457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617786985595944458971691 926680478393916688457537)
          ·
            refine ⟨695010358795437516343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926680478393916688457537 695010358795437516343153)
            ·
              refine ⟨521257769096578137257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695010358795437516343153 521257769096578137257365)
              ·
                refine ⟨24433957926402100183939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 521257769096578137257365 24433957926402100183939)
                ·
                  rfl

theorem cell22_642397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 6].length) (baseStart_642397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642397 prefixEnd_642397 := by exact prefixLift 642397
  have htrace : WordTrace (prefixWord ++ tailWord_642397) baseStart_642397 baseEnd_642397 := by
    simpa [prefixWord, tailWord_642397, baseEnd_642397] using wordTrace_append hprefix tailTrace_642397
  have hstable : (prefixWord ++ tailWord_642397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642397).length < 2 ^ (prefixWord ++ tailWord_642397).sum := by decide
  have hdescent : baseEnd_642397 < baseStart_642397 := by decide
  rcases family_descends (prefixWord ++ tailWord_642397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642436 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_642436 : Nat := 118140960795 + 642436 * 2 ^ 59
def prefixEnd_642436 : Nat := 4983230072969 + 3 ^ 40 * 642436 * 2
def baseEnd_642436 : Nat := 73306323944878599976777

theorem tailTrace_642436 : CollatzResearch.WordTrace tailWord_642436 prefixEnd_642436 73306323944878599976777 := by
  unfold tailWord_642436
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715782950285783089353581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15621043933714377452471441 11715782950285783089353581)
  ·
    refine ⟨4393418606357168658507593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11715782950285783089353581 4393418606357168658507593)
    ·
      refine ⟨3295063954767876493880695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4393418606357168658507593 3295063954767876493880695)
      ·
        refine ⟨4942595932151814740821043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295063954767876493880695 4942595932151814740821043)
        ·
          refine ⟨7413893898227722111231565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942595932151814740821043 7413893898227722111231565)
          ·
            refine ⟨2780210211835395791711837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7413893898227722111231565 2780210211835395791711837)
            ·
              refine ⟨1042578829438273421891939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2780210211835395791711837 1042578829438273421891939)
              ·
                refine ⟨1563868244157410132837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042578829438273421891939 1563868244157410132837909)
                ·
                  refine ⟨73306323944878599976777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1563868244157410132837909 73306323944878599976777)
                  ·
                    rfl

theorem cell22_642436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_642436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642436 prefixEnd_642436 := by exact prefixLift 642436
  have htrace : WordTrace (prefixWord ++ tailWord_642436) baseStart_642436 baseEnd_642436 := by
    simpa [prefixWord, tailWord_642436, baseEnd_642436] using wordTrace_append hprefix tailTrace_642436
  have hstable : (prefixWord ++ tailWord_642436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642436).length < 2 ^ (prefixWord ++ tailWord_642436).sum := by decide
  have hdescent : baseEnd_642436 < baseStart_642436 := by decide
  rcases family_descends (prefixWord ++ tailWord_642436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642464 : List Nat := [2, 1, 1, 4, 1, 2, 1, 10]
def baseStart_642464 : Nat := 118140960795 + 642464 * 2 ^ 59
def prefixEnd_642464 : Nat := 4983230072969 + 3 ^ 40 * 642464 * 2
def baseEnd_642464 : Nat := 24436506311872562247805

theorem tailTrace_642464 : CollatzResearch.WordTrace tailWord_642464 prefixEnd_642464 24436506311872562247805 := by
  unfold tailWord_642464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716293572235063480363223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15621724762980084640484297 11716293572235063480363223)
  ·
    refine ⟨17574440358352595220544835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716293572235063480363223 17574440358352595220544835)
    ·
      refine ⟨26361660537528892830817253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17574440358352595220544835 26361660537528892830817253)
      ·
        refine ⟨4942811350786667405778235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26361660537528892830817253 4942811350786667405778235)
        ·
          refine ⟨7414217026180001108667353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942811350786667405778235 7414217026180001108667353)
          ·
            refine ⟨5560662769635000831500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7414217026180001108667353 5560662769635000831500515)
            ·
              refine ⟨8340994154452501247250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5560662769635000831500515 8340994154452501247250773)
              ·
                refine ⟨24436506311872562247805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8340994154452501247250773 24436506311872562247805)
                ·
                  rfl

theorem cell22_642464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_642464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642464 prefixEnd_642464 := by exact prefixLift 642464
  have htrace : WordTrace (prefixWord ++ tailWord_642464) baseStart_642464 baseEnd_642464 := by
    simpa [prefixWord, tailWord_642464, baseEnd_642464] using wordTrace_append hprefix tailTrace_642464
  have hstable : (prefixWord ++ tailWord_642464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642464).length < 2 ^ (prefixWord ++ tailWord_642464).sum := by decide
  have hdescent : baseEnd_642464 < baseStart_642464 := by decide
  rcases family_descends (prefixWord ++ tailWord_642464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642472 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_642472 : Nat := 118140960795 + 642472 * 2 ^ 59
def prefixEnd_642472 : Nat := 4983230072969 + 3 ^ 40 * 642472 * 2
def baseEnd_642472 : Nat := 219931295370343706030221

theorem tailTrace_642472 : CollatzResearch.WordTrace tailWord_642472 prefixEnd_642472 219931295370343706030221 := by
  unfold tailWord_642472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716439464220572163508835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15621919285627429551345113 11716439464220572163508835)
  ·
    refine ⟨17574659196330858245263253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716439464220572163508835 17574659196330858245263253)
    ·
      refine ⟨823812149828008980246715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17574659196330858245263253 823812149828008980246715)
      ·
        refine ⟨1235718224742013470370073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823812149828008980246715 1235718224742013470370073)
        ·
          refine ⟨926788668556510102777555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235718224742013470370073 926788668556510102777555)
          ·
            refine ⟨1390183002834765154166333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926788668556510102777555 1390183002834765154166333)
            ·
              refine ⟨521318626063036932812375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1390183002834765154166333 521318626063036932812375)
              ·
                refine ⟨781977939094555399218563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521318626063036932812375 781977939094555399218563)
                ·
                  refine ⟨1172966908641833098827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781977939094555399218563 1172966908641833098827845)
                  ·
                    refine ⟨219931295370343706030221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1172966908641833098827845 219931295370343706030221)
                    ·
                      rfl

theorem cell22_642472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_642472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642472 prefixEnd_642472 := by exact prefixLift 642472
  have htrace : WordTrace (prefixWord ++ tailWord_642472) baseStart_642472 baseEnd_642472 := by
    simpa [prefixWord, tailWord_642472, baseEnd_642472] using wordTrace_append hprefix tailTrace_642472
  have hstable : (prefixWord ++ tailWord_642472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642472).length < 2 ^ (prefixWord ++ tailWord_642472).sum := by decide
  have hdescent : baseEnd_642472 < baseStart_642472 := by decide
  rcases family_descends (prefixWord ++ tailWord_642472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642485 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_642485 : Nat := 118140960795 + 642485 * 2 ^ 59
def prefixEnd_642485 : Nat := 4983230072969 + 3 ^ 40 * 642485 * 2
def baseEnd_642485 : Nat := 219935745536016005455181

theorem tailTrace_642485 : CollatzResearch.WordTrace tailWord_642485 prefixEnd_642485 219935745536016005455181 := by
  unfold tailWord_642485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23433353077394047547240909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15622235384929365031493939 23433353077394047547240909)
  ·
    refine ⟨8787507404022767830215341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23433353077394047547240909 8787507404022767830215341)
    ·
      refine ⟨3295315276508537936330753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8787507404022767830215341 3295315276508537936330753)
      ·
        refine ⟨2471486457381403452248065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3295315276508537936330753 2471486457381403452248065)
        ·
          refine ⟨1853614843036052589186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2471486457381403452248065 1853614843036052589186049)
          ·
            refine ⟨1390211132277039441889537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853614843036052589186049 1390211132277039441889537)
            ·
              refine ⟨1042658349207779581417153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390211132277039441889537 1042658349207779581417153)
              ·
                refine ⟨781993761905834686062865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042658349207779581417153 781993761905834686062865)
                ·
                  refine ⟨586495321429376014547149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781993761905834686062865 586495321429376014547149)
                  ·
                    refine ⟨219935745536016005455181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586495321429376014547149 219935745536016005455181)
                    ·
                      rfl

theorem cell22_642485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_642485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642485 prefixEnd_642485 := by exact prefixLift 642485
  have htrace : WordTrace (prefixWord ++ tailWord_642485) baseStart_642485 baseEnd_642485 := by
    simpa [prefixWord, tailWord_642485, baseEnd_642485] using wordTrace_append hprefix tailTrace_642485
  have hstable : (prefixWord ++ tailWord_642485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642485).length < 2 ^ (prefixWord ++ tailWord_642485).sum := by decide
  have hdescent : baseEnd_642485 < baseStart_642485 := by decide
  rcases family_descends (prefixWord ++ tailWord_642485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642556 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_642556 : Nat := 118140960795 + 642556 * 2 ^ 59
def prefixEnd_642556 : Nat := 4983230072969 + 3 ^ 40 * 642556 * 2
def baseEnd_642556 : Nat := 219960050286995486929963

theorem tailTrace_642556 : CollatzResearch.WordTrace tailWord_642556 prefixEnd_642556 219960050286995486929963 := by
  unfold tailWord_642556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11717971330068413336537761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15623961773424551115383681 11717971330068413336537761)
  ·
    refine ⟨8788478497551310002403321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11717971330068413336537761 8788478497551310002403321)
    ·
      refine ⟨6591358873163482501802491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8788478497551310002403321 6591358873163482501802491)
      ·
        refine ⟨9887038309745223752703737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591358873163482501802491 9887038309745223752703737)
        ·
          refine ⟨7415278732308917814527803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9887038309745223752703737 7415278732308917814527803)
          ·
            refine ⟨11122918098463376721791705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415278732308917814527803 11122918098463376721791705)
            ·
              refine ⟨8342188573847532541343779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11122918098463376721791705 8342188573847532541343779)
              ·
                refine ⟨12513282860771298812015669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342188573847532541343779 12513282860771298812015669)
                ·
                  refine ⟨1173120268197309263626469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12513282860771298812015669 1173120268197309263626469)
                  ·
                    refine ⟨219960050286995486929963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173120268197309263626469 219960050286995486929963)
                    ·
                      rfl

theorem cell22_642556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_642556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642556 prefixEnd_642556 := by exact prefixLift 642556
  have htrace : WordTrace (prefixWord ++ tailWord_642556) baseStart_642556 baseEnd_642556 := by
    simpa [prefixWord, tailWord_642556, baseEnd_642556] using wordTrace_append hprefix tailTrace_642556
  have hstable : (prefixWord ++ tailWord_642556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642556).length < 2 ^ (prefixWord ++ tailWord_642556).sum := by decide
  have hdescent : baseEnd_642556 < baseStart_642556 := by decide
  rcases family_descends (prefixWord ++ tailWord_642556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642566 : List Nat := [6, 2, 1, 1, 3, 1, 2, 6]
def baseStart_642566 : Nat := 118140960795 + 642566 * 2 ^ 59
def prefixEnd_642566 : Nat := 4983230072969 + 3 ^ 40 * 642566 * 2
def baseEnd_642566 : Nat := 24440385943484310464437

theorem tailTrace_642566 : CollatzResearch.WordTrace tailWord_642566 prefixEnd_642566 24440385943484310464437 := by
  unfold tailWord_642566
  simp only [CollatzResearch.WordTrace]
  refine ⟨732384605940643699404361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15624204926733732253959701 732384605940643699404361)
  ·
    refine ⟨549288454455482774553271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732384605940643699404361 549288454455482774553271)
    ·
      refine ⟨823932681683224161829907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549288454455482774553271 823932681683224161829907)
      ·
        refine ⟨1235899022524836242744861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823932681683224161829907 1235899022524836242744861)
        ·
          refine ⟨463462133446813591029323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235899022524836242744861 463462133446813591029323)
          ·
            refine ⟨695193200170220386543985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463462133446813591029323 695193200170220386543985)
            ·
              refine ⟨521394900127665289907989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695193200170220386543985 521394900127665289907989)
              ·
                refine ⟨24440385943484310464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 521394900127665289907989 24440385943484310464437)
                ·
                  rfl

theorem cell22_642566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_642566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642566 prefixEnd_642566 := by exact prefixLift 642566
  have htrace : WordTrace (prefixWord ++ tailWord_642566) baseStart_642566 baseEnd_642566 := by
    simpa [prefixWord, tailWord_642566, baseEnd_642566] using wordTrace_append hprefix tailTrace_642566
  have hstable : (prefixWord ++ tailWord_642566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642566).length < 2 ^ (prefixWord ++ tailWord_642566).sum := by decide
  have hdescent : baseEnd_642566 < baseStart_642566 := by decide
  rcases family_descends (prefixWord ++ tailWord_642566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642586 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_642586 : Nat := 118140960795 + 642586 * 2 ^ 59
def prefixEnd_642586 : Nat := 4983230072969 + 3 ^ 40 * 642586 * 2
def baseEnd_642586 : Nat := 219970319900085408679871

theorem tailTrace_642586 : CollatzResearch.WordTrace tailWord_642586 prefixEnd_642586 219970319900085408679871 := by
  unfold tailWord_642586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859259212507035449166903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15624691233352094531111741 5859259212507035449166903)
  ·
    refine ⟨8788888818760553173750355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5859259212507035449166903 8788888818760553173750355)
    ·
      refine ⟨13183333228140829760625533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8788888818760553173750355 13183333228140829760625533)
      ·
        refine ⟨4943749960552811160234575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13183333228140829760625533 4943749960552811160234575)
        ·
          refine ⟨7415624940829216740351863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943749960552811160234575 7415624940829216740351863)
          ·
            refine ⟨11123437411243825110527795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415624940829216740351863 11123437411243825110527795)
            ·
              refine ⟨16685156116865737665791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11123437411243825110527795 16685156116865737665791693)
              ·
                refine ⟨6256933543824651624671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16685156116865737665791693 6256933543824651624671885)
                ·
                  refine ⟨2346350078934244359251957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6256933543824651624671885 2346350078934244359251957)
                  ·
                    refine ⟨219970319900085408679871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2346350078934244359251957 219970319900085408679871)
                    ·
                      rfl

theorem cell22_642586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_642586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642586 prefixEnd_642586 := by exact prefixLift 642586
  have htrace : WordTrace (prefixWord ++ tailWord_642586) baseStart_642586 baseEnd_642586 := by
    simpa [prefixWord, tailWord_642586, baseEnd_642586] using wordTrace_append hprefix tailTrace_642586
  have hstable : (prefixWord ++ tailWord_642586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642586).length < 2 ^ (prefixWord ++ tailWord_642586).sum := by decide
  have hdescent : baseEnd_642586 < baseStart_642586 := by decide
  rcases family_descends (prefixWord ++ tailWord_642586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642616 : List Nat := [2, 1, 2, 1, 4, 2, 1, 9]
def baseStart_642616 : Nat := 118140960795 + 642616 * 2 ^ 59
def prefixEnd_642616 : Nat := 4983230072969 + 3 ^ 40 * 642616 * 2
def baseEnd_642616 : Nat := 24442287723686147825531

theorem tailTrace_642616 : CollatzResearch.WordTrace tailWord_642616 prefixEnd_642616 24442287723686147825531 := by
  unfold tailWord_642616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719065519959728460129851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15625420693279637946839801 11719065519959728460129851)
  ·
    refine ⟨17578598279939592690194777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11719065519959728460129851 17578598279939592690194777)
    ·
      refine ⟨13183948709954694517646083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17578598279939592690194777 13183948709954694517646083)
      ·
        refine ⟨19775923064932041776469125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13183948709954694517646083 19775923064932041776469125)
        ·
          refine ⟨3707985574674757833087961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19775923064932041776469125 3707985574674757833087961)
          ·
            refine ⟨2780989181006068374815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707985574674757833087961 2780989181006068374815971)
            ·
              refine ⟨4171483771509102562223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780989181006068374815971 4171483771509102562223957)
              ·
                refine ⟨24442287723686147825531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4171483771509102562223957 24442287723686147825531)
                ·
                  rfl

theorem cell22_642616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_642616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642616 prefixEnd_642616 := by exact prefixLift 642616
  have htrace : WordTrace (prefixWord ++ tailWord_642616) baseStart_642616 baseEnd_642616 := by
    simpa [prefixWord, tailWord_642616, baseEnd_642616] using wordTrace_append hprefix tailTrace_642616
  have hstable : (prefixWord ++ tailWord_642616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642616).length < 2 ^ (prefixWord ++ tailWord_642616).sum := by decide
  have hdescent : baseEnd_642616 < baseStart_642616 := by decide
  rcases family_descends (prefixWord ++ tailWord_642616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642723 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 6]
def baseStart_642723 : Nat := 118140960795 + 642723 * 2 ^ 59
def prefixEnd_642723 : Nat := 4983230072969 + 3 ^ 40 * 642723 * 2
def baseEnd_642723 : Nat := 73339072599954239334817

theorem tailTrace_642723 : CollatzResearch.WordTrace tailWord_642723 prefixEnd_642723 73339072599954239334817 := by
  unfold tailWord_642723
  simp only [CollatzResearch.WordTrace]
  refine ⟨23442033650531814194404823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15628022433687876129603215 23442033650531814194404823)
  ·
    refine ⟨35163050475797721291607235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23442033650531814194404823 35163050475797721291607235)
    ·
      refine ⟨52744575713696581937410853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35163050475797721291607235 52744575713696581937410853)
      ·
        refine ⟨9889607946318109113264535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52744575713696581937410853 9889607946318109113264535)
        ·
          refine ⟨14834411919477163669896803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889607946318109113264535 14834411919477163669896803)
          ·
            refine ⟨22251617879215745504845205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14834411919477163669896803 22251617879215745504845205)
            ·
              refine ⟨1043044588088238070539619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22251617879215745504845205 1043044588088238070539619)
              ·
                refine ⟨1564566882132357105809429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043044588088238070539619 1564566882132357105809429)
                ·
                  refine ⟨73339072599954239334817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1564566882132357105809429 73339072599954239334817)
                  ·
                    rfl

theorem cell22_642723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_642723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642723 prefixEnd_642723 := by exact prefixLift 642723
  have htrace : WordTrace (prefixWord ++ tailWord_642723) baseStart_642723 baseEnd_642723 := by
    simpa [prefixWord, tailWord_642723, baseEnd_642723] using wordTrace_append hprefix tailTrace_642723
  have hstable : (prefixWord ++ tailWord_642723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642723).length < 2 ^ (prefixWord ++ tailWord_642723).sum := by decide
  have hdescent : baseEnd_642723 < baseStart_642723 := by decide
  rcases family_descends (prefixWord ++ tailWord_642723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642770 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_642770 : Nat := 118140960795 + 642770 * 2 ^ 59
def prefixEnd_642770 : Nat := 4983230072969 + 3 ^ 40 * 642770 * 2
def baseEnd_642770 : Nat := 220033306860370262079307

theorem tailTrace_642770 : CollatzResearch.WordTrace tailWord_642770 prefixEnd_642770 220033306860370262079307 := by
  unfold tailWord_642770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860936970340385305341441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15629165254241027480910509 5860936970340385305341441)
  ·
    refine ⟨4395702727755288979006081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5860936970340385305341441 4395702727755288979006081)
    ·
      refine ⟨3296777045816466734254561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395702727755288979006081 3296777045816466734254561)
      ·
        refine ⟨2472582784362350050690921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296777045816466734254561 2472582784362350050690921)
        ·
          refine ⟨1854437088271762538018191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472582784362350050690921 1854437088271762538018191)
          ·
            refine ⟨2781655632407643807027287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854437088271762538018191 2781655632407643807027287)
            ·
              refine ⟨4172483448611465710540931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781655632407643807027287 4172483448611465710540931)
              ·
                refine ⟨6258725172917198565811397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172483448611465710540931 6258725172917198565811397)
                ·
                  refine ⟨1173510969921974731089637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6258725172917198565811397 1173510969921974731089637)
                  ·
                    refine ⟨220033306860370262079307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173510969921974731089637 220033306860370262079307)
                    ·
                      rfl

theorem cell22_642770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_642770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642770 prefixEnd_642770 := by exact prefixLift 642770
  have htrace : WordTrace (prefixWord ++ tailWord_642770) baseStart_642770 baseEnd_642770 := by
    simpa [prefixWord, tailWord_642770, baseEnd_642770] using wordTrace_append hprefix tailTrace_642770
  have hstable : (prefixWord ++ tailWord_642770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642770).length < 2 ^ (prefixWord ++ tailWord_642770).sum := by decide
  have hdescent : baseEnd_642770 < baseStart_642770 := by decide
  rcases family_descends (prefixWord ++ tailWord_642770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642772 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_642772 : Nat := 118140960795 + 642772 * 2 ^ 59
def prefixEnd_642772 : Nat := 4983230072969 + 3 ^ 40 * 642772 * 2
def baseEnd_642772 : Nat := 220033991501242923529301

theorem tailTrace_642772 : CollatzResearch.WordTrace tailWord_642772 prefixEnd_642772 220033991501242923529301 := by
  unfold tailWord_642772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721910413677147781469285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15629213884902863708625713 11721910413677147781469285)
  ·
    refine ⟨2197858202564465209025491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11721910413677147781469285 2197858202564465209025491)
    ·
      refine ⟨3296787303846697813538237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197858202564465209025491 3296787303846697813538237)
      ·
        refine ⟨1236295238942511680076839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3296787303846697813538237 1236295238942511680076839)
        ·
          refine ⟨1854442858413767520115259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236295238942511680076839 1854442858413767520115259)
          ·
            refine ⟨2781664287620651280172889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854442858413767520115259 2781664287620651280172889)
            ·
              refine ⟨2086248215715488460129667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781664287620651280172889 2086248215715488460129667)
              ·
                refine ⟨3129372323573232690194501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086248215715488460129667 3129372323573232690194501)
                ·
                  refine ⟨586757310669981129411469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3129372323573232690194501 586757310669981129411469)
                  ·
                    refine ⟨220033991501242923529301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586757310669981129411469 220033991501242923529301)
                    ·
                      rfl

theorem cell22_642772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_642772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642772 prefixEnd_642772 := by exact prefixLift 642772
  have htrace : WordTrace (prefixWord ++ tailWord_642772) baseStart_642772 baseEnd_642772 := by
    simpa [prefixWord, tailWord_642772, baseEnd_642772] using wordTrace_append hprefix tailTrace_642772
  have hstable : (prefixWord ++ tailWord_642772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642772).length < 2 ^ (prefixWord ++ tailWord_642772).sum := by decide
  have hdescent : baseEnd_642772 < baseStart_642772 := by decide
  rcases family_descends (prefixWord ++ tailWord_642772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642785 : List Nat := [1, 2, 3, 1, 5, 1, 2, 7]
def baseStart_642785 : Nat := 118140960795 + 642785 * 2 ^ 59
def prefixEnd_642785 : Nat := 4983230072969 + 3 ^ 40 * 642785 * 2
def baseEnd_642785 : Nat := 24448715740768358106029

theorem tailTrace_642785 : CollatzResearch.WordTrace tailWord_642785 prefixEnd_642785 24448715740768358106029 := by
  unfold tailWord_642785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444294976307198783161809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15629529984204799188774539 23444294976307198783161809)
  ·
    refine ⟨17583221232230399087371357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23444294976307198783161809 17583221232230399087371357)
    ·
      refine ⟨6593707962086399657764259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17583221232230399087371357 6593707962086399657764259)
      ·
        refine ⟨9890561943129599486646389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593707962086399657764259 9890561943129599486646389)
        ·
          refine ⟨927240182168399951873099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9890561943129599486646389 927240182168399951873099)
          ·
            refine ⟨1390860273252599927809649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927240182168399951873099 1390860273252599927809649)
            ·
              refine ⟨1043145204939449945857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390860273252599927809649 1043145204939449945857237)
              ·
                refine ⟨24448715740768358106029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1043145204939449945857237 24448715740768358106029)
                ·
                  rfl

theorem cell22_642785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 7].length) (baseStart_642785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642785 prefixEnd_642785 := by exact prefixLift 642785
  have htrace : WordTrace (prefixWord ++ tailWord_642785) baseStart_642785 baseEnd_642785 := by
    simpa [prefixWord, tailWord_642785, baseEnd_642785] using wordTrace_append hprefix tailTrace_642785
  have hstable : (prefixWord ++ tailWord_642785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642785).length < 2 ^ (prefixWord ++ tailWord_642785).sum := by decide
  have hdescent : baseEnd_642785 < baseStart_642785 := by decide
  rcases family_descends (prefixWord ++ tailWord_642785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642804 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_642804 : Nat := 118140960795 + 642804 * 2 ^ 59
def prefixEnd_642804 : Nat := 4983230072969 + 3 ^ 40 * 642804 * 2
def baseEnd_642804 : Nat := 220044945755205506729203

theorem tailTrace_642804 : CollatzResearch.WordTrace tailWord_642804 prefixEnd_642804 220044945755205506729203 := by
  unfold tailWord_642804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11722493981619182514051733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15629991975492243352068977 11722493981619182514051733)
  ·
    refine ⟨549491905388399180346175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11722493981619182514051733 549491905388399180346175)
    ·
      refine ⟨824237858082598770519263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549491905388399180346175 824237858082598770519263)
      ·
        refine ⟨1236356787123898155778895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824237858082598770519263 1236356787123898155778895)
        ·
          refine ⟨1854535180685847233668343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236356787123898155778895 1854535180685847233668343)
          ·
            refine ⟨2781802771028770850502515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854535180685847233668343 2781802771028770850502515)
            ·
              refine ⟨4172704156543156275753773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781802771028770850502515 4172704156543156275753773)
              ·
                refine ⟨1564764058703683603407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172704156543156275753773 1564764058703683603407665)
                ·
                  refine ⟨1173573044027762702555749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564764058703683603407665 1173573044027762702555749)
                  ·
                    refine ⟨220044945755205506729203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173573044027762702555749 220044945755205506729203)
                    ·
                      rfl

theorem cell22_642804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_642804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642804 prefixEnd_642804 := by exact prefixLift 642804
  have htrace : WordTrace (prefixWord ++ tailWord_642804) baseStart_642804 baseEnd_642804 := by
    simpa [prefixWord, tailWord_642804, baseEnd_642804] using wordTrace_append hprefix tailTrace_642804
  have hstable : (prefixWord ++ tailWord_642804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642804).length < 2 ^ (prefixWord ++ tailWord_642804).sum := by decide
  have hdescent : baseEnd_642804 < baseStart_642804 := by decide
  rcases family_descends (prefixWord ++ tailWord_642804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642813 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 7]
def baseStart_642813 : Nat := 118140960795 + 642813 * 2 ^ 59
def prefixEnd_642813 : Nat := 4983230072969 + 3 ^ 40 * 642813 * 2
def baseEnd_642813 : Nat := 73349342213044161084725

theorem tailTrace_642813 : CollatzResearch.WordTrace tailWord_642813 prefixEnd_642813 73349342213044161084725 := by
  unfold tailWord_642813
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445316220205759565181093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15630210813470506376787395 23445316220205759565181093)
  ·
    refine ⟨4395996791288579918471455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23445316220205759565181093 4395996791288579918471455)
    ·
      refine ⟨6593995186932869877707183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395996791288579918471455 6593995186932869877707183)
      ·
        refine ⟨9890992780399304816560775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593995186932869877707183 9890992780399304816560775)
        ·
          refine ⟨14836489170598957224841163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890992780399304816560775 14836489170598957224841163)
          ·
            refine ⟨22254733755898435837261745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14836489170598957224841163 22254733755898435837261745)
            ·
              refine ⟨16691050316923826877946309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22254733755898435837261745 16691050316923826877946309)
              ·
                refine ⟨3129571934423217539614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16691050316923826877946309 3129571934423217539614933)
                ·
                  refine ⟨73349342213044161084725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3129571934423217539614933 73349342213044161084725)
                  ·
                    rfl

theorem cell22_642813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_642813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642813 prefixEnd_642813 := by exact prefixLift 642813
  have htrace : WordTrace (prefixWord ++ tailWord_642813) baseStart_642813 baseEnd_642813 := by
    simpa [prefixWord, tailWord_642813, baseEnd_642813] using wordTrace_append hprefix tailTrace_642813
  have hstable : (prefixWord ++ tailWord_642813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642813).length < 2 ^ (prefixWord ++ tailWord_642813).sum := by decide
  have hdescent : baseEnd_642813 < baseStart_642813 := by decide
  rcases family_descends (prefixWord ++ tailWord_642813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642830 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_642830 : Nat := 118140960795 + 642830 * 2 ^ 59
def prefixEnd_642830 : Nat := 4983230072969 + 3 ^ 40 * 642830 * 2
def baseEnd_642830 : Nat := 73351282028850035193041

theorem tailTrace_642830 : CollatzResearch.WordTrace tailWord_642830 prefixEnd_642830 73351282028850035193041 := by
  unfold tailWord_642830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930742032643021433568743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15630624174096114312366629 2930742032643021433568743)
  ·
    refine ⟨4396113048964532150353115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930742032643021433568743 4396113048964532150353115)
    ·
      refine ⟨6594169573446798225529673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396113048964532150353115 6594169573446798225529673)
      ·
        refine ⟨4945627180085098669147255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594169573446798225529673 4945627180085098669147255)
        ·
          refine ⟨7418440770127648003720883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945627180085098669147255 7418440770127648003720883)
          ·
            refine ⟨11127661155191472005581325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418440770127648003720883 11127661155191472005581325)
            ·
              refine ⟨4172872933196802002092997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11127661155191472005581325 4172872933196802002092997)
              ·
                refine ⟨782413674974400375392437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4172872933196802002092997 782413674974400375392437)
                ·
                  refine ⟨73351282028850035193041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 782413674974400375392437 73351282028850035193041)
                  ·
                    rfl

theorem cell22_642830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_642830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642830 prefixEnd_642830 := by exact prefixLift 642830
  have htrace : WordTrace (prefixWord ++ tailWord_642830) baseStart_642830 baseEnd_642830 := by
    simpa [prefixWord, tailWord_642830, baseEnd_642830] using wordTrace_append hprefix tailTrace_642830
  have hstable : (prefixWord ++ tailWord_642830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642830).length < 2 ^ (prefixWord ++ tailWord_642830).sum := by decide
  have hdescent : baseEnd_642830 < baseStart_642830 := by decide
  rcases family_descends (prefixWord ++ tailWord_642830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642836 : List Nat := [2, 4, 4, 1, 1, 2, 1, 7]
def baseStart_642836 : Nat := 118140960795 + 642836 * 2 ^ 59
def prefixEnd_642836 : Nat := 4983230072969 + 3 ^ 40 * 642836 * 2
def baseEnd_642836 : Nat := 24450655556574232214345

theorem tailTrace_642836 : CollatzResearch.WordTrace tailWord_642836 prefixEnd_642836 24450655556574232214345 := by
  unfold tailWord_642836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723077549561217246634181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15630770066081622995512241 11723077549561217246634181)
  ·
    refine ⟨2198077040542728233743909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11723077549561217246634181 2198077040542728233743909)
    ·
      refine ⟨412139445101761543826983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2198077040542728233743909 412139445101761543826983)
      ·
        refine ⟨618209167652642315740475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412139445101761543826983 618209167652642315740475)
        ·
          refine ⟨927313751478963473610713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618209167652642315740475 927313751478963473610713)
          ·
            refine ⟨695485313609222605208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927313751478963473610713 695485313609222605208035)
            ·
              refine ⟨1043227970413833907812053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695485313609222605208035 1043227970413833907812053)
              ·
                refine ⟨24450655556574232214345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1043227970413833907812053 24450655556574232214345)
                ·
                  rfl

theorem cell22_642836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_642836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642836 prefixEnd_642836 := by exact prefixLift 642836
  have htrace : WordTrace (prefixWord ++ tailWord_642836) baseStart_642836 baseEnd_642836 := by
    simpa [prefixWord, tailWord_642836, baseEnd_642836] using wordTrace_append hprefix tailTrace_642836
  have hstable : (prefixWord ++ tailWord_642836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642836).length < 2 ^ (prefixWord ++ tailWord_642836).sum := by decide
  have hdescent : baseEnd_642836 < baseStart_642836 := by decide
  rcases family_descends (prefixWord ++ tailWord_642836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642860 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_642860 : Nat := 118140960795 + 642860 * 2 ^ 59
def prefixEnd_642860 : Nat := 4983230072969 + 3 ^ 40 * 642860 * 2
def baseEnd_642860 : Nat := 220064115699640027329031

theorem tailTrace_642860 : CollatzResearch.WordTrace tailWord_642860 prefixEnd_642860 220064115699640027329031 := by
  unfold tailWord_642860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723515225517743296071017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15631353634023657728094689 11723515225517743296071017)
  ·
    refine ⟨8792636419138307472053263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11723515225517743296071017 8792636419138307472053263)
    ·
      refine ⟨13188954628707461208079895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8792636419138307472053263 13188954628707461208079895)
      ·
        refine ⟨19783431943061191812119843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13188954628707461208079895 19783431943061191812119843)
        ·
          refine ⟨29675147914591787718179765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19783431943061191812119843 29675147914591787718179765)
          ·
            refine ⟨2782045116992980098579353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29675147914591787718179765 2782045116992980098579353)
            ·
              refine ⟨2086533837744735073934515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782045116992980098579353 2086533837744735073934515)
              ·
                refine ⟨3129800756617102610901773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086533837744735073934515 3129800756617102610901773)
                ·
                  refine ⟨1173675283731413479088165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3129800756617102610901773 1173675283731413479088165)
                  ·
                    refine ⟨220064115699640027329031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173675283731413479088165 220064115699640027329031)
                    ·
                      rfl

theorem cell22_642860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_642860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642860 prefixEnd_642860 := by exact prefixLift 642860
  have htrace : WordTrace (prefixWord ++ tailWord_642860) baseStart_642860 baseEnd_642860 := by
    simpa [prefixWord, tailWord_642860, baseEnd_642860] using wordTrace_append hprefix tailTrace_642860
  have hstable : (prefixWord ++ tailWord_642860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642860).length < 2 ^ (prefixWord ++ tailWord_642860).sum := by decide
  have hdescent : baseEnd_642860 < baseStart_642860 := by decide
  rcases family_descends (prefixWord ++ tailWord_642860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642892 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_642892 : Nat := 118140960795 + 642892 * 2 ^ 59
def prefixEnd_642892 : Nat := 4983230072969 + 3 ^ 40 * 642892 * 2
def baseEnd_642892 : Nat := 73358356651200870176311

theorem tailTrace_642892 : CollatzResearch.WordTrace tailWord_642892 prefixEnd_642892 73358356651200870176311 := by
  unfold tailWord_642892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724098793459778028653465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15632131724613037371537953 11724098793459778028653465)
  ·
    refine ⟨8793074095094833521490099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11724098793459778028653465 8793074095094833521490099)
    ·
      refine ⟨13189611142642250282235149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793074095094833521490099 13189611142642250282235149)
      ·
        refine ⟨4946104178490843855838181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13189611142642250282235149 4946104178490843855838181)
        ·
          refine ⟨927394533467033222969659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4946104178490843855838181 927394533467033222969659)
          ·
            refine ⟨1391091800200549834454489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927394533467033222969659 1391091800200549834454489)
            ·
              refine ⟨1043318850150412375840867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391091800200549834454489 1043318850150412375840867)
              ·
                refine ⟨1564978275225618563761301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043318850150412375840867 1564978275225618563761301)
                ·
                  refine ⟨73358356651200870176311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1564978275225618563761301 73358356651200870176311)
                  ·
                    rfl

theorem cell22_642892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_642892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642892 prefixEnd_642892 := by exact prefixLift 642892
  have htrace : WordTrace (prefixWord ++ tailWord_642892) baseStart_642892 baseEnd_642892 := by
    simpa [prefixWord, tailWord_642892, baseEnd_642892] using wordTrace_append hprefix tailTrace_642892
  have hstable : (prefixWord ++ tailWord_642892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642892).length < 2 ^ (prefixWord ++ tailWord_642892).sum := by decide
  have hdescent : baseEnd_642892 < baseStart_642892 := by decide
  rcases family_descends (prefixWord ++ tailWord_642892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642920 : List Nat := [2, 1, 4, 2, 1, 1, 3, 8]
def baseStart_642920 : Nat := 118140960795 + 642920 * 2 ^ 59
def prefixEnd_642920 : Nat := 4983230072969 + 3 ^ 40 * 642920 * 2
def baseEnd_642920 : Nat := 24453850547313318980983

theorem tailTrace_642920 : CollatzResearch.WordTrace tailWord_642920 prefixEnd_642920 24453850547313318980983 := by
  unfold tailWord_642920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724609415409058419663107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15632812553878744559550809 11724609415409058419663107)
  ·
    refine ⟨17586914123113587629494661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11724609415409058419663107 17586914123113587629494661)
    ·
      refine ⟨3297546398083797680530249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17586914123113587629494661 3297546398083797680530249)
      ·
        refine ⟨2473159798562848260397687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3297546398083797680530249 2473159798562848260397687)
        ·
          refine ⟨3709739697844272390596531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473159798562848260397687 3709739697844272390596531)
          ·
            refine ⟨5564609546766408585894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709739697844272390596531 5564609546766408585894797)
            ·
              refine ⟨2086728580037403219710549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5564609546766408585894797 2086728580037403219710549)
              ·
                refine ⟨24453850547313318980983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2086728580037403219710549 24453850547313318980983)
                ·
                  rfl

theorem cell22_642920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_642920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642920 prefixEnd_642920 := by exact prefixLift 642920
  have htrace : WordTrace (prefixWord ++ tailWord_642920) baseStart_642920 baseEnd_642920 := by
    simpa [prefixWord, tailWord_642920, baseEnd_642920] using wordTrace_append hprefix tailTrace_642920
  have hstable : (prefixWord ++ tailWord_642920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642920).length < 2 ^ (prefixWord ++ tailWord_642920).sum := by decide
  have hdescent : baseEnd_642920 < baseStart_642920 := by decide
  rcases family_descends (prefixWord ++ tailWord_642920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642926 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_642926 : Nat := 118140960795 + 642926 * 2 ^ 59
def prefixEnd_642926 : Nat := 4983230072969 + 3 ^ 40 * 642926 * 2
def baseEnd_642926 : Nat := 73362236282812618392943

theorem tailTrace_642926 : CollatzResearch.WordTrace tailWord_642926 prefixEnd_642926 73362236282812618392943 := by
  unfold tailWord_642926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931179708599547483005579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15632958445864253242696421 2931179708599547483005579)
  ·
    refine ⟨4396769562899321224508369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931179708599547483005579 4396769562899321224508369)
    ·
      refine ⟨3297577172174490918381277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4396769562899321224508369 3297577172174490918381277)
      ·
        refine ⟨1236591439565434094392979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3297577172174490918381277 1236591439565434094392979)
        ·
          refine ⟨1854887159348151141589469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236591439565434094392979 1854887159348151141589469)
          ·
            refine ⟨695582684755556678096051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1854887159348151141589469 695582684755556678096051)
            ·
              refine ⟨1043374027133335017144077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695582684755556678096051 1043374027133335017144077)
              ·
                refine ⟨391265260175000631429029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043374027133335017144077 391265260175000631429029)
                ·
                  refine ⟨73362236282812618392943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391265260175000631429029 73362236282812618392943)
                  ·
                    rfl

theorem cell22_642926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_642926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_642926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_642926 prefixEnd_642926 := by exact prefixLift 642926
  have htrace : WordTrace (prefixWord ++ tailWord_642926) baseStart_642926 baseEnd_642926 := by
    simpa [prefixWord, tailWord_642926, baseEnd_642926] using wordTrace_append hprefix tailTrace_642926
  have hstable : (prefixWord ++ tailWord_642926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642926).length < 2 ^ (prefixWord ++ tailWord_642926).sum := by decide
  have hdescent : baseEnd_642926 < baseStart_642926 := by decide
  rcases family_descends (prefixWord ++ tailWord_642926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643044 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_643044 : Nat := 118140960795 + 643044 * 2 ^ 59
def prefixEnd_643044 : Nat := 4983230072969 + 3 ^ 40 * 643044 * 2
def baseEnd_643044 : Nat := 73375700886641626909489

theorem tailTrace_643044 : CollatzResearch.WordTrace tailWord_643044 prefixEnd_643044 73375700886641626909489 := by
  unfold tailWord_643044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726870741184443008420093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15635827654912590677893457 11726870741184443008420093)
  ·
    refine ⟨4397576527944166128157535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11726870741184443008420093 4397576527944166128157535)
    ·
      refine ⟨6596364791916249192236303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397576527944166128157535 6596364791916249192236303)
      ·
        refine ⟨9894547187874373788354455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596364791916249192236303 9894547187874373788354455)
        ·
          refine ⟨14841820781811560682531683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894547187874373788354455 14841820781811560682531683)
          ·
            refine ⟨22262731172717341023797525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14841820781811560682531683 22262731172717341023797525)
            ·
              refine ⟨1043565523721125360490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22262731172717341023797525 1043565523721125360490509)
              ·
                refine ⟨391337071395422010183941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043565523721125360490509 391337071395422010183941)
                ·
                  refine ⟨73375700886641626909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391337071395422010183941 73375700886641626909489)
                  ·
                    rfl

theorem cell22_643044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_643044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643044 prefixEnd_643044 := by exact prefixLift 643044
  have htrace : WordTrace (prefixWord ++ tailWord_643044) baseStart_643044 baseEnd_643044 := by
    simpa [prefixWord, tailWord_643044, baseEnd_643044] using wordTrace_append hprefix tailTrace_643044
  have hstable : (prefixWord ++ tailWord_643044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643044).length < 2 ^ (prefixWord ++ tailWord_643044).sum := by decide
  have hdescent : baseEnd_643044 < baseStart_643044 := by decide
  rcases family_descends (prefixWord ++ tailWord_643044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643055 : List Nat := [1, 1, 2, 1, 4, 2, 11]
def baseStart_643055 : Nat := 118140960795 + 643055 * 2 ^ 59
def prefixEnd_643055 : Nat := 4983230072969 + 3 ^ 40 * 643055 * 2
def baseEnd_643055 : Nat := 8152995117952759951979

theorem tailTrace_643055 : CollatzResearch.WordTrace tailWord_643055 prefixEnd_643055 8152995117952759951979 := by
  unfold tailWord_643055
  simp only [CollatzResearch.WordTrace]
  refine ⟨23454142685329034895490619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15636095123552689930327079 23454142685329034895490619)
  ·
    refine ⟨35181214027993552343235929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23454142685329034895490619 35181214027993552343235929)
    ·
      refine ⟨26385910520995164257426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35181214027993552343235929 26385910520995164257426947)
      ·
        refine ⟨39578865781492746386140421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385910520995164257426947 39578865781492746386140421)
        ·
          refine ⟨7421037334029889947401329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39578865781492746386140421 7421037334029889947401329)
          ·
            refine ⟨5565778000522417460550997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7421037334029889947401329 5565778000522417460550997)
            ·
              refine ⟨8152995117952759951979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5565778000522417460550997 8152995117952759951979)
              ·
                rfl

theorem cell22_643055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 11].length) (baseStart_643055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643055 prefixEnd_643055 := by exact prefixLift 643055
  have htrace : WordTrace (prefixWord ++ tailWord_643055) baseStart_643055 baseEnd_643055 := by
    simpa [prefixWord, tailWord_643055, baseEnd_643055] using wordTrace_append hprefix tailTrace_643055
  have hstable : (prefixWord ++ tailWord_643055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643055).length < 2 ^ (prefixWord ++ tailWord_643055).sum := by decide
  have hdescent : baseEnd_643055 < baseStart_643055 := by decide
  rcases family_descends (prefixWord ++ tailWord_643055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643121 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_643121 : Nat := 118140960795 + 643121 * 2 ^ 59
def prefixEnd_643121 : Nat := 4983230072969 + 3 ^ 40 * 643121 * 2
def baseEnd_643121 : Nat := 220153461333522346553231

theorem tailTrace_643121 : CollatzResearch.WordTrace tailWord_643121 prefixEnd_643121 220153461333522346553231 := by
  unfold tailWord_643121
  simp only [CollatzResearch.WordTrace]
  refine ⟨23456549903089928167393217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15637699935393285444928811 23456549903089928167393217)
  ·
    refine ⟨17592412427317446125544913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23456549903089928167393217 17592412427317446125544913)
    ·
      refine ⟨13194309320488084594158685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17592412427317446125544913 13194309320488084594158685)
      ·
        refine ⟨4947865995183031722809507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13194309320488084594158685 4947865995183031722809507)
        ·
          refine ⟨7421798992774547584214261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947865995183031722809507 7421798992774547584214261)
          ·
            refine ⟨695793655572613836020087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7421798992774547584214261 695793655572613836020087)
            ·
              refine ⟨1043690483358920754030131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695793655572613836020087 1043690483358920754030131)
              ·
                refine ⟨1565535725038381131045197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043690483358920754030131 1565535725038381131045197)
                ·
                  refine ⟨587075896889392924141949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1565535725038381131045197 587075896889392924141949)
                  ·
                    refine ⟨220153461333522346553231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587075896889392924141949 220153461333522346553231)
                    ·
                      rfl

theorem cell22_643121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_643121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643121 prefixEnd_643121 := by exact prefixLift 643121
  have htrace : WordTrace (prefixWord ++ tailWord_643121) baseStart_643121 baseEnd_643121 := by
    simpa [prefixWord, tailWord_643121, baseEnd_643121] using wordTrace_append hprefix tailTrace_643121
  have hstable : (prefixWord ++ tailWord_643121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643121).length < 2 ^ (prefixWord ++ tailWord_643121).sum := by decide
  have hdescent : baseEnd_643121 < baseStart_643121 := by decide
  rcases family_descends (prefixWord ++ tailWord_643121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643132 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_643132 : Nat := 118140960795 + 643132 * 2 ^ 59
def prefixEnd_643132 : Nat := 4983230072969 + 3 ^ 40 * 643132 * 2
def baseEnd_643132 : Nat := 220157226858321984528197

theorem tailTrace_643132 : CollatzResearch.WordTrace tailWord_643132 prefixEnd_643132 220157226858321984528197 := by
  unfold tailWord_643132
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728475553025038523021825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15637967404033384697362433 11728475553025038523021825)
  ·
    refine ⟨8796356664768778892266369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11728475553025038523021825 8796356664768778892266369)
    ·
      refine ⟨6597267498576584169199777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8796356664768778892266369 6597267498576584169199777)
      ·
        refine ⟨4947950623932438126899833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6597267498576584169199777 4947950623932438126899833)
        ·
          refine ⟨3710962967949328595174875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4947950623932438126899833 3710962967949328595174875)
          ·
            refine ⟨5566444451923992892762313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710962967949328595174875 5566444451923992892762313)
            ·
              refine ⟨4174833338942994669571735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566444451923992892762313 4174833338942994669571735)
              ·
                refine ⟨6262250008414492004357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174833338942994669571735 6262250008414492004357603)
                ·
                  refine ⟨9393375012621738006536405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6262250008414492004357603 9393375012621738006536405)
                  ·
                    refine ⟨220157226858321984528197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9393375012621738006536405 220157226858321984528197)
                    ·
                      rfl

theorem cell22_643132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_643132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643132 prefixEnd_643132 := by exact prefixLift 643132
  have htrace : WordTrace (prefixWord ++ tailWord_643132) baseStart_643132 baseEnd_643132 := by
    simpa [prefixWord, tailWord_643132, baseEnd_643132] using wordTrace_append hprefix tailTrace_643132
  have hstable : (prefixWord ++ tailWord_643132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643132).length < 2 ^ (prefixWord ++ tailWord_643132).sum := by decide
  have hdescent : baseEnd_643132 < baseStart_643132 := by decide
  rcases family_descends (prefixWord ++ tailWord_643132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643147 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_643147 : Nat := 118140960795 + 643147 * 2 ^ 59
def prefixEnd_643147 : Nat := 4983230072969 + 3 ^ 40 * 643147 * 2
def baseEnd_643147 : Nat := 220162361664866945403151

theorem tailTrace_643147 : CollatzResearch.WordTrace tailWord_643147 prefixEnd_643147 220162361664866945403151 := by
  unfold tailWord_643147
  simp only [CollatzResearch.WordTrace]
  refine ⟨23457498200995734607839695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15638332133997156405226463 23457498200995734607839695)
  ·
    refine ⟨35186247301493601911759543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23457498200995734607839695 35186247301493601911759543)
    ·
      refine ⟨52779370952240402867639315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35186247301493601911759543 52779370952240402867639315)
      ·
        refine ⟨79169056428360604301458973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52779370952240402867639315 79169056428360604301458973)
        ·
          refine ⟨29688396160635226613047115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79169056428360604301458973 29688396160635226613047115)
          ·
            refine ⟨44532594240952839919570673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29688396160635226613047115 44532594240952839919570673)
            ·
              refine ⟨33399445680714629939678005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44532594240952839919570673 33399445680714629939678005)
              ·
                refine ⟨3131198032566996556844813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33399445680714629939678005 3131198032566996556844813)
                ·
                  refine ⟨1174199262212623708816805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3131198032566996556844813 1174199262212623708816805)
                  ·
                    refine ⟨220162361664866945403151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174199262212623708816805 220162361664866945403151)
                    ·
                      rfl

theorem cell22_643147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_643147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643147 prefixEnd_643147 := by exact prefixLift 643147
  have htrace : WordTrace (prefixWord ++ tailWord_643147) baseStart_643147 baseEnd_643147 := by
    simpa [prefixWord, tailWord_643147, baseEnd_643147] using wordTrace_append hprefix tailTrace_643147
  have hstable : (prefixWord ++ tailWord_643147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643147).length < 2 ^ (prefixWord ++ tailWord_643147).sum := by decide
  have hdescent : baseEnd_643147 < baseStart_643147 := by decide
  rcases family_descends (prefixWord ++ tailWord_643147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643177 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_643177 : Nat := 118140960795 + 643177 * 2 ^ 59
def prefixEnd_643177 : Nat := 4983230072969 + 3 ^ 40 * 643177 * 2
def baseEnd_643177 : Nat := 220172631277956867153059

theorem tailTrace_643177 : CollatzResearch.WordTrace tailWord_643177 prefixEnd_643177 220172631277956867153059 := by
  unfold tailWord_643177
  simp only [CollatzResearch.WordTrace]
  refine ⟨23458592390887049731431785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15639061593924699820954523 23458592390887049731431785)
  ·
    refine ⟨17593944293165287298573839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23458592390887049731431785 17593944293165287298573839)
    ·
      refine ⟨26390916439747930947860759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17593944293165287298573839 26390916439747930947860759)
      ·
        refine ⟨39586374659621896421791139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26390916439747930947860759 39586374659621896421791139)
        ·
          refine ⟨59379561989432844632686709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39586374659621896421791139 59379561989432844632686709)
          ·
            refine ⟨5566833936509329184314379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59379561989432844632686709 5566833936509329184314379)
            ·
              refine ⟨8350250904763993776471569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566833936509329184314379 8350250904763993776471569)
              ·
                refine ⟨6262688178572995332353677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8350250904763993776471569 6262688178572995332353677)
                ·
                  refine ⟨2348508066964873249632629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6262688178572995332353677 2348508066964873249632629)
                  ·
                    refine ⟨220172631277956867153059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2348508066964873249632629 220172631277956867153059)
                    ·
                      rfl

theorem cell22_643177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_643177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643177 prefixEnd_643177 := by exact prefixLift 643177
  have htrace : WordTrace (prefixWord ++ tailWord_643177) baseStart_643177 baseEnd_643177 := by
    simpa [prefixWord, tailWord_643177, baseEnd_643177] using wordTrace_append hprefix tailTrace_643177
  have hstable : (prefixWord ++ tailWord_643177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643177).length < 2 ^ (prefixWord ++ tailWord_643177).sum := by decide
  have hdescent : baseEnd_643177 < baseStart_643177 := by decide
  rcases family_descends (prefixWord ++ tailWord_643177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643192 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_643192 : Nat := 118140960795 + 643192 * 2 ^ 59
def prefixEnd_643192 : Nat := 4983230072969 + 3 ^ 40 * 643192 * 2
def baseEnd_643192 : Nat := 220177766084501828028013

theorem tailTrace_643192 : CollatzResearch.WordTrace tailWord_643192 prefixEnd_643192 220177766084501828028013 := by
  unfold tailWord_643192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11729569742916353646613915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15639426323888471528818553 11729569742916353646613915)
  ·
    refine ⟨17594354614374530469920873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11729569742916353646613915 17594354614374530469920873)
    ·
      refine ⟨13195765960780897852440655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17594354614374530469920873 13195765960780897852440655)
      ·
        refine ⟨19793648941171346778660983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13195765960780897852440655 19793648941171346778660983)
        ·
          refine ⟨29690473411757020167991475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19793648941171346778660983 29690473411757020167991475)
          ·
            refine ⟨44535710117635530251987213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29690473411757020167991475 44535710117635530251987213)
            ·
              refine ⟨16700891294113323844495205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44535710117635530251987213 16700891294113323844495205)
              ·
                refine ⟨3131417117646248220842851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16700891294113323844495205 3131417117646248220842851)
                ·
                  refine ⟨4697125676469372331264277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131417117646248220842851 4697125676469372331264277)
                  ·
                    refine ⟨220177766084501828028013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4697125676469372331264277 220177766084501828028013)
                    ·
                      rfl

theorem cell22_643192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_643192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643192 prefixEnd_643192 := by exact prefixLift 643192
  have htrace : WordTrace (prefixWord ++ tailWord_643192) baseStart_643192 baseEnd_643192 := by
    simpa [prefixWord, tailWord_643192, baseEnd_643192] using wordTrace_append hprefix tailTrace_643192
  have hstable : (prefixWord ++ tailWord_643192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643192).length < 2 ^ (prefixWord ++ tailWord_643192).sum := by decide
  have hdescent : baseEnd_643192 < baseStart_643192 := by decide
  rcases family_descends (prefixWord ++ tailWord_643192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643207 : List Nat := [1, 1, 4, 2, 1, 1, 2, 10]
def baseStart_643207 : Nat := 118140960795 + 643207 * 2 ^ 59
def prefixEnd_643207 : Nat := 4983230072969 + 3 ^ 40 * 643207 * 2
def baseEnd_643207 : Nat := 24464766765671865433663

theorem tailTrace_643207 : CollatzResearch.WordTrace tailWord_643207 prefixEnd_643207 24464766765671865433663 := by
  unfold tailWord_643207
  simp only [CollatzResearch.WordTrace]
  refine ⟨23459686580778364855023875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15639791053852243236682583 23459686580778364855023875)
  ·
    refine ⟨35189529871167547282535813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23459686580778364855023875 35189529871167547282535813)
    ·
      refine ⟨6598036850843915115475465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35189529871167547282535813 6598036850843915115475465)
      ·
        refine ⟨4948527638132936336606599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6598036850843915115475465 4948527638132936336606599)
        ·
          refine ⟨7422791457199404504909899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948527638132936336606599 7422791457199404504909899)
          ·
            refine ⟨11134187185799106757364849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7422791457199404504909899 11134187185799106757364849)
            ·
              refine ⟨8350640389349330068023637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11134187185799106757364849 8350640389349330068023637)
              ·
                refine ⟨24464766765671865433663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8350640389349330068023637 24464766765671865433663)
                ·
                  rfl

theorem cell22_643207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 10].length) (baseStart_643207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643207 prefixEnd_643207 := by exact prefixLift 643207
  have htrace : WordTrace (prefixWord ++ tailWord_643207) baseStart_643207 baseEnd_643207 := by
    simpa [prefixWord, tailWord_643207, baseEnd_643207] using wordTrace_append hprefix tailTrace_643207
  have hstable : (prefixWord ++ tailWord_643207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643207).length < 2 ^ (prefixWord ++ tailWord_643207).sum := by decide
  have hdescent : baseEnd_643207 < baseStart_643207 := by decide
  rcases family_descends (prefixWord ++ tailWord_643207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643224 : List Nat := [2, 1, 2, 4, 3, 1, 9]
def baseStart_643224 : Nat := 118140960795 + 643224 * 2 ^ 59
def prefixEnd_643224 : Nat := 4983230072969 + 3 ^ 40 * 643224 * 2
def baseEnd_643224 : Nat := 8155137790313496712145

theorem tailTrace_643224 : CollatzResearch.WordTrace tailWord_643224 prefixEnd_643224 8155137790313496712145 := by
  unfold tailWord_643224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730153310858388379196363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15640204414477851172261817 11730153310858388379196363)
  ·
    refine ⟨17595229966287582568794545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11730153310858388379196363 17595229966287582568794545)
    ·
      refine ⟨13196422474715686926595909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17595229966287582568794545 13196422474715686926595909)
      ·
        refine ⟨2474329214009191298736733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13196422474715686926595909 2474329214009191298736733)
        ·
          refine ⟨927873455253446737026275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2474329214009191298736733 927873455253446737026275)
          ·
            refine ⟨1391810182880170105539413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927873455253446737026275 1391810182880170105539413)
            ·
              refine ⟨8155137790313496712145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1391810182880170105539413 8155137790313496712145)
              ·
                rfl

theorem cell22_643224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 9].length) (baseStart_643224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643224 prefixEnd_643224 := by exact prefixLift 643224
  have htrace : WordTrace (prefixWord ++ tailWord_643224) baseStart_643224 baseEnd_643224 := by
    simpa [prefixWord, tailWord_643224, baseEnd_643224] using wordTrace_append hprefix tailTrace_643224
  have hstable : (prefixWord ++ tailWord_643224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643224).length < 2 ^ (prefixWord ++ tailWord_643224).sum := by decide
  have hdescent : baseEnd_643224 < baseStart_643224 := by decide
  rcases family_descends (prefixWord ++ tailWord_643224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643245 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_643245 : Nat := 118140960795 + 643245 * 2 ^ 59
def prefixEnd_643245 : Nat := 4983230072969 + 3 ^ 40 * 643245 * 2
def baseEnd_643245 : Nat := 220195909067627356452851

theorem tailTrace_643245 : CollatzResearch.WordTrace tailWord_643245 prefixEnd_643245 220195909067627356452851 := by
  unfold tailWord_643245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461072554640697344907189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15640715036427131563271459 23461072554640697344907189)
  ·
    refine ⟨2199475551997565376085049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23461072554640697344907189 2199475551997565376085049)
    ·
      refine ⟨1649606663998174032063787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2199475551997565376085049 1649606663998174032063787)
      ·
        refine ⟨2474409995997261048095681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649606663998174032063787 2474409995997261048095681)
        ·
          refine ⟨1855807496997945786071761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2474409995997261048095681 1855807496997945786071761)
          ·
            refine ⟨1391855622748459339553821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855807496997945786071761 1391855622748459339553821)
            ·
              refine ⟨521945858530672252332683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1391855622748459339553821 521945858530672252332683)
              ·
                refine ⟨782918787796008378499025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521945858530672252332683 782918787796008378499025)
                ·
                  refine ⟨587189090847006283874269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782918787796008378499025 587189090847006283874269)
                  ·
                    refine ⟨220195909067627356452851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587189090847006283874269 220195909067627356452851)
                    ·
                      rfl

theorem cell22_643245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_643245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643245 prefixEnd_643245 := by exact prefixLift 643245
  have htrace : WordTrace (prefixWord ++ tailWord_643245) baseStart_643245 baseEnd_643245 := by
    simpa [prefixWord, tailWord_643245, baseEnd_643245] using wordTrace_append hprefix tailTrace_643245
  have hstable : (prefixWord ++ tailWord_643245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643245).length < 2 ^ (prefixWord ++ tailWord_643245).sum := by decide
  have hdescent : baseEnd_643245 < baseStart_643245 := by decide
  rcases family_descends (prefixWord ++ tailWord_643245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643303 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 5]
def baseStart_643303 : Nat := 118140960795 + 643303 * 2 ^ 59
def prefixEnd_643303 : Nat := 4983230072969 + 3 ^ 40 * 643303 * 2
def baseEnd_643303 : Nat := 73405254550978179500891

theorem tailTrace_643303 : CollatzResearch.WordTrace tailWord_643303 prefixEnd_643303 73405254550978179500891 := by
  unfold tailWord_643303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463187988430573250518563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15642125325620382167012375 23463187988430573250518563)
  ·
    refine ⟨35194781982645859875777845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23463187988430573250518563 35194781982645859875777845)
    ·
      refine ⟨3299510810873049363354173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35194781982645859875777845 3299510810873049363354173)
      ·
        refine ⟨1237316554077393511257815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3299510810873049363354173 1237316554077393511257815)
        ·
          refine ⟨1855974831116090266886723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237316554077393511257815 1855974831116090266886723)
          ·
            refine ⟨2783962246674135400330085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855974831116090266886723 2783962246674135400330085)
            ·
              refine ⟨521992921251400387561891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2783962246674135400330085 521992921251400387561891)
              ·
                refine ⟨782989381877100581342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521992921251400387561891 782989381877100581342837)
                ·
                  refine ⟨73405254550978179500891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 782989381877100581342837 73405254550978179500891)
                  ·
                    rfl

theorem cell22_643303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 5].length) (baseStart_643303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643303 prefixEnd_643303 := by exact prefixLift 643303
  have htrace : WordTrace (prefixWord ++ tailWord_643303) baseStart_643303 baseEnd_643303 := by
    simpa [prefixWord, tailWord_643303, baseEnd_643303] using wordTrace_append hprefix tailTrace_643303
  have hstable : (prefixWord ++ tailWord_643303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643303).length < 2 ^ (prefixWord ++ tailWord_643303).sum := by decide
  have hdescent : baseEnd_643303 < baseStart_643303 := by decide
  rcases family_descends (prefixWord ++ tailWord_643303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643331 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 4]
def baseStart_643331 : Nat := 118140960795 + 643331 * 2 ^ 59
def prefixEnd_643331 : Nat := 4983230072969 + 3 ^ 40 * 643331 * 2
def baseEnd_643331 : Nat := 73408449541717266267529

theorem tailTrace_643331 : CollatzResearch.WordTrace tailWord_643331 prefixEnd_643331 73408449541717266267529 := by
  unfold tailWord_643331
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464209232329134032537847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15642806154886089355025231 23464209232329134032537847)
  ·
    refine ⟨35196313848493701048806771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23464209232329134032537847 35196313848493701048806771)
    ·
      refine ⟨52794470772740551573210157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35196313848493701048806771 52794470772740551573210157)
      ·
        refine ⟨19797926539777706839953809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52794470772740551573210157 19797926539777706839953809)
        ·
          refine ⟨14848444904833280129965357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19797926539777706839953809 14848444904833280129965357)
          ·
            refine ⟨5568166839312480048737009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14848444904833280129965357 5568166839312480048737009)
            ·
              refine ⟨4176125129484360036552757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568166839312480048737009 4176125129484360036552757)
              ·
                refine ⟨391511730889158753426821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4176125129484360036552757 391511730889158753426821)
                ·
                  refine ⟨73408449541717266267529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391511730889158753426821 73408449541717266267529)
                  ·
                    rfl

theorem cell22_643331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 4].length) (baseStart_643331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643331 prefixEnd_643331 := by exact prefixLift 643331
  have htrace : WordTrace (prefixWord ++ tailWord_643331) baseStart_643331 baseEnd_643331 := by
    simpa [prefixWord, tailWord_643331, baseEnd_643331] using wordTrace_append hprefix tailTrace_643331
  have hstable : (prefixWord ++ tailWord_643331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643331).length < 2 ^ (prefixWord ++ tailWord_643331).sum := by decide
  have hdescent : baseEnd_643331 < baseStart_643331 := by decide
  rcases family_descends (prefixWord ++ tailWord_643331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643391 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 5, 3]
def baseStart_643391 : Nat := 118140960795 + 643391 * 2 ^ 59
def prefixEnd_643391 : Nat := 4983230072969 + 3 ^ 40 * 643391 * 2
def baseEnd_643391 : Nat := 220245887851331642302403

theorem tailTrace_643391 : CollatzResearch.WordTrace tailWord_643391 prefixEnd_643391 220245887851331642302403 := by
  unfold tailWord_643391
  simp only [CollatzResearch.WordTrace]
  refine ⟨23466397612111764279722027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15644265074741176186481351 23466397612111764279722027)
  ·
    refine ⟨35199596418167646419583041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23466397612111764279722027 35199596418167646419583041)
    ·
      refine ⟨26399697313625734814687281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35199596418167646419583041 26399697313625734814687281)
      ·
        refine ⟨19799772985219301111015461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26399697313625734814687281 19799772985219301111015461)
        ·
          refine ⟨3712457434728618958315399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19799772985219301111015461 3712457434728618958315399)
          ·
            refine ⟨5568686152092928437473099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712457434728618958315399 5568686152092928437473099)
            ·
              refine ⟨8353029228139392656209649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568686152092928437473099 8353029228139392656209649)
              ·
                refine ⟨6264771921104544492157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8353029228139392656209649 6264771921104544492157237)
                ·
                  refine ⟨587322367603551046139741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6264771921104544492157237 587322367603551046139741)
                  ·
                    refine ⟨220245887851331642302403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587322367603551046139741 220245887851331642302403)
                    ·
                      rfl

theorem cell22_643391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_643391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643391 prefixEnd_643391 := by exact prefixLift 643391
  have htrace : WordTrace (prefixWord ++ tailWord_643391) baseStart_643391 baseEnd_643391 := by
    simpa [prefixWord, tailWord_643391, baseEnd_643391] using wordTrace_append hprefix tailTrace_643391
  have hstable : (prefixWord ++ tailWord_643391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643391).length < 2 ^ (prefixWord ++ tailWord_643391).sum := by decide
  have hdescent : baseEnd_643391 < baseStart_643391 := by decide
  rcases family_descends (prefixWord ++ tailWord_643391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643408 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_643408 : Nat := 118140960795 + 643408 * 2 ^ 59
def prefixEnd_643408 : Nat := 4983230072969 + 3 ^ 40 * 643408 * 2
def baseEnd_643408 : Nat := 220251707298749264627351

theorem tailTrace_643408 : CollatzResearch.WordTrace tailWord_643408 prefixEnd_643408 220251707298749264627351 := by
  unfold tailWord_643408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733508826525088091545439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15644678435366784122060585 11733508826525088091545439)
  ·
    refine ⟨17600263239787632137318159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11733508826525088091545439 17600263239787632137318159)
    ·
      refine ⟨26400394859681448205977239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17600263239787632137318159 26400394859681448205977239)
      ·
        refine ⟨39600592289522172308965859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26400394859681448205977239 39600592289522172308965859)
        ·
          refine ⟨59400888434283258463448789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39600592289522172308965859 59400888434283258463448789)
          ·
            refine ⟨1392208322678513870237081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59400888434283258463448789 1392208322678513870237081)
            ·
              refine ⟨1044156242008885402677811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392208322678513870237081 1044156242008885402677811)
              ·
                refine ⟨1566234363013328104016717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044156242008885402677811 1566234363013328104016717)
                ·
                  refine ⟨587337886129998039006269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1566234363013328104016717 587337886129998039006269)
                  ·
                    refine ⟨220251707298749264627351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587337886129998039006269 220251707298749264627351)
                    ·
                      rfl

theorem cell22_643408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_643408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643408 prefixEnd_643408 := by exact prefixLift 643408
  have htrace : WordTrace (prefixWord ++ tailWord_643408) baseStart_643408 baseEnd_643408 := by
    simpa [prefixWord, tailWord_643408, baseEnd_643408] using wordTrace_append hprefix tailTrace_643408
  have hstable : (prefixWord ++ tailWord_643408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643408).length < 2 ^ (prefixWord ++ tailWord_643408).sum := by decide
  have hdescent : baseEnd_643408 < baseStart_643408 := by decide
  rcases family_descends (prefixWord ++ tailWord_643408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643442 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_643442 : Nat := 118140960795 + 643442 * 2 ^ 59
def prefixEnd_643442 : Nat := 4983230072969 + 3 ^ 40 * 643442 * 2
def baseEnd_643442 : Nat := 220263346193584509277247

theorem tailTrace_643442 : CollatzResearch.WordTrace tailWord_643442 prefixEnd_643442 220263346193584509277247 := by
  unfold tailWord_643442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867064433731749997457145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15645505156617999993219053 5867064433731749997457145)
  ·
    refine ⟨4400298325298812498092859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5867064433731749997457145 4400298325298812498092859)
    ·
      refine ⟨6600447487948218747139289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400298325298812498092859 6600447487948218747139289)
      ·
        refine ⟨4950335615961164060354467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6600447487948218747139289 4950335615961164060354467)
        ·
          refine ⟨7425503423941746090531701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950335615961164060354467 7425503423941746090531701)
          ·
            refine ⟨696140945994538695987347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7425503423941746090531701 696140945994538695987347)
            ·
              refine ⟨1044211418991808043981021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696140945994538695987347 1044211418991808043981021)
              ·
                refine ⟨391579282121928016492883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1044211418991808043981021 391579282121928016492883)
                ·
                  refine ⟨587368923182892024739325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391579282121928016492883 587368923182892024739325)
                  ·
                    refine ⟨220263346193584509277247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587368923182892024739325 220263346193584509277247)
                    ·
                      rfl

theorem cell22_643442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_643442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643442 prefixEnd_643442 := by exact prefixLift 643442
  have htrace : WordTrace (prefixWord ++ tailWord_643442) baseStart_643442 baseEnd_643442 := by
    simpa [prefixWord, tailWord_643442, baseEnd_643442] using wordTrace_append hprefix tailTrace_643442
  have hstable : (prefixWord ++ tailWord_643442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643442).length < 2 ^ (prefixWord ++ tailWord_643442).sum := by decide
  have hdescent : baseEnd_643442 < baseStart_643442 := by decide
  rcases family_descends (prefixWord ++ tailWord_643442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643481 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_643481 : Nat := 118140960795 + 643481 * 2 ^ 59
def prefixEnd_643481 : Nat := 4983230072969 + 3 ^ 40 * 643481 * 2
def baseEnd_643481 : Nat := 220276696690601407552127

theorem tailTrace_643481 : CollatzResearch.WordTrace tailWord_643481 prefixEnd_643481 220276696690601407552127 := by
  unfold tailWord_643481
  simp only [CollatzResearch.WordTrace]
  refine ⟨23469680181785709650498297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15646453454523806433665531 23469680181785709650498297)
  ·
    refine ⟨17602260136339282237873723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23469680181785709650498297 17602260136339282237873723)
    ·
      refine ⟨26403390204508923356810585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17602260136339282237873723 26403390204508923356810585)
      ·
        refine ⟨19802542653381692517607939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26403390204508923356810585 19802542653381692517607939)
        ·
          refine ⟨29703813980072538776411909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19802542653381692517607939 29703813980072538776411909)
          ·
            refine ⟨5569465121263601020577233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29703813980072538776411909 5569465121263601020577233)
            ·
              refine ⟨4177098840947700765432925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569465121263601020577233 4177098840947700765432925)
              ·
                refine ⟨1566412065355387787037347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4177098840947700765432925 1566412065355387787037347)
                ·
                  refine ⟨2349618098033081680556021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566412065355387787037347 2349618098033081680556021)
                  ·
                    refine ⟨220276696690601407552127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2349618098033081680556021 220276696690601407552127)
                    ·
                      rfl

theorem cell22_643481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_643481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643481 prefixEnd_643481 := by exact prefixLift 643481
  have htrace : WordTrace (prefixWord ++ tailWord_643481) baseStart_643481 baseEnd_643481 := by
    simpa [prefixWord, tailWord_643481, baseEnd_643481] using wordTrace_append hprefix tailTrace_643481
  have hstable : (prefixWord ++ tailWord_643481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643481).length < 2 ^ (prefixWord ++ tailWord_643481).sum := by decide
  have hdescent : baseEnd_643481 < baseStart_643481 := by decide
  rcases family_descends (prefixWord ++ tailWord_643481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643513 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_643513 : Nat := 118140960795 + 643513 * 2 ^ 59
def prefixEnd_643513 : Nat := 4983230072969 + 3 ^ 40 * 643513 * 2
def baseEnd_643513 : Nat := 220287650944563990752029

theorem tailTrace_643513 : CollatzResearch.WordTrace tailWord_643513 prefixEnd_643513 220287650944563990752029 := by
  unfold tailWord_643513
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470847317669779115663193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15647231545113186077108795 23470847317669779115663193)
  ·
    refine ⟨17603135488252334336747395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23470847317669779115663193 17603135488252334336747395)
    ·
      refine ⟨26404703232378501505121093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17603135488252334336747395 26404703232378501505121093)
      ·
        refine ⟨4950881856070969032210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26404703232378501505121093 4950881856070969032210205)
        ·
          refine ⟨1856580696026613387078827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4950881856070969032210205 1856580696026613387078827)
          ·
            refine ⟨2784871044039920080618241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856580696026613387078827 2784871044039920080618241)
            ·
              refine ⟨2088653283029940060463681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784871044039920080618241 2088653283029940060463681)
              ·
                refine ⟨1566489962272455045347761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088653283029940060463681 1566489962272455045347761)
                ·
                  refine ⟨1174867471704341284010821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566489962272455045347761 1174867471704341284010821)
                  ·
                    refine ⟨220287650944563990752029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174867471704341284010821 220287650944563990752029)
                    ·
                      rfl

theorem cell22_643513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_643513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643513 prefixEnd_643513 := by exact prefixLift 643513
  have htrace : WordTrace (prefixWord ++ tailWord_643513) baseStart_643513 baseEnd_643513 := by
    simpa [prefixWord, tailWord_643513, baseEnd_643513] using wordTrace_append hprefix tailTrace_643513
  have hstable : (prefixWord ++ tailWord_643513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643513).length < 2 ^ (prefixWord ++ tailWord_643513).sum := by decide
  have hdescent : baseEnd_643513 < baseStart_643513 := by decide
  rcases family_descends (prefixWord ++ tailWord_643513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643517 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 4]
def baseStart_643517 : Nat := 118140960795 + 643517 * 2 ^ 59
def prefixEnd_643517 : Nat := 4983230072969 + 3 ^ 40 * 643517 * 2
def baseEnd_643517 : Nat := 73429673408769771217339

theorem tailTrace_643517 : CollatzResearch.WordTrace tailWord_643517 prefixEnd_643517 73429673408769771217339 := by
  unfold tailWord_643517
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470993209655287798808805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15647328806436858532539203 23470993209655287798808805)
  ·
    refine ⟨4400811226810366462276651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23470993209655287798808805 4400811226810366462276651)
    ·
      refine ⟨6601216840215549693414977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400811226810366462276651 6601216840215549693414977)
      ·
        refine ⟨4950912630161662270061233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6601216840215549693414977 4950912630161662270061233)
        ·
          refine ⟨3713184472621246702545925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4950912630161662270061233 3713184472621246702545925)
          ·
            refine ⟨696222088616483756727361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3713184472621246702545925 696222088616483756727361)
            ·
              refine ⟨522166566462362817545521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696222088616483756727361 522166566462362817545521)
              ·
                refine ⟨391624924846772113159141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522166566462362817545521 391624924846772113159141)
                ·
                  refine ⟨73429673408769771217339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391624924846772113159141 73429673408769771217339)
                  ·
                    rfl

theorem cell22_643517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_643517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643517 prefixEnd_643517 := by exact prefixLift 643517
  have htrace : WordTrace (prefixWord ++ tailWord_643517) baseStart_643517 baseEnd_643517 := by
    simpa [prefixWord, tailWord_643517, baseEnd_643517] using wordTrace_append hprefix tailTrace_643517
  have hstable : (prefixWord ++ tailWord_643517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643517).length < 2 ^ (prefixWord ++ tailWord_643517).sum := by decide
  have hdescent : baseEnd_643517 < baseStart_643517 := by decide
  rcases family_descends (prefixWord ++ tailWord_643517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643528 : List Nat := [2, 1, 3, 1, 3, 4, 1, 7]
def baseStart_643528 : Nat := 118140960795 + 643528 * 2 ^ 59
def prefixEnd_643528 : Nat := 4983230072969 + 3 ^ 40 * 643528 * 2
def baseEnd_643528 : Nat := 24476976194567661291887

theorem tailTrace_643528 : CollatzResearch.WordTrace tailWord_643528 prefixEnd_643528 24476976194567661291887 := by
  unfold tailWord_643528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735697206307718338729619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15647596275076957784972825 11735697206307718338729619)
  ·
    refine ⟨17603545809461577508094429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11735697206307718338729619 17603545809461577508094429)
    ·
      refine ⟨6601329678548091565535411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17603545809461577508094429 6601329678548091565535411)
      ·
        refine ⟨9901994517822137348303117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601329678548091565535411 9901994517822137348303117)
        ·
          refine ⟨3713247944183301505613669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9901994517822137348303117 3713247944183301505613669)
          ·
            refine ⟨696233989534369032302563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3713247944183301505613669 696233989534369032302563)
            ·
              refine ⟨1044350984301553548453845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696233989534369032302563 1044350984301553548453845)
              ·
                refine ⟨24476976194567661291887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1044350984301553548453845 24476976194567661291887)
                ·
                  rfl

theorem cell22_643528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_643528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643528 prefixEnd_643528 := by exact prefixLift 643528
  have htrace : WordTrace (prefixWord ++ tailWord_643528) baseStart_643528 baseEnd_643528 := by
    simpa [prefixWord, tailWord_643528, baseEnd_643528] using wordTrace_append hprefix tailTrace_643528
  have hstable : (prefixWord ++ tailWord_643528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643528).length < 2 ^ (prefixWord ++ tailWord_643528).sum := by decide
  have hdescent : baseEnd_643528 < baseStart_643528 := by decide
  rcases family_descends (prefixWord ++ tailWord_643528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643571 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_643571 : Nat := 118140960795 + 643571 * 2 ^ 59
def prefixEnd_643571 : Nat := 4983230072969 + 3 ^ 40 * 643571 * 2
def baseEnd_643571 : Nat := 220307505529871172801851

theorem tailTrace_643571 : CollatzResearch.WordTrace tailWord_643571 prefixEnd_643571 220307505529871172801851 := by
  unfold tailWord_643571
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472962751459655021274567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15648641834306436680849711 23472962751459655021274567)
  ·
    refine ⟨35209444127189482531911851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23472962751459655021274567 35209444127189482531911851)
    ·
      refine ⟨52814166190784223797867777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35209444127189482531911851 52814166190784223797867777)
      ·
        refine ⟨39610624643088167848400833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52814166190784223797867777 39610624643088167848400833)
        ·
          refine ⟨29707968482316125886300625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39610624643088167848400833 29707968482316125886300625)
          ·
            refine ⟨22280976361737094414725469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29707968482316125886300625 22280976361737094414725469)
            ·
              refine ⟨8355366135651410405522051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22280976361737094414725469 8355366135651410405522051)
              ·
                refine ⟨12533049203477115608283077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355366135651410405522051 12533049203477115608283077)
                ·
                  refine ⟨2349946725651959176553077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12533049203477115608283077 2349946725651959176553077)
                  ·
                    refine ⟨220307505529871172801851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2349946725651959176553077 220307505529871172801851)
                    ·
                      rfl

theorem cell22_643571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_643571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643571 prefixEnd_643571 := by exact prefixLift 643571
  have htrace : WordTrace (prefixWord ++ tailWord_643571) baseStart_643571 baseEnd_643571 := by
    simpa [prefixWord, tailWord_643571, baseEnd_643571] using wordTrace_append hprefix tailTrace_643571
  have hstable : (prefixWord ++ tailWord_643571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643571).length < 2 ^ (prefixWord ++ tailWord_643571).sum := by decide
  have hdescent : baseEnd_643571 < baseStart_643571 := by decide
  rcases family_descends (prefixWord ++ tailWord_643571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643601 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 8]
def baseStart_643601 : Nat := 118140960795 + 643601 * 2 ^ 59
def prefixEnd_643601 : Nat := 4983230072969 + 3 ^ 40 * 643601 * 2
def baseEnd_643601 : Nat := 73439258380987031517253

theorem tailTrace_643601 : CollatzResearch.WordTrace tailWord_643601 prefixEnd_643601 73439258380987031517253 := by
  unfold tailWord_643601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23474056941350970144866657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15649371294233980096577771 23474056941350970144866657)
  ·
    refine ⟨17605542706013227608649993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23474056941350970144866657 17605542706013227608649993)
    ·
      refine ⟨13204157029509920706487495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17605542706013227608649993 13204157029509920706487495)
      ·
        refine ⟨19806235544264881059731243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13204157029509920706487495 19806235544264881059731243)
        ·
          refine ⟨29709353316397321589596865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19806235544264881059731243 29709353316397321589596865)
          ·
            refine ⟨22282014987297991192197649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29709353316397321589596865 22282014987297991192197649)
            ·
              refine ⟨16711511240473493394148237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22282014987297991192197649 16711511240473493394148237)
              ·
                refine ⟨6266816715177560022805589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16711511240473493394148237 6266816715177560022805589)
                ·
                  refine ⟨73439258380987031517253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6266816715177560022805589 73439258380987031517253)
                  ·
                    rfl

theorem cell22_643601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_643601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643601 prefixEnd_643601 := by exact prefixLift 643601
  have htrace : WordTrace (prefixWord ++ tailWord_643601) baseStart_643601 baseEnd_643601 := by
    simpa [prefixWord, tailWord_643601, baseEnd_643601] using wordTrace_append hprefix tailTrace_643601
  have hstable : (prefixWord ++ tailWord_643601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643601).length < 2 ^ (prefixWord ++ tailWord_643601).sum := by decide
  have hdescent : baseEnd_643601 < baseStart_643601 := by decide
  rcases family_descends (prefixWord ++ tailWord_643601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643631 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_643631 : Nat := 118140960795 + 643631 * 2 ^ 59
def prefixEnd_643631 : Nat := 4983230072969 + 3 ^ 40 * 643631 * 2
def baseEnd_643631 : Nat := 220328044756051016301667

theorem tailTrace_643631 : CollatzResearch.WordTrace tailWord_643631 prefixEnd_643631 220328044756051016301667 := by
  unfold tailWord_643631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475151131242285268458747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650100754161523512305831 23475151131242285268458747)
  ·
    refine ⟨35212726696863427902688121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23475151131242285268458747 35212726696863427902688121)
    ·
      refine ⟨26409545022647570927016091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35212726696863427902688121 26409545022647570927016091)
      ·
        refine ⟨39614317533971356390524137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26409545022647570927016091 39614317533971356390524137)
        ·
          refine ⟨29710738150478517292893103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39614317533971356390524137 29710738150478517292893103)
          ·
            refine ⟨44566107225717775939339655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29710738150478517292893103 44566107225717775939339655)
            ·
              refine ⟨66849160838576663909009483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44566107225717775939339655 66849160838576663909009483)
              ·
                refine ⟨100273741257864995863514225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66849160838576663909009483 100273741257864995863514225)
                ·
                  refine ⟨75205305943398746897635669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100273741257864995863514225 75205305943398746897635669)
                  ·
                    refine ⟨220328044756051016301667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 75205305943398746897635669 220328044756051016301667)
                    ·
                      rfl

theorem cell22_643631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_643631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643631 prefixEnd_643631 := by exact prefixLift 643631
  have htrace : WordTrace (prefixWord ++ tailWord_643631) baseStart_643631 baseEnd_643631 := by
    simpa [prefixWord, tailWord_643631, baseEnd_643631] using wordTrace_append hprefix tailTrace_643631
  have hstable : (prefixWord ++ tailWord_643631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643631).length < 2 ^ (prefixWord ++ tailWord_643631).sum := by decide
  have hdescent : baseEnd_643631 < baseStart_643631 := by decide
  rcases family_descends (prefixWord ++ tailWord_643631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643654 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_643654 : Nat := 118140960795 + 643654 * 2 ^ 59
def prefixEnd_643654 : Nat := 4983230072969 + 3 ^ 40 * 643654 * 2
def baseEnd_643654 : Nat := 220335918126086622976597

theorem tailTrace_643654 : CollatzResearch.WordTrace tailWord_643654 prefixEnd_643654 220335918126086622976597 := by
  unfold tailWord_643654
  simp only [CollatzResearch.WordTrace]
  refine ⟨733624687817467506142063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15650660006772640131030677 733624687817467506142063)
  ·
    refine ⟨1100437031726201259213095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733624687817467506142063 1100437031726201259213095)
    ·
      refine ⟨1650655547589301888819643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100437031726201259213095 1650655547589301888819643)
      ·
        refine ⟨2475983321383952833229465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650655547589301888819643 2475983321383952833229465)
        ·
          refine ⟨1856987491037964624922099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475983321383952833229465 1856987491037964624922099)
          ·
            refine ⟨2785481236556946937383149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856987491037964624922099 2785481236556946937383149)
            ·
              refine ⟨1044555463708855101518681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2785481236556946937383149 1044555463708855101518681)
              ·
                refine ⟨783416597781641326139011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044555463708855101518681 783416597781641326139011)
                ·
                  refine ⟨1175124896672461989208517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783416597781641326139011 1175124896672461989208517)
                  ·
                    refine ⟨220335918126086622976597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175124896672461989208517 220335918126086622976597)
                    ·
                      rfl

theorem cell22_643654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_643654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643654 prefixEnd_643654 := by exact prefixLift 643654
  have htrace : WordTrace (prefixWord ++ tailWord_643654) baseStart_643654 baseEnd_643654 := by
    simpa [prefixWord, tailWord_643654, baseEnd_643654] using wordTrace_append hprefix tailTrace_643654
  have hstable : (prefixWord ++ tailWord_643654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643654).length < 2 ^ (prefixWord ++ tailWord_643654).sum := by decide
  have hdescent : baseEnd_643654 < baseStart_643654 := by decide
  rcases family_descends (prefixWord ++ tailWord_643654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643665 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_643665 : Nat := 118140960795 + 643665 * 2 ^ 59
def prefixEnd_643665 : Nat := 4983230072969 + 3 ^ 40 * 643665 * 2
def baseEnd_643665 : Nat := 220339683650886260951563

theorem tailTrace_643665 : CollatzResearch.WordTrace tailWord_643665 prefixEnd_643665 220339683650886260951563 := by
  unfold tailWord_643665
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476391213119109075196449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650927475412739383464299 23476391213119109075196449)
  ·
    refine ⟨17607293409839331806397337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23476391213119109075196449 17607293409839331806397337)
    ·
      refine ⟨13205470057379498854798003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17607293409839331806397337 13205470057379498854798003)
      ·
        refine ⟨19808205086069248282197005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13205470057379498854798003 19808205086069248282197005)
        ·
          refine ⟨7428076907275968105823877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19808205086069248282197005 7428076907275968105823877)
          ·
            refine ⟨1392764420114244019841977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7428076907275968105823877 1392764420114244019841977)
            ·
              refine ⟨1044573315085683014881483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392764420114244019841977 1044573315085683014881483)
              ·
                refine ⟨1566859972628524522322225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044573315085683014881483 1566859972628524522322225)
                ·
                  refine ⟨1175144979471393391741669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566859972628524522322225 1175144979471393391741669)
                  ·
                    refine ⟨220339683650886260951563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175144979471393391741669 220339683650886260951563)
                    ·
                      rfl

theorem cell22_643665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_643665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643665 prefixEnd_643665 := by exact prefixLift 643665
  have htrace : WordTrace (prefixWord ++ tailWord_643665) baseStart_643665 baseEnd_643665 := by
    simpa [prefixWord, tailWord_643665, baseEnd_643665] using wordTrace_append hprefix tailTrace_643665
  have hstable : (prefixWord ++ tailWord_643665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643665).length < 2 ^ (prefixWord ++ tailWord_643665).sum := by decide
  have hdescent : baseEnd_643665 < baseStart_643665 := by decide
  rcases family_descends (prefixWord ++ tailWord_643665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643740 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_643740 : Nat := 118140960795 + 643740 * 2 ^ 59
def prefixEnd_643740 : Nat := 4983230072969 + 3 ^ 40 * 643740 * 2
def baseEnd_643740 : Nat := 220365357683611065326333

theorem tailTrace_643740 : CollatzResearch.WordTrace tailWord_643740 prefixEnd_643740 220365357683611065326333 := by
  unfold tailWord_643740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739563343923698442088337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15652751125231597922784449 11739563343923698442088337)
  ·
    refine ⟨8804672507942773831566253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11739563343923698442088337 8804672507942773831566253)
    ·
      refine ⟨3301752190478540186837345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8804672507942773831566253 3301752190478540186837345)
      ·
        refine ⟨2476314142858905140128009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301752190478540186837345 2476314142858905140128009)
        ·
          refine ⟨1857235607144178855096007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2476314142858905140128009 1857235607144178855096007)
          ·
            refine ⟨2785853410716268282644011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857235607144178855096007 2785853410716268282644011)
            ·
              refine ⟨4178780116074402423966017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785853410716268282644011 4178780116074402423966017)
              ·
                refine ⟨3134085087055801817974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178780116074402423966017 3134085087055801817974513)
                ·
                  refine ⟨2350563815291851363480885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134085087055801817974513 2350563815291851363480885)
                  ·
                    refine ⟨220365357683611065326333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2350563815291851363480885 220365357683611065326333)
                    ·
                      rfl

theorem cell22_643740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_643740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643740 prefixEnd_643740 := by exact prefixLift 643740
  have htrace : WordTrace (prefixWord ++ tailWord_643740) baseStart_643740 baseEnd_643740 := by
    simpa [prefixWord, tailWord_643740, baseEnd_643740] using wordTrace_append hprefix tailTrace_643740
  have hstable : (prefixWord ++ tailWord_643740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643740).length < 2 ^ (prefixWord ++ tailWord_643740).sum := by decide
  have hdescent : baseEnd_643740 < baseStart_643740 := by decide
  rcases family_descends (prefixWord ++ tailWord_643740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643753 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 6]
def baseStart_643753 : Nat := 118140960795 + 643753 * 2 ^ 59
def prefixEnd_643753 : Nat := 4983230072969 + 3 ^ 40 * 643753 * 2
def baseEnd_643753 : Nat := 73456602616427788250431

theorem tailTrace_643753 : CollatzResearch.WordTrace tailWord_643753 prefixEnd_643753 73456602616427788250431 := by
  unfold tailWord_643753
  simp only [CollatzResearch.WordTrace]
  refine ⟨23479600836800300104399913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15653067224533533402933275 23479600836800300104399913)
  ·
    refine ⟨17609700627600225078299935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23479600836800300104399913 17609700627600225078299935)
    ·
      refine ⟨26414550941400337617449903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17609700627600225078299935 26414550941400337617449903)
      ·
        refine ⟨39621826412100506426174855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26414550941400337617449903 39621826412100506426174855)
        ·
          refine ⟨59432739618150759639262283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39621826412100506426174855 59432739618150759639262283)
          ·
            refine ⟨89149109427226139458893425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59432739618150759639262283 89149109427226139458893425)
            ·
              refine ⟨66861832070419604594170069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89149109427226139458893425 66861832070419604594170069)
              ·
                refine ⟨1567074189150459482675861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66861832070419604594170069 1567074189150459482675861)
                ·
                  refine ⟨73456602616427788250431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1567074189150459482675861 73456602616427788250431)
                  ·
                    rfl

theorem cell22_643753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_643753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643753 prefixEnd_643753 := by exact prefixLift 643753
  have htrace : WordTrace (prefixWord ++ tailWord_643753) baseStart_643753 baseEnd_643753 := by
    simpa [prefixWord, tailWord_643753, baseEnd_643753] using wordTrace_append hprefix tailTrace_643753
  have hstable : (prefixWord ++ tailWord_643753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643753).length < 2 ^ (prefixWord ++ tailWord_643753).sum := by decide
  have hdescent : baseEnd_643753 < baseStart_643753 := by decide
  rcases family_descends (prefixWord ++ tailWord_643753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643772 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_643772 : Nat := 118140960795 + 643772 * 2 ^ 59
def prefixEnd_643772 : Nat := 4983230072969 + 3 ^ 40 * 643772 * 2
def baseEnd_643772 : Nat := 220376311937573648526235

theorem tailTrace_643772 : CollatzResearch.WordTrace tailWord_643772 prefixEnd_643772 220376311937573648526235 := by
  unfold tailWord_643772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740146911865733174670785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15653529215820977566227713 11740146911865733174670785)
  ·
    refine ⟨8805110183899299881003089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11740146911865733174670785 8805110183899299881003089)
    ·
      refine ⟨6603832637924474910752317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8805110183899299881003089 6603832637924474910752317)
      ·
        refine ⟨2476437239221678091532119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6603832637924474910752317 2476437239221678091532119)
        ·
          refine ⟨3714655858832517137298179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476437239221678091532119 3714655858832517137298179)
          ·
            refine ⟨5571983788248775705947269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714655858832517137298179 5571983788248775705947269)
            ·
              refine ⟨1044746960296645444865113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5571983788248775705947269 1044746960296645444865113)
              ·
                refine ⟨783560220222484083648835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044746960296645444865113 783560220222484083648835)
                ·
                  refine ⟨1175340330333726125473253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783560220222484083648835 1175340330333726125473253)
                  ·
                    refine ⟨220376311937573648526235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175340330333726125473253 220376311937573648526235)
                    ·
                      rfl

theorem cell22_643772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_643772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643772 prefixEnd_643772 := by exact prefixLift 643772
  have htrace : WordTrace (prefixWord ++ tailWord_643772) baseStart_643772 baseEnd_643772 := by
    simpa [prefixWord, tailWord_643772, baseEnd_643772] using wordTrace_append hprefix tailTrace_643772
  have hstable : (prefixWord ++ tailWord_643772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643772).length < 2 ^ (prefixWord ++ tailWord_643772).sum := by decide
  have hdescent : baseEnd_643772 < baseStart_643772 := by decide
  rcases family_descends (prefixWord ++ tailWord_643772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643800 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_643800 : Nat := 118140960795 + 643800 * 2 ^ 59
def prefixEnd_643800 : Nat := 4983230072969 + 3 ^ 40 * 643800 * 2
def baseEnd_643800 : Nat := 220385896909790908826149

theorem tailTrace_643800 : CollatzResearch.WordTrace tailWord_643800 prefixEnd_643800 220385896909790908826149 := by
  unfold tailWord_643800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740657533815013565680427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15654210045086684754240569 11740657533815013565680427)
  ·
    refine ⟨17610986300722520348520641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11740657533815013565680427 17610986300722520348520641)
    ·
      refine ⟨13208239725541890261390481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17610986300722520348520641 13208239725541890261390481)
      ·
        refine ⟨9906179794156417696042861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13208239725541890261390481 9906179794156417696042861)
        ·
          refine ⟨3714817422808656636016073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9906179794156417696042861 3714817422808656636016073)
          ·
            refine ⟨2786113067106492477012055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3714817422808656636016073 2786113067106492477012055)
            ·
              refine ⟨4179169600659738715518083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786113067106492477012055 4179169600659738715518083)
              ·
                refine ⟨6268754400989608073277125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179169600659738715518083 6268754400989608073277125)
                ·
                  refine ⟨1175391450185551513739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6268754400989608073277125 1175391450185551513739461)
                  ·
                    refine ⟨220385896909790908826149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175391450185551513739461 220385896909790908826149)
                    ·
                      rfl

theorem cell22_643800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_643800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643800 prefixEnd_643800 := by exact prefixLift 643800
  have htrace : WordTrace (prefixWord ++ tailWord_643800) baseStart_643800 baseEnd_643800 := by
    simpa [prefixWord, tailWord_643800, baseEnd_643800] using wordTrace_append hprefix tailTrace_643800
  have hstable : (prefixWord ++ tailWord_643800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643800).length < 2 ^ (prefixWord ++ tailWord_643800).sum := by decide
  have hdescent : baseEnd_643800 < baseStart_643800 := by decide
  rcases family_descends (prefixWord ++ tailWord_643800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643802 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_643802 : Nat := 118140960795 + 643802 * 2 ^ 59
def prefixEnd_643802 : Nat := 4983230072969 + 3 ^ 40 * 643802 * 2
def baseEnd_643802 : Nat := 220386581550663570276143

theorem tailTrace_643802 : CollatzResearch.WordTrace tailWord_643802 prefixEnd_643802 220386581550663570276143 := by
  unfold tailWord_643802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870347003405695368233415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15654258675748520981955773 5870347003405695368233415)
  ·
    refine ⟨8805520505108543052350123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5870347003405695368233415 8805520505108543052350123)
    ·
      refine ⟨13208280757662814578525185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8805520505108543052350123 13208280757662814578525185)
      ·
        refine ⟨9906210568247110933893889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13208280757662814578525185 9906210568247110933893889)
        ·
          refine ⟨7429657926185333200420417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9906210568247110933893889 7429657926185333200420417)
          ·
            refine ⟨5572243444638999900315313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7429657926185333200420417 5572243444638999900315313)
            ·
              refine ⟨4179182583479249925236485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572243444638999900315313 4179182583479249925236485)
              ·
                refine ⟨783596734402359360981841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4179182583479249925236485 783596734402359360981841)
                ·
                  refine ⟨587697550801769520736381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783596734402359360981841 587697550801769520736381)
                  ·
                    refine ⟨220386581550663570276143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587697550801769520736381 220386581550663570276143)
                    ·
                      rfl

theorem cell22_643802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_643802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643802 prefixEnd_643802 := by exact prefixLift 643802
  have htrace : WordTrace (prefixWord ++ tailWord_643802) baseStart_643802 baseEnd_643802 := by
    simpa [prefixWord, tailWord_643802, baseEnd_643802] using wordTrace_append hprefix tailTrace_643802
  have hstable : (prefixWord ++ tailWord_643802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643802).length < 2 ^ (prefixWord ++ tailWord_643802).sum := by decide
  have hdescent : baseEnd_643802 < baseStart_643802 := by decide
  rcases family_descends (prefixWord ++ tailWord_643802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643804 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_643804 : Nat := 118140960795 + 643804 * 2 ^ 59
def prefixEnd_643804 : Nat := 4983230072969 + 3 ^ 40 * 643804 * 2
def baseEnd_643804 : Nat := 73462422063845410575379

theorem tailTrace_643804 : CollatzResearch.WordTrace tailWord_643804 prefixEnd_643804 73462422063845410575379 := by
  unfold tailWord_643804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740730479807767907253233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15654307306410357209670977 11740730479807767907253233)
  ·
    refine ⟨8805547859855825930439925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11740730479807767907253233 8805547859855825930439925)
    ·
      refine ⟨825520111861483680978743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8805547859855825930439925 825520111861483680978743)
      ·
        refine ⟨1238280167792225521468115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825520111861483680978743 1238280167792225521468115)
        ·
          refine ⟨1857420251688338282202173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238280167792225521468115 1857420251688338282202173)
          ·
            refine ⟨696532594383126855825815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1857420251688338282202173 696532594383126855825815)
            ·
              refine ⟨1044798891574690283738723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696532594383126855825815 1044798891574690283738723)
              ·
                refine ⟨1567198337362035425608085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044798891574690283738723 1567198337362035425608085)
                ·
                  refine ⟨73462422063845410575379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1567198337362035425608085 73462422063845410575379)
                  ·
                    rfl

theorem cell22_643804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_643804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643804 prefixEnd_643804 := by exact prefixLift 643804
  have htrace : WordTrace (prefixWord ++ tailWord_643804) baseStart_643804 baseEnd_643804 := by
    simpa [prefixWord, tailWord_643804, baseEnd_643804] using wordTrace_append hprefix tailTrace_643804
  have hstable : (prefixWord ++ tailWord_643804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643804).length < 2 ^ (prefixWord ++ tailWord_643804).sum := by decide
  have hdescent : baseEnd_643804 < baseStart_643804 := by decide
  rcases family_descends (prefixWord ++ tailWord_643804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643907 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 1, 4]
def baseStart_643907 : Nat := 118140960795 + 643907 * 2 ^ 59
def prefixEnd_643907 : Nat := 4983230072969 + 3 ^ 40 * 643907 * 2
def baseEnd_643907 : Nat := 220422525196478296400821

theorem tailTrace_643907 : CollatzResearch.WordTrace tailWord_643907 prefixEnd_643907 220422525196478296400821 := by
  unfold tailWord_643907
  simp only [CollatzResearch.WordTrace]
  refine ⟨23485217678242384405505975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15656811785494922937003983 23485217678242384405505975)
  ·
    refine ⟨35227826517363576608258963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23485217678242384405505975 35227826517363576608258963)
    ·
      refine ⟨52841739776045364912388445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35227826517363576608258963 52841739776045364912388445)
      ·
        refine ⟨19815652416017011842145667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52841739776045364912388445 19815652416017011842145667)
        ·
          refine ⟨29723478624025517763218501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19815652416017011842145667 29723478624025517763218501)
          ·
            refine ⟨5573152242004784580603469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29723478624025517763218501 5573152242004784580603469)
            ·
              refine ⟨2089932090751794217726301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5573152242004784580603469 2089932090751794217726301)
              ·
                refine ⟨783724534031922831647363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2089932090751794217726301 783724534031922831647363)
                ·
                  refine ⟨1175586801047884247471045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783724534031922831647363 1175586801047884247471045)
                  ·
                    refine ⟨220422525196478296400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175586801047884247471045 220422525196478296400821)
                    ·
                      rfl

theorem cell22_643907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_643907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643907 prefixEnd_643907 := by exact prefixLift 643907
  have htrace : WordTrace (prefixWord ++ tailWord_643907) baseStart_643907 baseEnd_643907 := by
    simpa [prefixWord, tailWord_643907, baseEnd_643907] using wordTrace_append hprefix tailTrace_643907
  have hstable : (prefixWord ++ tailWord_643907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643907).length < 2 ^ (prefixWord ++ tailWord_643907).sum := by decide
  have hdescent : baseEnd_643907 < baseStart_643907 := by decide
  rcases family_descends (prefixWord ++ tailWord_643907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643920 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_643920 : Nat := 118140960795 + 643920 * 2 ^ 59
def prefixEnd_643920 : Nat := 4983230072969 + 3 ^ 40 * 643920 * 2
def baseEnd_643920 : Nat := 220426975362150595825781

theorem tailTrace_643920 : CollatzResearch.WordTrace tailWord_643920 prefixEnd_643920 220426975362150595825781 := by
  unfold tailWord_643920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742845913597643812864607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15657127884796858417152809 11742845913597643812864607)
  ·
    refine ⟨17614268870396465719296911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11742845913597643812864607 17614268870396465719296911)
    ·
      refine ⟨26421403305594698578945367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17614268870396465719296911 26421403305594698578945367)
      ·
        refine ⟨39632104958392047868418051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26421403305594698578945367 39632104958392047868418051)
        ·
          refine ⟨59448157437588071802627077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39632104958392047868418051 59448157437588071802627077)
          ·
            refine ⟨11146529519547763462992577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59448157437588071802627077 11146529519547763462992577)
            ·
              refine ⟨8359897139660822597244433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11146529519547763462992577 8359897139660822597244433)
              ·
                refine ⟨6269922854745616947933325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8359897139660822597244433 6269922854745616947933325)
                ·
                  refine ⟨2351221070529606355474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6269922854745616947933325 2351221070529606355474997)
                  ·
                    refine ⟨220426975362150595825781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2351221070529606355474997 220426975362150595825781)
                    ·
                      rfl

theorem cell22_643920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_643920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643920 prefixEnd_643920 := by exact prefixLift 643920
  have htrace : WordTrace (prefixWord ++ tailWord_643920) baseStart_643920 baseEnd_643920 := by
    simpa [prefixWord, tailWord_643920, baseEnd_643920] using wordTrace_append hprefix tailTrace_643920
  have hstable : (prefixWord ++ tailWord_643920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643920).length < 2 ^ (prefixWord ++ tailWord_643920).sum := by decide
  have hdescent : baseEnd_643920 < baseStart_643920 := by decide
  rcases family_descends (prefixWord ++ tailWord_643920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643922 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_643922 : Nat := 118140960795 + 643922 * 2 ^ 59
def prefixEnd_643922 : Nat := 4983230072969 + 3 ^ 40 * 643922 * 2
def baseEnd_643922 : Nat := 73475886667674419091925

theorem tailTrace_643922 : CollatzResearch.WordTrace tailWord_643922 prefixEnd_643922 73475886667674419091925 := by
  unfold tailWord_643922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871441193297010491825505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15657176515458694644868013 5871441193297010491825505)
  ·
    refine ⟨4403580894972757868869129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5871441193297010491825505 4403580894972757868869129)
    ·
      refine ⟨3302685671229568401651847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4403580894972757868869129 3302685671229568401651847)
      ·
        refine ⟨4954028506844352602477771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302685671229568401651847 4954028506844352602477771)
        ·
          refine ⟨7431042760266528903716657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954028506844352602477771 7431042760266528903716657)
          ·
            refine ⟨5573282070199896677787493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7431042760266528903716657 5573282070199896677787493)
            ·
              refine ⟨1044990388162480627085155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5573282070199896677787493 1044990388162480627085155)
              ·
                refine ⟨1567485582243720940627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044990388162480627085155 1567485582243720940627733)
                ·
                  refine ⟨73475886667674419091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1567485582243720940627733 73475886667674419091925)
                  ·
                    rfl

theorem cell22_643922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_643922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643922 prefixEnd_643922 := by exact prefixLift 643922
  have htrace : WordTrace (prefixWord ++ tailWord_643922) baseStart_643922 baseEnd_643922 := by
    simpa [prefixWord, tailWord_643922, baseEnd_643922] using wordTrace_append hprefix tailTrace_643922
  have hstable : (prefixWord ++ tailWord_643922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643922).length < 2 ^ (prefixWord ++ tailWord_643922).sum := by decide
  have hdescent : baseEnd_643922 < baseStart_643922 := by decide
  rcases family_descends (prefixWord ++ tailWord_643922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643935 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_643935 : Nat := 118140960795 + 643935 * 2 ^ 59
def prefixEnd_643935 : Nat := 4983230072969 + 3 ^ 40 * 643935 * 2
def baseEnd_643935 : Nat := 220432110168695556700735

theorem tailTrace_643935 : CollatzResearch.WordTrace tailWord_643935 prefixEnd_643935 220432110168695556700735 := by
  unfold tailWord_643935
  simp only [CollatzResearch.WordTrace]
  refine ⟨23486238922140945187525259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15657492614760630125016839 23486238922140945187525259)
  ·
    refine ⟨35229358383211417781287889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23486238922140945187525259 35229358383211417781287889)
    ·
      refine ⟨26422018787408563335965917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35229358383211417781287889 26422018787408563335965917)
      ·
        refine ⟨9908257045278211250987219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26422018787408563335965917 9908257045278211250987219)
        ·
          refine ⟨14862385567917316876480829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908257045278211250987219 14862385567917316876480829)
          ·
            refine ⟨5573394587968993828680311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14862385567917316876480829 5573394587968993828680311)
            ·
              refine ⟨8360091881953490743020467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573394587968993828680311 8360091881953490743020467)
              ·
                refine ⟨12540137822930236114530701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8360091881953490743020467 12540137822930236114530701)
                ·
                  refine ⟨4702551683598838542949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12540137822930236114530701 4702551683598838542949013)
                  ·
                    refine ⟨220432110168695556700735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4702551683598838542949013 220432110168695556700735)
                    ·
                      rfl

theorem cell22_643935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_643935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_643935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_643935 prefixEnd_643935 := by exact prefixLift 643935
  have htrace : WordTrace (prefixWord ++ tailWord_643935) baseStart_643935 baseEnd_643935 := by
    simpa [prefixWord, tailWord_643935, baseEnd_643935] using wordTrace_append hprefix tailTrace_643935
  have hstable : (prefixWord ++ tailWord_643935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643935).length < 2 ^ (prefixWord ++ tailWord_643935).sum := by decide
  have hdescent : baseEnd_643935 < baseStart_643935 := by decide
  rcases family_descends (prefixWord ++ tailWord_643935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644022 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_644022 : Nat := 118140960795 + 644022 * 2 ^ 59
def prefixEnd_644022 : Nat := 4983230072969 + 3 ^ 40 * 644022 * 2
def baseEnd_644022 : Nat := 220461892046656329775469

theorem tailTrace_644022 : CollatzResearch.WordTrace tailWord_644022 prefixEnd_644022 220461892046656329775469 := by
  unfold tailWord_644022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468088254551609940371395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15659608048550506030628213 1468088254551609940371395)
  ·
    refine ⟨2202132381827414910557093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468088254551609940371395 2202132381827414910557093)
    ·
      refine ⟨412899821592640295729455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2202132381827414910557093 412899821592640295729455)
      ·
        refine ⟨619349732388960443594183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412899821592640295729455 619349732388960443594183)
        ·
          refine ⟨929024598583440665391275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619349732388960443594183 929024598583440665391275)
          ·
            refine ⟨1393536897875160998086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929024598583440665391275 1393536897875160998086913)
            ·
              refine ⟨1045152673406370748565185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393536897875160998086913 1045152673406370748565185)
              ·
                refine ⟨783864505054778061423889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045152673406370748565185 783864505054778061423889)
                ·
                  refine ⟨587898378791083546067917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783864505054778061423889 587898378791083546067917)
                  ·
                    refine ⟨220461892046656329775469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587898378791083546067917 220461892046656329775469)
                    ·
                      rfl

theorem cell22_644022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_644022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644022 prefixEnd_644022 := by exact prefixLift 644022
  have htrace : WordTrace (prefixWord ++ tailWord_644022) baseStart_644022 baseEnd_644022 := by
    simpa [prefixWord, tailWord_644022, baseEnd_644022] using wordTrace_append hprefix tailTrace_644022
  have hstable : (prefixWord ++ tailWord_644022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644022).length < 2 ^ (prefixWord ++ tailWord_644022).sum := by decide
  have hdescent : baseEnd_644022 < baseStart_644022 := by decide
  rcases family_descends (prefixWord ++ tailWord_644022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644057 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 8]
def baseStart_644057 : Nat := 118140960795 + 644057 * 2 ^ 59
def prefixEnd_644057 : Nat := 4983230072969 + 3 ^ 40 * 644057 * 2
def baseEnd_644057 : Nat := 73491291087309301716787

theorem tailTrace_644057 : CollatzResearch.WordTrace tailWord_644057 prefixEnd_644057 73491291087309301716787 := by
  unfold tailWord_644057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23490688627698960023466425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15660459085132640015644283 23490688627698960023466425)
  ·
    refine ⟨17618016470774220017599819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23490688627698960023466425 17618016470774220017599819)
    ·
      refine ⟨26427024706161330026399729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17618016470774220017599819 26427024706161330026399729)
      ·
        refine ⟨19820268529620997519799797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26427024706161330026399729 19820268529620997519799797)
        ·
          refine ⟨1858150174651968517481231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19820268529620997519799797 1858150174651968517481231)
          ·
            refine ⟨2787225261977952776221847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858150174651968517481231 2787225261977952776221847)
            ·
              refine ⟨4180837892966929164332771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787225261977952776221847 4180837892966929164332771)
              ·
                refine ⟨6271256839450393746499157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180837892966929164332771 6271256839450393746499157)
                ·
                  refine ⟨73491291087309301716787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6271256839450393746499157 73491291087309301716787)
                  ·
                    rfl

theorem cell22_644057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_644057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644057 prefixEnd_644057 := by exact prefixLift 644057
  have htrace : WordTrace (prefixWord ++ tailWord_644057) baseStart_644057 baseEnd_644057 := by
    simpa [prefixWord, tailWord_644057, baseEnd_644057] using wordTrace_append hprefix tailTrace_644057
  have hstable : (prefixWord ++ tailWord_644057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644057).length < 2 ^ (prefixWord ++ tailWord_644057).sum := by decide
  have hdescent : baseEnd_644057 < baseStart_644057 := by decide
  rcases family_descends (prefixWord ++ tailWord_644057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644089 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_644089 : Nat := 118140960795 + 644089 * 2 ^ 59
def prefixEnd_644089 : Nat := 4983230072969 + 3 ^ 40 * 644089 * 2
def baseEnd_644089 : Nat := 220484827515890488350263

theorem tailTrace_644089 : CollatzResearch.WordTrace tailWord_644089 prefixEnd_644089 220484827515890488350263 := by
  unfold tailWord_644089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491855763583029488631321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15661237175722019659087547 23491855763583029488631321)
  ·
    refine ⟨17618891822687272116473491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23491855763583029488631321 17618891822687272116473491)
    ·
      refine ⟨26428337734030908174710237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17618891822687272116473491 26428337734030908174710237)
      ·
        refine ⟨9910626650261590565516339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26428337734030908174710237 9910626650261590565516339)
        ·
          refine ⟨14865939975392385848274509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910626650261590565516339 14865939975392385848274509)
          ·
            refine ⟨5574727490772144693102941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14865939975392385848274509 5574727490772144693102941)
            ·
              refine ⟨2090522809039554259913603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5574727490772144693102941 2090522809039554259913603)
              ·
                refine ⟨3135784213559331389870405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090522809039554259913603 3135784213559331389870405)
                ·
                  refine ⟨587959540042374635600701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3135784213559331389870405 587959540042374635600701)
                  ·
                    refine ⟨220484827515890488350263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 587959540042374635600701 220484827515890488350263)
                    ·
                      rfl

theorem cell22_644089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_644089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644089 prefixEnd_644089 := by exact prefixLift 644089
  have htrace : WordTrace (prefixWord ++ tailWord_644089) baseStart_644089 baseEnd_644089 := by
    simpa [prefixWord, tailWord_644089, baseEnd_644089] using wordTrace_append hprefix tailTrace_644089
  have hstable : (prefixWord ++ tailWord_644089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644089).length < 2 ^ (prefixWord ++ tailWord_644089).sum := by decide
  have hdescent : baseEnd_644089 < baseStart_644089 := by decide
  rcases family_descends (prefixWord ++ tailWord_644089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644106 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_644106 : Nat := 118140960795 + 644106 * 2 ^ 59
def prefixEnd_644106 : Nat := 4983230072969 + 3 ^ 40 * 644106 * 2
def baseEnd_644106 : Nat := 220490646963308110675211

theorem tailTrace_644106 : CollatzResearch.WordTrace tailWord_644106 prefixEnd_644106 220490646963308110675211 := by
  unfold tailWord_644106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873118951130360348000043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15661650536347627594666781 5873118951130360348000043)
  ·
    refine ⟨8809678426695540522000065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5873118951130360348000043 8809678426695540522000065)
    ·
      refine ⟨6607258820021655391500049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809678426695540522000065 6607258820021655391500049)
      ·
        refine ⟨4955444115016241543625037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6607258820021655391500049 4955444115016241543625037)
        ·
          refine ⟨1858291543131090578859389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4955444115016241543625037 1858291543131090578859389)
          ·
            refine ⟨696859328674158967072271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858291543131090578859389 696859328674158967072271)
            ·
              refine ⟨1045288993011238450608407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696859328674158967072271 1045288993011238450608407)
              ·
                refine ⟨1567933489516857675912611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045288993011238450608407 1567933489516857675912611)
                ·
                  refine ⟨2351900234275286513868917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567933489516857675912611 2351900234275286513868917)
                  ·
                    refine ⟨220490646963308110675211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2351900234275286513868917 220490646963308110675211)
                    ·
                      rfl

theorem cell22_644106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_644106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644106 prefixEnd_644106 := by exact prefixLift 644106
  have htrace : WordTrace (prefixWord ++ tailWord_644106) baseStart_644106 baseEnd_644106 := by
    simpa [prefixWord, tailWord_644106, baseEnd_644106] using wordTrace_append hprefix tailTrace_644106
  have hstable : (prefixWord ++ tailWord_644106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644106).length < 2 ^ (prefixWord ++ tailWord_644106).sum := by decide
  have hdescent : baseEnd_644106 < baseStart_644106 := by decide
  rcases family_descends (prefixWord ++ tailWord_644106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644119 : List Nat := [1, 1, 3, 5, 1, 2, 1, 8]
def baseStart_644119 : Nat := 118140960795 + 644119 * 2 ^ 59
def prefixEnd_644119 : Nat := 4983230072969 + 3 ^ 40 * 644119 * 2
def baseEnd_644119 : Nat := 24499455236553378900019

theorem tailTrace_644119 : CollatzResearch.WordTrace tailWord_644119 prefixEnd_644119 24499455236553378900019 := by
  unfold tailWord_644119
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492949953474344612223411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15661966635649563074815607 23492949953474344612223411)
  ·
    refine ⟨35239424930211516918335117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23492949953474344612223411 35239424930211516918335117)
    ·
      refine ⟨13214784348829318844375669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35239424930211516918335117 13214784348829318844375669)
      ·
        refine ⟨1238886032702748641660219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13214784348829318844375669 1238886032702748641660219)
        ·
          refine ⟨1858329049054122962490329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238886032702748641660219 1858329049054122962490329)
          ·
            refine ⟨1393746786790592221867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858329049054122962490329 1393746786790592221867747)
            ·
              refine ⟨2090620180185888332801621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393746786790592221867747 2090620180185888332801621)
              ·
                refine ⟨24499455236553378900019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2090620180185888332801621 24499455236553378900019)
                ·
                  rfl

theorem cell22_644119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 8].length) (baseStart_644119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644119 prefixEnd_644119 := by exact prefixLift 644119
  have htrace : WordTrace (prefixWord ++ tailWord_644119) baseStart_644119 baseEnd_644119 := by
    simpa [prefixWord, tailWord_644119, baseEnd_644119] using wordTrace_append hprefix tailTrace_644119
  have hstable : (prefixWord ++ tailWord_644119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644119).length < 2 ^ (prefixWord ++ tailWord_644119).sum := by decide
  have hdescent : baseEnd_644119 < baseStart_644119 := by decide
  rcases family_descends (prefixWord ++ tailWord_644119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644125 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 4]
def baseStart_644125 : Nat := 118140960795 + 644125 * 2 ^ 59
def prefixEnd_644125 : Nat := 4983230072969 + 3 ^ 40 * 644125 * 2
def baseEnd_644125 : Nat := 73499050350532798150051

theorem tailTrace_644125 : CollatzResearch.WordTrace tailWord_644125 prefixEnd_644125 73499050350532798150051 := by
  unfold tailWord_644125
  simp only [CollatzResearch.WordTrace]
  refine ⟨23493168791452607636941829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15662112527635071757961219 23493168791452607636941829)
  ·
    refine ⟨4404969148397363931926593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23493168791452607636941829 4404969148397363931926593)
    ·
      refine ⟨3303726861298022948944945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4404969148397363931926593 3303726861298022948944945)
      ·
        refine ⟨2477795145973517211708709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303726861298022948944945 2477795145973517211708709)
        ·
          refine ⟨464586589870034477195383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2477795145973517211708709 464586589870034477195383)
          ·
            refine ⟨696879884805051715793075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464586589870034477195383 696879884805051715793075)
            ·
              refine ⟨1045319827207577573689613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696879884805051715793075 1045319827207577573689613)
              ·
                refine ⟨391994935202841590133605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045319827207577573689613 391994935202841590133605)
                ·
                  refine ⟨73499050350532798150051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391994935202841590133605 73499050350532798150051)
                  ·
                    rfl

theorem cell22_644125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_644125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644125 prefixEnd_644125 := by exact prefixLift 644125
  have htrace : WordTrace (prefixWord ++ tailWord_644125) baseStart_644125 baseEnd_644125 := by
    simpa [prefixWord, tailWord_644125, baseEnd_644125] using wordTrace_append hprefix tailTrace_644125
  have hstable : (prefixWord ++ tailWord_644125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644125).length < 2 ^ (prefixWord ++ tailWord_644125).sum := by decide
  have hdescent : baseEnd_644125 < baseStart_644125 := by decide
  rcases family_descends (prefixWord ++ tailWord_644125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644202 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_644202 : Nat := 118140960795 + 644202 * 2 ^ 59
def prefixEnd_644202 : Nat := 4983230072969 + 3 ^ 40 * 644202 * 2
def baseEnd_644202 : Nat := 220523509725195860274917

theorem tailTrace_644202 : CollatzResearch.WordTrace tailWord_644202 prefixEnd_644202 220523509725195860274917 := by
  unfold tailWord_644202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873994303043412446873715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15663984808115766524996573 5873994303043412446873715)
  ·
    refine ⟨8810991454565118670310573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5873994303043412446873715 8810991454565118670310573)
    ·
      refine ⟨3304121795461919501366465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8810991454565118670310573 3304121795461919501366465)
      ·
        refine ⟨2478091346596439626024849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3304121795461919501366465 2478091346596439626024849)
        ·
          refine ⟨1858568509947329719518637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2478091346596439626024849 1858568509947329719518637)
          ·
            refine ⟨696963191230248644819489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858568509947329719518637 696963191230248644819489)
            ·
              refine ⟨522722393422686483614617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696963191230248644819489 522722393422686483614617)
              ·
                refine ⟨392041795067014862710963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522722393422686483614617 392041795067014862710963)
                ·
                  refine ⟨588062692600522294066445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392041795067014862710963 588062692600522294066445)
                  ·
                    refine ⟨220523509725195860274917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588062692600522294066445 220523509725195860274917)
                    ·
                      rfl

theorem cell22_644202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_644202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644202 prefixEnd_644202 := by exact prefixLift 644202
  have htrace : WordTrace (prefixWord ++ tailWord_644202) baseStart_644202 baseEnd_644202 := by
    simpa [prefixWord, tailWord_644202, baseEnd_644202] using wordTrace_append hprefix tailTrace_644202
  have hstable : (prefixWord ++ tailWord_644202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644202).length < 2 ^ (prefixWord ++ tailWord_644202).sum := by decide
  have hdescent : baseEnd_644202 < baseStart_644202 := by decide
  rcases family_descends (prefixWord ++ tailWord_644202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644213 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_644213 : Nat := 118140960795 + 644213 * 2 ^ 59
def prefixEnd_644213 : Nat := 4983230072969 + 3 ^ 40 * 644213 * 2
def baseEnd_644213 : Nat := 220527275249995498249883

theorem tailTrace_644213 : CollatzResearch.WordTrace tailWord_644213 prefixEnd_644213 220527275249995498249883 := by
  unfold tailWord_644213
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496378415133798666145293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664252276755865777430195 23496378415133798666145293)
  ·
    refine ⟨8811141905675174499804485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23496378415133798666145293 8811141905675174499804485)
    ·
      refine ⟨1652089107314095218713341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8811141905675174499804485 1652089107314095218713341)
      ·
        refine ⟨619533415242785707017503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1652089107314095218713341 619533415242785707017503)
        ·
          refine ⟨929300122864178560526255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619533415242785707017503 929300122864178560526255)
          ·
            refine ⟨1393950184296267840789383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929300122864178560526255 1393950184296267840789383)
            ·
              refine ⟨2090925276444401761184075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393950184296267840789383 2090925276444401761184075)
              ·
                refine ⟨3136387914666602641776113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090925276444401761184075 3136387914666602641776113)
                ·
                  refine ⟨2352290935999951981332085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136387914666602641776113 2352290935999951981332085)
                  ·
                    refine ⟨220527275249995498249883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2352290935999951981332085 220527275249995498249883)
                    ·
                      rfl

theorem cell22_644213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_644213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644213 prefixEnd_644213 := by exact prefixLift 644213
  have htrace : WordTrace (prefixWord ++ tailWord_644213) baseStart_644213 baseEnd_644213 := by
    simpa [prefixWord, tailWord_644213, baseEnd_644213] using wordTrace_append hprefix tailTrace_644213
  have hstable : (prefixWord ++ tailWord_644213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644213).length < 2 ^ (prefixWord ++ tailWord_644213).sum := by decide
  have hdescent : baseEnd_644213 < baseStart_644213 := by decide
  rcases family_descends (prefixWord ++ tailWord_644213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644224 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_644224 : Nat := 118140960795 + 644224 * 2 ^ 59
def prefixEnd_644224 : Nat := 4983230072969 + 3 ^ 40 * 644224 * 2
def baseEnd_644224 : Nat := 220531040774795136224849

theorem tailTrace_644224 : CollatzResearch.WordTrace tailWord_644224 prefixEnd_644224 220531040774795136224849 := by
  unfold tailWord_644224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748389809046973772397863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15664519745395965029863817 11748389809046973772397863)
  ·
    refine ⟨17622584713570460658596795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11748389809046973772397863 17622584713570460658596795)
    ·
      refine ⟨26433877070355690987895193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622584713570460658596795 26433877070355690987895193)
      ·
        refine ⟨19825407802766768240921395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26433877070355690987895193 19825407802766768240921395)
        ·
          refine ⟨29738111704150152361382093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19825407802766768240921395 29738111704150152361382093)
          ·
            refine ⟨11151791889056307135518285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29738111704150152361382093 11151791889056307135518285)
            ·
              refine ⟨4181921958396115175819357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11151791889056307135518285 4181921958396115175819357)
              ·
                refine ⟨1568220734398543190932259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181921958396115175819357 1568220734398543190932259)
                ·
                  refine ⟨2352331101597814786398389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568220734398543190932259 2352331101597814786398389)
                  ·
                    refine ⟨220531040774795136224849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2352331101597814786398389 220531040774795136224849)
                    ·
                      rfl

theorem cell22_644224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_644224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644224 prefixEnd_644224 := by exact prefixLift 644224
  have htrace : WordTrace (prefixWord ++ tailWord_644224) baseStart_644224 baseEnd_644224 := by
    simpa [prefixWord, tailWord_644224, baseEnd_644224] using wordTrace_append hprefix tailTrace_644224
  have hstable : (prefixWord ++ tailWord_644224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644224).length < 2 ^ (prefixWord ++ tailWord_644224).sum := by decide
  have hdescent : baseEnd_644224 < baseStart_644224 := by decide
  rcases family_descends (prefixWord ++ tailWord_644224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644288 : List Nat := [2, 1, 1, 2, 6, 2, 2, 6]
def baseStart_644288 : Nat := 118140960795 + 644288 * 2 ^ 59
def prefixEnd_644288 : Nat := 4983230072969 + 3 ^ 40 * 644288 * 2
def baseEnd_644288 : Nat := 24505883253635589180517

theorem tailTrace_644288 : CollatzResearch.WordTrace tailWord_644288 prefixEnd_644288 24505883253635589180517 := by
  unfold tailWord_644288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11749556944931043237562759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15666075926574724316750345 11749556944931043237562759)
  ·
    refine ⟨17624335417396564856344139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11749556944931043237562759 17624335417396564856344139)
    ·
      refine ⟨26436503126094847284516209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17624335417396564856344139 26436503126094847284516209)
      ·
        refine ⟨19827377344571135463387157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26436503126094847284516209 19827377344571135463387157)
        ·
          refine ⟨929408313026771974846273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19827377344571135463387157 929408313026771974846273)
          ·
            refine ⟨697056234770078981134705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929408313026771974846273 697056234770078981134705)
            ·
              refine ⟨522792176077559235851029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697056234770078981134705 522792176077559235851029)
              ·
                refine ⟨24505883253635589180517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 522792176077559235851029 24505883253635589180517)
                ·
                  rfl

theorem cell22_644288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_644288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644288 prefixEnd_644288 := by exact prefixLift 644288
  have htrace : WordTrace (prefixWord ++ tailWord_644288) baseStart_644288 baseEnd_644288 := by
    simpa [prefixWord, tailWord_644288, baseEnd_644288] using wordTrace_append hprefix tailTrace_644288
  have hstable : (prefixWord ++ tailWord_644288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644288).length < 2 ^ (prefixWord ++ tailWord_644288).sum := by decide
  have hdescent : baseEnd_644288 < baseStart_644288 := by decide
  rcases family_descends (prefixWord ++ tailWord_644288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644303 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 1, 3]
def baseStart_644303 : Nat := 118140960795 + 644303 * 2 ^ 59
def prefixEnd_644303 : Nat := 4983230072969 + 3 ^ 40 * 644303 * 2
def baseEnd_644303 : Nat := 220558084089265263499607

theorem tailTrace_644303 : CollatzResearch.WordTrace tailWord_644303 prefixEnd_644303 220558084089265263499607 := by
  unfold tailWord_644303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499660984807744036921563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666440656538496024614375 23499660984807744036921563)
  ·
    refine ⟨35249491477211616055382345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23499660984807744036921563 35249491477211616055382345)
    ·
      refine ⟨26437118607908712041536759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35249491477211616055382345 26437118607908712041536759)
      ·
        refine ⟨39655677911863068062305139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26437118607908712041536759 39655677911863068062305139)
        ·
          refine ⟨59483516867794602093457709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39655677911863068062305139 59483516867794602093457709)
          ·
            refine ⟨22306318825422975785046641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59483516867794602093457709 22306318825422975785046641)
            ·
              refine ⟨16729739119067231838784981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22306318825422975785046641 16729739119067231838784981)
              ·
                refine ⟨392103260603138246221523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16729739119067231838784981 392103260603138246221523)
                ·
                  refine ⟨588154890904707369332285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392103260603138246221523 588154890904707369332285)
                  ·
                    refine ⟨220558084089265263499607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588154890904707369332285 220558084089265263499607)
                    ·
                      rfl

theorem cell22_644303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_644303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644303 prefixEnd_644303 := by exact prefixLift 644303
  have htrace : WordTrace (prefixWord ++ tailWord_644303) baseStart_644303 baseEnd_644303 := by
    simpa [prefixWord, tailWord_644303, baseEnd_644303] using wordTrace_append hprefix tailTrace_644303
  have hstable : (prefixWord ++ tailWord_644303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644303).length < 2 ^ (prefixWord ++ tailWord_644303).sum := by decide
  have hdescent : baseEnd_644303 < baseStart_644303 := by decide
  rcases family_descends (prefixWord ++ tailWord_644303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644333 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 5]
def baseStart_644333 : Nat := 118140960795 + 644333 * 2 ^ 59
def prefixEnd_644333 : Nat := 4983230072969 + 3 ^ 40 * 644333 * 2
def baseEnd_644333 : Nat := 73522784567451728416505

theorem tailTrace_644333 : CollatzResearch.WordTrace tailWord_644333 prefixEnd_644333 73522784567451728416505 := by
  unfold tailWord_644333
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500755174699059160513653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15667170116466039440342435 23500755174699059160513653)
  ·
    refine ⟨2203195797628036796298155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23500755174699059160513653 2203195797628036796298155)
    ·
      refine ⟨3304793696442055194447233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203195797628036796298155 3304793696442055194447233)
      ·
        refine ⟨2478595272331541395835425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3304793696442055194447233 2478595272331541395835425)
        ·
          refine ⟨1858946454248656046876569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2478595272331541395835425 1858946454248656046876569)
          ·
            refine ⟨1394209840686492035157427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858946454248656046876569 1394209840686492035157427)
            ·
              refine ⟨2091314761029738052736141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394209840686492035157427 2091314761029738052736141)
              ·
                refine ⟨784243035386151769776053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091314761029738052736141 784243035386151769776053)
                ·
                  refine ⟨73522784567451728416505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784243035386151769776053 73522784567451728416505)
                  ·
                    rfl

theorem cell22_644333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_644333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644333 prefixEnd_644333 := by exact prefixLift 644333
  have htrace : WordTrace (prefixWord ++ tailWord_644333) baseStart_644333 baseEnd_644333 := by
    simpa [prefixWord, tailWord_644333, baseEnd_644333] using wordTrace_append hprefix tailTrace_644333
  have hstable : (prefixWord ++ tailWord_644333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644333).length < 2 ^ (prefixWord ++ tailWord_644333).sum := by decide
  have hdescent : baseEnd_644333 < baseStart_644333 := by decide
  rcases family_descends (prefixWord ++ tailWord_644333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644346 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_644346 : Nat := 118140960795 + 644346 * 2 ^ 59
def prefixEnd_644346 : Nat := 4983230072969 + 3 ^ 40 * 644346 * 2
def baseEnd_644346 : Nat := 220572803868027484674475

theorem tailTrace_644346 : CollatzResearch.WordTrace tailWord_644346 prefixEnd_644346 220572803868027484674475 := by
  unfold tailWord_644346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875307330912990595184223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15667486215767974920491261 5875307330912990595184223)
  ·
    refine ⟨8812960996369485892776335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5875307330912990595184223 8812960996369485892776335)
    ·
      refine ⟨13219441494554228839164503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812960996369485892776335 13219441494554228839164503)
      ·
        refine ⟨19829162241831343258746755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13219441494554228839164503 19829162241831343258746755)
        ·
          refine ⟨29743743362747014888120133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19829162241831343258746755 29743743362747014888120133)
          ·
            refine ⟨5576951880515065291522525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29743743362747014888120133 5576951880515065291522525)
            ·
              refine ⟨2091356955193149484320947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5576951880515065291522525 2091356955193149484320947)
              ·
                refine ⟨3137035432789724226481421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091356955193149484320947 3137035432789724226481421)
                ·
                  refine ⟨1176388287296146584930533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3137035432789724226481421 1176388287296146584930533)
                  ·
                    refine ⟨220572803868027484674475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1176388287296146584930533 220572803868027484674475)
                    ·
                      rfl

theorem cell22_644346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_644346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644346 prefixEnd_644346 := by exact prefixLift 644346
  have htrace : WordTrace (prefixWord ++ tailWord_644346) baseStart_644346 baseEnd_644346 := by
    simpa [prefixWord, tailWord_644346, baseEnd_644346] using wordTrace_append hprefix tailTrace_644346
  have hstable : (prefixWord ++ tailWord_644346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644346).length < 2 ^ (prefixWord ++ tailWord_644346).sum := by decide
  have hdescent : baseEnd_644346 < baseStart_644346 := by decide
  rcases family_descends (prefixWord ++ tailWord_644346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644489 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_644489 : Nat := 118140960795 + 644489 * 2 ^ 59
def prefixEnd_644489 : Nat := 4983230072969 + 3 ^ 40 * 644489 * 2
def baseEnd_644489 : Nat := 220621755690422778349037

theorem tailTrace_644489 : CollatzResearch.WordTrace tailWord_644489 prefixEnd_644489 220621755690422778349037 := by
  unfold tailWord_644489
  simp only [CollatzResearch.WordTrace]
  refine ⟨23506444962133897803192521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15670963308089265202128347 23506444962133897803192521)
  ·
    refine ⟨17629833721600423352394391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23506444962133897803192521 17629833721600423352394391)
    ·
      refine ⟨26444750582400635028591587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17629833721600423352394391 26444750582400635028591587)
      ·
        refine ⟨39667125873600952542887381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26444750582400635028591587 39667125873600952542887381)
        ·
          refine ⟨929698262662522325223923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39667125873600952542887381 929698262662522325223923)
          ·
            refine ⟨1394547393993783487835885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929698262662522325223923 1394547393993783487835885)
            ·
              refine ⟨522955272747668807938457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1394547393993783487835885 522955272747668807938457)
              ·
                refine ⟨392216454560751605953843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522955272747668807938457 392216454560751605953843)
                ·
                  refine ⟨588324681841127408930765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392216454560751605953843 588324681841127408930765)
                  ·
                    refine ⟨220621755690422778349037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588324681841127408930765 220621755690422778349037)
                    ·
                      rfl

theorem cell22_644489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_644489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644489 prefixEnd_644489 := by exact prefixLift 644489
  have htrace : WordTrace (prefixWord ++ tailWord_644489) baseStart_644489 baseEnd_644489 := by
    simpa [prefixWord, tailWord_644489, baseEnd_644489] using wordTrace_append hprefix tailTrace_644489
  have hstable : (prefixWord ++ tailWord_644489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644489).length < 2 ^ (prefixWord ++ tailWord_644489).sum := by decide
  have hdescent : baseEnd_644489 < baseStart_644489 := by decide
  rcases family_descends (prefixWord ++ tailWord_644489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644528 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_644528 : Nat := 118140960795 + 644528 * 2 ^ 59
def prefixEnd_644528 : Nat := 4983230072969 + 3 ^ 40 * 644528 * 2
def baseEnd_644528 : Nat := 220635106187439676623917

theorem tailTrace_644528 : CollatzResearch.WordTrace tailWord_644528 prefixEnd_644528 220635106187439676623917 := by
  unfold tailWord_644528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753933704496303731931119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15671911605995071642574825 11753933704496303731931119)
  ·
    refine ⟨17630900556744455597896679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11753933704496303731931119 17630900556744455597896679)
    ·
      refine ⟨26446350835116683396845019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630900556744455597896679 26446350835116683396845019)
      ·
        refine ⟨39669526252675025095267529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26446350835116683396845019 39669526252675025095267529)
        ·
          refine ⟨29752144689506268821450647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39669526252675025095267529 29752144689506268821450647)
          ·
            refine ⟨44628217034259403232175971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29752144689506268821450647 44628217034259403232175971)
            ·
              refine ⟨66942325551389104848263957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44628217034259403232175971 66942325551389104848263957)
              ·
                refine ⟨3137921510221364289762373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66942325551389104848263957 3137921510221364289762373)
                ·
                  refine ⟨588360283166505804330445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3137921510221364289762373 588360283166505804330445)
                  ·
                    refine ⟨220635106187439676623917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588360283166505804330445 220635106187439676623917)
                    ·
                      rfl

theorem cell22_644528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_644528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644528 prefixEnd_644528 := by exact prefixLift 644528
  have htrace : WordTrace (prefixWord ++ tailWord_644528) baseStart_644528 baseEnd_644528 := by
    simpa [prefixWord, tailWord_644528, baseEnd_644528] using wordTrace_append hprefix tailTrace_644528
  have hstable : (prefixWord ++ tailWord_644528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644528).length < 2 ^ (prefixWord ++ tailWord_644528).sum := by decide
  have hdescent : baseEnd_644528 < baseStart_644528 := by decide
  rcases family_descends (prefixWord ++ tailWord_644528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644558 : List Nat := [4, 1, 1, 1, 2, 1, 5, 7]
def baseStart_644558 : Nat := 118140960795 + 644558 * 2 ^ 59
def prefixEnd_644558 : Nat := 4983230072969 + 3 ^ 40 * 644558 * 2
def baseEnd_644558 : Nat := 24516152866725510930425

theorem tailTrace_644558 : CollatzResearch.WordTrace tailWord_644558 prefixEnd_644558 24516152866725510930425 := by
  unfold tailWord_644558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938620199860490323431791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15672641065922615058302885 2938620199860490323431791)
  ·
    refine ⟨4407930299790735485147687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938620199860490323431791 4407930299790735485147687)
    ·
      refine ⟨6611895449686103227721531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407930299790735485147687 6611895449686103227721531)
      ·
        refine ⟨9917843174529154841582297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611895449686103227721531 9917843174529154841582297)
        ·
          refine ⟨7438382380896866131186723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9917843174529154841582297 7438382380896866131186723)
          ·
            refine ⟨11157573571345299196780085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438382380896866131186723 11157573571345299196780085)
            ·
              refine ⟨1046022522313621799698133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11157573571345299196780085 1046022522313621799698133)
              ·
                refine ⟨24516152866725510930425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1046022522313621799698133 24516152866725510930425)
                ·
                  rfl

theorem cell22_644558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_644558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644558 prefixEnd_644558 := by exact prefixLift 644558
  have htrace : WordTrace (prefixWord ++ tailWord_644558) baseStart_644558 baseEnd_644558 := by
    simpa [prefixWord, tailWord_644558, baseEnd_644558] using wordTrace_append hprefix tailTrace_644558
  have hstable : (prefixWord ++ tailWord_644558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644558).length < 2 ^ (prefixWord ++ tailWord_644558).sum := by decide
  have hdescent : baseEnd_644558 < baseStart_644558 := by decide
  rcases family_descends (prefixWord ++ tailWord_644558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644590 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_644590 : Nat := 118140960795 + 644590 * 2 ^ 59
def prefixEnd_644590 : Nat := 4983230072969 + 3 ^ 40 * 644590 * 2
def baseEnd_644590 : Nat := 220656330054492181573727

theorem tailTrace_644590 : CollatzResearch.WordTrace tailWord_644590 prefixEnd_644590 220656330054492181573727 := by
  unfold tailWord_644590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938766091845999006577403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15673419156511994701746149 2938766091845999006577403)
  ·
    refine ⟨4408149137768998509866105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938766091845999006577403 4408149137768998509866105)
    ·
      refine ⟨3306111853326748882399579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4408149137768998509866105 3306111853326748882399579)
      ·
        refine ⟨4959167779990123323599369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306111853326748882399579 4959167779990123323599369)
        ·
          refine ⟨3719375834992592492699527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959167779990123323599369 3719375834992592492699527)
          ·
            refine ⟨5579063752488888739049291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719375834992592492699527 5579063752488888739049291)
            ·
              refine ⟨8368595628733333108573937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579063752488888739049291 8368595628733333108573937)
              ·
                refine ⟨6276446721549999831430453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368595628733333108573937 6276446721549999831430453)
                ·
                  refine ⟨588416880145312484196605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6276446721549999831430453 588416880145312484196605)
                  ·
                    refine ⟨220656330054492181573727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588416880145312484196605 220656330054492181573727)
                    ·
                      rfl

theorem cell22_644590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_644590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644590 prefixEnd_644590 := by exact prefixLift 644590
  have htrace : WordTrace (prefixWord ++ tailWord_644590) baseStart_644590 baseEnd_644590 := by
    simpa [prefixWord, tailWord_644590, baseEnd_644590] using wordTrace_append hprefix tailTrace_644590
  have hstable : (prefixWord ++ tailWord_644590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644590).length < 2 ^ (prefixWord ++ tailWord_644590).sum := by decide
  have hdescent : baseEnd_644590 < baseStart_644590 := by decide
  rcases family_descends (prefixWord ++ tailWord_644590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644665 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 6]
def baseStart_644665 : Nat := 118140960795 + 644665 * 2 ^ 59
def prefixEnd_644665 : Nat := 4983230072969 + 3 ^ 40 * 644665 * 2
def baseEnd_644665 : Nat := 73560668029072328649499

theorem tailTrace_644665 : CollatzResearch.WordTrace tailWord_644665 prefixEnd_644665 73560668029072328649499 := by
  unfold tailWord_644665
  simp only [CollatzResearch.WordTrace]
  refine ⟨23512864209496279861599449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15675242806330853241066299 23512864209496279861599449)
  ·
    refine ⟨17634648157122209896199587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23512864209496279861599449 17634648157122209896199587)
    ·
      refine ⟨26451972235683314844299381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17634648157122209896199587 26451972235683314844299381)
      ·
        refine ⟨2479872397095310766653067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26451972235683314844299381 2479872397095310766653067)
        ·
          refine ⟨3719808595642966149979601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479872397095310766653067 3719808595642966149979601)
          ·
            refine ⟨2789856446732224612484701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719808595642966149979601 2789856446732224612484701)
            ·
              refine ⟨1046196167524584229681763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2789856446732224612484701 1046196167524584229681763)
              ·
                refine ⟨1569294251286876344522645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046196167524584229681763 1569294251286876344522645)
                ·
                  refine ⟨73560668029072328649499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1569294251286876344522645 73560668029072328649499)
                  ·
                    rfl

theorem cell22_644665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_644665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644665 prefixEnd_644665 := by exact prefixLift 644665
  have htrace : WordTrace (prefixWord ++ tailWord_644665) baseStart_644665 baseEnd_644665 := by
    simpa [prefixWord, tailWord_644665, baseEnd_644665] using wordTrace_append hprefix tailTrace_644665
  have hstable : (prefixWord ++ tailWord_644665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644665).length < 2 ^ (prefixWord ++ tailWord_644665).sum := by decide
  have hdescent : baseEnd_644665 < baseStart_644665 := by decide
  rcases family_descends (prefixWord ++ tailWord_644665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644695 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_644695 : Nat := 118140960795 + 644695 * 2 ^ 59
def prefixEnd_644695 : Nat := 4983230072969 + 3 ^ 40 * 644695 * 2
def baseEnd_644695 : Nat := 220692273700306907698405

theorem tailTrace_644695 : CollatzResearch.WordTrace tailWord_644695 prefixEnd_644695 220692273700306907698405 := by
  unfold tailWord_644695
  simp only [CollatzResearch.WordTrace]
  refine ⟨23513958399387594985191539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15675972266258396656794359 23513958399387594985191539)
  ·
    refine ⟨35270937599081392477787309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23513958399387594985191539 35270937599081392477787309)
    ·
      refine ⟨13226601599655522179170241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35270937599081392477787309 13226601599655522179170241)
      ·
        refine ⟨9919951199741641634377681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13226601599655522179170241 9919951199741641634377681)
        ·
          refine ⟨7439963399806231225783261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9919951199741641634377681 7439963399806231225783261)
          ·
            refine ⟨2789986274927336709668723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7439963399806231225783261 2789986274927336709668723)
            ·
              refine ⟨4184979412391005064503085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789986274927336709668723 4184979412391005064503085)
              ·
                refine ⟨1569367279646626899188657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4184979412391005064503085 1569367279646626899188657)
                ·
                  refine ⟨1177025459734970174391493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569367279646626899188657 1177025459734970174391493)
                  ·
                    refine ⟨220692273700306907698405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177025459734970174391493 220692273700306907698405)
                    ·
                      rfl

theorem cell22_644695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_644695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644695 prefixEnd_644695 := by exact prefixLift 644695
  have htrace : WordTrace (prefixWord ++ tailWord_644695) baseStart_644695 baseEnd_644695 := by
    simpa [prefixWord, tailWord_644695, baseEnd_644695] using wordTrace_append hprefix tailTrace_644695
  have hstable : (prefixWord ++ tailWord_644695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644695).length < 2 ^ (prefixWord ++ tailWord_644695).sum := by decide
  have hdescent : baseEnd_644695 < baseStart_644695 := by decide
  rcases family_descends (prefixWord ++ tailWord_644695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644712 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_644712 : Nat := 118140960795 + 644712 * 2 ^ 59
def prefixEnd_644712 : Nat := 4983230072969 + 3 ^ 40 * 644712 * 2
def baseEnd_644712 : Nat := 220698093147724530023353

theorem tailTrace_644712 : CollatzResearch.WordTrace tailWord_644712 prefixEnd_644712 220698093147724530023353 := by
  unfold tailWord_644712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757289220163003444280195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15676385626884004592373593 11757289220163003444280195)
  ·
    refine ⟨17635933830244505166420293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757289220163003444280195 17635933830244505166420293)
    ·
      refine ⟨3306737593170844718703805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17635933830244505166420293 3306737593170844718703805)
      ·
        refine ⟨1240026597439066769513927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3306737593170844718703805 1240026597439066769513927)
        ·
          refine ⟨1860039896158600154270891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240026597439066769513927 1860039896158600154270891)
          ·
            refine ⟨2790059844237900231406337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860039896158600154270891 2790059844237900231406337)
            ·
              refine ⟨2092544883178425173554753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790059844237900231406337 2092544883178425173554753)
              ·
                refine ⟨1569408662383818880166065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092544883178425173554753 1569408662383818880166065)
                ·
                  refine ⟨1177056496787864160124549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569408662383818880166065 1177056496787864160124549)
                  ·
                    refine ⟨220698093147724530023353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177056496787864160124549 220698093147724530023353)
                    ·
                      rfl

theorem cell22_644712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_644712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644712 prefixEnd_644712 := by exact prefixLift 644712
  have htrace : WordTrace (prefixWord ++ tailWord_644712) baseStart_644712 baseEnd_644712 := by
    simpa [prefixWord, tailWord_644712, baseEnd_644712] using wordTrace_append hprefix tailTrace_644712
  have hstable : (prefixWord ++ tailWord_644712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644712).length < 2 ^ (prefixWord ++ tailWord_644712).sum := by decide
  have hdescent : baseEnd_644712 < baseStart_644712 := by decide
  rcases family_descends (prefixWord ++ tailWord_644712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644714 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_644714 : Nat := 118140960795 + 644714 * 2 ^ 59
def prefixEnd_644714 : Nat := 4983230072969 + 3 ^ 40 * 644714 * 2
def baseEnd_644714 : Nat := 220698777788597191473347

theorem tailTrace_644714 : CollatzResearch.WordTrace tailWord_644714 prefixEnd_644714 220698777788597191473347 := by
  unfold tailWord_644714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878662846579690307533299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15676434257545840820088797 5878662846579690307533299)
  ·
    refine ⟨8817994269869535461299949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5878662846579690307533299 8817994269869535461299949)
    ·
      refine ⟨3306747851201075797987481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8817994269869535461299949 3306747851201075797987481)
      ·
        refine ⟨2480060888400806848490611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306747851201075797987481 2480060888400806848490611)
        ·
          refine ⟨3720091332601210272735917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480060888400806848490611 3720091332601210272735917)
          ·
            refine ⟨1395034249725453852275969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3720091332601210272735917 1395034249725453852275969)
            ·
              refine ⟨1046275687294090389206977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1395034249725453852275969 1046275687294090389206977)
              ·
                refine ⟨784706765470567791905233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046275687294090389206977 784706765470567791905233)
                ·
                  refine ⟨588530074102925843928925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784706765470567791905233 588530074102925843928925)
                  ·
                    refine ⟨220698777788597191473347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588530074102925843928925 220698777788597191473347)
                    ·
                      rfl

theorem cell22_644714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_644714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644714 prefixEnd_644714 := by exact prefixLift 644714
  have htrace : WordTrace (prefixWord ++ tailWord_644714) baseStart_644714 baseEnd_644714 := by
    simpa [prefixWord, tailWord_644714, baseEnd_644714] using wordTrace_append hprefix tailTrace_644714
  have hstable : (prefixWord ++ tailWord_644714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644714).length < 2 ^ (prefixWord ++ tailWord_644714).sum := by decide
  have hdescent : baseEnd_644714 < baseStart_644714 := by decide
  rcases family_descends (prefixWord ++ tailWord_644714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644744 : List Nat := [2, 1, 3, 5, 1, 1, 3, 6]
def baseStart_644744 : Nat := 118140960795 + 644744 * 2 ^ 59
def prefixEnd_644744 : Nat := 4983230072969 + 3 ^ 40 * 644744 * 2
def baseEnd_644744 : Nat := 24523227489076345913695

theorem tailTrace_644744 : CollatzResearch.WordTrace tailWord_644744 prefixEnd_644744 24523227489076345913695 := by
  unfold tailWord_644744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757872788105038176862643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15677163717473384235816857 11757872788105038176862643)
  ·
    refine ⟨17636809182157557265293965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757872788105038176862643 17636809182157557265293965)
    ·
      refine ⟨6613803443309083974485237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17636809182157557265293965 6613803443309083974485237)
      ·
        refine ⟨620044072810226622607991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6613803443309083974485237 620044072810226622607991)
        ·
          refine ⟨930066109215339933911987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620044072810226622607991 930066109215339933911987)
          ·
            refine ⟨1395099163823009900867981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930066109215339933911987 1395099163823009900867981)
            ·
              refine ⟨523162186433628712825493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395099163823009900867981 523162186433628712825493)
              ·
                refine ⟨24523227489076345913695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523162186433628712825493 24523227489076345913695)
                ·
                  rfl

theorem cell22_644744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_644744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644744 prefixEnd_644744 := by exact prefixLift 644744
  have htrace : WordTrace (prefixWord ++ tailWord_644744) baseStart_644744 baseEnd_644744 := by
    simpa [prefixWord, tailWord_644744, baseEnd_644744] using wordTrace_append hprefix tailTrace_644744
  have hstable : (prefixWord ++ tailWord_644744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644744).length < 2 ^ (prefixWord ++ tailWord_644744).sum := by decide
  have hdescent : baseEnd_644744 < baseStart_644744 := by decide
  rcases family_descends (prefixWord ++ tailWord_644744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644759 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 1, 3]
def baseStart_644759 : Nat := 118140960795 + 644759 * 2 ^ 59
def prefixEnd_644759 : Nat := 4983230072969 + 3 ^ 40 * 644759 * 2
def baseEnd_644759 : Nat := 220714182208232074098209

theorem tailTrace_644759 : CollatzResearch.WordTrace tailWord_644759 prefixEnd_644759 220714182208232074098209 := by
  unfold tailWord_644759
  simp only [CollatzResearch.WordTrace]
  refine ⟨23516292671155733915521331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15677528447437155943680887 23516292671155733915521331)
  ·
    refine ⟨35274439006733600873281997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23516292671155733915521331 35274439006733600873281997)
    ·
      refine ⟨13227914627525100327480749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35274439006733600873281997 13227914627525100327480749)
      ·
        refine ⟨4960467985321912622805281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13227914627525100327480749 4960467985321912622805281)
        ·
          refine ⟨3720350988991434467103961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960467985321912622805281 3720350988991434467103961)
          ·
            refine ⟨2790263241743575850327971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720350988991434467103961 2790263241743575850327971)
            ·
              refine ⟨4185394862615363775491957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790263241743575850327971 4185394862615363775491957)
              ·
                refine ⟨392380768370190353952371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4185394862615363775491957 392380768370190353952371)
                ·
                  refine ⟨588571152555285530928557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392380768370190353952371 588571152555285530928557)
                  ·
                    refine ⟨220714182208232074098209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588571152555285530928557 220714182208232074098209)
                    ·
                      rfl

theorem cell22_644759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_644759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644759 prefixEnd_644759 := by exact prefixLift 644759
  have htrace : WordTrace (prefixWord ++ tailWord_644759) baseStart_644759 baseEnd_644759 := by
    simpa [prefixWord, tailWord_644759, baseEnd_644759] using wordTrace_append hprefix tailTrace_644759
  have hstable : (prefixWord ++ tailWord_644759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644759).length < 2 ^ (prefixWord ++ tailWord_644759).sum := by decide
  have hdescent : baseEnd_644759 < baseStart_644759 := by decide
  rcases family_descends (prefixWord ++ tailWord_644759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644772 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_644772 : Nat := 118140960795 + 644772 * 2 ^ 59
def prefixEnd_644772 : Nat := 4983230072969 + 3 ^ 40 * 644772 * 2
def baseEnd_644772 : Nat := 73572877457968124507723

theorem tailTrace_644772 : CollatzResearch.WordTrace tailWord_644772 prefixEnd_644772 73572877457968124507723 := by
  unfold tailWord_644772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758383410054318567872285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15677844546739091423829713 11758383410054318567872285)
  ·
    refine ⟨4409393778770369462952107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11758383410054318567872285 4409393778770369462952107)
    ·
      refine ⟨6614090668155554194428161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409393778770369462952107 6614090668155554194428161)
      ·
        refine ⟨4960568001116665645821121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614090668155554194428161 4960568001116665645821121)
        ·
          refine ⟨3720426000837499234365841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960568001116665645821121 3720426000837499234365841)
          ·
            refine ⟨2790319500628124425774381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720426000837499234365841 2790319500628124425774381)
            ·
              refine ⟨1046369812735546659665393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790319500628124425774381 1046369812735546659665393)
              ·
                refine ⟨784777359551659994749045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046369812735546659665393 784777359551659994749045)
                ·
                  refine ⟨73572877457968124507723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784777359551659994749045 73572877457968124507723)
                  ·
                    rfl

theorem cell22_644772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_644772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644772 prefixEnd_644772 := by exact prefixLift 644772
  have htrace : WordTrace (prefixWord ++ tailWord_644772) baseStart_644772 baseEnd_644772 := by
    simpa [prefixWord, tailWord_644772, baseEnd_644772] using wordTrace_append hprefix tailTrace_644772
  have hstable : (prefixWord ++ tailWord_644772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644772).length < 2 ^ (prefixWord ++ tailWord_644772).sum := by decide
  have hdescent : baseEnd_644772 < baseStart_644772 := by decide
  rcases family_descends (prefixWord ++ tailWord_644772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644800 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_644800 : Nat := 118140960795 + 644800 * 2 ^ 59
def prefixEnd_644800 : Nat := 4983230072969 + 3 ^ 40 * 644800 * 2
def baseEnd_644800 : Nat := 73576072448707211274361

theorem tailTrace_644800 : CollatzResearch.WordTrace tailWord_644800 prefixEnd_644800 73576072448707211274361 := by
  unfold tailWord_644800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758894032003598958881927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15678525376004798611842569 11758894032003598958881927)
  ·
    refine ⟨17638341048005398438322891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11758894032003598958881927 17638341048005398438322891)
    ·
      refine ⟨26457511572008097657484337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17638341048005398438322891 26457511572008097657484337)
      ·
        refine ⟨19843133679006073243113253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26457511572008097657484337 19843133679006073243113253)
        ·
          refine ⟨3720587564813638733083735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19843133679006073243113253 3720587564813638733083735)
          ·
            refine ⟨5580881347220458099625603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720587564813638733083735 5580881347220458099625603)
            ·
              refine ⟨8371322020830687149438405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580881347220458099625603 8371322020830687149438405)
              ·
                refine ⟨1569622878905753840519701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8371322020830687149438405 1569622878905753840519701)
                ·
                  refine ⟨73576072448707211274361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1569622878905753840519701 73576072448707211274361)
                  ·
                    rfl

theorem cell22_644800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_644800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644800 prefixEnd_644800 := by exact prefixLift 644800
  have htrace : WordTrace (prefixWord ++ tailWord_644800) baseStart_644800 baseEnd_644800 := by
    simpa [prefixWord, tailWord_644800, baseEnd_644800] using wordTrace_append hprefix tailTrace_644800
  have hstable : (prefixWord ++ tailWord_644800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644800).length < 2 ^ (prefixWord ++ tailWord_644800).sum := by decide
  have hdescent : baseEnd_644800 < baseStart_644800 := by decide
  rcases family_descends (prefixWord ++ tailWord_644800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644815 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_644815 : Nat := 118140960795 + 644815 * 2 ^ 59
def prefixEnd_644815 : Nat := 4983230072969 + 3 ^ 40 * 644815 * 2
def baseEnd_644815 : Nat := 220733352152666594698037

theorem tailTrace_644815 : CollatzResearch.WordTrace tailWord_644815 prefixEnd_644815 220733352152666594698037 := by
  unfold tailWord_644815
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518335158952855479559899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15678890105968570319706599 23518335158952855479559899)
  ·
    refine ⟨35277502738429283219339849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23518335158952855479559899 35277502738429283219339849)
    ·
      refine ⟨26458127053821962414504887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35277502738429283219339849 26458127053821962414504887)
      ·
        refine ⟨39687190580732943621757331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26458127053821962414504887 39687190580732943621757331)
        ·
          refine ⟨59530785871099415432635997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39687190580732943621757331 59530785871099415432635997)
          ·
            refine ⟨22324044701662280787238499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59530785871099415432635997 22324044701662280787238499)
            ·
              refine ⟨33486067052493421180857749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22324044701662280787238499 33486067052493421180857749)
              ·
                refine ⟨1569659393085629117852707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33486067052493421180857749 1569659393085629117852707)
                ·
                  refine ⟨2354489089628443676779061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569659393085629117852707 2354489089628443676779061)
                  ·
                    refine ⟨220733352152666594698037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2354489089628443676779061 220733352152666594698037)
                    ·
                      rfl

theorem cell22_644815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_644815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644815 prefixEnd_644815 := by exact prefixLift 644815
  have htrace : WordTrace (prefixWord ++ tailWord_644815) baseStart_644815 baseEnd_644815 := by
    simpa [prefixWord, tailWord_644815, baseEnd_644815] using wordTrace_append hprefix tailTrace_644815
  have hstable : (prefixWord ++ tailWord_644815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644815).length < 2 ^ (prefixWord ++ tailWord_644815).sum := by decide
  have hdescent : baseEnd_644815 < baseStart_644815 := by decide
  rcases family_descends (prefixWord ++ tailWord_644815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644832 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_644832 : Nat := 118140960795 + 644832 * 2 ^ 59
def prefixEnd_644832 : Nat := 4983230072969 + 3 ^ 40 * 644832 * 2
def baseEnd_644832 : Nat := 220739171600084217022985

theorem tailTrace_644832 : CollatzResearch.WordTrace tailWord_644832 prefixEnd_644832 220739171600084217022985 := by
  unfold tailWord_644832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759477599945633691464375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15679303466594178255285833 11759477599945633691464375)
  ·
    refine ⟨17639216399918450537196563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11759477599945633691464375 17639216399918450537196563)
    ·
      refine ⟨26458824599877675805794845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17639216399918450537196563 26458824599877675805794845)
      ·
        refine ⟨9922059224954128427173067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26458824599877675805794845 9922059224954128427173067)
        ·
          refine ⟨14883088837431192640759601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922059224954128427173067 14883088837431192640759601)
          ·
            refine ⟨11162316628073394480569701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14883088837431192640759601 11162316628073394480569701)
            ·
              refine ⟨2092934367763761465106819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11162316628073394480569701 2092934367763761465106819)
              ·
                refine ⟨3139401551645642197660229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092934367763761465106819 3139401551645642197660229)
                ·
                  refine ⟨588637790933557912061293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3139401551645642197660229 588637790933557912061293)
                  ·
                    refine ⟨220739171600084217022985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588637790933557912061293 220739171600084217022985)
                    ·
                      rfl

theorem cell22_644832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_644832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644832 prefixEnd_644832 := by exact prefixLift 644832
  have htrace : WordTrace (prefixWord ++ tailWord_644832) baseStart_644832 baseEnd_644832 := by
    simpa [prefixWord, tailWord_644832, baseEnd_644832] using wordTrace_append hprefix tailTrace_644832
  have hstable : (prefixWord ++ tailWord_644832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644832).length < 2 ^ (prefixWord ++ tailWord_644832).sum := by decide
  have hdescent : baseEnd_644832 < baseStart_644832 := by decide
  rcases family_descends (prefixWord ++ tailWord_644832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644849 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_644849 : Nat := 118140960795 + 644849 * 2 ^ 59
def prefixEnd_644849 : Nat := 4983230072969 + 3 ^ 40 * 644849 * 2
def baseEnd_644849 : Nat := 220744991047501839347933

theorem tailTrace_644849 : CollatzResearch.WordTrace tailWord_644849 prefixEnd_644849 220744991047501839347933 := by
  unfold tailWord_644849
  simp only [CollatzResearch.WordTrace]
  refine ⟨23519575240829679286297601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15679716827219786190865067 23519575240829679286297601)
  ·
    refine ⟨17639681430622259464723201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23519575240829679286297601 17639681430622259464723201)
    ·
      refine ⟨13229761072966694598542401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17639681430622259464723201 13229761072966694598542401)
      ·
        refine ⟨9922320804725020948906801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13229761072966694598542401 9922320804725020948906801)
        ·
          refine ⟨7441740603543765711680101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922320804725020948906801 7441740603543765711680101)
          ·
            refine ⟨1395326363164456070940019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7441740603543765711680101 1395326363164456070940019)
            ·
              refine ⟨2092989544746684106410029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395326363164456070940019 2092989544746684106410029)
              ·
                refine ⟨784871079280006539903761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2092989544746684106410029 784871079280006539903761)
                ·
                  refine ⟨588653309460004904927821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784871079280006539903761 588653309460004904927821)
                  ·
                    refine ⟨220744991047501839347933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588653309460004904927821 220744991047501839347933)
                    ·
                      rfl

theorem cell22_644849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_644849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644849 prefixEnd_644849 := by exact prefixLift 644849
  have htrace : WordTrace (prefixWord ++ tailWord_644849) baseStart_644849 baseEnd_644849 := by
    simpa [prefixWord, tailWord_644849, baseEnd_644849] using wordTrace_append hprefix tailTrace_644849
  have hstable : (prefixWord ++ tailWord_644849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644849).length < 2 ^ (prefixWord ++ tailWord_644849).sum := by decide
  have hdescent : baseEnd_644849 < baseStart_644849 := by decide
  rcases family_descends (prefixWord ++ tailWord_644849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644941 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 5]
def baseStart_644941 : Nat := 118140960795 + 644941 * 2 ^ 59
def prefixEnd_644941 : Nat := 4983230072969 + 3 ^ 40 * 644941 * 2
def baseEnd_644941 : Nat := 73592161509214755349217

theorem tailTrace_644941 : CollatzResearch.WordTrace tailWord_644941 prefixEnd_644941 73592161509214755349217 := by
  unfold tailWord_644941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23522930756496378998646677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15681953837664252665764451 23522930756496378998646677)
  ·
    refine ⟨1102637379210767765561563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23522930756496378998646677 1102637379210767765561563)
    ·
      refine ⟨1653956068816151648342345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102637379210767765561563 1653956068816151648342345)
      ·
        refine ⟨1240467051612113736256759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1653956068816151648342345 1240467051612113736256759)
        ·
          refine ⟨1860700577418170604385139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240467051612113736256759 1860700577418170604385139)
          ·
            refine ⟨2791050866127255906577709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860700577418170604385139 2791050866127255906577709)
            ·
              refine ⟨1046644074797720964966641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2791050866127255906577709 1046644074797720964966641)
              ·
                refine ⟨784983056098290723724981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046644074797720964966641 784983056098290723724981)
                ·
                  refine ⟨73592161509214755349217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784983056098290723724981 73592161509214755349217)
                  ·
                    rfl

theorem cell22_644941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_644941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_644941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_644941 prefixEnd_644941 := by exact prefixLift 644941
  have htrace : WordTrace (prefixWord ++ tailWord_644941) baseStart_644941 baseEnd_644941 := by
    simpa [prefixWord, tailWord_644941, baseEnd_644941] using wordTrace_append hprefix tailTrace_644941
  have hstable : (prefixWord ++ tailWord_644941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644941).length < 2 ^ (prefixWord ++ tailWord_644941).sum := by decide
  have hdescent : baseEnd_644941 < baseStart_644941 := by decide
  rcases family_descends (prefixWord ++ tailWord_644941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645018 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_645018 : Nat := 118140960795 + 645018 * 2 ^ 59
def prefixEnd_645018 : Nat := 4983230072969 + 3 ^ 40 * 645018 * 2
def baseEnd_645018 : Nat := 220802843201241731872415

theorem tailTrace_645018 : CollatzResearch.WordTrace tailWord_645018 prefixEnd_645018 220802843201241731872415 := by
  unfold tailWord_645018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881434794304355287299927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15683826118144947432799805 5881434794304355287299927)
  ·
    refine ⟨8822152191456532930949891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5881434794304355287299927 8822152191456532930949891)
    ·
      refine ⟨13233228287184799396424837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8822152191456532930949891 13233228287184799396424837)
      ·
        refine ⟨2481230303847149886829657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13233228287184799396424837 2481230303847149886829657)
        ·
          refine ⟨1860922727885362415122243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481230303847149886829657 1860922727885362415122243)
          ·
            refine ⟨2791384091828043622683365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860922727885362415122243 2791384091828043622683365)
            ·
              refine ⟨523384517217758179253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2791384091828043622683365 523384517217758179253131)
              ·
                refine ⟨785076775826637268879697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523384517217758179253131 785076775826637268879697)
                ·
                  refine ⟨588807581869977951659773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785076775826637268879697 588807581869977951659773)
                  ·
                    refine ⟨220802843201241731872415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588807581869977951659773 220802843201241731872415)
                    ·
                      rfl

theorem cell22_645018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_645018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645018 prefixEnd_645018 := by exact prefixLift 645018
  have htrace : WordTrace (prefixWord ++ tailWord_645018) baseStart_645018 baseEnd_645018 := by
    simpa [prefixWord, tailWord_645018, baseEnd_645018] using wordTrace_append hprefix tailTrace_645018
  have hstable : (prefixWord ++ tailWord_645018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645018).length < 2 ^ (prefixWord ++ tailWord_645018).sum := by decide
  have hdescent : baseEnd_645018 < baseStart_645018 := by decide
  rcases family_descends (prefixWord ++ tailWord_645018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645022 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_645022 : Nat := 118140960795 + 645022 * 2 ^ 59
def prefixEnd_645022 : Nat := 4983230072969 + 3 ^ 40 * 645022 * 2
def baseEnd_645022 : Nat := 220804212482987054772403

theorem tailTrace_645022 : CollatzResearch.WordTrace tailWord_645022 prefixEnd_645022 220804212482987054772403 := by
  unfold tailWord_645022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940735633650366229043165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15683923379468619888230213 2940735633650366229043165)
  ·
    refine ⟨1102775862618887335891187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2940735633650366229043165 1102775862618887335891187)
    ·
      refine ⟨1654163793928331003836781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102775862618887335891187 1654163793928331003836781)
      ·
        refine ⟨620311422723124126438793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1654163793928331003836781 620311422723124126438793)
        ·
          refine ⟨465233567042343094829095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620311422723124126438793 465233567042343094829095)
          ·
            refine ⟨697850350563514642243643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465233567042343094829095 697850350563514642243643)
            ·
              refine ⟨1046775525845271963365465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697850350563514642243643 1046775525845271963365465)
              ·
                refine ⟨785081644383953972524099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046775525845271963365465 785081644383953972524099)
                ·
                  refine ⟨1177622466575930958786149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785081644383953972524099 1177622466575930958786149)
                  ·
                    refine ⟨220804212482987054772403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177622466575930958786149 220804212482987054772403)
                    ·
                      rfl

theorem cell22_645022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_645022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645022 prefixEnd_645022 := by exact prefixLift 645022
  have htrace : WordTrace (prefixWord ++ tailWord_645022) baseStart_645022 baseEnd_645022 := by
    simpa [prefixWord, tailWord_645022, baseEnd_645022] using wordTrace_append hprefix tailTrace_645022
  have hstable : (prefixWord ++ tailWord_645022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645022).length < 2 ^ (prefixWord ++ tailWord_645022).sum := by decide
  have hdescent : baseEnd_645022 < baseStart_645022 := by decide
  rcases family_descends (prefixWord ++ tailWord_645022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645029 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_645029 : Nat := 118140960795 + 645029 * 2 ^ 59
def prefixEnd_645029 : Nat := 4983230072969 + 3 ^ 40 * 645029 * 2
def baseEnd_645029 : Nat := 220806608726041369847381

theorem tailTrace_645029 : CollatzResearch.WordTrace tailWord_645029 prefixEnd_645029 220806608726041369847381 := by
  unfold tailWord_645029
  simp only [CollatzResearch.WordTrace]
  refine ⟨23526140380177570027850141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15684093586785046685233427 23526140380177570027850141)
  ·
    refine ⟨8822302642566588760443803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23526140380177570027850141 8822302642566588760443803)
    ·
      refine ⟨13233453963849883140665705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8822302642566588760443803 13233453963849883140665705)
      ·
        refine ⟨9925090472887412355499279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13233453963849883140665705 9925090472887412355499279)
        ·
          refine ⟨14887635709331118533248919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925090472887412355499279 14887635709331118533248919)
          ·
            refine ⟨22331453563996677799873379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887635709331118533248919 22331453563996677799873379)
            ·
              refine ⟨33497180345995016699810069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22331453563996677799873379 33497180345995016699810069)
              ·
                refine ⟨1570180328718516407803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33497180345995016699810069 1570180328718516407803597)
                ·
                  refine ⟨588817623269443652926349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1570180328718516407803597 588817623269443652926349)
                  ·
                    refine ⟨220806608726041369847381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588817623269443652926349 220806608726041369847381)
                    ·
                      rfl

theorem cell22_645029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_645029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645029 prefixEnd_645029 := by exact prefixLift 645029
  have htrace : WordTrace (prefixWord ++ tailWord_645029) baseStart_645029 baseEnd_645029 := by
    simpa [prefixWord, tailWord_645029, baseEnd_645029] using wordTrace_append hprefix tailTrace_645029
  have hstable : (prefixWord ++ tailWord_645029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645029).length < 2 ^ (prefixWord ++ tailWord_645029).sum := by decide
  have hdescent : baseEnd_645029 < baseStart_645029 := by decide
  rcases family_descends (prefixWord ++ tailWord_645029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645042 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_645042 : Nat := 118140960795 + 645042 * 2 ^ 59
def prefixEnd_645042 : Nat := 4983230072969 + 3 ^ 40 * 645042 * 2
def baseEnd_645042 : Nat := 73603686297237889757447

theorem tailTrace_645042 : CollatzResearch.WordTrace tailWord_645042 prefixEnd_645042 73603686297237889757447 := by
  unfold tailWord_645042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881653632282618312018345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15684409686086982165382253 5881653632282618312018345)
  ·
    refine ⟨4411240224211963734013759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5881653632282618312018345 4411240224211963734013759)
    ·
      refine ⟨6616860336317945601020639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411240224211963734013759 6616860336317945601020639)
      ·
        refine ⟨9925290504476918401530959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6616860336317945601020639 9925290504476918401530959)
        ·
          refine ⟨14887935756715377602296439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925290504476918401530959 14887935756715377602296439)
          ·
            refine ⟨22331903635073066403444659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887935756715377602296439 22331903635073066403444659)
            ·
              refine ⟨33497855452609599605166989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22331903635073066403444659 33497855452609599605166989)
              ·
                refine ⟨12561695794728599851937621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33497855452609599605166989 12561695794728599851937621)
                ·
                  refine ⟨73603686297237889757447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12561695794728599851937621 73603686297237889757447)
                  ·
                    rfl

theorem cell22_645042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_645042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645042 prefixEnd_645042 := by exact prefixLift 645042
  have htrace : WordTrace (prefixWord ++ tailWord_645042) baseStart_645042 baseEnd_645042 := by
    simpa [prefixWord, tailWord_645042, baseEnd_645042] using wordTrace_append hprefix tailTrace_645042
  have hstable : (prefixWord ++ tailWord_645042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645042).length < 2 ^ (prefixWord ++ tailWord_645042).sum := by decide
  have hdescent : baseEnd_645042 < baseStart_645042 := by decide
  rcases family_descends (prefixWord ++ tailWord_645042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645089 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_645089 : Nat := 118140960795 + 645089 * 2 ^ 59
def prefixEnd_645089 : Nat := 4983230072969 + 3 ^ 40 * 645089 * 2
def baseEnd_645089 : Nat := 220827147952221213347197

theorem tailTrace_645089 : CollatzResearch.WordTrace tailWord_645089 prefixEnd_645089 220827147952221213347197 := by
  unfold tailWord_645089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528328759960200275034321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15685552506640133516689547 23528328759960200275034321)
  ·
    refine ⟨17646246569970150206275741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23528328759960200275034321 17646246569970150206275741)
    ·
      refine ⟨6617342463738806327353403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17646246569970150206275741 6617342463738806327353403)
      ·
        refine ⟨9926013695608209491030105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617342463738806327353403 9926013695608209491030105)
        ·
          refine ⟨7444510271706157118272579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9926013695608209491030105 7444510271706157118272579)
          ·
            refine ⟨11166765407559235677408869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444510271706157118272579 11166765407559235677408869)
            ·
              refine ⟨2093768513917356689514163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11166765407559235677408869 2093768513917356689514163)
              ·
                refine ⟨3140652770876035034271245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093768513917356689514163 3140652770876035034271245)
                ·
                  refine ⟨1177744789078513137851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3140652770876035034271245 1177744789078513137851717)
                  ·
                    refine ⟨220827147952221213347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177744789078513137851717 220827147952221213347197)
                    ·
                      rfl

theorem cell22_645089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_645089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645089 prefixEnd_645089 := by exact prefixLift 645089
  have htrace : WordTrace (prefixWord ++ tailWord_645089) baseStart_645089 baseEnd_645089 := by
    simpa [prefixWord, tailWord_645089, baseEnd_645089] using wordTrace_append hprefix tailTrace_645089
  have hstable : (prefixWord ++ tailWord_645089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645089).length < 2 ^ (prefixWord ++ tailWord_645089).sum := by decide
  have hdescent : baseEnd_645089 < baseStart_645089 := by decide
  rcases family_descends (prefixWord ++ tailWord_645089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645110 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_645110 : Nat := 118140960795 + 645110 * 2 ^ 59
def prefixEnd_645110 : Nat := 4983230072969 + 3 ^ 40 * 645110 * 2
def baseEnd_645110 : Nat := 73611445560461386190711

theorem tailTrace_645110 : CollatzResearch.WordTrace tailWord_645110 prefixEnd_645110 73611445560461386190711 := by
  unfold tailWord_645110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470568418305257553846799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15686063128589413907699189 1470568418305257553846799)
  ·
    refine ⟨2205852627457886330770199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470568418305257553846799 2205852627457886330770199)
    ·
      refine ⟨3308778941186829496155299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205852627457886330770199 3308778941186829496155299)
      ·
        refine ⟨4963168411780244244232949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308778941186829496155299 4963168411780244244232949)
        ·
          refine ⟨465297038604397897896839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4963168411780244244232949 465297038604397897896839)
          ·
            refine ⟨697945557906596846845259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465297038604397897896839 697945557906596846845259)
            ·
              refine ⟨1046918336859895270267889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697945557906596846845259 1046918336859895270267889)
              ·
                refine ⟨785188752644921452700917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046918336859895270267889 785188752644921452700917)
                ·
                  refine ⟨73611445560461386190711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785188752644921452700917 73611445560461386190711)
                  ·
                    rfl

theorem cell22_645110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_645110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645110 prefixEnd_645110 := by exact prefixLift 645110
  have htrace : WordTrace (prefixWord ++ tailWord_645110) baseStart_645110 baseEnd_645110 := by
    simpa [prefixWord, tailWord_645110, baseEnd_645110] using wordTrace_append hprefix tailTrace_645110
  have hstable : (prefixWord ++ tailWord_645110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645110).length < 2 ^ (prefixWord ++ tailWord_645110).sum := by decide
  have hdescent : baseEnd_645110 < baseStart_645110 := by decide
  rcases family_descends (prefixWord ++ tailWord_645110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645121 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 4]
def baseStart_645121 : Nat := 118140960795 + 645121 * 2 ^ 59
def prefixEnd_645121 : Nat := 4983230072969 + 3 ^ 40 * 645121 * 2
def baseEnd_645121 : Nat := 73612700735394598849033

theorem tailTrace_645121 : CollatzResearch.WordTrace tailWord_645121 prefixEnd_645121 73612700735394598849033 := by
  unfold tailWord_645121
  simp only [CollatzResearch.WordTrace]
  refine ⟨23529495895844269740199217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15686330597229513160132811 23529495895844269740199217)
  ·
    refine ⟨17647121921883202305149413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23529495895844269740199217 17647121921883202305149413)
    ·
      refine ⟨3308835360353100432215515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17647121921883202305149413 3308835360353100432215515)
      ·
        refine ⟨4963253040529650648323273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308835360353100432215515 4963253040529650648323273)
        ·
          refine ⟨3722439780397237986242455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963253040529650648323273 3722439780397237986242455)
          ·
            refine ⟨5583659670595856979363683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722439780397237986242455 5583659670595856979363683)
            ·
              refine ⟨8375489505893785469045525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583659670595856979363683 8375489505893785469045525)
              ·
                refine ⟨392601070588771193861509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8375489505893785469045525 392601070588771193861509)
                ·
                  refine ⟨73612700735394598849033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392601070588771193861509 73612700735394598849033)
                  ·
                    rfl

theorem cell22_645121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_645121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645121 prefixEnd_645121 := by exact prefixLift 645121
  have htrace : WordTrace (prefixWord ++ tailWord_645121) baseStart_645121 baseEnd_645121 := by
    simpa [prefixWord, tailWord_645121, baseEnd_645121] using wordTrace_append hprefix tailTrace_645121
  have hstable : (prefixWord ++ tailWord_645121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645121).length < 2 ^ (prefixWord ++ tailWord_645121).sum := by decide
  have hdescent : baseEnd_645121 < baseStart_645121 := by decide
  rcases family_descends (prefixWord ++ tailWord_645121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645134 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_645134 : Nat := 118140960795 + 645134 * 2 ^ 59
def prefixEnd_645134 : Nat := 4983230072969 + 3 ^ 40 * 645134 * 2
def baseEnd_645134 : Nat := 220842552371856095972059

theorem tailTrace_645134 : CollatzResearch.WordTrace tailWord_645134 prefixEnd_645134 220842552371856095972059 := by
  unfold tailWord_645134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941246255599646620052807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15686646696531448640281637 2941246255599646620052807)
  ·
    refine ⟨4411869383399469930079211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941246255599646620052807 4411869383399469930079211)
    ·
      refine ⟨6617804075099204895118817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411869383399469930079211 6617804075099204895118817)
      ·
        refine ⟨4963353056324403671339113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6617804075099204895118817 4963353056324403671339113)
        ·
          refine ⟨3722514792243302753504335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963353056324403671339113 3722514792243302753504335)
          ·
            refine ⟨5583772188364954130256503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722514792243302753504335 5583772188364954130256503)
            ·
              refine ⟨8375658282547431195384755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583772188364954130256503 8375658282547431195384755)
              ·
                refine ⟨12563487423821146793077133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375658282547431195384755 12563487423821146793077133)
                ·
                  refine ⟨4711307783932930047403925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12563487423821146793077133 4711307783932930047403925)
                  ·
                    refine ⟨220842552371856095972059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4711307783932930047403925 220842552371856095972059)
                    ·
                      rfl

theorem cell22_645134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_645134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645134 prefixEnd_645134 := by exact prefixLift 645134
  have htrace : WordTrace (prefixWord ++ tailWord_645134) baseStart_645134 baseEnd_645134 := by
    simpa [prefixWord, tailWord_645134, baseEnd_645134] using wordTrace_append hprefix tailTrace_645134
  have hstable : (prefixWord ++ tailWord_645134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645134).length < 2 ^ (prefixWord ++ tailWord_645134).sum := by decide
  have hdescent : baseEnd_645134 < baseStart_645134 := by decide
  rcases family_descends (prefixWord ++ tailWord_645134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645166 : List Nat := [4, 1, 3, 1, 1, 4, 8]
def baseStart_645166 : Nat := 118140960795 + 645166 * 2 ^ 59
def prefixEnd_645166 : Nat := 4983230072969 + 3 ^ 40 * 645166 * 2
def baseEnd_645166 : Nat := 8179759504659951080443

theorem tailTrace_645166 : CollatzResearch.WordTrace tailWord_645166 prefixEnd_645166 8179759504659951080443 := by
  unfold tailWord_645166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941392147585155303198419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15687424787120828283724901 2941392147585155303198419)
  ·
    refine ⟨4412088221377732954797629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941392147585155303198419 4412088221377732954797629)
    ·
      refine ⟨1654533083016649858049111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4412088221377732954797629 1654533083016649858049111)
      ·
        refine ⟨2481799624524974787073667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654533083016649858049111 2481799624524974787073667)
        ·
          refine ⟨3722699436787462180610501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481799624524974787073667 3722699436787462180610501)
          ·
            refine ⟨698006144397649158864469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3722699436787462180610501 698006144397649158864469)
            ·
              refine ⟨8179759504659951080443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 698006144397649158864469 8179759504659951080443)
              ·
                rfl

theorem cell22_645166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 8].length) (baseStart_645166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645166 prefixEnd_645166 := by exact prefixLift 645166
  have htrace : WordTrace (prefixWord ++ tailWord_645166) baseStart_645166 baseEnd_645166 := by
    simpa [prefixWord, tailWord_645166, baseEnd_645166] using wordTrace_append hprefix tailTrace_645166
  have hstable : (prefixWord ++ tailWord_645166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645166).length < 2 ^ (prefixWord ++ tailWord_645166).sum := by decide
  have hdescent : baseEnd_645166 < baseStart_645166 := by decide
  rcases family_descends (prefixWord ++ tailWord_645166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645172 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_645172 : Nat := 118140960795 + 645172 * 2 ^ 59
def prefixEnd_645172 : Nat := 4983230072969 + 3 ^ 40 * 645172 * 2
def baseEnd_645172 : Nat := 73618520182812221173981

theorem tailTrace_645172 : CollatzResearch.WordTrace tailWord_645172 prefixEnd_645172 73618520182812221173981 := by
  unfold tailWord_645172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765678009329752725152885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15687570679106336966870513 11765678009329752725152885)
  ·
    refine ⟨1103032313374664317983083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11765678009329752725152885 1103032313374664317983083)
    ·
      refine ⟨1654548470061996476974625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103032313374664317983083 1654548470061996476974625)
      ·
        refine ⟨1240911352546497357730969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1654548470061996476974625 1240911352546497357730969)
        ·
          refine ⟨930683514409873018298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240911352546497357730969 930683514409873018298227)
          ·
            refine ⟨1396025271614809527447341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930683514409873018298227 1396025271614809527447341)
            ·
              refine ⟨523509476855553572792753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396025271614809527447341 523509476855553572792753)
              ·
                refine ⟨392632107641665179594565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523509476855553572792753 392632107641665179594565)
                ·
                  refine ⟨73618520182812221173981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392632107641665179594565 73618520182812221173981)
                  ·
                    rfl

theorem cell22_645172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_645172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645172 prefixEnd_645172 := by exact prefixLift 645172
  have htrace : WordTrace (prefixWord ++ tailWord_645172) baseStart_645172 baseEnd_645172 := by
    simpa [prefixWord, tailWord_645172, baseEnd_645172] using wordTrace_append hprefix tailTrace_645172
  have hstable : (prefixWord ++ tailWord_645172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645172).length < 2 ^ (prefixWord ++ tailWord_645172).sum := by decide
  have hdescent : baseEnd_645172 < baseStart_645172 := by decide
  rcases family_descends (prefixWord ++ tailWord_645172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645232 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_645232 : Nat := 118140960795 + 645232 * 2 ^ 59
def prefixEnd_645232 : Nat := 4983230072969 + 3 ^ 40 * 645232 * 2
def baseEnd_645232 : Nat := 220876099774616507021759

theorem tailTrace_645232 : CollatzResearch.WordTrace tailWord_645232 prefixEnd_645232 220876099774616507021759 := by
  unfold tailWord_645232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766772199221067848744975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15689029598961423798326633 11766772199221067848744975)
  ·
    refine ⟨17650158298831601773117463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11766772199221067848744975 17650158298831601773117463)
    ·
      refine ⟨26475237448247402659676195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17650158298831601773117463 26475237448247402659676195)
      ·
        refine ⟨39712856172371103989514293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26475237448247402659676195 39712856172371103989514293)
        ·
          refine ⟨3723080266159790999016965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39712856172371103989514293 3723080266159790999016965)
          ·
            refine ⟨698077549904960812315681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3723080266159790999016965 698077549904960812315681)
            ·
              refine ⟨523558162428720609236761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698077549904960812315681 523558162428720609236761)
              ·
                refine ⟨392668621821540456927571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523558162428720609236761 392668621821540456927571)
                ·
                  refine ⟨589002932732310685391357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392668621821540456927571 589002932732310685391357)
                  ·
                    refine ⟨220876099774616507021759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589002932732310685391357 220876099774616507021759)
                    ·
                      rfl

theorem cell22_645232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_645232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645232 prefixEnd_645232 := by exact prefixLift 645232
  have htrace : WordTrace (prefixWord ++ tailWord_645232) baseStart_645232 baseEnd_645232 := by
    simpa [prefixWord, tailWord_645232, baseEnd_645232] using wordTrace_append hprefix tailTrace_645232
  have hstable : (prefixWord ++ tailWord_645232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645232).length < 2 ^ (prefixWord ++ tailWord_645232).sum := by decide
  have hdescent : baseEnd_645232 < baseStart_645232 := by decide
  rcases family_descends (prefixWord ++ tailWord_645232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645241 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_645241 : Nat := 118140960795 + 645241 * 2 ^ 59
def prefixEnd_645241 : Nat := 4983230072969 + 3 ^ 40 * 645241 * 2
def baseEnd_645241 : Nat := 220879180658543483546731

theorem tailTrace_645241 : CollatzResearch.WordTrace tailWord_645241 prefixEnd_645241 220879180658543483546731 := by
  unfold tailWord_645241
  simp only [CollatzResearch.WordTrace]
  refine ⟨23533872655409530234567577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15689248436939686823045051 23533872655409530234567577)
  ·
    refine ⟨17650404491557147675925683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23533872655409530234567577 17650404491557147675925683)
    ·
      refine ⟨26475606737335721513888525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17650404491557147675925683 26475606737335721513888525)
      ·
        refine ⟨9928352526500895567708197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26475606737335721513888525 9928352526500895567708197)
        ·
          refine ⟨1861566098718917918945287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9928352526500895567708197 1861566098718917918945287)
          ·
            refine ⟨2792349148078376878417931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861566098718917918945287 2792349148078376878417931)
            ·
              refine ⟨4188523722117565317626897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792349148078376878417931 4188523722117565317626897)
              ·
                refine ⟨3141392791588173988220173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188523722117565317626897 3141392791588173988220173)
                ·
                  refine ⟨1178022296845565245582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3141392791588173988220173 1178022296845565245582565)
                  ·
                    refine ⟨220879180658543483546731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1178022296845565245582565 220879180658543483546731)
                    ·
                      rfl

theorem cell22_645241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_645241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645241 prefixEnd_645241 := by exact prefixLift 645241
  have htrace : WordTrace (prefixWord ++ tailWord_645241) baseStart_645241 baseEnd_645241 := by
    simpa [prefixWord, tailWord_645241, baseEnd_645241] using wordTrace_append hprefix tailTrace_645241
  have hstable : (prefixWord ++ tailWord_645241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645241).length < 2 ^ (prefixWord ++ tailWord_645241).sum := by decide
  have hdescent : baseEnd_645241 < baseStart_645241 := by decide
  rcases family_descends (prefixWord ++ tailWord_645241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645256 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_645256 : Nat := 118140960795 + 645256 * 2 ^ 59
def prefixEnd_645256 : Nat := 4983230072969 + 3 ^ 40 * 645256 * 2
def baseEnd_645256 : Nat := 73628105155029481473895

theorem tailTrace_645256 : CollatzResearch.WordTrace tailWord_645256 prefixEnd_645256 73628105155029481473895 := by
  unfold tailWord_645256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11767209875177593898181811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15689613166903458530909081 11767209875177593898181811)
  ·
    refine ⟨17650814812766390847272717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11767209875177593898181811 17650814812766390847272717)
    ·
      refine ⟨6619055554787396567727269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17650814812766390847272717 6619055554787396567727269)
      ·
        refine ⟨1241072916522636856448863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6619055554787396567727269 1241072916522636856448863)
        ·
          refine ⟨1861609374783955284673295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241072916522636856448863 1861609374783955284673295)
          ·
            refine ⟨2792414062175932927009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861609374783955284673295 2792414062175932927009943)
            ·
              refine ⟨4188621093263899390514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792414062175932927009943 4188621093263899390514915)
              ·
                refine ⟨6282931639895849085772373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188621093263899390514915 6282931639895849085772373)
                ·
                  refine ⟨73628105155029481473895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6282931639895849085772373 73628105155029481473895)
                  ·
                    rfl

theorem cell22_645256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_645256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645256 prefixEnd_645256 := by exact prefixLift 645256
  have htrace : WordTrace (prefixWord ++ tailWord_645256) baseStart_645256 baseEnd_645256 := by
    simpa [prefixWord, tailWord_645256, baseEnd_645256] using wordTrace_append hprefix tailTrace_645256
  have hstable : (prefixWord ++ tailWord_645256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645256).length < 2 ^ (prefixWord ++ tailWord_645256).sum := by decide
  have hdescent : baseEnd_645256 < baseStart_645256 := by decide
  rcases family_descends (prefixWord ++ tailWord_645256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645290 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_645290 : Nat := 118140960795 + 645290 * 2 ^ 59
def prefixEnd_645290 : Nat := 4983230072969 + 3 ^ 40 * 645290 * 2
def baseEnd_645290 : Nat := 73631984786641229690527

theorem tailTrace_645290 : CollatzResearch.WordTrace tailWord_645290 prefixEnd_645290 73631984786641229690527 := by
  unfold tailWord_645290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883914958058002900775331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15690439888154674402067549 5883914958058002900775331)
  ·
    refine ⟨8825872437087004351162997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5883914958058002900775331 8825872437087004351162997)
    ·
      refine ⟨827425540976906657921531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8825872437087004351162997 827425540976906657921531)
      ·
        refine ⟨1241138311465359986882297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827425540976906657921531 1241138311465359986882297)
        ·
          refine ⟨930853733599019990161723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241138311465359986882297 930853733599019990161723)
          ·
            refine ⟨1396280600398529985242585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930853733599019990161723 1396280600398529985242585)
            ·
              refine ⟨1047210450298897488931939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396280600398529985242585 1047210450298897488931939)
              ·
                refine ⟨1570815675448346233397909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047210450298897488931939 1570815675448346233397909)
                ·
                  refine ⟨73631984786641229690527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1570815675448346233397909 73631984786641229690527)
                  ·
                    rfl

theorem cell22_645290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_645290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645290 prefixEnd_645290 := by exact prefixLift 645290
  have htrace : WordTrace (prefixWord ++ tailWord_645290) baseStart_645290 baseEnd_645290 := by
    simpa [prefixWord, tailWord_645290, baseEnd_645290] using wordTrace_append hprefix tailTrace_645290
  have hstable : (prefixWord ++ tailWord_645290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645290).length < 2 ^ (prefixWord ++ tailWord_645290).sum := by decide
  have hdescent : baseEnd_645290 < baseStart_645290 := by decide
  rcases family_descends (prefixWord ++ tailWord_645290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645305 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_645305 : Nat := 118140960795 + 645305 * 2 ^ 59
def prefixEnd_645305 : Nat := 4983230072969 + 3 ^ 40 * 645305 * 2
def baseEnd_645305 : Nat := 220901089166468649946535

theorem tailTrace_645305 : CollatzResearch.WordTrace tailWord_645305 prefixEnd_645305 220901089166468649946535 := by
  unfold tailWord_645305
  simp only [CollatzResearch.WordTrace]
  refine ⟨23536206927177669164897369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15690804618118446109931579 23536206927177669164897369)
  ·
    refine ⟨17652155195383251873673027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23536206927177669164897369 17652155195383251873673027)
    ·
      refine ⟨26478232793074877810509541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17652155195383251873673027 26478232793074877810509541)
      ·
        refine ⟨4964668648701539589470539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26478232793074877810509541 4964668648701539589470539)
        ·
          refine ⟨7447002973052309384205809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964668648701539589470539 7447002973052309384205809)
          ·
            refine ⟨5585252229789232038154357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447002973052309384205809 5585252229789232038154357)
            ·
              refine ⟨523617396542740503576971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5585252229789232038154357 523617396542740503576971)
              ·
                refine ⟨785426094814110755365457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523617396542740503576971 785426094814110755365457)
                ·
                  refine ⟨589069571110583066524093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785426094814110755365457 589069571110583066524093)
                  ·
                    refine ⟨220901089166468649946535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589069571110583066524093 220901089166468649946535)
                    ·
                      rfl

theorem cell22_645305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_645305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645305 prefixEnd_645305 := by exact prefixLift 645305
  have htrace : WordTrace (prefixWord ++ tailWord_645305) baseStart_645305 baseEnd_645305 := by
    simpa [prefixWord, tailWord_645305, baseEnd_645305] using wordTrace_append hprefix tailTrace_645305
  have hstable : (prefixWord ++ tailWord_645305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645305).length < 2 ^ (prefixWord ++ tailWord_645305).sum := by decide
  have hdescent : baseEnd_645305 < baseStart_645305 := by decide
  rcases family_descends (prefixWord ++ tailWord_645305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645324 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_645324 : Nat := 118140960795 + 645324 * 2 ^ 59
def prefixEnd_645324 : Nat := 4983230072969 + 3 ^ 40 * 645324 * 2
def baseEnd_645324 : Nat := 73635864418252977907159

theorem tailTrace_645324 : CollatzResearch.WordTrace tailWord_645324 prefixEnd_645324 73635864418252977907159 := by
  unfold tailWord_645324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768449957054417704919513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15691266609405890273226017 11768449957054417704919513)
  ·
    refine ⟨8826337467790813278689635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11768449957054417704919513 8826337467790813278689635)
    ·
      refine ⟨13239506201686219918034453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826337467790813278689635 13239506201686219918034453)
      ·
        refine ⟨620601853204041558657865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13239506201686219918034453 620601853204041558657865)
        ·
          refine ⟨465451389903031168993399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620601853204041558657865 465451389903031168993399)
          ·
            refine ⟨698177084854546753490099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465451389903031168993399 698177084854546753490099)
            ·
              refine ⟨1047265627281820130235149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698177084854546753490099 1047265627281820130235149)
              ·
                refine ⟨392724610230682548838181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047265627281820130235149 392724610230682548838181)
                ·
                  refine ⟨73635864418252977907159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392724610230682548838181 73635864418252977907159)
                  ·
                    rfl

theorem cell22_645324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_645324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645324 prefixEnd_645324 := by exact prefixLift 645324
  have htrace : WordTrace (prefixWord ++ tailWord_645324) baseStart_645324 baseEnd_645324 := by
    simpa [prefixWord, tailWord_645324, baseEnd_645324] using wordTrace_append hprefix tailTrace_645324
  have hstable : (prefixWord ++ tailWord_645324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645324).length < 2 ^ (prefixWord ++ tailWord_645324).sum := by decide
  have hdescent : baseEnd_645324 < baseStart_645324 := by decide
  rcases family_descends (prefixWord ++ tailWord_645324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645361 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_645361 : Nat := 118140960795 + 645361 * 2 ^ 59
def prefixEnd_645361 : Nat := 4983230072969 + 3 ^ 40 * 645361 * 2
def baseEnd_645361 : Nat := 220920259110903170546363

theorem tailTrace_645361 : CollatzResearch.WordTrace tailWord_645361 prefixEnd_645361 220920259110903170546363 := by
  unfold tailWord_645361
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538249414974790728935937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15692166276649860485957291 23538249414974790728935937)
  ·
    refine ⟨17653687061231093046701953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23538249414974790728935937 17653687061231093046701953)
    ·
      refine ⟨13240265295923319785026465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17653687061231093046701953 13240265295923319785026465)
      ·
        refine ⟨9930198971942489838769849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13240265295923319785026465 9930198971942489838769849)
        ·
          refine ⟨7447649228956867379077387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930198971942489838769849 7447649228956867379077387)
          ·
            refine ⟨11171473843435301068616081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447649228956867379077387 11171473843435301068616081)
            ·
              refine ⟨8378605382576475801462061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171473843435301068616081 8378605382576475801462061)
              ·
                refine ⟨3141977018466178425548273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378605382576475801462061 3141977018466178425548273)
                ·
                  refine ⟨2356482763849633819161205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141977018466178425548273 2356482763849633819161205)
                  ·
                    refine ⟨220920259110903170546363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2356482763849633819161205 220920259110903170546363)
                    ·
                      rfl

theorem cell22_645361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_645361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645361 prefixEnd_645361 := by exact prefixLift 645361
  have htrace : WordTrace (prefixWord ++ tailWord_645361) baseStart_645361 baseEnd_645361 := by
    simpa [prefixWord, tailWord_645361, baseEnd_645361] using wordTrace_append hprefix tailTrace_645361
  have hstable : (prefixWord ++ tailWord_645361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645361).length < 2 ^ (prefixWord ++ tailWord_645361).sum := by decide
  have hdescent : baseEnd_645361 < baseStart_645361 := by decide
  rcases family_descends (prefixWord ++ tailWord_645361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645457 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_645457 : Nat := 118140960795 + 645457 * 2 ^ 59
def prefixEnd_645457 : Nat := 4983230072969 + 3 ^ 40 * 645457 * 2
def baseEnd_645457 : Nat := 220953121872790920146069

theorem tailTrace_645457 : CollatzResearch.WordTrace tailWord_645457 prefixEnd_645457 220953121872790920146069 := by
  unfold tailWord_645457
  simp only [CollatzResearch.WordTrace]
  refine ⟨23541750822626999124430625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15694500548417999416287083 23541750822626999124430625)
  ·
    refine ⟨17656313116970249343322969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23541750822626999124430625 17656313116970249343322969)
    ·
      refine ⟨13242234837727687007492227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17656313116970249343322969 13242234837727687007492227)
      ·
        refine ⟨19863352256591530511238341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13242234837727687007492227 19863352256591530511238341)
        ·
          refine ⟨3724378548110911970857189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19863352256591530511238341 3724378548110911970857189)
          ·
            refine ⟨698320977770795994535723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3724378548110911970857189 698320977770795994535723)
            ·
              refine ⟨1047481466656193991803585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698320977770795994535723 1047481466656193991803585)
              ·
                refine ⟨785611099992145493852689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047481466656193991803585 785611099992145493852689)
                ·
                  refine ⟨589208324994109120389517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785611099992145493852689 589208324994109120389517)
                  ·
                    refine ⟨220953121872790920146069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589208324994109120389517 220953121872790920146069)
                    ·
                      rfl

theorem cell22_645457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_645457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645457 prefixEnd_645457 := by exact prefixLift 645457
  have htrace : WordTrace (prefixWord ++ tailWord_645457) baseStart_645457 baseEnd_645457 := by
    simpa [prefixWord, tailWord_645457, baseEnd_645457] using wordTrace_append hprefix tailTrace_645457
  have hstable : (prefixWord ++ tailWord_645457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645457).length < 2 ^ (prefixWord ++ tailWord_645457).sum := by decide
  have hdescent : baseEnd_645457 < baseStart_645457 := by decide
  rcases family_descends (prefixWord ++ tailWord_645457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645474 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_645474 : Nat := 118140960795 + 645474 * 2 ^ 59
def prefixEnd_645474 : Nat := 4983230072969 + 3 ^ 40 * 645474 * 2
def baseEnd_645474 : Nat := 220958941320208542471017

theorem tailTrace_645474 : CollatzResearch.WordTrace tailWord_645474 prefixEnd_645474 220958941320208542471017 := by
  unfold tailWord_645474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885592715891352756949869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15694913909043607351866317 5885592715891352756949869)
  ·
    refine ⟨2207097268459257283856201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5885592715891352756949869 2207097268459257283856201)
    ·
      refine ⟨1655322951344442962892151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207097268459257283856201 1655322951344442962892151)
      ·
        refine ⟨2482984427016664444338227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655322951344442962892151 2482984427016664444338227)
        ·
          refine ⟨3724476640524996666507341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482984427016664444338227 3724476640524996666507341)
          ·
            refine ⟨1396678740196873749940253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724476640524996666507341 1396678740196873749940253)
            ·
              refine ⟨523754527573827656227595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396678740196873749940253 523754527573827656227595)
              ·
                refine ⟨785631791360741484341393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523754527573827656227595 785631791360741484341393)
                ·
                  refine ⟨589223843520556113256045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785631791360741484341393 589223843520556113256045)
                  ·
                    refine ⟨220958941320208542471017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589223843520556113256045 220958941320208542471017)
                    ·
                      rfl

theorem cell22_645474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_645474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645474 prefixEnd_645474 := by exact prefixLift 645474
  have htrace : WordTrace (prefixWord ++ tailWord_645474) baseStart_645474 baseEnd_645474 := by
    simpa [prefixWord, tailWord_645474, baseEnd_645474] using wordTrace_append hprefix tailTrace_645474
  have hstable : (prefixWord ++ tailWord_645474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645474).length < 2 ^ (prefixWord ++ tailWord_645474).sum := by decide
  have hdescent : baseEnd_645474 < baseStart_645474 := by decide
  rcases family_descends (prefixWord ++ tailWord_645474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645485 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_645485 : Nat := 118140960795 + 645485 * 2 ^ 59
def prefixEnd_645485 : Nat := 4983230072969 + 3 ^ 40 * 645485 * 2
def baseEnd_645485 : Nat := 220962706845008180445983

theorem tailTrace_645485 : CollatzResearch.WordTrace tailWord_645485 prefixEnd_645485 220962706845008180445983 := by
  unfold tailWord_645485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23542772066525559906449909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15695181377683706604299939 23542772066525559906449909)
  ·
    refine ⟨2207134881236771241229679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23542772066525559906449909 2207134881236771241229679)
    ·
      refine ⟨3310702321855156861844519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207134881236771241229679 3310702321855156861844519)
      ·
        refine ⟨4966053482782735292766779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310702321855156861844519 4966053482782735292766779)
        ·
          refine ⟨7449080224174102939150169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966053482782735292766779 7449080224174102939150169)
          ·
            refine ⟨5586810168130577204362627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449080224174102939150169 5586810168130577204362627)
            ·
              refine ⟨8380215252195865806543941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586810168130577204362627 8380215252195865806543941)
              ·
                refine ⟨1571290359786724838726989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8380215252195865806543941 1571290359786724838726989)
                ·
                  refine ⟨589233884920021814522621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1571290359786724838726989 589233884920021814522621)
                  ·
                    refine ⟨220962706845008180445983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589233884920021814522621 220962706845008180445983)
                    ·
                      rfl

theorem cell22_645485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_645485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645485 prefixEnd_645485 := by exact prefixLift 645485
  have htrace : WordTrace (prefixWord ++ tailWord_645485) baseStart_645485 baseEnd_645485 := by
    simpa [prefixWord, tailWord_645485, baseEnd_645485] using wordTrace_append hprefix tailTrace_645485
  have hstable : (prefixWord ++ tailWord_645485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645485).length < 2 ^ (prefixWord ++ tailWord_645485).sum := by decide
  have hdescent : baseEnd_645485 < baseStart_645485 := by decide
  rcases family_descends (prefixWord ++ tailWord_645485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645560 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_645560 : Nat := 118140960795 + 645560 * 2 ^ 59
def prefixEnd_645560 : Nat := 4983230072969 + 3 ^ 40 * 645560 * 2
def baseEnd_645560 : Nat := 73662793625910994940251

theorem tailTrace_645560 : CollatzResearch.WordTrace tailWord_645560 prefixEnd_645560 73662793625910994940251 := by
  unfold tailWord_645560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11772753770626923857715067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15697005027502565143620089 11772753770626923857715067)
  ·
    refine ⟨17659130655940385786572601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11772753770626923857715067 17659130655940385786572601)
    ·
      refine ⟨13244347991955289339929451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17659130655940385786572601 13244347991955289339929451)
      ·
        refine ⟨19866521987932934009894177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13244347991955289339929451 19866521987932934009894177)
        ·
          refine ⟨14899891490949700507420633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19866521987932934009894177 14899891490949700507420633)
          ·
            refine ⟨11174918618212275380565475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14899891490949700507420633 11174918618212275380565475)
            ·
              refine ⟨16762377927318413070848213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11174918618212275380565475 16762377927318413070848213)
              ·
                refine ⟨392868232671525306348005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16762377927318413070848213 392868232671525306348005)
                ·
                  refine ⟨73662793625910994940251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392868232671525306348005 73662793625910994940251)
                  ·
                    rfl

theorem cell22_645560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_645560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645560 prefixEnd_645560 := by exact prefixLift 645560
  have htrace : WordTrace (prefixWord ++ tailWord_645560) baseStart_645560 baseEnd_645560 := by
    simpa [prefixWord, tailWord_645560, baseEnd_645560] using wordTrace_append hprefix tailTrace_645560
  have hstable : (prefixWord ++ tailWord_645560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645560).length < 2 ^ (prefixWord ++ tailWord_645560).sum := by decide
  have hdescent : baseEnd_645560 < baseStart_645560 := by decide
  rcases family_descends (prefixWord ++ tailWord_645560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645577 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 4]
def baseStart_645577 : Nat := 118140960795 + 645577 * 2 ^ 59
def prefixEnd_645577 : Nat := 4983230072969 + 3 ^ 40 * 645577 * 2
def baseEnd_645577 : Nat := 73664733441716869048567

theorem tailTrace_645577 : CollatzResearch.WordTrace tailWord_645577 prefixEnd_645577 73664733441716869048567 := by
  unfold tailWord_645577
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546127582192259618798985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15697418388128173079199323 23546127582192259618798985)
  ·
    refine ⟨17659595686644194714099239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23546127582192259618798985 17659595686644194714099239)
    ·
      refine ⟨26489393529966292071148859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17659595686644194714099239 26489393529966292071148859)
      ·
        refine ⟨39734090294949438106723289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26489393529966292071148859 39734090294949438106723289)
        ·
          refine ⟨29800567721212078580042467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39734090294949438106723289 29800567721212078580042467)
          ·
            refine ⟨44700851581818117870063701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29800567721212078580042467 44700851581818117870063701)
            ·
              refine ⟨523838104474431068789809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 44700851581818117870063701 523838104474431068789809)
              ·
                refine ⟨392878578355823301592357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523838104474431068789809 392878578355823301592357)
                ·
                  refine ⟨73664733441716869048567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392878578355823301592357 73664733441716869048567)
                  ·
                    rfl

theorem cell22_645577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_645577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645577 prefixEnd_645577 := by exact prefixLift 645577
  have htrace : WordTrace (prefixWord ++ tailWord_645577) baseStart_645577 baseEnd_645577 := by
    simpa [prefixWord, tailWord_645577, baseEnd_645577] using wordTrace_append hprefix tailTrace_645577
  have hstable : (prefixWord ++ tailWord_645577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645577).length < 2 ^ (prefixWord ++ tailWord_645577).sum := by decide
  have hdescent : baseEnd_645577 < baseStart_645577 := by decide
  rcases family_descends (prefixWord ++ tailWord_645577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645648 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_645648 : Nat := 118140960795 + 645648 * 2 ^ 59
def prefixEnd_645648 : Nat := 4983230072969 + 3 ^ 40 * 645648 * 2
def baseEnd_645648 : Nat := 221018505076130088620483

theorem tailTrace_645648 : CollatzResearch.WordTrace tailWord_645648 prefixEnd_645648 221018505076130088620483 := by
  unfold tailWord_645648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774358582467519372316799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15699144776623359163089065 11774358582467519372316799)
  ·
    refine ⟨17661537873701279058475199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11774358582467519372316799 17661537873701279058475199)
    ·
      refine ⟨26492306810551918587712799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17661537873701279058475199 26492306810551918587712799)
      ·
        refine ⟨39738460215827877881569199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492306810551918587712799 39738460215827877881569199)
        ·
          refine ⟨59607690323741816822353799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39738460215827877881569199 59607690323741816822353799)
          ·
            refine ⟨89411535485612725233530699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59607690323741816822353799 89411535485612725233530699)
            ·
              refine ⟨134117303228419087850296049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89411535485612725233530699 134117303228419087850296049)
              ·
                refine ⟨100587977421314315887722037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134117303228419087850296049 100587977421314315887722037)
                ·
                  refine ⟨9430122883248217114473941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100587977421314315887722037 9430122883248217114473941)
                  ·
                    refine ⟨221018505076130088620483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9430122883248217114473941 221018505076130088620483)
                    ·
                      rfl

theorem cell22_645648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_645648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645648 prefixEnd_645648 := by exact prefixLift 645648
  have htrace : WordTrace (prefixWord ++ tailWord_645648) baseStart_645648 baseEnd_645648 := by
    simpa [prefixWord, tailWord_645648, baseEnd_645648] using wordTrace_append hprefix tailTrace_645648
  have hstable : (prefixWord ++ tailWord_645648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645648).length < 2 ^ (prefixWord ++ tailWord_645648).sum := by decide
  have hdescent : baseEnd_645648 < baseStart_645648 := by decide
  rcases family_descends (prefixWord ++ tailWord_645648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645785 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 7]
def baseStart_645785 : Nat := 118140960795 + 645785 * 2 ^ 59
def prefixEnd_645785 : Nat := 4983230072969 + 3 ^ 40 * 645785 * 2
def baseEnd_645785 : Nat := 73688467658635799315021

theorem tailTrace_645785 : CollatzResearch.WordTrace tailWord_645785 prefixEnd_645785 73688467658635799315021 := by
  unfold tailWord_645785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23553713965438711142370809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15702475976959140761580539 23553713965438711142370809)
  ·
    refine ⟨17665285474079033356778107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23553713965438711142370809 17665285474079033356778107)
    ·
      refine ⟨26497928211118550035167161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17665285474079033356778107 26497928211118550035167161)
      ·
        refine ⟨19873446158338912526375371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26497928211118550035167161 19873446158338912526375371)
        ·
          refine ⟨29810169237508368789563057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19873446158338912526375371 29810169237508368789563057)
          ·
            refine ⟨22357626928131276592172293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29810169237508368789563057 22357626928131276592172293)
            ·
              refine ⟨4192055049024614361032305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22357626928131276592172293 4192055049024614361032305)
              ·
                refine ⟨3144041286768460770774229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192055049024614361032305 3144041286768460770774229)
                ·
                  refine ⟨73688467658635799315021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3144041286768460770774229 73688467658635799315021)
                  ·
                    rfl

theorem cell22_645785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_645785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645785 prefixEnd_645785 := by exact prefixLift 645785
  have htrace : WordTrace (prefixWord ++ tailWord_645785) baseStart_645785 baseEnd_645785 := by
    simpa [prefixWord, tailWord_645785, baseEnd_645785] using wordTrace_append hprefix tailTrace_645785
  have hstable : (prefixWord ++ tailWord_645785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645785).length < 2 ^ (prefixWord ++ tailWord_645785).sum := by decide
  have hdescent : baseEnd_645785 < baseStart_645785 := by decide
  rcases family_descends (prefixWord ++ tailWord_645785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645806 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_645806 : Nat := 118140960795 + 645806 * 2 ^ 59
def prefixEnd_645806 : Nat := 4983230072969 + 3 ^ 40 * 645806 * 2
def baseEnd_645806 : Nat := 221072591705070343169999

theorem tailTrace_645806 : CollatzResearch.WordTrace tailWord_645806 prefixEnd_645806 221072591705070343169999 := by
  unfold tailWord_645806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944309987295328966110659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15702986598908421152590181 2944309987295328966110659)
  ·
    refine ⟨4416464980942993449165989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2944309987295328966110659 4416464980942993449165989)
    ·
      refine ⟨828087183926811271718623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4416464980942993449165989 828087183926811271718623)
      ·
        refine ⟨1242130775890216907577935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828087183926811271718623 1242130775890216907577935)
        ·
          refine ⟨1863196163835325361366903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242130775890216907577935 1863196163835325361366903)
          ·
            refine ⟨2794794245752988042050355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863196163835325361366903 2794794245752988042050355)
            ·
              refine ⟨4192191368629482063075533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794794245752988042050355 4192191368629482063075533)
              ·
                refine ⟨1572071763236055773653325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4192191368629482063075533 1572071763236055773653325)
                ·
                  refine ⟨589526911213520915119997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1572071763236055773653325 589526911213520915119997)
                  ·
                    refine ⟨221072591705070343169999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589526911213520915119997 221072591705070343169999)
                    ·
                      rfl

theorem cell22_645806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_645806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645806 prefixEnd_645806 := by exact prefixLift 645806
  have htrace : WordTrace (prefixWord ++ tailWord_645806) baseStart_645806 baseEnd_645806 := by
    simpa [prefixWord, tailWord_645806, baseEnd_645806] using wordTrace_append hprefix tailTrace_645806
  have hstable : (prefixWord ++ tailWord_645806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645806).length < 2 ^ (prefixWord ++ tailWord_645806).sum := by decide
  have hdescent : baseEnd_645806 < baseStart_645806 := by decide
  rcases family_descends (prefixWord ++ tailWord_645806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645892 : List Nat := [2, 3, 2, 2, 1, 1, 1, 10]
def baseStart_645892 : Nat := 118140960795 + 645892 * 2 ^ 59
def prefixEnd_645892 : Nat := 4983230072969 + 3 ^ 40 * 645892 * 2
def baseEnd_645892 : Nat := 24566892362510531724415

theorem tailTrace_645892 : CollatzResearch.WordTrace tailWord_645892 prefixEnd_645892 24566892362510531724415 := by
  unfold tailWord_645892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778808288025534208257965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15705077717367378944343953 11778808288025534208257965)
  ·
    refine ⟨4417053108009575328096737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11778808288025534208257965 4417053108009575328096737)
    ·
      refine ⟨3312789831007181496072553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4417053108009575328096737 3312789831007181496072553)
      ·
        refine ⟨2484592373255386122054415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3312789831007181496072553 2484592373255386122054415)
        ·
          refine ⟨3726888559883079183081623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484592373255386122054415 3726888559883079183081623)
          ·
            refine ⟨5590332839824618774622435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726888559883079183081623 5590332839824618774622435)
            ·
              refine ⟨8385499259736928161933653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590332839824618774622435 8385499259736928161933653)
              ·
                refine ⟨24566892362510531724415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8385499259736928161933653 24566892362510531724415)
                ·
                  rfl

theorem cell22_645892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_645892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645892 prefixEnd_645892 := by exact prefixLift 645892
  have htrace : WordTrace (prefixWord ++ tailWord_645892) baseStart_645892 baseEnd_645892 := by
    simpa [prefixWord, tailWord_645892, baseEnd_645892] using wordTrace_append hprefix tailTrace_645892
  have hstable : (prefixWord ++ tailWord_645892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645892).length < 2 ^ (prefixWord ++ tailWord_645892).sum := by decide
  have hdescent : baseEnd_645892 < baseStart_645892 := by decide
  rcases family_descends (prefixWord ++ tailWord_645892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645941 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_645941 : Nat := 118140960795 + 645941 * 2 ^ 59
def prefixEnd_645941 : Nat := 4983230072969 + 3 ^ 40 * 645941 * 2
def baseEnd_645941 : Nat := 221118804963974991044585

theorem tailTrace_645941 : CollatzResearch.WordTrace tailWord_645941 prefixEnd_645941 221118804963974991044585 := by
  unfold tailWord_645941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23559403752873549785049677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15706269168582366523366451 23559403752873549785049677)
  ·
    refine ⟨8834776407327581169393629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23559403752873549785049677 8834776407327581169393629)
    ·
      refine ⟨3313041152747842938522611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8834776407327581169393629 3313041152747842938522611)
      ·
        refine ⟨4969561729121764407783917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313041152747842938522611 4969561729121764407783917)
        ·
          refine ⟨1863585648420661652918969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4969561729121764407783917 1863585648420661652918969)
          ·
            refine ⟨1397689236315496239689227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863585648420661652918969 1397689236315496239689227)
            ·
              refine ⟨2096533854473244359533841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397689236315496239689227 2096533854473244359533841)
              ·
                refine ⟨1572400390854933269650381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2096533854473244359533841 1572400390854933269650381)
                ·
                  refine ⟨589650146570599976118893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1572400390854933269650381 589650146570599976118893)
                  ·
                    refine ⟨221118804963974991044585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589650146570599976118893 221118804963974991044585)
                    ·
                      rfl

theorem cell22_645941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_645941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_645941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_645941 prefixEnd_645941 := by exact prefixLift 645941
  have htrace : WordTrace (prefixWord ++ tailWord_645941) baseStart_645941 baseEnd_645941 := by
    simpa [prefixWord, tailWord_645941, baseEnd_645941] using wordTrace_append hprefix tailTrace_645941
  have hstable : (prefixWord ++ tailWord_645941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645941).length < 2 ^ (prefixWord ++ tailWord_645941).sum := by decide
  have hdescent : baseEnd_645941 < baseStart_645941 := by decide
  rcases family_descends (prefixWord ++ tailWord_645941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646001 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_646001 : Nat := 118140960795 + 646001 * 2 ^ 59
def prefixEnd_646001 : Nat := 4983230072969 + 3 ^ 40 * 646001 * 2
def baseEnd_646001 : Nat := 221139344190154834544401

theorem tailTrace_646001 : CollatzResearch.WordTrace tailWord_646001 prefixEnd_646001 221139344190154834544401 := by
  unfold tailWord_646001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23561592132656180032233857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15707728088437453354822571 23561592132656180032233857)
  ·
    refine ⟨17671194099492135024175393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23561592132656180032233857 17671194099492135024175393)
    ·
      refine ⟨13253395574619101268131545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17671194099492135024175393 13253395574619101268131545)
      ·
        refine ⟨9940046680964325951098659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253395574619101268131545 9940046680964325951098659)
        ·
          refine ⟨14910070021446488926647989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940046680964325951098659 14910070021446488926647989)
          ·
            refine ⟨1397819064510608336873249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14910070021446488926647989 1397819064510608336873249)
            ·
              refine ⟨1048364298382956252654937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397819064510608336873249 1048364298382956252654937)
              ·
                refine ⟨786273223787217189491203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048364298382956252654937 786273223787217189491203)
                ·
                  refine ⟨1179409835680825784236805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786273223787217189491203 1179409835680825784236805)
                  ·
                    refine ⟨221139344190154834544401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179409835680825784236805 221139344190154834544401)
                    ·
                      rfl

theorem cell22_646001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_646001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646001 prefixEnd_646001 := by exact prefixLift 646001
  have htrace : WordTrace (prefixWord ++ tailWord_646001) baseStart_646001 baseEnd_646001 := by
    simpa [prefixWord, tailWord_646001, baseEnd_646001] using wordTrace_append hprefix tailTrace_646001
  have hstable : (prefixWord ++ tailWord_646001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646001).length < 2 ^ (prefixWord ++ tailWord_646001).sum := by decide
  have hdescent : baseEnd_646001 < baseStart_646001 := by decide
  rcases family_descends (prefixWord ++ tailWord_646001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646027 : List Nat := [1, 1, 1, 1, 4, 2, 12]
def baseStart_646027 : Nat := 118140960795 + 646027 * 2 ^ 59
def prefixEnd_646027 : Nat := 4983230072969 + 3 ^ 40 * 646027 * 2
def baseEnd_646027 : Nat := 8190675723018497533123

theorem tailTrace_646027 : CollatzResearch.WordTrace tailWord_646027 prefixEnd_646027 8190675723018497533123 := by
  unfold tailWord_646027
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562540430561986472680335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15708360287041324315120223 23562540430561986472680335)
  ·
    refine ⟨35343810645842979709020503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23562540430561986472680335 35343810645842979709020503)
    ·
      refine ⟨53015715968764469563530755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35343810645842979709020503 53015715968764469563530755)
      ·
        refine ⟨79523573953146704345296133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53015715968764469563530755 79523573953146704345296133)
        ·
          refine ⟨14910670116215007064743025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79523573953146704345296133 14910670116215007064743025)
          ·
            refine ⟨11183002587161255298557269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910670116215007064743025 11183002587161255298557269)
            ·
              refine ⟨8190675723018497533123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11183002587161255298557269 8190675723018497533123)
              ·
                rfl

theorem cell22_646027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 12].length) (baseStart_646027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646027 prefixEnd_646027 := by exact prefixLift 646027
  have htrace : WordTrace (prefixWord ++ tailWord_646027) baseStart_646027 baseEnd_646027 := by
    simpa [prefixWord, tailWord_646027, baseEnd_646027] using wordTrace_append hprefix tailTrace_646027
  have hstable : (prefixWord ++ tailWord_646027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646027).length < 2 ^ (prefixWord ++ tailWord_646027).sum := by decide
  have hdescent : baseEnd_646027 < baseStart_646027 := by decide
  rcases family_descends (prefixWord ++ tailWord_646027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646048 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_646048 : Nat := 118140960795 + 646048 * 2 ^ 59
def prefixEnd_646048 : Nat := 4983230072969 + 3 ^ 40 * 646048 * 2
def baseEnd_646048 : Nat := 221155433250662378619257

theorem tailTrace_646048 : CollatzResearch.WordTrace tailWord_646048 prefixEnd_646048 221155433250662378619257 := by
  unfold tailWord_646048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781653181742953529597399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15708870908990604706129865 11781653181742953529597399)
  ·
    refine ⟨17672479772614430294396099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11781653181742953529597399 17672479772614430294396099)
    ·
      refine ⟨26508719658921645441594149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17672479772614430294396099 26508719658921645441594149)
      ·
        refine ⟨4970384936047808520298903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26508719658921645441594149 4970384936047808520298903)
        ·
          refine ⟨7455577404071712780448355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970384936047808520298903 7455577404071712780448355)
          ·
            refine ⟨11183366106107569170672533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455577404071712780448355 11183366106107569170672533)
            ·
              refine ⟨524220286223792304875275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11183366106107569170672533 524220286223792304875275)
              ·
                refine ⟨786330429335688457312913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524220286223792304875275 786330429335688457312913)
                ·
                  refine ⟨589747822001766342984685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 786330429335688457312913 589747822001766342984685)
                  ·
                    refine ⟨221155433250662378619257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589747822001766342984685 221155433250662378619257)
                    ·
                      rfl

theorem cell22_646048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_646048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646048 prefixEnd_646048 := by exact prefixLift 646048
  have htrace : WordTrace (prefixWord ++ tailWord_646048) baseStart_646048 baseEnd_646048 := by
    simpa [prefixWord, tailWord_646048, baseEnd_646048] using wordTrace_append hprefix tailTrace_646048
  have hstable : (prefixWord ++ tailWord_646048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646048).length < 2 ^ (prefixWord ++ tailWord_646048).sum := by decide
  have hdescent : baseEnd_646048 < baseStart_646048 := by decide
  rcases family_descends (prefixWord ++ tailWord_646048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646084 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_646084 : Nat := 118140960795 + 646084 * 2 ^ 59
def prefixEnd_646084 : Nat := 4983230072969 + 3 ^ 40 * 646084 * 2
def baseEnd_646084 : Nat := 73722585595456761573049

theorem tailTrace_646084 : CollatzResearch.WordTrace tailWord_646084 prefixEnd_646084 73722585595456761573049 := by
  unfold tailWord_646084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782309695677742603752653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15709746260903656805003537 11782309695677742603752653)
  ·
    refine ⟨4418366135879153476407245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11782309695677742603752653 4418366135879153476407245)
    ·
      refine ⟨1656887300954682553652717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4418366135879153476407245 1656887300954682553652717)
      ·
        refine ⟨621332737858005957619769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1656887300954682553652717 621332737858005957619769)
        ·
          refine ⟨465999553393504468214827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621332737858005957619769 465999553393504468214827)
          ·
            refine ⟨698999330090256702322241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465999553393504468214827 698999330090256702322241)
            ·
              refine ⟨524249497567692526741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698999330090256702322241 524249497567692526741681)
              ·
                refine ⟨393187123175769395056261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524249497567692526741681 393187123175769395056261)
                ·
                  refine ⟨73722585595456761573049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393187123175769395056261 73722585595456761573049)
                  ·
                    rfl

theorem cell22_646084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_646084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646084 prefixEnd_646084 := by exact prefixLift 646084
  have htrace : WordTrace (prefixWord ++ tailWord_646084) baseStart_646084 baseEnd_646084 := by
    simpa [prefixWord, tailWord_646084, baseEnd_646084] using wordTrace_append hprefix tailTrace_646084
  have hstable : (prefixWord ++ tailWord_646084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646084).length < 2 ^ (prefixWord ++ tailWord_646084).sum := by decide
  have hdescent : baseEnd_646084 < baseStart_646084 := by decide
  rcases family_descends (prefixWord ++ tailWord_646084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646104 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_646104 : Nat := 118140960795 + 646104 * 2 ^ 59
def prefixEnd_646104 : Nat := 4983230072969 + 3 ^ 40 * 646104 * 2
def baseEnd_646104 : Nat := 221174603195096899219085

theorem tailTrace_646104 : CollatzResearch.WordTrace tailWord_646104 prefixEnd_646104 221174603195096899219085 := by
  unfold tailWord_646104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782674425641514311616683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15710232567522019082155577 11782674425641514311616683)
  ·
    refine ⟨17674011638462271467425025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11782674425641514311616683 17674011638462271467425025)
    ·
      refine ⟨13255508728846703600568769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17674011638462271467425025 13255508728846703600568769)
      ·
        refine ⟨9941631546635027700426577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13255508728846703600568769 9941631546635027700426577)
        ·
          refine ⟨7456223659976270775319933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941631546635027700426577 7456223659976270775319933)
          ·
            refine ⟨2796083872491101540744975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7456223659976270775319933 2796083872491101540744975)
            ·
              refine ⟨4194125808736652311117463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796083872491101540744975 4194125808736652311117463)
              ·
                refine ⟨6291188713104978466676195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194125808736652311117463 6291188713104978466676195)
                ·
                  refine ⟨9436783069657467700014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291188713104978466676195 9436783069657467700014293)
                  ·
                    refine ⟨221174603195096899219085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9436783069657467700014293 221174603195096899219085)
                    ·
                      rfl

theorem cell22_646104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_646104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646104 prefixEnd_646104 := by exact prefixLift 646104
  have htrace : WordTrace (prefixWord ++ tailWord_646104) baseStart_646104 baseEnd_646104 := by
    simpa [prefixWord, tailWord_646104, baseEnd_646104] using wordTrace_append hprefix tailTrace_646104
  have hstable : (prefixWord ++ tailWord_646104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646104).length < 2 ^ (prefixWord ++ tailWord_646104).sum := by decide
  have hdescent : baseEnd_646104 < baseStart_646104 := by decide
  rcases family_descends (prefixWord ++ tailWord_646104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646106 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_646106 : Nat := 118140960795 + 646106 * 2 ^ 59
def prefixEnd_646106 : Nat := 4983230072969 + 3 ^ 40 * 646106 * 2
def baseEnd_646106 : Nat := 73725095945323186889693

theorem tailTrace_646106 : CollatzResearch.WordTrace tailWord_646106 prefixEnd_646106 73725095945323186889693 := by
  unfold tailWord_646106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891355449318945741201543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15710281198183855309870781 5891355449318945741201543)
  ·
    refine ⟨8837033173978418611802315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891355449318945741201543 8837033173978418611802315)
    ·
      refine ⟨13255549760967627917703473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837033173978418611802315 13255549760967627917703473)
      ·
        refine ⟨9941662320725720938277605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13255549760967627917703473 9941662320725720938277605)
        ·
          refine ⟨1864061685136072675927051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9941662320725720938277605 1864061685136072675927051)
          ·
            refine ⟨2796092527704109013890577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864061685136072675927051 2796092527704109013890577)
            ·
              refine ⟨2097069395778081760417933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796092527704109013890577 2097069395778081760417933)
              ·
                refine ⟨786401023416780660156725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2097069395778081760417933 786401023416780660156725)
                ·
                  refine ⟨73725095945323186889693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786401023416780660156725 73725095945323186889693)
                  ·
                    rfl

theorem cell22_646106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_646106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646106 prefixEnd_646106 := by exact prefixLift 646106
  have htrace : WordTrace (prefixWord ++ tailWord_646106) baseStart_646106 baseEnd_646106 := by
    simpa [prefixWord, tailWord_646106, baseEnd_646106] using wordTrace_append hprefix tailTrace_646106
  have hstable : (prefixWord ++ tailWord_646106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646106).length < 2 ^ (prefixWord ++ tailWord_646106).sum := by decide
  have hdescent : baseEnd_646106 < baseStart_646106 := by decide
  rcases family_descends (prefixWord ++ tailWord_646106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646151 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 6]
def baseStart_646151 : Nat := 118140960795 + 646151 * 2 ^ 59
def prefixEnd_646151 : Nat := 4983230072969 + 3 ^ 40 * 646151 * 2
def baseEnd_646151 : Nat := 73730230751868147764647

theorem tailTrace_646151 : CollatzResearch.WordTrace tailWord_646151 prefixEnd_646151 73730230751868147764647 := by
  unfold tailWord_646151
  simp only [CollatzResearch.WordTrace]
  refine ⟨23567063082112755650194307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15711375388075170433462871 23567063082112755650194307)
  ·
    refine ⟨35350594623169133475291461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23567063082112755650194307 35350594623169133475291461)
    ·
      refine ⟨6628236491844212526617149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35350594623169133475291461 6628236491844212526617149)
      ·
        refine ⟨2485588684441579697481431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6628236491844212526617149 2485588684441579697481431)
        ·
          refine ⟨3728383026662369546222147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485588684441579697481431 3728383026662369546222147)
          ·
            refine ⟨5592574539993554319333221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728383026662369546222147 5592574539993554319333221)
            ·
              refine ⟨1048607726248791434874979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5592574539993554319333221 1048607726248791434874979)
              ·
                refine ⟨1572911589373187152312469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048607726248791434874979 1572911589373187152312469)
                ·
                  refine ⟨73730230751868147764647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1572911589373187152312469 73730230751868147764647)
                  ·
                    rfl

theorem cell22_646151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_646151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646151 prefixEnd_646151 := by exact prefixLift 646151
  have htrace : WordTrace (prefixWord ++ tailWord_646151) baseStart_646151 baseEnd_646151 := by
    simpa [prefixWord, tailWord_646151, baseEnd_646151] using wordTrace_append hprefix tailTrace_646151
  have hstable : (prefixWord ++ tailWord_646151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646151).length < 2 ^ (prefixWord ++ tailWord_646151).sum := by decide
  have hdescent : baseEnd_646151 < baseStart_646151 := by decide
  rcases family_descends (prefixWord ++ tailWord_646151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646181 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_646181 : Nat := 118140960795 + 646181 * 2 ^ 59
def prefixEnd_646181 : Nat := 4983230072969 + 3 ^ 40 * 646181 * 2
def baseEnd_646181 : Nat := 221200961868694365043849

theorem tailTrace_646181 : CollatzResearch.WordTrace tailWord_646181 prefixEnd_646181 221200961868694365043849 := by
  unfold tailWord_646181
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568157272004070773786397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15712104848002713849190931 23568157272004070773786397)
  ·
    refine ⟨8838058977001526540169899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23568157272004070773786397 8838058977001526540169899)
    ·
      refine ⟨13257088465502289810254849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838058977001526540169899 13257088465502289810254849)
      ·
        refine ⟨9942816349126717357691137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13257088465502289810254849 9942816349126717357691137)
        ·
          refine ⟨7457112261845038018268353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9942816349126717357691137 7457112261845038018268353)
          ·
            refine ⟨5592834196383778513701265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7457112261845038018268353 5592834196383778513701265)
            ·
              refine ⟨4194625647287833885275949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5592834196383778513701265 4194625647287833885275949)
              ·
                refine ⟨1572984617732937706978481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4194625647287833885275949 1572984617732937706978481)
                ·
                  refine ⟨1179738463299703280233861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572984617732937706978481 1179738463299703280233861)
                  ·
                    refine ⟨221200961868694365043849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179738463299703280233861 221200961868694365043849)
                    ·
                      rfl

theorem cell22_646181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_646181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646181 prefixEnd_646181 := by exact prefixLift 646181
  have htrace : WordTrace (prefixWord ++ tailWord_646181) baseStart_646181 baseEnd_646181 := by
    simpa [prefixWord, tailWord_646181, baseEnd_646181] using wordTrace_append hprefix tailTrace_646181
  have hstable : (prefixWord ++ tailWord_646181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646181).length < 2 ^ (prefixWord ++ tailWord_646181).sum := by decide
  have hdescent : baseEnd_646181 < baseStart_646181 := by decide
  rcases family_descends (prefixWord ++ tailWord_646181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646198 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_646198 : Nat := 118140960795 + 646198 * 2 ^ 59
def prefixEnd_646198 : Nat := 4983230072969 + 3 ^ 40 * 646198 * 2
def baseEnd_646198 : Nat := 221206781316111987368797

theorem tailTrace_646198 : CollatzResearch.WordTrace tailWord_646198 prefixEnd_646198 221206781316111987368797 := by
  unfold tailWord_646198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473048582058905167322203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15712518208628321784770165 1473048582058905167322203)
  ·
    refine ⟨2209572873088357750983305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473048582058905167322203 2209572873088357750983305)
    ·
      refine ⟨1657179654816268313237479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209572873088357750983305 1657179654816268313237479)
      ·
        refine ⟨2485769482224402469856219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657179654816268313237479 2485769482224402469856219)
        ·
          refine ⟨3728654223336603704784329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485769482224402469856219 3728654223336603704784329)
          ·
            refine ⟨2796490667502452778588247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728654223336603704784329 2796490667502452778588247)
            ·
              refine ⟨4194736001253679167882371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796490667502452778588247 4194736001253679167882371)
              ·
                refine ⟨6292104001880518751823557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194736001253679167882371 6292104001880518751823557)
                ·
                  refine ⟨1179769500352597265966917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6292104001880518751823557 1179769500352597265966917)
                  ·
                    refine ⟨221206781316111987368797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179769500352597265966917 221206781316111987368797)
                    ·
                      rfl

theorem cell22_646198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_646198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646198 prefixEnd_646198 := by exact prefixLift 646198
  have htrace : WordTrace (prefixWord ++ tailWord_646198) baseStart_646198 baseEnd_646198 := by
    simpa [prefixWord, tailWord_646198, baseEnd_646198] using wordTrace_append hprefix tailTrace_646198
  have hstable : (prefixWord ++ tailWord_646198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646198).length < 2 ^ (prefixWord ++ tailWord_646198).sum := by decide
  have hdescent : baseEnd_646198 < baseStart_646198 := by decide
  rcases family_descends (prefixWord ++ tailWord_646198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646228 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_646228 : Nat := 118140960795 + 646228 * 2 ^ 59
def prefixEnd_646228 : Nat := 4983230072969 + 3 ^ 40 * 646228 * 2
def baseEnd_646228 : Nat := 221217050929201909118705

theorem tailTrace_646228 : CollatzResearch.WordTrace tailWord_646228 prefixEnd_646228 221217050929201909118705 := by
  unfold tailWord_646228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784935751416898900373669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15713247668555865200498225 11784935751416898900373669)
  ·
    refine ⟨2209675453390668543820063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11784935751416898900373669 2209675453390668543820063)
    ·
      refine ⟨3314513180086002815730095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209675453390668543820063 3314513180086002815730095)
      ·
        refine ⟨4971769770129004223595143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314513180086002815730095 4971769770129004223595143)
        ·
          refine ⟨7457654655193506335392715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971769770129004223595143 7457654655193506335392715)
          ·
            refine ⟨11186481982790259503089073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457654655193506335392715 11186481982790259503089073)
            ·
              refine ⟨8389861487092694627316805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11186481982790259503089073 8389861487092694627316805)
              ·
                refine ⟨1573099028829880242621901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8389861487092694627316805 1573099028829880242621901)
                ·
                  refine ⟨589912135811205090983213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1573099028829880242621901 589912135811205090983213)
                  ·
                    refine ⟨221217050929201909118705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589912135811205090983213 221217050929201909118705)
                    ·
                      rfl

theorem cell22_646228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_646228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646228 prefixEnd_646228 := by exact prefixLift 646228
  have htrace : WordTrace (prefixWord ++ tailWord_646228) baseStart_646228 baseEnd_646228 := by
    simpa [prefixWord, tailWord_646228, baseEnd_646228] using wordTrace_append hprefix tailTrace_646228
  have hstable : (prefixWord ++ tailWord_646228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646228).length < 2 ^ (prefixWord ++ tailWord_646228).sum := by decide
  have hdescent : baseEnd_646228 < baseStart_646228 := by decide
  rcases family_descends (prefixWord ++ tailWord_646228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646245 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_646245 : Nat := 118140960795 + 646245 * 2 ^ 59
def prefixEnd_646245 : Nat := 4983230072969 + 3 ^ 40 * 646245 * 2
def baseEnd_646245 : Nat := 221222870376619531443653

theorem tailTrace_646245 : CollatzResearch.WordTrace tailWord_646245 prefixEnd_646245 221222870376619531443653 := by
  unfold tailWord_646245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23570491543772209704116189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15713661029181473136077459 23570491543772209704116189)
  ·
    refine ⟨8838934328914578639043571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23570491543772209704116189 8838934328914578639043571)
    ·
      refine ⟨13258401493371867958565357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838934328914578639043571 13258401493371867958565357)
      ·
        refine ⟨4971900560014450484462009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13258401493371867958565357 4971900560014450484462009)
        ·
          refine ⟨3728925420010837863346507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4971900560014450484462009 3728925420010837863346507)
          ·
            refine ⟨5593388130016256795019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728925420010837863346507 5593388130016256795019761)
            ·
              refine ⟨4195041097512192596264821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593388130016256795019761 4195041097512192596264821)
              ·
                refine ⟨393285102891768055899827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4195041097512192596264821 393285102891768055899827)
                ·
                  refine ⟨589927654337652083849741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393285102891768055899827 589927654337652083849741)
                  ·
                    refine ⟨221222870376619531443653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589927654337652083849741 221222870376619531443653)
                    ·
                      rfl

theorem cell22_646245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_646245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646245 prefixEnd_646245 := by exact prefixLift 646245
  have htrace : WordTrace (prefixWord ++ tailWord_646245) baseStart_646245 baseEnd_646245 := by
    simpa [prefixWord, tailWord_646245, baseEnd_646245] using wordTrace_append hprefix tailTrace_646245
  have hstable : (prefixWord ++ tailWord_646245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646245).length < 2 ^ (prefixWord ++ tailWord_646245).sum := by decide
  have hdescent : baseEnd_646245 < baseStart_646245 := by decide
  rcases family_descends (prefixWord ++ tailWord_646245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646256 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_646256 : Nat := 118140960795 + 646256 * 2 ^ 59
def prefixEnd_646256 : Nat := 4983230072969 + 3 ^ 40 * 646256 * 2
def baseEnd_646256 : Nat := 221226635901419169418619

theorem tailTrace_646256 : CollatzResearch.WordTrace tailWord_646256 prefixEnd_646256 221226635901419169418619 := by
  unfold tailWord_646256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785446373366179291383311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15713928497821572388511081 11785446373366179291383311)
  ·
    refine ⟨17678169560049268937074967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11785446373366179291383311 17678169560049268937074967)
    ·
      refine ⟨26517254340073903405612451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17678169560049268937074967 26517254340073903405612451)
      ·
        refine ⟨39775881510110855108418677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26517254340073903405612451 39775881510110855108418677)
        ·
          refine ⟨3728988891572892666414251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39775881510110855108418677 3728988891572892666414251)
          ·
            refine ⟨5593483337359338999621377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728988891572892666414251 5593483337359338999621377)
            ·
              refine ⟨4195112503019504249716033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593483337359338999621377 4195112503019504249716033)
              ·
                refine ⟨3146334377264628187287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195112503019504249716033 3146334377264628187287025)
                ·
                  refine ⟨2359750782948471140465269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146334377264628187287025 2359750782948471140465269)
                  ·
                    refine ⟨221226635901419169418619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2359750782948471140465269 221226635901419169418619)
                    ·
                      rfl

theorem cell22_646256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_646256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646256 prefixEnd_646256 := by exact prefixLift 646256
  have htrace : WordTrace (prefixWord ++ tailWord_646256) baseStart_646256 baseEnd_646256 := by
    simpa [prefixWord, tailWord_646256, baseEnd_646256] using wordTrace_append hprefix tailTrace_646256
  have hstable : (prefixWord ++ tailWord_646256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646256).length < 2 ^ (prefixWord ++ tailWord_646256).sum := by decide
  have hdescent : baseEnd_646256 < baseStart_646256 := by decide
  rcases family_descends (prefixWord ++ tailWord_646256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646258 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_646258 : Nat := 118140960795 + 646258 * 2 ^ 59
def prefixEnd_646258 : Nat := 4983230072969 + 3 ^ 40 * 646258 * 2
def baseEnd_646258 : Nat := 73742440180763943622871

theorem tailTrace_646258 : CollatzResearch.WordTrace tailWord_646258 prefixEnd_646258 73742440180763943622871 := by
  unfold tailWord_646258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5892741423181278231084857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15713977128483408616226285 5892741423181278231084857)
  ·
    refine ⟨4419556067385958673313643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5892741423181278231084857 4419556067385958673313643)
    ·
      refine ⟨6629334101078938009970465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419556067385958673313643 6629334101078938009970465)
      ·
        refine ⟨4972000575809203507477849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6629334101078938009970465 4972000575809203507477849)
        ·
          refine ⟨3729000431856902630608387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4972000575809203507477849 3729000431856902630608387)
          ·
            refine ⟨5593500647785353945912581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729000431856902630608387 5593500647785353945912581)
            ·
              refine ⟨1048781371459753864858609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5593500647785353945912581 1048781371459753864858609)
              ·
                refine ⟨786586028594815398643957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048781371459753864858609 786586028594815398643957)
                ·
                  refine ⟨73742440180763943622871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786586028594815398643957 73742440180763943622871)
                  ·
                    rfl

theorem cell22_646258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_646258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646258 prefixEnd_646258 := by exact prefixLift 646258
  have htrace : WordTrace (prefixWord ++ tailWord_646258) baseStart_646258 baseEnd_646258 := by
    simpa [prefixWord, tailWord_646258, baseEnd_646258] using wordTrace_append hprefix tailTrace_646258
  have hstable : (prefixWord ++ tailWord_646258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646258).length < 2 ^ (prefixWord ++ tailWord_646258).sum := by decide
  have hdescent : baseEnd_646258 < baseStart_646258 := by decide
  rcases family_descends (prefixWord ++ tailWord_646258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646262 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_646262 : Nat := 118140960795 + 646262 * 2 ^ 59
def prefixEnd_646262 : Nat := 4983230072969 + 3 ^ 40 * 646262 * 2
def baseEnd_646262 : Nat := 221228689824037153768601

theorem tailTrace_646262 : CollatzResearch.WordTrace tailWord_646262 prefixEnd_646262 221228689824037153768601 := by
  unfold tailWord_646262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473194474044413850467815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15714074389807081071656693 1473194474044413850467815)
  ·
    refine ⟨2209791711066620775701723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473194474044413850467815 2209791711066620775701723)
    ·
      refine ⟨3314687566599931163552585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209791711066620775701723 3314687566599931163552585)
      ·
        refine ⟨2486015674949948372664439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314687566599931163552585 2486015674949948372664439)
        ·
          refine ⟨3729023512424922558996659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486015674949948372664439 3729023512424922558996659)
          ·
            refine ⟨5593535268637383838494989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729023512424922558996659 5593535268637383838494989)
            ·
              refine ⟨2097575725739018939435621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5593535268637383838494989 2097575725739018939435621)
              ·
                refine ⟨393295448576066051144179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2097575725739018939435621 393295448576066051144179)
                ·
                  refine ⟨589943172864099076716269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393295448576066051144179 589943172864099076716269)
                  ·
                    refine ⟨221228689824037153768601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589943172864099076716269 221228689824037153768601)
                    ·
                      rfl

theorem cell22_646262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_646262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646262 prefixEnd_646262 := by exact prefixLift 646262
  have htrace : WordTrace (prefixWord ++ tailWord_646262) baseStart_646262 baseEnd_646262 := by
    simpa [prefixWord, tailWord_646262, baseEnd_646262] using wordTrace_append hprefix tailTrace_646262
  have hstable : (prefixWord ++ tailWord_646262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646262).length < 2 ^ (prefixWord ++ tailWord_646262).sum := by decide
  have hdescent : baseEnd_646262 < baseStart_646262 := by decide
  rcases family_descends (prefixWord ++ tailWord_646262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646273 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_646273 : Nat := 118140960795 + 646273 * 2 ^ 59
def prefixEnd_646273 : Nat := 4983230072969 + 3 ^ 40 * 646273 * 2
def baseEnd_646273 : Nat := 221232455348836791743567

theorem tailTrace_646273 : CollatzResearch.WordTrace tailWord_646273 prefixEnd_646273 221232455348836791743567 := by
  unfold tailWord_646273
  simp only [CollatzResearch.WordTrace]
  refine ⟨23571512787670770486135473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15714341858447180324090315 23571512787670770486135473)
  ·
    refine ⟨17678634590753077864601605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23571512787670770486135473 17678634590753077864601605)
    ·
      refine ⟨3314743985766202099612801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17678634590753077864601605 3314743985766202099612801)
      ·
        refine ⟨2486057989324651574709601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314743985766202099612801 2486057989324651574709601)
        ·
          refine ⟨1864543491993488681032201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486057989324651574709601 1864543491993488681032201)
          ·
            refine ⟨1398407618995116510774151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864543491993488681032201 1398407618995116510774151)
            ·
              refine ⟨2097611428492674766161227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398407618995116510774151 2097611428492674766161227)
              ·
                refine ⟨3146417142739012149241841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097611428492674766161227 3146417142739012149241841)
                ·
                  refine ⟨2359812857054259111931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146417142739012149241841 2359812857054259111931381)
                  ·
                    refine ⟨221232455348836791743567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2359812857054259111931381 221232455348836791743567)
                    ·
                      rfl

theorem cell22_646273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_646273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646273 prefixEnd_646273 := by exact prefixLift 646273
  have htrace : WordTrace (prefixWord ++ tailWord_646273) baseStart_646273 baseEnd_646273 := by
    simpa [prefixWord, tailWord_646273, baseEnd_646273] using wordTrace_append hprefix tailTrace_646273
  have hstable : (prefixWord ++ tailWord_646273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646273).length < 2 ^ (prefixWord ++ tailWord_646273).sum := by decide
  have hdescent : baseEnd_646273 < baseStart_646273 := by decide
  rcases family_descends (prefixWord ++ tailWord_646273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646361 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_646361 : Nat := 118140960795 + 646361 * 2 ^ 59
def prefixEnd_646361 : Nat := 4983230072969 + 3 ^ 40 * 646361 * 2
def baseEnd_646361 : Nat := 221262579547233895543297

theorem tailTrace_646361 : CollatzResearch.WordTrace tailWord_646361 prefixEnd_646361 221262579547233895543297 := by
  unfold tailWord_646361
  simp only [CollatzResearch.WordTrace]
  refine ⟨23574722411351961515338937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15716481607567974343559291 23574722411351961515338937)
  ·
    refine ⟨17681041808513971136504203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23574722411351961515338937 17681041808513971136504203)
    ·
      refine ⟨26521562712770956704756305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17681041808513971136504203 26521562712770956704756305)
      ·
        refine ⟨19891172034578217528567229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26521562712770956704756305 19891172034578217528567229)
        ·
          refine ⟨7459189512966831573212711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19891172034578217528567229 7459189512966831573212711)
          ·
            refine ⟨11188784269450247359819067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459189512966831573212711 11188784269450247359819067)
            ·
              refine ⟨16783176404175371039728601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188784269450247359819067 16783176404175371039728601)
              ·
                refine ⟨12587382303131528279796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16783176404175371039728601 12587382303131528279796451)
                ·
                  refine ⟨18881073454697292419694677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12587382303131528279796451 18881073454697292419694677)
                  ·
                    refine ⟨221262579547233895543297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18881073454697292419694677 221262579547233895543297)
                    ·
                      rfl

theorem cell22_646361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_646361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646361 prefixEnd_646361 := by exact prefixLift 646361
  have htrace : WordTrace (prefixWord ++ tailWord_646361) baseStart_646361 baseEnd_646361 := by
    simpa [prefixWord, tailWord_646361, baseEnd_646361] using wordTrace_append hprefix tailTrace_646361
  have hstable : (prefixWord ++ tailWord_646361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646361).length < 2 ^ (prefixWord ++ tailWord_646361).sum := by decide
  have hdescent : baseEnd_646361 < baseStart_646361 := by decide
  rcases family_descends (prefixWord ++ tailWord_646361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646365 : List Nat := [1, 4, 3, 2, 2, 2, 8]
def baseStart_646365 : Nat := 118140960795 + 646365 * 2 ^ 59
def prefixEnd_646365 : Nat := 4983230072969 + 3 ^ 40 * 646365 * 2
def baseEnd_646365 : Nat := 8194961067739971053455

theorem tailTrace_646365 : CollatzResearch.WordTrace tailWord_646365 prefixEnd_646365 8194961067739971053455 := by
  unfold tailWord_646365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23574868303337470198484549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15716578868891646798989699 23574868303337470198484549)
  ·
    refine ⟨4420287806875775662215853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23574868303337470198484549 4420287806875775662215853)
    ·
      refine ⟨1657607927578415873330945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4420287806875775662215853 1657607927578415873330945)
      ·
        refine ⟨1243205945683811904998209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1657607927578415873330945 1243205945683811904998209)
        ·
          refine ⟨932404459262858928748657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1243205945683811904998209 932404459262858928748657)
          ·
            refine ⟨699303344447144196561493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932404459262858928748657 699303344447144196561493)
            ·
              refine ⟨8194961067739971053455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 699303344447144196561493 8194961067739971053455)
              ·
                rfl

theorem cell22_646365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 8].length) (baseStart_646365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646365 prefixEnd_646365 := by exact prefixLift 646365
  have htrace : WordTrace (prefixWord ++ tailWord_646365) baseStart_646365 baseEnd_646365 := by
    simpa [prefixWord, tailWord_646365, baseEnd_646365] using wordTrace_append hprefix tailTrace_646365
  have hstable : (prefixWord ++ tailWord_646365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646365).length < 2 ^ (prefixWord ++ tailWord_646365).sum := by decide
  have hdescent : baseEnd_646365 < baseStart_646365 := by decide
  rcases family_descends (prefixWord ++ tailWord_646365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646380 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_646380 : Nat := 118140960795 + 646380 * 2 ^ 59
def prefixEnd_646380 : Nat := 4983230072969 + 3 ^ 40 * 646380 * 2
def baseEnd_646380 : Nat := 221269083635524179318239

theorem tailTrace_646380 : CollatzResearch.WordTrace tailWord_646380 prefixEnd_646380 221269083635524179318239 := by
  unfold tailWord_646380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11787707699141563880140297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15716943598855418506853729 11787707699141563880140297)
  ·
    refine ⟨8840780774356172910105223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11787707699141563880140297 8840780774356172910105223)
    ·
      refine ⟨13261171161534259365157835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8840780774356172910105223 13261171161534259365157835)
      ·
        refine ⟨19891756742301389047736753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261171161534259365157835 19891756742301389047736753)
        ·
          refine ⟨14918817556726041785802565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19891756742301389047736753 14918817556726041785802565)
          ·
            refine ⟨2797278291886132834837981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14918817556726041785802565 2797278291886132834837981)
            ·
              refine ⟨1048979359457299813064243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2797278291886132834837981 1048979359457299813064243)
              ·
                refine ⟨1573469039185949719596365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048979359457299813064243 1573469039185949719596365)
                ·
                  refine ⟨590050889694731144848637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1573469039185949719596365 590050889694731144848637)
                  ·
                    refine ⟨221269083635524179318239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590050889694731144848637 221269083635524179318239)
                    ·
                      rfl

theorem cell22_646380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_646380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646380 prefixEnd_646380 := by exact prefixLift 646380
  have htrace : WordTrace (prefixWord ++ tailWord_646380) baseStart_646380 baseEnd_646380 := by
    simpa [prefixWord, tailWord_646380, baseEnd_646380] using wordTrace_append hprefix tailTrace_646380
  have hstable : (prefixWord ++ tailWord_646380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646380).length < 2 ^ (prefixWord ++ tailWord_646380).sum := by decide
  have hdescent : baseEnd_646380 < baseStart_646380 := by decide
  rcases family_descends (prefixWord ++ tailWord_646380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
