import V185TrunkScan22Chunk326

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2918105 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_2918105 : Nat := 118140960795 + 2918105 * 2 ^ 59
def prefixEnd_2918105 : Nat := 4983230072969 + 3 ^ 40 * 2918105 * 2
def baseEnd_2918105 : Nat := 998926976858940422978257

theorem tailTrace_2918105 : CollatzResearch.WordTrace tailWord_2918105 prefixEnd_2918105 998926976858940422978257 := by
  unfold tailWord_2918105
  simp only [CollatzResearch.WordTrace]
  refine ⟨106432033093211432501635769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70954688728807621667757179 106432033093211432501635769)
  ·
    refine ⟨79824024819908574376226827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106432033093211432501635769 79824024819908574376226827)
    ·
      refine ⟨119736037229862861564340241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79824024819908574376226827 119736037229862861564340241)
      ·
        refine ⟨89802027922397146173255181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119736037229862861564340241 89802027922397146173255181)
        ·
          refine ⟨33675760470898929814970693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89802027922397146173255181 33675760470898929814970693)
          ·
            refine ⟨6314205088293549340307005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33675760470898929814970693 6314205088293549340307005)
            ·
              refine ⟨2367826908110081002615127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6314205088293549340307005 2367826908110081002615127)
              ·
                refine ⟨3551740362165121503922691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367826908110081002615127 3551740362165121503922691)
                ·
                  refine ⟨5327610543247682255884037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551740362165121503922691 5327610543247682255884037)
                  ·
                    refine ⟨998926976858940422978257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327610543247682255884037 998926976858940422978257)
                    ·
                      rfl

theorem cell22_2918105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_2918105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918105 prefixEnd_2918105 := by exact prefixLift 2918105
  have htrace : WordTrace (prefixWord ++ tailWord_2918105) baseStart_2918105 baseEnd_2918105 := by
    simpa [prefixWord, tailWord_2918105, baseEnd_2918105] using wordTrace_append hprefix tailTrace_2918105
  have hstable : (prefixWord ++ tailWord_2918105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918105).length < 2 ^ (prefixWord ++ tailWord_2918105).sum := by decide
  have hdescent : baseEnd_2918105 < baseStart_2918105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918120 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_2918120 : Nat := 118140960795 + 2918120 * 2 ^ 59
def prefixEnd_2918120 : Nat := 4983230072969 + 3 ^ 40 * 2918120 * 2
def baseEnd_2918120 : Nat := 332977370555161794617737

theorem tailTrace_2918120 : CollatzResearch.WordTrace tailWord_2918120 prefixEnd_2918120 332977370555161794617737 := by
  unfold tailWord_2918120
  simp only [CollatzResearch.WordTrace]
  refine ⟨53216290094078545031715907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70955053458771393375621209 53216290094078545031715907)
  ·
    refine ⟨79824435141117817547573861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53216290094078545031715907 79824435141117817547573861)
    ·
      refine ⟨14967081588959590790170099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79824435141117817547573861 14967081588959590790170099)
      ·
        refine ⟨22450622383439386185255149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967081588959590790170099 22450622383439386185255149)
        ·
          refine ⟨8418983393789769819470681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22450622383439386185255149 8418983393789769819470681)
          ·
            refine ⟨6314237545342327364603011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8418983393789769819470681 6314237545342327364603011)
            ·
              refine ⟨9471356318013491046904517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314237545342327364603011 9471356318013491046904517)
              ·
                refine ⟨1775879309627529571294597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9471356318013491046904517 1775879309627529571294597)
                ·
                  refine ⟨332977370555161794617737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775879309627529571294597 332977370555161794617737)
                  ·
                    rfl

theorem cell22_2918120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_2918120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918120 prefixEnd_2918120 := by exact prefixLift 2918120
  have htrace : WordTrace (prefixWord ++ tailWord_2918120) baseStart_2918120 baseEnd_2918120 := by
    simpa [prefixWord, tailWord_2918120, baseEnd_2918120] using wordTrace_append hprefix tailTrace_2918120
  have hstable : (prefixWord ++ tailWord_2918120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918120).length < 2 ^ (prefixWord ++ tailWord_2918120).sum := by decide
  have hdescent : baseEnd_2918120 < baseStart_2918120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918131 : List Nat := [1, 1, 1, 2, 2, 3, 5, 7]
def baseStart_2918131 : Nat := 118140960795 + 2918131 * 2 ^ 59
def prefixEnd_2918131 : Nat := 4983230072969 + 3 ^ 40 * 2918131 * 2
def baseEnd_2918131 : Nat := 110992875243365002425353

theorem tailTrace_2918131 : CollatzResearch.WordTrace tailWord_2918131 prefixEnd_2918131 110992875243365002425353 := by
  unfold tailWord_2918131
  simp only [CollatzResearch.WordTrace]
  refine ⟨106432981391117238942082247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70955320927411492628054831 106432981391117238942082247)
  ·
    refine ⟨159649472086675858413123371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106432981391117238942082247 159649472086675858413123371)
    ·
      refine ⟨239474208130013787619685057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159649472086675858413123371 239474208130013787619685057)
      ·
        refine ⟨179605656097510340714763793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239474208130013787619685057 179605656097510340714763793)
        ·
          refine ⟨134704242073132755536072845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179605656097510340714763793 134704242073132755536072845)
          ·
            refine ⟨50514090777424783326027317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134704242073132755536072845 50514090777424783326027317)
            ·
              refine ⟨4735696010383573436815061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50514090777424783326027317 4735696010383573436815061)
              ·
                refine ⟨110992875243365002425353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4735696010383573436815061 110992875243365002425353)
                ·
                  rfl

theorem cell22_2918131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 7].length) (baseStart_2918131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918131 prefixEnd_2918131 := by exact prefixLift 2918131
  have htrace : WordTrace (prefixWord ++ tailWord_2918131) baseStart_2918131 baseEnd_2918131 := by
    simpa [prefixWord, tailWord_2918131, baseEnd_2918131] using wordTrace_append hprefix tailTrace_2918131
  have hstable : (prefixWord ++ tailWord_2918131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918131).length < 2 ^ (prefixWord ++ tailWord_2918131).sum := by decide
  have hdescent : baseEnd_2918131 < baseStart_2918131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918180 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2918180 : Nat := 118140960795 + 2918180 * 2 ^ 59
def prefixEnd_2918180 : Nat := 4983230072969 + 3 ^ 40 * 2918180 * 2
def baseEnd_2918180 : Nat := 998952650891665227353027

theorem tailTrace_2918180 : CollatzResearch.WordTrace tailWord_2918180 prefixEnd_2918180 998952650891665227353027 := by
  unfold tailWord_2918180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53217384283969860155307997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70956512378626480207077329 53217384283969860155307997)
  ·
    refine ⟨19956519106488697558240499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53217384283969860155307997 19956519106488697558240499)
    ·
      refine ⟨29934778659733046337360749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19956519106488697558240499 29934778659733046337360749)
      ·
        refine ⟨11225541997399892376510281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29934778659733046337360749 11225541997399892376510281)
        ·
          refine ⟨8419156498049919282382711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11225541997399892376510281 8419156498049919282382711)
          ·
            refine ⟨12628734747074878923574067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419156498049919282382711 12628734747074878923574067)
            ·
              refine ⟨18943102120612318385361101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12628734747074878923574067 18943102120612318385361101)
              ·
                refine ⟨7103663295229619394510413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18943102120612318385361101 7103663295229619394510413)
                ·
                  refine ⟨2663873735711107272941405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7103663295229619394510413 2663873735711107272941405)
                  ·
                    refine ⟨998952650891665227353027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663873735711107272941405 998952650891665227353027)
                    ·
                      rfl

theorem cell22_2918180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2918180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918180 prefixEnd_2918180 := by exact prefixLift 2918180
  have htrace : WordTrace (prefixWord ++ tailWord_2918180) baseStart_2918180 baseEnd_2918180 := by
    simpa [prefixWord, tailWord_2918180, baseEnd_2918180] using wordTrace_append hprefix tailTrace_2918180
  have hstable : (prefixWord ++ tailWord_2918180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918180).length < 2 ^ (prefixWord ++ tailWord_2918180).sum := by decide
  have hdescent : baseEnd_2918180 < baseStart_2918180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918244 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_2918244 : Nat := 118140960795 + 2918244 * 2 ^ 59
def prefixEnd_2918244 : Nat := 4983230072969 + 3 ^ 40 * 2918244 * 2
def baseEnd_2918244 : Nat := 332991519799863464584277

theorem tailTrace_2918244 : CollatzResearch.WordTrace tailWord_2918244 prefixEnd_2918244 332991519799863464584277 := by
  unfold tailWord_2918244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53218551419853929620472893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70958068559805239493963857 53218551419853929620472893)
  ·
    refine ⟨19956956782445223607677335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53218551419853929620472893 19956956782445223607677335)
    ·
      refine ⟨29935435173667835411516003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19956956782445223607677335 29935435173667835411516003)
      ·
        refine ⟨44903152760501753117274005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29935435173667835411516003 44903152760501753117274005)
        ·
          refine ⟨2104835285648519677372219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44903152760501753117274005 2104835285648519677372219)
          ·
            refine ⟨3157252928472779516058329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104835285648519677372219 3157252928472779516058329)
            ·
              refine ⟨2367939696354584637043747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157252928472779516058329 2367939696354584637043747)
              ·
                refine ⟨3551909544531876955565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367939696354584637043747 3551909544531876955565621)
                ·
                  refine ⟨332991519799863464584277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3551909544531876955565621 332991519799863464584277)
                  ·
                    rfl

theorem cell22_2918244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_2918244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918244 prefixEnd_2918244 := by exact prefixLift 2918244
  have htrace : WordTrace (prefixWord ++ tailWord_2918244) baseStart_2918244 baseEnd_2918244 := by
    simpa [prefixWord, tailWord_2918244, baseEnd_2918244] using wordTrace_append hprefix tailTrace_2918244
  have hstable : (prefixWord ++ tailWord_2918244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918244).length < 2 ^ (prefixWord ++ tailWord_2918244).sum := by decide
  have hdescent : baseEnd_2918244 < baseStart_2918244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918300 : List Nat := [2, 2, 3, 3, 1, 1, 3, 7]
def baseStart_2918300 : Nat := 118140960795 + 2918300 * 2 ^ 59
def prefixEnd_2918300 : Nat := 4983230072969 + 3 ^ 40 * 2918300 * 2
def baseEnd_2918300 : Nat := 110999303260447212705851

theorem tailTrace_2918300 : CollatzResearch.WordTrace tailWord_2918300 prefixEnd_2918300 110999303260447212705851 := by
  unfold tailWord_2918300
  simp only [CollatzResearch.WordTrace]
  refine ⟨53219572663752490402492177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70959430218336653869989569 53219572663752490402492177)
  ·
    refine ⟨39914679497814367801869133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53219572663752490402492177 39914679497814367801869133)
    ·
      refine ⟨14968004811680387925700925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39914679497814367801869133 14968004811680387925700925)
      ·
        refine ⟨5613001804380145472137847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14968004811680387925700925 5613001804380145472137847)
        ·
          refine ⟨8419502706570218208206771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613001804380145472137847 8419502706570218208206771)
          ·
            refine ⟨12629254059855327312310157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419502706570218208206771 12629254059855327312310157)
            ·
              refine ⟨4735970272445747742116309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12629254059855327312310157 4735970272445747742116309)
              ·
                refine ⟨110999303260447212705851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4735970272445747742116309 110999303260447212705851)
                ·
                  rfl

theorem cell22_2918300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_2918300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918300 prefixEnd_2918300 := by exact prefixLift 2918300
  have htrace : WordTrace (prefixWord ++ tailWord_2918300) baseStart_2918300 baseEnd_2918300 := by
    simpa [prefixWord, tailWord_2918300, baseEnd_2918300] using wordTrace_append hprefix tailTrace_2918300
  have hstable : (prefixWord ++ tailWord_2918300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918300).length < 2 ^ (prefixWord ++ tailWord_2918300).sum := by decide
  have hdescent : baseEnd_2918300 < baseStart_2918300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918328 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_2918328 : Nat := 118140960795 + 2918328 * 2 ^ 59
def prefixEnd_2918328 : Nat := 4983230072969 + 3 ^ 40 * 2918328 * 2
def baseEnd_2918328 : Nat := 333001104772080724884191

theorem tailTrace_2918328 : CollatzResearch.WordTrace tailWord_2918328 prefixEnd_2918328 333001104772080724884191 := by
  unfold tailWord_2918328
  simp only [CollatzResearch.WordTrace]
  refine ⟨53220083285701770793501819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70960111047602361058002425 53220083285701770793501819)
  ·
    refine ⟨79830124928552656190252729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53220083285701770793501819 79830124928552656190252729)
    ·
      refine ⟨59872593696414492142689547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79830124928552656190252729 59872593696414492142689547)
      ·
        refine ⟨89808890544621738214034321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59872593696414492142689547 89808890544621738214034321)
        ·
          refine ⟨67356667908466303660525741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89808890544621738214034321 67356667908466303660525741)
          ·
            refine ⟨25258750465674863872697153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67356667908466303660525741 25258750465674863872697153)
            ·
              refine ⟨18944062849256147904522865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25258750465674863872697153 18944062849256147904522865)
              ·
                refine ⟨14208047136942110928392149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18944062849256147904522865 14208047136942110928392149)
                ·
                  refine ⟨333001104772080724884191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14208047136942110928392149 333001104772080724884191)
                  ·
                    rfl

theorem cell22_2918328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_2918328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918328 prefixEnd_2918328 := by exact prefixLift 2918328
  have htrace : WordTrace (prefixWord ++ tailWord_2918328) baseStart_2918328 baseEnd_2918328 := by
    simpa [prefixWord, tailWord_2918328, baseEnd_2918328] using wordTrace_append hprefix tailTrace_2918328
  have hstable : (prefixWord ++ tailWord_2918328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918328).length < 2 ^ (prefixWord ++ tailWord_2918328).sum := by decide
  have hdescent : baseEnd_2918328 < baseStart_2918328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918407 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 6]
def baseStart_2918407 : Nat := 118140960795 + 2918407 * 2 ^ 59
def prefixEnd_2918407 : Nat := 4983230072969 + 3 ^ 40 * 2918407 * 2
def baseEnd_2918407 : Nat := 333010119210237433975777

theorem tailTrace_2918407 : CollatzResearch.WordTrace tailWord_2918407 prefixEnd_2918407 333010119210237433975777 := by
  unfold tailWord_2918407
  simp only [CollatzResearch.WordTrace]
  refine ⟨106443047938117338079129475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70962031958744892052752983 106443047938117338079129475)
  ·
    refine ⟨159664571907176007118694213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106443047938117338079129475 159664571907176007118694213)
    ·
      refine ⟨29937107232595501334755165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159664571907176007118694213 29937107232595501334755165)
      ·
        refine ⟨11226415212223313000533187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29937107232595501334755165 11226415212223313000533187)
        ·
          refine ⟨16839622818334969500799781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226415212223313000533187 16839622818334969500799781)
          ·
            refine ⟨3157429278437806781399959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16839622818334969500799781 3157429278437806781399959)
            ·
              refine ⟨4736143917656710172099939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157429278437806781399959 4736143917656710172099939)
              ·
                refine ⟨7104215876485065258149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736143917656710172099939 7104215876485065258149909)
                ·
                  refine ⟨333010119210237433975777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7104215876485065258149909 333010119210237433975777)
                  ·
                    rfl

theorem cell22_2918407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].length) (baseStart_2918407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918407 prefixEnd_2918407 := by exact prefixLift 2918407
  have htrace : WordTrace (prefixWord ++ tailWord_2918407) baseStart_2918407 baseEnd_2918407 := by
    simpa [prefixWord, tailWord_2918407, baseEnd_2918407] using wordTrace_append hprefix tailTrace_2918407
  have hstable : (prefixWord ++ tailWord_2918407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918407).length < 2 ^ (prefixWord ++ tailWord_2918407).sum := by decide
  have hdescent : baseEnd_2918407 < baseStart_2918407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918437 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2918437 : Nat := 118140960795 + 2918437 * 2 ^ 59
def prefixEnd_2918437 : Nat := 4983230072969 + 3 ^ 40 * 2918437 * 2
def baseEnd_2918437 : Nat := 999040627243802223677239

theorem tailTrace_2918437 : CollatzResearch.WordTrace tailWord_2918437 prefixEnd_2918437 999040627243802223677239 := by
  unfold tailWord_2918437
  simp only [CollatzResearch.WordTrace]
  refine ⟨106444142128008653202721565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70962761418672435468481043 106444142128008653202721565)
  ·
    refine ⟨39916553298003244951020587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106444142128008653202721565 39916553298003244951020587)
    ·
      refine ⟨59874829947004867426530881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39916553298003244951020587 59874829947004867426530881)
      ·
        refine ⟨44906122460253650569898161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59874829947004867426530881 44906122460253650569898161)
        ·
          refine ⟨33679591845190237927423621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44906122460253650569898161 33679591845190237927423621)
          ·
            refine ⟨6314923470973169611391929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33679591845190237927423621 6314923470973169611391929)
            ·
              refine ⟨4736192603229877208543947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6314923470973169611391929 4736192603229877208543947)
              ·
                refine ⟨7104288904844815812815921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736192603229877208543947 7104288904844815812815921)
                ·
                  refine ⟨5328216678633611859611941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7104288904844815812815921 5328216678633611859611941)
                  ·
                    refine ⟨999040627243802223677239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328216678633611859611941 999040627243802223677239)
                    ·
                      rfl

theorem cell22_2918437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2918437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918437 prefixEnd_2918437 := by exact prefixLift 2918437
  have htrace : WordTrace (prefixWord ++ tailWord_2918437) baseStart_2918437 baseEnd_2918437 := by
    simpa [prefixWord, tailWord_2918437, baseEnd_2918437] using wordTrace_append hprefix tailTrace_2918437
  have hstable : (prefixWord ++ tailWord_2918437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918437).length < 2 ^ (prefixWord ++ tailWord_2918437).sum := by decide
  have hdescent : baseEnd_2918437 < baseStart_2918437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918439 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2918439 : Nat := 118140960795 + 2918439 * 2 ^ 59
def prefixEnd_2918439 : Nat := 4983230072969 + 3 ^ 40 * 2918439 * 2
def baseEnd_2918439 : Nat := 999041311884674885127233

theorem tailTrace_2918439 : CollatzResearch.WordTrace tailWord_2918439 prefixEnd_2918439 999041311884674885127233 := by
  unfold tailWord_2918439
  simp only [CollatzResearch.WordTrace]
  refine ⟨106444215074001407544294371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70962810049334271696196247 106444215074001407544294371)
  ·
    refine ⟨159666322611002111316441557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106444215074001407544294371 159666322611002111316441557)
    ·
      refine ⟨3742179436195361983979099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 159666322611002111316441557 3742179436195361983979099)
      ·
        refine ⟨5613269154293042975968649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742179436195361983979099 5613269154293042975968649)
        ·
          refine ⟨4209951865719782231976487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613269154293042975968649 4209951865719782231976487)
          ·
            refine ⟨6314927798579673347964731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209951865719782231976487 6314927798579673347964731)
            ·
              refine ⟨9472391697869510021947097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314927798579673347964731 9472391697869510021947097)
              ·
                refine ⟨7104293773402132516460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9472391697869510021947097 7104293773402132516460323)
                ·
                  refine ⟨10656440660103198774690485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104293773402132516460323 10656440660103198774690485)
                  ·
                    refine ⟨999041311884674885127233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10656440660103198774690485 999041311884674885127233)
                    ·
                      rfl

theorem cell22_2918439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2918439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918439 prefixEnd_2918439 := by exact prefixLift 2918439
  have htrace : WordTrace (prefixWord ++ tailWord_2918439) baseStart_2918439 baseEnd_2918439 := by
    simpa [prefixWord, tailWord_2918439, baseEnd_2918439] using wordTrace_append hprefix tailTrace_2918439
  have hstable : (prefixWord ++ tailWord_2918439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918439).length < 2 ^ (prefixWord ++ tailWord_2918439).sum := by decide
  have hdescent : baseEnd_2918439 < baseStart_2918439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918452 : List Nat := [2, 5, 1, 2, 2, 10]
def baseStart_2918452 : Nat := 118140960795 + 2918452 * 2 ^ 59
def prefixEnd_2918452 : Nat := 4983230072969 + 3 ^ 40 * 2918452 * 2
def baseEnd_2918452 : Nat := 12333898296917866475953

theorem tailTrace_2918452 : CollatzResearch.WordTrace tailWord_2918452 prefixEnd_2918452 12333898296917866475953 := by
  unfold tailWord_2918452
  simp only [CollatzResearch.WordTrace]
  refine ⟨53222344611477155382258805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70963126148636207176345073 53222344611477155382258805)
  ·
    refine ⟨4989594807325983317086763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53222344611477155382258805 4989594807325983317086763)
    ·
      refine ⟨7484392210988974975630145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4989594807325983317086763 7484392210988974975630145)
      ·
        refine ⟨5613294158241731231722609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7484392210988974975630145 5613294158241731231722609)
        ·
          refine ⟨4209970618681298423791957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613294158241731231722609 4209970618681298423791957)
          ·
            refine ⟨12333898296917866475953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4209970618681298423791957 12333898296917866475953)
            ·
              rfl

theorem cell22_2918452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 10].length) (baseStart_2918452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918452 prefixEnd_2918452 := by exact prefixLift 2918452
  have htrace : WordTrace (prefixWord ++ tailWord_2918452) baseStart_2918452 baseEnd_2918452 := by
    simpa [prefixWord, tailWord_2918452, baseEnd_2918452] using wordTrace_append hprefix tailTrace_2918452
  have hstable : (prefixWord ++ tailWord_2918452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918452).length < 2 ^ (prefixWord ++ tailWord_2918452).sum := by decide
  have hdescent : baseEnd_2918452 < baseStart_2918452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918486 : List Nat := [5, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2918486 : Nat := 118140960795 + 2918486 * 2 ^ 59
def prefixEnd_2918486 : Nat := 4983230072969 + 3 ^ 40 * 2918486 * 2
def baseEnd_2918486 : Nat := 111006377882798047689121

theorem tailTrace_2918486 : CollatzResearch.WordTrace tailWord_2918486 prefixEnd_2918486 111006377882798047689121 := by
  unfold tailWord_2918486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652870581551945910703457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70963952869887423047503541 6652870581551945910703457)
  ·
    refine ⟨4989652936163959433027593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6652870581551945910703457 4989652936163959433027593)
    ·
      refine ⟨3742239702122969574770695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4989652936163959433027593 3742239702122969574770695)
      ·
        refine ⟨5613359553184454362156043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742239702122969574770695 5613359553184454362156043)
        ·
          refine ⟨8420039329776681543234065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613359553184454362156043 8420039329776681543234065)
          ·
            refine ⟨6315029497332511157425549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8420039329776681543234065 6315029497332511157425549)
            ·
              refine ⟨2368136061499691684034581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6315029497332511157425549 2368136061499691684034581)
              ·
                refine ⟨111006377882798047689121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2368136061499691684034581 111006377882798047689121)
                ·
                  rfl

theorem cell22_2918486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2918486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918486 prefixEnd_2918486 := by exact prefixLift 2918486
  have htrace : WordTrace (prefixWord ++ tailWord_2918486) baseStart_2918486 baseEnd_2918486 := by
    simpa [prefixWord, tailWord_2918486, baseEnd_2918486] using wordTrace_append hprefix tailTrace_2918486
  have hstable : (prefixWord ++ tailWord_2918486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918486).length < 2 ^ (prefixWord ++ tailWord_2918486).sum := by decide
  have hdescent : baseEnd_2918486 < baseStart_2918486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918501 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_2918501 : Nat := 118140960795 + 2918501 * 2 ^ 59
def prefixEnd_2918501 : Nat := 4983230072969 + 3 ^ 40 * 2918501 * 2
def baseEnd_2918501 : Nat := 999062535751727390077043

theorem tailTrace_2918501 : CollatzResearch.WordTrace tailWord_2918501 prefixEnd_2918501 999062535751727390077043 := by
  unfold tailWord_2918501
  simp only [CollatzResearch.WordTrace]
  refine ⟨106446476399776792133051357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70964317599851194755367571 106446476399776792133051357)
  ·
    refine ⟨39917428649916297049894259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106446476399776792133051357 39917428649916297049894259)
    ·
      refine ⟨59876142974874445574841389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39917428649916297049894259 59876142974874445574841389)
      ·
        refine ⟨22453553615577917090565521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59876142974874445574841389 22453553615577917090565521)
        ·
          refine ⟨16840165211683437817924141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22453553615577917090565521 16840165211683437817924141)
          ·
            refine ⟨6315061954381289181721553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16840165211683437817924141 6315061954381289181721553)
            ·
              refine ⟨4736296465785966886291165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315061954381289181721553 4736296465785966886291165)
              ·
                refine ⟨1776111174669737582359187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736296465785966886291165 1776111174669737582359187)
                ·
                  refine ⟨2664166762004606373538781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776111174669737582359187 2664166762004606373538781)
                  ·
                    refine ⟨999062535751727390077043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664166762004606373538781 999062535751727390077043)
                    ·
                      rfl

theorem cell22_2918501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_2918501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918501 prefixEnd_2918501 := by exact prefixLift 2918501
  have htrace : WordTrace (prefixWord ++ tailWord_2918501) baseStart_2918501 baseEnd_2918501 := by
    simpa [prefixWord, tailWord_2918501, baseEnd_2918501] using wordTrace_append hprefix tailTrace_2918501
  have hstable : (prefixWord ++ tailWord_2918501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918501).length < 2 ^ (prefixWord ++ tailWord_2918501).sum := by decide
  have hdescent : baseEnd_2918501 < baseStart_2918501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918514 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_2918514 : Nat := 118140960795 + 2918514 * 2 ^ 59
def prefixEnd_2918514 : Nat := 4983230072969 + 3 ^ 40 * 2918514 * 2
def baseEnd_2918514 : Nat := 333022328639133229834001

theorem tailTrace_2918514 : CollatzResearch.WordTrace tailWord_2918514 prefixEnd_2918514 333022328639133229834001 := by
  unfold tailWord_2918514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611737637182423838318649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70964633699153130235516397 26611737637182423838318649)
  ·
    refine ⟨19958803227886817878738987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26611737637182423838318649 19958803227886817878738987)
    ·
      refine ⟨29938204841830226818108481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19958803227886817878738987 29938204841830226818108481)
      ·
        refine ⟨22453653631372670113581361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29938204841830226818108481 22453653631372670113581361)
        ·
          refine ⟨16840240223529502585186021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22453653631372670113581361 16840240223529502585186021)
          ·
            refine ⟨3157545041911781734722379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16840240223529502585186021 3157545041911781734722379)
            ·
              refine ⟨4736317562867672602083569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157545041911781734722379 4736317562867672602083569)
              ·
                refine ⟨3552238172150754451562677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4736317562867672602083569 3552238172150754451562677)
                ·
                  refine ⟨333022328639133229834001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3552238172150754451562677 333022328639133229834001)
                  ·
                    rfl

theorem cell22_2918514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_2918514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918514 prefixEnd_2918514 := by exact prefixLift 2918514
  have htrace : WordTrace (prefixWord ++ tailWord_2918514) baseStart_2918514 baseEnd_2918514 := by
    simpa [prefixWord, tailWord_2918514, baseEnd_2918514] using wordTrace_append hprefix tailTrace_2918514
  have hstable : (prefixWord ++ tailWord_2918514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918514).length < 2 ^ (prefixWord ++ tailWord_2918514).sum := by decide
  have hdescent : baseEnd_2918514 < baseStart_2918514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918555 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_2918555 : Nat := 118140960795 + 2918555 * 2 ^ 59
def prefixEnd_2918555 : Nat := 4983230072969 + 3 ^ 40 * 2918555 * 2
def baseEnd_2918555 : Nat := 999081021055289249226877

theorem tailTrace_2918555 : CollatzResearch.WordTrace tailWord_2918555 prefixEnd_2918555 999081021055289249226877 := by
  unfold tailWord_2918555
  simp only [CollatzResearch.WordTrace]
  refine ⟨106448445941581159355517119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70965630627720772903678079 106448445941581159355517119)
  ·
    refine ⟨159672668912371739033275679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106448445941581159355517119 159672668912371739033275679)
    ·
      refine ⟨239509003368557608549913519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159672668912371739033275679 239509003368557608549913519)
      ·
        refine ⟨359263505052836412824870279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239509003368557608549913519 359263505052836412824870279)
        ·
          refine ⟨538895257579254619237305419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359263505052836412824870279 538895257579254619237305419)
          ·
            refine ⟨808342886368881928855958129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538895257579254619237305419 808342886368881928855958129)
            ·
              refine ⟨606257164776661446641968597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808342886368881928855958129 606257164776661446641968597)
              ·
                refine ⟨14209152299453002655671139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606257164776661446641968597 14209152299453002655671139)
                ·
                  refine ⟨21313728449179503983506709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14209152299453002655671139 21313728449179503983506709)
                  ·
                    refine ⟨999081021055289249226877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21313728449179503983506709 999081021055289249226877)
                    ·
                      rfl

theorem cell22_2918555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_2918555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918555 prefixEnd_2918555 := by exact prefixLift 2918555
  have htrace : WordTrace (prefixWord ++ tailWord_2918555) baseStart_2918555 baseEnd_2918555 := by
    simpa [prefixWord, tailWord_2918555, baseEnd_2918555] using wordTrace_append hprefix tailTrace_2918555
  have hstable : (prefixWord ++ tailWord_2918555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918555).length < 2 ^ (prefixWord ++ tailWord_2918555).sum := by decide
  have hdescent : baseEnd_2918555 < baseStart_2918555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918636 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_2918636 : Nat := 118140960795 + 2918636 * 2 ^ 59
def prefixEnd_2918636 : Nat := 4983230072969 + 3 ^ 40 * 2918636 * 2
def baseEnd_2918636 : Nat := 999108749010632037951629

theorem tailTrace_2918636 : CollatzResearch.WordTrace tailWord_2918636 prefixEnd_2918636 999108749010632037951629 := by
  unfold tailWord_2918636
  simp only [CollatzResearch.WordTrace]
  refine ⟨53225700127143855094607881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70967600169525140126143841 53225700127143855094607881)
  ·
    refine ⟨39919275095357891320955911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53225700127143855094607881 39919275095357891320955911)
    ·
      refine ⟨59878912643036836981433867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39919275095357891320955911 59878912643036836981433867)
      ·
        refine ⟨89818368964555255472150801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59878912643036836981433867 89818368964555255472150801)
        ·
          refine ⟨67363776723416441604113101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89818368964555255472150801 67363776723416441604113101)
          ·
            refine ⟨25261416271281165601542413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67363776723416441604113101 25261416271281165601542413)
            ·
              refine ⟨9473031101730437100578405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25261416271281165601542413 9473031101730437100578405)
              ·
                refine ⟨1776193331574456956358451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9473031101730437100578405 1776193331574456956358451)
                ·
                  refine ⟨2664289997361685434537677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776193331574456956358451 2664289997361685434537677)
                  ·
                    refine ⟨999108749010632037951629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664289997361685434537677 999108749010632037951629)
                    ·
                      rfl

theorem cell22_2918636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_2918636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918636 prefixEnd_2918636 := by exact prefixLift 2918636
  have htrace : WordTrace (prefixWord ++ tailWord_2918636) baseStart_2918636 baseEnd_2918636 := by
    simpa [prefixWord, tailWord_2918636, baseEnd_2918636] using wordTrace_append hprefix tailTrace_2918636
  have hstable : (prefixWord ++ tailWord_2918636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918636).length < 2 ^ (prefixWord ++ tailWord_2918636).sum := by decide
  have hdescent : baseEnd_2918636 < baseStart_2918636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918707 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_2918707 : Nat := 118140960795 + 2918707 * 2 ^ 59
def prefixEnd_2918707 : Nat := 4983230072969 + 3 ^ 40 * 2918707 * 2
def baseEnd_2918707 : Nat := 999133053761611519426411

theorem tailTrace_2918707 : CollatzResearch.WordTrace tailWord_2918707 prefixEnd_2918707 999133053761611519426411 := by
  unfold tailWord_2918707
  simp only [CollatzResearch.WordTrace]
  refine ⟨106453989837030489315050375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70969326558020326210033583 106453989837030489315050375)
  ·
    refine ⟨159680984755545733972575563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106453989837030489315050375 159680984755545733972575563)
    ·
      refine ⟨239521477133318600958863345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159680984755545733972575563 239521477133318600958863345)
      ·
        refine ⟨179641107849988950719147509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239521477133318600958863345 179641107849988950719147509)
        ·
          refine ⟨16841353860936464129920079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179641107849988950719147509 16841353860936464129920079)
          ·
            refine ⟨25262030791404696194880119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16841353860936464129920079 25262030791404696194880119)
            ·
              refine ⟨37893046187107044292320179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25262030791404696194880119 37893046187107044292320179)
              ·
                refine ⟨56839569280660566438480269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37893046187107044292320179 56839569280660566438480269)
                ·
                  refine ⟨21314838480247712414430101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56839569280660566438480269 21314838480247712414430101)
                  ·
                    refine ⟨999133053761611519426411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21314838480247712414430101 999133053761611519426411)
                    ·
                      rfl

theorem cell22_2918707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_2918707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918707 prefixEnd_2918707 := by exact prefixLift 2918707
  have htrace : WordTrace (prefixWord ++ tailWord_2918707) baseStart_2918707 baseEnd_2918707 := by
    simpa [prefixWord, tailWord_2918707, baseEnd_2918707] using wordTrace_append hprefix tailTrace_2918707
  have hstable : (prefixWord ++ tailWord_2918707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918707).length < 2 ^ (prefixWord ++ tailWord_2918707).sum := by decide
  have hdescent : baseEnd_2918707 < baseStart_2918707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918741 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2918741 : Nat := 118140960795 + 2918741 * 2 ^ 59
def prefixEnd_2918741 : Nat := 4983230072969 + 3 ^ 40 * 2918741 * 2
def baseEnd_2918741 : Nat := 999144692656446764076307

theorem tailTrace_2918741 : CollatzResearch.WordTrace tailWord_2918741 prefixEnd_2918741 999144692656446764076307 := by
  unfold tailWord_2918741
  simp only [CollatzResearch.WordTrace]
  refine ⟨106455229918907313121788077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70970153279271542081192051 106455229918907313121788077)
  ·
    refine ⟨39920711219590242420670529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106455229918907313121788077 39920711219590242420670529)
    ·
      refine ⟨29940533414692681815502897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39920711219590242420670529 29940533414692681815502897)
      ·
        refine ⟨22455400061019511361627173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29940533414692681815502897 22455400061019511361627173)
        ·
          refine ⟨4210387511441158380305095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22455400061019511361627173 4210387511441158380305095)
          ·
            refine ⟨6315581267161737570457643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210387511441158380305095 6315581267161737570457643)
            ·
              refine ⟨9473371900742606355686465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315581267161737570457643 9473371900742606355686465)
              ·
                refine ⟨7105028925556954766764849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9473371900742606355686465 7105028925556954766764849)
                ·
                  refine ⟨5328771694167716075073637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105028925556954766764849 5328771694167716075073637)
                  ·
                    refine ⟨999144692656446764076307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328771694167716075073637 999144692656446764076307)
                    ·
                      rfl

theorem cell22_2918741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2918741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918741 prefixEnd_2918741 := by exact prefixLift 2918741
  have htrace : WordTrace (prefixWord ++ tailWord_2918741) baseStart_2918741 baseEnd_2918741 := by
    simpa [prefixWord, tailWord_2918741, baseEnd_2918741] using wordTrace_append hprefix tailTrace_2918741
  have hstable : (prefixWord ++ tailWord_2918741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918741).length < 2 ^ (prefixWord ++ tailWord_2918741).sum := by decide
  have hdescent : baseEnd_2918741 < baseStart_2918741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918760 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_2918760 : Nat := 118140960795 + 2918760 * 2 ^ 59
def prefixEnd_2918760 : Nat := 4983230072969 + 3 ^ 40 * 2918760 * 2
def baseEnd_2918760 : Nat := 999151196744737047851249

theorem tailTrace_2918760 : CollatzResearch.WordTrace tailWord_2918760 prefixEnd_2918760 999151196744737047851249 := by
  unfold tailWord_2918760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53227961452919239683364867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70970615270558986244486489 53227961452919239683364867)
  ·
    refine ⟨79841942179378859525047301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53227961452919239683364867 79841942179378859525047301)
    ·
      refine ⟨14970364158633536160946369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79841942179378859525047301 14970364158633536160946369)
      ·
        refine ⟨11227773118975152120709777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14970364158633536160946369 11227773118975152120709777)
        ·
          refine ⟨8420829839231364090532333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11227773118975152120709777 8420829839231364090532333)
          ·
            refine ⟨3157811189711761533949625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8420829839231364090532333 3157811189711761533949625)
            ·
              refine ⟨2368358392283821150462219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157811189711761533949625 2368358392283821150462219)
              ·
                refine ⟨3552537588425731725693329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368358392283821150462219 3552537588425731725693329)
                ·
                  refine ⟨2664403191319298794269997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552537588425731725693329 2664403191319298794269997)
                  ·
                    refine ⟨999151196744737047851249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664403191319298794269997 999151196744737047851249)
                    ·
                      rfl

theorem cell22_2918760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_2918760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918760 prefixEnd_2918760 := by exact prefixLift 2918760
  have htrace : WordTrace (prefixWord ++ tailWord_2918760) baseStart_2918760 baseEnd_2918760 := by
    simpa [prefixWord, tailWord_2918760, baseEnd_2918760] using wordTrace_append hprefix tailTrace_2918760
  have hstable : (prefixWord ++ tailWord_2918760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918760).length < 2 ^ (prefixWord ++ tailWord_2918760).sum := by decide
  have hdescent : baseEnd_2918760 < baseStart_2918760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918767 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 9]
def baseStart_2918767 : Nat := 118140960795 + 2918767 * 2 ^ 59
def prefixEnd_2918767 : Nat := 4983230072969 + 3 ^ 40 * 2918767 * 2
def baseEnd_2918767 : Nat := 333051197662597120975409

theorem tailTrace_2918767 : CollatzResearch.WordTrace tailWord_2918767 prefixEnd_2918767 333051197662597120975409 := by
  unfold tailWord_2918767
  simp only [CollatzResearch.WordTrace]
  refine ⟨106456178216813119562234555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70970785477875413041489703 106456178216813119562234555)
  ·
    refine ⟨159684267325219679343351833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106456178216813119562234555 159684267325219679343351833)
    ·
      refine ⟨119763200493914759507513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159684267325219679343351833 119763200493914759507513875)
      ·
        refine ⟨179644800740872139261270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119763200493914759507513875 179644800740872139261270813)
        ·
          refine ⟨67366800277827052222976555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179644800740872139261270813 67366800277827052222976555)
          ·
            refine ⟨101050200416740578334464833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67366800277827052222976555 101050200416740578334464833)
            ·
              refine ⟨75787650312555433750848625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101050200416740578334464833 75787650312555433750848625)
              ·
                refine ⟨56840737734416575313136469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75787650312555433750848625 56840737734416575313136469)
                ·
                  refine ⟨333051197662597120975409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56840737734416575313136469 333051197662597120975409)
                  ·
                    rfl

theorem cell22_2918767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_2918767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918767 prefixEnd_2918767 := by exact prefixLift 2918767
  have htrace : WordTrace (prefixWord ++ tailWord_2918767) baseStart_2918767 baseEnd_2918767 := by
    simpa [prefixWord, tailWord_2918767, baseEnd_2918767] using wordTrace_append hprefix tailTrace_2918767
  have hstable : (prefixWord ++ tailWord_2918767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918767).length < 2 ^ (prefixWord ++ tailWord_2918767).sum := by decide
  have hdescent : baseEnd_2918767 < baseStart_2918767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918788 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2918788 : Nat := 118140960795 + 2918788 * 2 ^ 59
def prefixEnd_2918788 : Nat := 4983230072969 + 3 ^ 40 * 2918788 * 2
def baseEnd_2918788 : Nat := 999160781716954308151163

theorem tailTrace_2918788 : CollatzResearch.WordTrace tailWord_2918788 prefixEnd_2918788 999160781716954308151163 := by
  unfold tailWord_2918788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53228472074868520074374509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70971296099824693432499345 53228472074868520074374509)
  ·
    refine ⟨19960677028075695027890441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53228472074868520074374509 19960677028075695027890441)
    ·
      refine ⟨14970507771056771270917831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19960677028075695027890441 14970507771056771270917831)
      ·
        refine ⟨22455761656585156906376747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14970507771056771270917831 22455761656585156906376747)
        ·
          refine ⟨33683642484877735359565121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22455761656585156906376747 33683642484877735359565121)
          ·
            refine ⟨25262731863658301519673841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33683642484877735359565121 25262731863658301519673841)
            ·
              refine ⟨18947048897743726139755381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25262731863658301519673841 18947048897743726139755381)
              ·
                refine ⟨1776285834163474325602067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18947048897743726139755381 1776285834163474325602067)
                ·
                  refine ⟨2664428751245211488403101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776285834163474325602067 2664428751245211488403101)
                  ·
                    refine ⟨999160781716954308151163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664428751245211488403101 999160781716954308151163)
                    ·
                      rfl

theorem cell22_2918788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2918788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918788 prefixEnd_2918788 := by exact prefixLift 2918788
  have htrace : WordTrace (prefixWord ++ tailWord_2918788) baseStart_2918788 baseEnd_2918788 := by
    simpa [prefixWord, tailWord_2918788, baseEnd_2918788] using wordTrace_append hprefix tailTrace_2918788
  have hstable : (prefixWord ++ tailWord_2918788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918788).length < 2 ^ (prefixWord ++ tailWord_2918788).sum := by decide
  have hdescent : baseEnd_2918788 < baseStart_2918788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918859 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_2918859 : Nat := 118140960795 + 2918859 * 2 ^ 59
def prefixEnd_2918859 : Nat := 4983230072969 + 3 ^ 40 * 2918859 * 2
def baseEnd_2918859 : Nat := 999185086467933789625945

theorem tailTrace_2918859 : CollatzResearch.WordTrace tailWord_2918859 prefixEnd_2918859 999185086467933789625945 := by
  unfold tailWord_2918859
  simp only [CollatzResearch.WordTrace]
  refine ⟨106459533732479819274583631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70973022488319879516389087 106459533732479819274583631)
  ·
    refine ⟨159689300598719728911875447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106459533732479819274583631 159689300598719728911875447)
    ·
      refine ⟨239533950898079593367813171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159689300598719728911875447 239533950898079593367813171)
      ·
        refine ⟨359300926347119390051719757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239533950898079593367813171 359300926347119390051719757)
        ·
          refine ⟨134737847380169771269394909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359300926347119390051719757 134737847380169771269394909)
          ·
            refine ⟨50526692767563664226023091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134737847380169771269394909 50526692767563664226023091)
            ·
              refine ⟨75790039151345496339034637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50526692767563664226023091 75790039151345496339034637)
              ·
                refine ⟨28421264681754561127137989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75790039151345496339034637 28421264681754561127137989)
                ·
                  refine ⟨5328987127828980211338373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28421264681754561127137989 5328987127828980211338373)
                  ·
                    refine ⟨999185086467933789625945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328987127828980211338373 999185086467933789625945)
                    ·
                      rfl

theorem cell22_2918859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_2918859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918859 prefixEnd_2918859 := by exact prefixLift 2918859
  have htrace : WordTrace (prefixWord ++ tailWord_2918859) baseStart_2918859 baseEnd_2918859 := by
    simpa [prefixWord, tailWord_2918859, baseEnd_2918859] using wordTrace_append hprefix tailTrace_2918859
  have hstable : (prefixWord ++ tailWord_2918859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918859).length < 2 ^ (prefixWord ++ tailWord_2918859).sum := by decide
  have hdescent : baseEnd_2918859 < baseStart_2918859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918874 : List Nat := [3, 1, 1, 2, 3, 1, 2, 9]
def baseStart_2918874 : Nat := 118140960795 + 2918874 * 2 ^ 59
def prefixEnd_2918874 : Nat := 4983230072969 + 3 ^ 40 * 2918874 * 2
def baseEnd_2918874 : Nat := 111021135697164305611211

theorem tailTrace_2918874 : CollatzResearch.WordTrace tailWord_2918874 prefixEnd_2918874 111021135697164305611211 := by
  unfold tailWord_2918874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615020206856369209094919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70973387218283651224253117 26615020206856369209094919)
  ·
    refine ⟨39922530310284553813642379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26615020206856369209094919 39922530310284553813642379)
    ·
      refine ⟨59883795465426830720463569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39922530310284553813642379 59883795465426830720463569)
      ·
        refine ⟨44912846599070123040347677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59883795465426830720463569 44912846599070123040347677)
        ·
          refine ⟨16842317474651296140130379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44912846599070123040347677 16842317474651296140130379)
          ·
            refine ⟨25263476211976944210195569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16842317474651296140130379 25263476211976944210195569)
            ·
              refine ⟨18947607158982708157646677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25263476211976944210195569 18947607158982708157646677)
              ·
                refine ⟨111021135697164305611211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18947607158982708157646677 111021135697164305611211)
                ·
                  rfl

theorem cell22_2918874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_2918874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918874 prefixEnd_2918874 := by exact prefixLift 2918874
  have htrace : WordTrace (prefixWord ++ tailWord_2918874) baseStart_2918874 baseEnd_2918874 := by
    simpa [prefixWord, tailWord_2918874, baseEnd_2918874] using wordTrace_append hprefix tailTrace_2918874
  have hstable : (prefixWord ++ tailWord_2918874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918874).length < 2 ^ (prefixWord ++ tailWord_2918874).sum := by decide
  have hdescent : baseEnd_2918874 < baseStart_2918874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918882 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2918882 : Nat := 118140960795 + 2918882 * 2 ^ 59
def prefixEnd_2918882 : Nat := 4983230072969 + 3 ^ 40 * 2918882 * 2
def baseEnd_2918882 : Nat := 999192959837969396300875

theorem tailTrace_2918882 : CollatzResearch.WordTrace tailWord_2918882 prefixEnd_2918882 999192959837969396300875 := by
  unfold tailWord_2918882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615093152849123550667725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70973581740930996135113933 26615093152849123550667725)
  ·
    refine ⟨9980659932318421331500397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26615093152849123550667725 9980659932318421331500397)
    ·
      refine ⟨3742747474619407999312649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9980659932318421331500397 3742747474619407999312649)
      ·
        refine ⟨2807060605964555999484487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3742747474619407999312649 2807060605964555999484487)
        ·
          refine ⟨4210590908946833999226731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807060605964555999484487 4210590908946833999226731)
          ·
            refine ⟨6315886363420250998840097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210590908946833999226731 6315886363420250998840097)
            ·
              refine ⟨4736914772565188249130073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315886363420250998840097 4736914772565188249130073)
              ·
                refine ⟨3552686079423891186847555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4736914772565188249130073 3552686079423891186847555)
                ·
                  refine ⟨5329029119135836780271333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552686079423891186847555 5329029119135836780271333)
                  ·
                    refine ⟨999192959837969396300875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329029119135836780271333 999192959837969396300875)
                    ·
                      rfl

theorem cell22_2918882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2918882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918882 prefixEnd_2918882 := by exact prefixLift 2918882
  have htrace : WordTrace (prefixWord ++ tailWord_2918882) baseStart_2918882 baseEnd_2918882 := by
    simpa [prefixWord, tailWord_2918882, baseEnd_2918882] using wordTrace_append hprefix tailTrace_2918882
  have hstable : (prefixWord ++ tailWord_2918882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918882).length < 2 ^ (prefixWord ++ tailWord_2918882).sum := by decide
  have hdescent : baseEnd_2918882 < baseStart_2918882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918923 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 3, 3]
def baseStart_2918923 : Nat := 118140960795 + 2918923 * 2 ^ 59
def prefixEnd_2918923 : Nat := 4983230072969 + 3 ^ 40 * 2918923 * 2
def baseEnd_2918923 : Nat := 999206994975858956025749

theorem tailTrace_2918923 : CollatzResearch.WordTrace tailWord_2918923 prefixEnd_2918923 999206994975858956025749 := by
  unfold tailWord_2918923
  simp only [CollatzResearch.WordTrace]
  refine ⟨106461868004247958204913423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70974578669498638803275615 106461868004247958204913423)
  ·
    refine ⟨159692802006371937307370135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106461868004247958204913423 159692802006371937307370135)
    ·
      refine ⟨239539203009557905961055203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159692802006371937307370135 239539203009557905961055203)
      ·
        refine ⟨359308804514336858941582805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239539203009557905961055203 359308804514336858941582805)
        ·
          refine ⟨8421300105804770131443347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 359308804514336858941582805 8421300105804770131443347)
          ·
            refine ⟨12631950158707155197165021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421300105804770131443347 12631950158707155197165021)
            ·
              refine ⟨4736981309515183198936883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12631950158707155197165021 4736981309515183198936883)
              ·
                refine ⟨7105471964272774798405325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736981309515183198936883 7105471964272774798405325)
                ·
                  refine ⟨2664551986602290549401997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7105471964272774798405325 2664551986602290549401997)
                  ·
                    refine ⟨999206994975858956025749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664551986602290549401997 999206994975858956025749)
                    ·
                      rfl

theorem cell22_2918923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].length) (baseStart_2918923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918923 prefixEnd_2918923 := by exact prefixLift 2918923
  have htrace : WordTrace (prefixWord ++ tailWord_2918923) baseStart_2918923 baseEnd_2918923 := by
    simpa [prefixWord, tailWord_2918923, baseEnd_2918923] using wordTrace_append hprefix tailTrace_2918923
  have hstable : (prefixWord ++ tailWord_2918923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918923).length < 2 ^ (prefixWord ++ tailWord_2918923).sum := by decide
  have hdescent : baseEnd_2918923 < baseStart_2918923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918925 : List Nat := [1, 7, 1, 1, 1, 2, 2, 7]
def baseStart_2918925 : Nat := 118140960795 + 2918925 * 2 ^ 59
def prefixEnd_2918925 : Nat := 4983230072969 + 3 ^ 40 * 2918925 * 2
def baseEnd_2918925 : Nat := 111023075512970179719527

theorem tailTrace_2918925 : CollatzResearch.WordTrace tailWord_2918925 prefixEnd_2918925 111023075512970179719527 := by
  unfold tailWord_2918925
  simp only [CollatzResearch.WordTrace]
  refine ⟨106461940950240712546486229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70974627300160475030990819 106461940950240712546486229)
  ·
    refine ⟨2495201741021266700308271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106461940950240712546486229 2495201741021266700308271)
    ·
      refine ⟨3742802611531900050462407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495201741021266700308271 3742802611531900050462407)
      ·
        refine ⟨5614203917297850075693611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742802611531900050462407 5614203917297850075693611)
        ·
          refine ⟨8421305875946775113540417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614203917297850075693611 8421305875946775113540417)
          ·
            refine ⟨6315979406960081335155313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8421305875946775113540417 6315979406960081335155313)
            ·
              refine ⟨4736984555220061001366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315979406960081335155313 4736984555220061001366485)
              ·
                refine ⟨111023075512970179719527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4736984555220061001366485 111023075512970179719527)
                ·
                  rfl

theorem cell22_2918925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 7].length) (baseStart_2918925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918925 prefixEnd_2918925 := by exact prefixLift 2918925
  have htrace : WordTrace (prefixWord ++ tailWord_2918925) baseStart_2918925 baseEnd_2918925 := by
    simpa [prefixWord, tailWord_2918925, baseEnd_2918925] using wordTrace_append hprefix tailTrace_2918925
  have hstable : (prefixWord ++ tailWord_2918925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918925).length < 2 ^ (prefixWord ++ tailWord_2918925).sum := by decide
  have hdescent : baseEnd_2918925 < baseStart_2918925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918974 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2918974 : Nat := 118140960795 + 2918974 * 2 ^ 59
def prefixEnd_2918974 : Nat := 4983230072969 + 3 ^ 40 * 2918974 * 2
def baseEnd_2918974 : Nat := 999224453318111823000593

theorem tailTrace_2918974 : CollatzResearch.WordTrace tailWord_2918974 prefixEnd_2918974 999224453318111823000593 := by
  unfold tailWord_2918974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307966015882899239377497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70975818751375462610013317 13307966015882899239377497)
  ·
    refine ⟨9980974511912174429533123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13307966015882899239377497 9980974511912174429533123)
    ·
      refine ⟨14971461767868261644299685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980974511912174429533123 14971461767868261644299685)
      ·
        refine ⟨2807149081475299058306191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14971461767868261644299685 2807149081475299058306191)
        ·
          refine ⟨4210723622212948587459287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807149081475299058306191 4210723622212948587459287)
          ·
            refine ⟨6316085433319422881188931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210723622212948587459287 6316085433319422881188931)
            ·
              refine ⟨9474128149979134321783397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316085433319422881188931 9474128149979134321783397)
              ·
                refine ⟨1776399028121087685334387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9474128149979134321783397 1776399028121087685334387)
                ·
                  refine ⟨2664598542181631528001581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776399028121087685334387 2664598542181631528001581)
                  ·
                    refine ⟨999224453318111823000593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664598542181631528001581 999224453318111823000593)
                    ·
                      rfl

theorem cell22_2918974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2918974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918974 prefixEnd_2918974 := by exact prefixLift 2918974
  have htrace : WordTrace (prefixWord ++ tailWord_2918974) baseStart_2918974 baseEnd_2918974 := by
    simpa [prefixWord, tailWord_2918974, baseEnd_2918974] using wordTrace_append hprefix tailTrace_2918974
  have hstable : (prefixWord ++ tailWord_2918974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918974).length < 2 ^ (prefixWord ++ tailWord_2918974).sum := by decide
  have hdescent : baseEnd_2918974 < baseStart_2918974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919011 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_2919011 : Nat := 118140960795 + 2919011 * 2 ^ 59
def prefixEnd_2919011 : Nat := 4983230072969 + 3 ^ 40 * 2919011 * 2
def baseEnd_2919011 : Nat := 999237119174256059825479

theorem tailTrace_2919011 : CollatzResearch.WordTrace tailWord_2919011 prefixEnd_2919011 999237119174256059825479 := by
  unfold tailWord_2919011
  simp only [CollatzResearch.WordTrace]
  refine ⟨106465077627929149234116887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70976718418619432822744591 106465077627929149234116887)
  ·
    refine ⟨159697616441893723851175331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106465077627929149234116887 159697616441893723851175331)
    ·
      refine ⟨239546424662840585776762997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159697616441893723851175331 239546424662840585776762997)
      ·
        refine ⟨22457477312141304916571531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239546424662840585776762997 22457477312141304916571531)
        ·
          refine ⟨33686215968211957374857297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22457477312141304916571531 33686215968211957374857297)
          ·
            refine ⟨25264661976158968031142973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33686215968211957374857297 25264661976158968031142973)
            ·
              refine ⟨9474248241059613011678615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25264661976158968031142973 9474248241059613011678615)
              ·
                refine ⟨14211372361589419517517923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9474248241059613011678615 14211372361589419517517923)
                ·
                  refine ⟨21317058542384129276276885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14211372361589419517517923 21317058542384129276276885)
                  ·
                    refine ⟨999237119174256059825479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21317058542384129276276885 999237119174256059825479)
                    ·
                      rfl

theorem cell22_2919011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_2919011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919011 prefixEnd_2919011 := by exact prefixLift 2919011
  have htrace : WordTrace (prefixWord ++ tailWord_2919011) baseStart_2919011 baseEnd_2919011 := by
    simpa [prefixWord, tailWord_2919011, baseEnd_2919011] using wordTrace_append hprefix tailTrace_2919011
  have hstable : (prefixWord ++ tailWord_2919011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919011).length < 2 ^ (prefixWord ++ tailWord_2919011).sum := by decide
  have hdescent : baseEnd_2919011 < baseStart_2919011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919060 : List Nat := [2, 4, 2, 2, 1, 1, 4, 6]
def baseStart_2919060 : Nat := 118140960795 + 2919060 * 2 ^ 59
def prefixEnd_2919060 : Nat := 4983230072969 + 3 ^ 40 * 2919060 * 2
def baseEnd_2919060 : Nat := 111028210319515140594481

theorem tailTrace_2919060 : CollatzResearch.WordTrace tailWord_2919060 prefixEnd_2919060 111028210319515140594481 := by
  unfold tailWord_2919060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53233432402375815301325317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70977909869834420401767089 53233432402375815301325317)
  ·
    refine ⟨9981268575445465368998497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53233432402375815301325317 9981268575445465368998497)
    ·
      refine ⟨7485951431584099026748873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9981268575445465368998497 7485951431584099026748873)
      ·
        refine ⟨5614463573688074270061655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7485951431584099026748873 5614463573688074270061655)
        ·
          refine ⟨8421695360532111405092483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614463573688074270061655 8421695360532111405092483)
          ·
            refine ⟨12632543040798167107638725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421695360532111405092483 12632543040798167107638725)
            ·
              refine ⟨2368601820149656332682261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12632543040798167107638725 2368601820149656332682261)
              ·
                refine ⟨111028210319515140594481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2368601820149656332682261 111028210319515140594481)
                ·
                  rfl

theorem cell22_2919060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_2919060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919060 prefixEnd_2919060 := by exact prefixLift 2919060
  have htrace : WordTrace (prefixWord ++ tailWord_2919060) baseStart_2919060 baseEnd_2919060 := by
    simpa [prefixWord, tailWord_2919060, baseEnd_2919060] using wordTrace_append hprefix tailTrace_2919060
  have hstable : (prefixWord ++ tailWord_2919060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919060).length < 2 ^ (prefixWord ++ tailWord_2919060).sum := by decide
  have hdescent : baseEnd_2919060 < baseStart_2919060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919075 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 1, 3]
def baseStart_2919075 : Nat := 118140960795 + 2919075 * 2 ^ 59
def prefixEnd_2919075 : Nat := 4983230072969 + 3 ^ 40 * 2919075 * 2
def baseEnd_2919075 : Nat := 999259027682181226225283

theorem tailTrace_2919075 : CollatzResearch.WordTrace tailWord_2919075 prefixEnd_2919075 999259027682181226225283 := by
  unfold tailWord_2919075
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467411899697288164446679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70978274599798192109631119 106467411899697288164446679)
  ·
    refine ⟨159701117849545932246670019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106467411899697288164446679 159701117849545932246670019)
    ·
      refine ⟨239551676774318898370005029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159701117849545932246670019 239551676774318898370005029)
      ·
        refine ⟨44915939395184793444375943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239551676774318898370005029 44915939395184793444375943)
        ·
          refine ⟨67373909092777190166563915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44915939395184793444375943 67373909092777190166563915)
          ·
            refine ⟨101060863639165785249845873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67373909092777190166563915 101060863639165785249845873)
            ·
              refine ⟨75795647729374338937384405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101060863639165785249845873 75795647729374338937384405)
              ·
                refine ⟨1776460493657211068844947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75795647729374338937384405 1776460493657211068844947)
                ·
                  refine ⟨2664690740485816603267421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776460493657211068844947 2664690740485816603267421)
                  ·
                    refine ⟨999259027682181226225283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664690740485816603267421 999259027682181226225283)
                    ·
                      rfl

theorem cell22_2919075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 3].length) (baseStart_2919075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919075 prefixEnd_2919075 := by exact prefixLift 2919075
  have htrace : WordTrace (prefixWord ++ tailWord_2919075) baseStart_2919075 baseEnd_2919075 := by
    simpa [prefixWord, tailWord_2919075, baseEnd_2919075] using wordTrace_append hprefix tailTrace_2919075
  have hstable : (prefixWord ++ tailWord_2919075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919075).length < 2 ^ (prefixWord ++ tailWord_2919075).sum := by decide
  have hdescent : baseEnd_2919075 < baseStart_2919075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919165 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2919165 : Nat := 118140960795 + 2919165 * 2 ^ 59
def prefixEnd_2919165 : Nat := 4983230072969 + 3 ^ 40 * 2919165 * 2
def baseEnd_2919165 : Nat := 999289836521450991475007

theorem tailTrace_2919165 : CollatzResearch.WordTrace tailWord_2919165 prefixEnd_2919165 999289836521450991475007 := by
  unfold tailWord_2919165
  simp only [CollatzResearch.WordTrace]
  refine ⟨106470694469371233535222949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70980462979580822356815299 106470694469371233535222949)
  ·
    refine ⟨19963255213007106287854303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106470694469371233535222949 19963255213007106287854303)
    ·
      refine ⟨29944882819510659431781455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963255213007106287854303 29944882819510659431781455)
      ·
        refine ⟨44917324229265989147672183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29944882819510659431781455 44917324229265989147672183)
        ·
          refine ⟨67375986343898983721508275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44917324229265989147672183 67375986343898983721508275)
          ·
            refine ⟨101063979515848475582262413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67375986343898983721508275 101063979515848475582262413)
            ·
              refine ⟨37898992318443178343348405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101063979515848475582262413 37898992318443178343348405)
              ·
                refine ⟨3553030529854047969688913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37898992318443178343348405 3553030529854047969688913)
                ·
                  refine ⟨2664772897390535977266685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553030529854047969688913 2664772897390535977266685)
                  ·
                    refine ⟨999289836521450991475007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664772897390535977266685 999289836521450991475007)
                    ·
                      rfl

theorem cell22_2919165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2919165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919165 prefixEnd_2919165 := by exact prefixLift 2919165
  have htrace : WordTrace (prefixWord ++ tailWord_2919165) baseStart_2919165 baseEnd_2919165 := by
    simpa [prefixWord, tailWord_2919165, baseEnd_2919165] using wordTrace_append hprefix tailTrace_2919165
  have hstable : (prefixWord ++ tailWord_2919165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919165).length < 2 ^ (prefixWord ++ tailWord_2919165).sum := by decide
  have hdescent : baseEnd_2919165 < baseStart_2919165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919186 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2919186 : Nat := 118140960795 + 2919186 * 2 ^ 59
def prefixEnd_2919186 : Nat := 4983230072969 + 3 ^ 40 * 2919186 * 2
def baseEnd_2919186 : Nat := 999297025250613936699943

theorem tailTrace_2919186 : CollatzResearch.WordTrace tailWord_2919186 prefixEnd_2919186 999297025250613936699943 := by
  unfold tailWord_2919186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26617865100573788530434353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70980973601530102747824941 26617865100573788530434353)
  ·
    refine ⟨19963398825430341397825765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26617865100573788530434353 19963398825430341397825765)
    ·
      refine ⟨3743137279768189012092331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19963398825430341397825765 3743137279768189012092331)
      ·
        refine ⟨5614705919652283518138497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743137279768189012092331 5614705919652283518138497)
        ·
          refine ⟨4211029439739212638603873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5614705919652283518138497 4211029439739212638603873)
          ·
            refine ⟨3158272079804409478952905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211029439739212638603873 3158272079804409478952905)
            ·
              refine ⟨2368704059853307109214679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158272079804409478952905 2368704059853307109214679)
              ·
                refine ⟨3553056089779960663822019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368704059853307109214679 3553056089779960663822019)
                ·
                  refine ⟨5329584134669940995733029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553056089779960663822019 5329584134669940995733029)
                  ·
                    refine ⟨999297025250613936699943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329584134669940995733029 999297025250613936699943)
                    ·
                      rfl

theorem cell22_2919186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2919186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919186 prefixEnd_2919186 := by exact prefixLift 2919186
  have htrace : WordTrace (prefixWord ++ tailWord_2919186) baseStart_2919186 baseEnd_2919186 := by
    simpa [prefixWord, tailWord_2919186, baseEnd_2919186] using wordTrace_append hprefix tailTrace_2919186
  have hstable : (prefixWord ++ tailWord_2919186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919186).length < 2 ^ (prefixWord ++ tailWord_2919186).sum := by decide
  have hdescent : baseEnd_2919186 < baseStart_2919186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919229 : List Nat := [1, 4, 1, 4, 3, 1, 2, 6]
def baseStart_2919229 : Nat := 118140960795 + 2919229 * 2 ^ 59
def prefixEnd_2919229 : Nat := 4983230072969 + 3 ^ 40 * 2919229 * 2
def baseEnd_2919229 : Nat := 111034638336597350874979

theorem tailTrace_2919229 : CollatzResearch.WordTrace tailWord_2919229 prefixEnd_2919229 111034638336597350874979 := by
  unfold tailWord_2919229
  simp only [CollatzResearch.WordTrace]
  refine ⟨106473028741139372465552741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70982019160759581643701827 106473028741139372465552741)
  ·
    refine ⟨19963692888963632337291139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106473028741139372465552741 19963692888963632337291139)
    ·
      refine ⟨29945539333445448505936709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963692888963632337291139 29945539333445448505936709)
      ·
        refine ⟨5614788625021021594863133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29945539333445448505936709 5614788625021021594863133)
        ·
          refine ⟨2105545734382883098073675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5614788625021021594863133 2105545734382883098073675)
          ·
            refine ⟨3158318601574324647110513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105545734382883098073675 3158318601574324647110513)
            ·
              refine ⟨2368738951180743485332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158318601574324647110513 2368738951180743485332885)
              ·
                refine ⟨111034638336597350874979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2368738951180743485332885 111034638336597350874979)
                ·
                  rfl

theorem cell22_2919229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 6].length) (baseStart_2919229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919229 prefixEnd_2919229 := by exact prefixLift 2919229
  have htrace : WordTrace (prefixWord ++ tailWord_2919229) baseStart_2919229 baseEnd_2919229 := by
    simpa [prefixWord, tailWord_2919229, baseEnd_2919229] using wordTrace_append hprefix tailTrace_2919229
  have hstable : (prefixWord ++ tailWord_2919229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919229).length < 2 ^ (prefixWord ++ tailWord_2919229).sum := by decide
  have hdescent : baseEnd_2919229 < baseStart_2919229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919244 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_2919244 : Nat := 118140960795 + 2919244 * 2 ^ 59
def prefixEnd_2919244 : Nat := 4983230072969 + 3 ^ 40 * 2919244 * 2
def baseEnd_2919244 : Nat := 999316879835921118749765

theorem tailTrace_2919244 : CollatzResearch.WordTrace tailWord_2919244 prefixEnd_2919244 999316879835921118749765 := by
  unfold tailWord_2919244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53236787918042515013674393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70982383890723353351565857 53236787918042515013674393)
  ·
    refine ⟨39927590938531886260255795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53236787918042515013674393 39927590938531886260255795)
    ·
      refine ⟨59891386407797829390383693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39927590938531886260255795 59891386407797829390383693)
      ·
        refine ⟨22459269902924186021393885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59891386407797829390383693 22459269902924186021393885)
        ·
          refine ⟨8422226213596569758022707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22459269902924186021393885 8422226213596569758022707)
          ·
            refine ⟨12633339320394854637034061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8422226213596569758022707 12633339320394854637034061)
            ·
              refine ⟨4737502245148070488887773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12633339320394854637034061 4737502245148070488887773)
              ·
                refine ⟨1776563341930526433332915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4737502245148070488887773 1776563341930526433332915)
                ·
                  refine ⟨2664845012895789649999373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776563341930526433332915 2664845012895789649999373)
                  ·
                    refine ⟨999316879835921118749765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664845012895789649999373 999316879835921118749765)
                    ·
                      rfl

theorem cell22_2919244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_2919244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919244 prefixEnd_2919244 := by exact prefixLift 2919244
  have htrace : WordTrace (prefixWord ++ tailWord_2919244) baseStart_2919244 baseEnd_2919244 := by
    simpa [prefixWord, tailWord_2919244, baseEnd_2919244] using wordTrace_append hprefix tailTrace_2919244
  have hstable : (prefixWord ++ tailWord_2919244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919244).length < 2 ^ (prefixWord ++ tailWord_2919244).sum := by decide
  have hdescent : baseEnd_2919244 < baseStart_2919244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919304 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_2919304 : Nat := 118140960795 + 2919304 * 2 ^ 59
def prefixEnd_2919304 : Nat := 4983230072969 + 3 ^ 40 * 2919304 * 2
def baseEnd_2919304 : Nat := 999337419062100962249581

theorem tailTrace_2919304 : CollatzResearch.WordTrace tailWord_2919304 prefixEnd_2919304 999337419062100962249581 := by
  unfold tailWord_2919304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53237882107933830137266483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70983842810578440183021977 53237882107933830137266483)
  ·
    refine ⟨79856823161900745205899725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53237882107933830137266483 79856823161900745205899725)
    ·
      refine ⟨29946308685712779452212397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79856823161900745205899725 29946308685712779452212397)
      ·
        refine ⟨11229865757142292294579649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29946308685712779452212397 11229865757142292294579649)
        ·
          refine ⟨8422399317856719220934737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11229865757142292294579649 8422399317856719220934737)
          ·
            refine ⟨6316799488392539415701053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422399317856719220934737 6316799488392539415701053)
            ·
              refine ⟨2368799808147202280887895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6316799488392539415701053 2368799808147202280887895)
              ·
                refine ⟨3553199712220803421331843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368799808147202280887895 3553199712220803421331843)
                ·
                  refine ⟨5329799568331205131997765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553199712220803421331843 5329799568331205131997765)
                  ·
                    refine ⟨999337419062100962249581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329799568331205131997765 999337419062100962249581)
                    ·
                      rfl

theorem cell22_2919304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_2919304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919304 prefixEnd_2919304 := by exact prefixLift 2919304
  have htrace : WordTrace (prefixWord ++ tailWord_2919304) baseStart_2919304 baseEnd_2919304 := by
    simpa [prefixWord, tailWord_2919304, baseEnd_2919304] using wordTrace_append hprefix tailTrace_2919304
  have hstable : (prefixWord ++ tailWord_2919304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919304).length < 2 ^ (prefixWord ++ tailWord_2919304).sum := by decide
  have hdescent : baseEnd_2919304 < baseStart_2919304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919317 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2919317 : Nat := 118140960795 + 2919317 * 2 ^ 59
def prefixEnd_2919317 : Nat := 4983230072969 + 3 ^ 40 * 2919317 * 2
def baseEnd_2919317 : Nat := 999341869227773261674541

theorem tailTrace_2919317 : CollatzResearch.WordTrace tailWord_2919317 prefixEnd_2919317 999341869227773261674541 := by
  unfold tailWord_2919317
  simp only [CollatzResearch.WordTrace]
  refine ⟨106476238364820563494756205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70984158909880375663170803 106476238364820563494756205)
  ·
    refine ⟨39928589386807711310533577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106476238364820563494756205 39928589386807711310533577)
    ·
      refine ⟨29946442040105783482900183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39928589386807711310533577 29946442040105783482900183)
      ·
        refine ⟨44919663060158675224350275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29946442040105783482900183 44919663060158675224350275)
        ·
          refine ⟨67379494590238012836525413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44919663060158675224350275 67379494590238012836525413)
          ·
            refine ⟨12633655235669627406848515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67379494590238012836525413 12633655235669627406848515)
            ·
              refine ⟨18950482853504441110272773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633655235669627406848515 18950482853504441110272773)
              ·
                refine ⟨3553215535032082708176145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18950482853504441110272773 3553215535032082708176145)
                ·
                  refine ⟨2664911651274062031132109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553215535032082708176145 2664911651274062031132109)
                  ·
                    refine ⟨999341869227773261674541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664911651274062031132109 999341869227773261674541)
                    ·
                      rfl

theorem cell22_2919317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2919317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919317 prefixEnd_2919317 := by exact prefixLift 2919317
  have htrace : WordTrace (prefixWord ++ tailWord_2919317) baseStart_2919317 baseEnd_2919317 := by
    simpa [prefixWord, tailWord_2919317, baseEnd_2919317] using wordTrace_append hprefix tailTrace_2919317
  have hstable : (prefixWord ++ tailWord_2919317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919317).length < 2 ^ (prefixWord ++ tailWord_2919317).sum := by decide
  have hdescent : baseEnd_2919317 < baseStart_2919317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919375 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 7]
def baseStart_2919375 : Nat := 118140960795 + 2919375 * 2 ^ 59
def prefixEnd_2919375 : Nat := 4983230072969 + 3 ^ 40 * 2919375 * 2
def baseEnd_2919375 : Nat := 333120574604360147908121

theorem tailTrace_2919375 : CollatzResearch.WordTrace tailWord_2919375 prefixEnd_2919375 333120574604360147908121 := by
  unfold tailWord_2919375
  simp only [CollatzResearch.WordTrace]
  refine ⟨106478353798610439400367579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70985569199073626266911719 106478353798610439400367579)
  ·
    refine ⟨159717530697915659100551369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106478353798610439400367579 159717530697915659100551369)
    ·
      refine ⟨119788148023436744325413527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159717530697915659100551369 119788148023436744325413527)
      ·
        refine ⟨179682222035155116488120291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119788148023436744325413527 179682222035155116488120291)
        ·
          refine ⟨269523333052732674732180437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179682222035155116488120291 269523333052732674732180437)
          ·
            refine ⟨6316953118423422064035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 269523333052732674732180437 6316953118423422064035479)
            ·
              refine ⟨9475429677635133096053219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316953118423422064035479 9475429677635133096053219)
              ·
                refine ⟨14213144516452699644079829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475429677635133096053219 14213144516452699644079829)
                ·
                  refine ⟨333120574604360147908121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14213144516452699644079829 333120574604360147908121)
                  ·
                    rfl

theorem cell22_2919375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_2919375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919375 prefixEnd_2919375 := by exact prefixLift 2919375
  have htrace : WordTrace (prefixWord ++ tailWord_2919375) baseStart_2919375 baseEnd_2919375 := by
    simpa [prefixWord, tailWord_2919375, baseEnd_2919375] using wordTrace_append hprefix tailTrace_2919375
  have hstable : (prefixWord ++ tailWord_2919375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919375).length < 2 ^ (prefixWord ++ tailWord_2919375).sum := by decide
  have hdescent : baseEnd_2919375 < baseStart_2919375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919467 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_2919467 : Nat := 118140960795 + 2919467 * 2 ^ 59
def prefixEnd_2919467 : Nat := 4983230072969 + 3 ^ 40 * 2919467 * 2
def baseEnd_2919467 : Nat := 999393217293222870424081

theorem tailTrace_2919467 : CollatzResearch.WordTrace tailWord_2919467 prefixEnd_2919467 999393217293222870424081 := by
  unfold tailWord_2919467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106481709314277139112716655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70987806209518092741811103 106481709314277139112716655)
  ·
    refine ⟨159722563971415708669074983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106481709314277139112716655 159722563971415708669074983)
    ·
      refine ⟨239583845957123563003612475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159722563971415708669074983 239583845957123563003612475)
      ·
        refine ⟨359375768935685344505418713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239583845957123563003612475 359375768935685344505418713)
        ·
          refine ⟨269531826701764008379064035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359375768935685344505418713 269531826701764008379064035)
          ·
            refine ⟨404297740052646012568596053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269531826701764008379064035 404297740052646012568596053)
            ·
              refine ⟨4737864141241945459788235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 404297740052646012568596053 4737864141241945459788235)
              ·
                refine ⟨7106796211862918189682353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737864141241945459788235 7106796211862918189682353)
                ·
                  refine ⟨5330097158897188642261765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7106796211862918189682353 5330097158897188642261765)
                  ·
                    refine ⟨999393217293222870424081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330097158897188642261765 999393217293222870424081)
                    ·
                      rfl

theorem cell22_2919467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_2919467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919467 prefixEnd_2919467 := by exact prefixLift 2919467
  have htrace : WordTrace (prefixWord ++ tailWord_2919467) baseStart_2919467 baseEnd_2919467 := by
    simpa [prefixWord, tailWord_2919467, baseEnd_2919467] using wordTrace_append hprefix tailTrace_2919467
  have hstable : (prefixWord ++ tailWord_2919467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919467).length < 2 ^ (prefixWord ++ tailWord_2919467).sum := by decide
  have hdescent : baseEnd_2919467 < baseStart_2919467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919486 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2919486 : Nat := 118140960795 + 2919486 * 2 ^ 59
def prefixEnd_2919486 : Nat := 4983230072969 + 3 ^ 40 * 2919486 * 2
def baseEnd_2919486 : Nat := 999399721381513154199023

theorem tailTrace_2919486 : CollatzResearch.WordTrace tailWord_2919486 prefixEnd_2919486 999399721381513154199023 := by
  unfold tailWord_2919486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310300287651038169707289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70988268200805536905105541 13310300287651038169707289)
  ·
    refine ⟨9982725215738278627280467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13310300287651038169707289 9982725215738278627280467)
    ·
      refine ⟨14974087823607417940920701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9982725215738278627280467 14974087823607417940920701)
      ·
        refine ⟨5615282933852781727845263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14974087823607417940920701 5615282933852781727845263)
        ·
          refine ⟨8422924400779172591767895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615282933852781727845263 8422924400779172591767895)
          ·
            refine ⟨12634386601168758887651843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8422924400779172591767895 12634386601168758887651843)
            ·
              refine ⟨18951579901753138331477765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12634386601168758887651843 18951579901753138331477765)
              ·
                refine ⟨3553421231578713437152081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18951579901753138331477765 3553421231578713437152081)
                ·
                  refine ⟨2665065923684035077864061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553421231578713437152081 2665065923684035077864061)
                  ·
                    refine ⟨999399721381513154199023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665065923684035077864061 999399721381513154199023)
                    ·
                      rfl

theorem cell22_2919486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2919486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919486 prefixEnd_2919486 := by exact prefixLift 2919486
  have htrace : WordTrace (prefixWord ++ tailWord_2919486) baseStart_2919486 baseEnd_2919486 := by
    simpa [prefixWord, tailWord_2919486, baseEnd_2919486] using wordTrace_append hprefix tailTrace_2919486
  have hstable : (prefixWord ++ tailWord_2919486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919486).length < 2 ^ (prefixWord ++ tailWord_2919486).sum := by decide
  have hdescent : baseEnd_2919486 < baseStart_2919486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919518 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2919518 : Nat := 118140960795 + 2919518 * 2 ^ 59
def prefixEnd_2919518 : Nat := 4983230072969 + 3 ^ 40 * 2919518 * 2
def baseEnd_2919518 : Nat := 999410675635475737398925

theorem tailTrace_2919518 : CollatzResearch.WordTrace tailWord_2919518 prefixEnd_2919518 999410675635475737398925 := by
  unfold tailWord_2919518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310446179636546852852901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70989046291394916548548805 13310446179636546852852901)
  ·
    refine ⟨2495708658681852534909919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13310446179636546852852901 2495708658681852534909919)
    ·
      refine ⟨3743562988022778802364879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495708658681852534909919 3743562988022778802364879)
      ·
        refine ⟨5615344482034168203547319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743562988022778802364879 5615344482034168203547319)
        ·
          refine ⟨8423016723051252305320979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615344482034168203547319 8423016723051252305320979)
          ·
            refine ⟨12634525084576878457981469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423016723051252305320979 12634525084576878457981469)
            ·
              refine ⟨4737946906716329421743051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12634525084576878457981469 4737946906716329421743051)
              ·
                refine ⟨7106920360074494132614577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737946906716329421743051 7106920360074494132614577)
                ·
                  refine ⟨5330190270055870599460933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7106920360074494132614577 5330190270055870599460933)
                  ·
                    refine ⟨999410675635475737398925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330190270055870599460933 999410675635475737398925)
                    ·
                      rfl

theorem cell22_2919518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2919518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919518 prefixEnd_2919518 := by exact prefixLift 2919518
  have htrace : WordTrace (prefixWord ++ tailWord_2919518) baseStart_2919518 baseEnd_2919518 := by
    simpa [prefixWord, tailWord_2919518, baseEnd_2919518] using wordTrace_append hprefix tailTrace_2919518
  have hstable : (prefixWord ++ tailWord_2919518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919518).length < 2 ^ (prefixWord ++ tailWord_2919518).sum := by decide
  have hdescent : baseEnd_2919518 < baseStart_2919518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919587 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_2919587 : Nat := 118140960795 + 2919587 * 2 ^ 59
def prefixEnd_2919587 : Nat := 4983230072969 + 3 ^ 40 * 2919587 * 2
def baseEnd_2919587 : Nat := 999434295745582557423713

theorem tailTrace_2919587 : CollatzResearch.WordTrace tailWord_2919587 prefixEnd_2919587 999434295745582557423713 := by
  unfold tailWord_2919587
  simp only [CollatzResearch.WordTrace]
  refine ⟨106486086073842399607085015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70990724049228266404723343 106486086073842399607085015)
  ·
    refine ⟨159729129110763599410627523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106486086073842399607085015 159729129110763599410627523)
    ·
      refine ⟨239593693666145399115941285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159729129110763599410627523 239593693666145399115941285)
      ·
        refine ⟨44923817562402262334238991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239593693666145399115941285 44923817562402262334238991)
        ·
          refine ⟨67385726343603393501358487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44923817562402262334238991 67385726343603393501358487)
          ·
            refine ⟨101078589515405090252037731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67385726343603393501358487 101078589515405090252037731)
            ·
              refine ⟨151617884273107635378056597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101078589515405090252037731 151617884273107635378056597)
              ·
                refine ⟨7107088325301920408346403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151617884273107635378056597 7107088325301920408346403)
                ·
                  refine ⟨10660632487952880612519605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107088325301920408346403 10660632487952880612519605)
                  ·
                    refine ⟨999434295745582557423713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10660632487952880612519605 999434295745582557423713)
                    ·
                      rfl

theorem cell22_2919587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_2919587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919587 prefixEnd_2919587 := by exact prefixLift 2919587
  have htrace : WordTrace (prefixWord ++ tailWord_2919587) baseStart_2919587 baseEnd_2919587 := by
    simpa [prefixWord, tailWord_2919587, baseEnd_2919587] using wordTrace_append hprefix tailTrace_2919587
  have hstable : (prefixWord ++ tailWord_2919587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919587).length < 2 ^ (prefixWord ++ tailWord_2919587).sum := by decide
  have hdescent : baseEnd_2919587 < baseStart_2919587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919591 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2919591 : Nat := 118140960795 + 2919591 * 2 ^ 59
def prefixEnd_2919591 : Nat := 4983230072969 + 3 ^ 40 * 2919591 * 2
def baseEnd_2919591 : Nat := 999435665027327880323701

theorem tailTrace_2919591 : CollatzResearch.WordTrace tailWord_2919591 prefixEnd_2919591 999435665027327880323701 := by
  unfold tailWord_2919591
  simp only [CollatzResearch.WordTrace]
  refine ⟨106486231965827908290230627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70990821310551938860153751 106486231965827908290230627)
  ·
    refine ⟨159729347948741862435345941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106486231965827908290230627 159729347948741862435345941)
    ·
      refine ⟨7487313185097274801656841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159729347948741862435345941 7487313185097274801656841)
      ·
        refine ⟨5615484888822956101242631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487313185097274801656841 5615484888822956101242631)
        ·
          refine ⟨8423227333234434151863947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615484888822956101242631 8423227333234434151863947)
          ·
            refine ⟨12634840999851651227795921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423227333234434151863947 12634840999851651227795921)
            ·
              refine ⟨9476130749888738420846941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12634840999851651227795921 9476130749888738420846941)
              ·
                refine ⟨3553549031208276907817603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476130749888738420846941 3553549031208276907817603)
                ·
                  refine ⟨5330323546812415361726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553549031208276907817603 5330323546812415361726405)
                  ·
                    refine ⟨999435665027327880323701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330323546812415361726405 999435665027327880323701)
                    ·
                      rfl

theorem cell22_2919591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2919591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919591 prefixEnd_2919591 := by exact prefixLift 2919591
  have htrace : WordTrace (prefixWord ++ tailWord_2919591) baseStart_2919591 baseEnd_2919591 := by
    simpa [prefixWord, tailWord_2919591, baseEnd_2919591] using wordTrace_append hprefix tailTrace_2919591
  have hstable : (prefixWord ++ tailWord_2919591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919591).length < 2 ^ (prefixWord ++ tailWord_2919591).sum := by decide
  have hdescent : baseEnd_2919591 < baseStart_2919591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919638 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2919638 : Nat := 118140960795 + 2919638 * 2 ^ 59
def prefixEnd_2919638 : Nat := 4983230072969 + 3 ^ 40 * 2919638 * 2
def baseEnd_2919638 : Nat := 999451754087835424398557

theorem tailTrace_2919638 : CollatzResearch.WordTrace tailWord_2919638 prefixEnd_2919638 999451754087835424398557 := by
  unfold tailWord_2919638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655496637291102207324473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70991964131105090211461045 6655496637291102207324473)
  ·
    refine ⟨4991622477968326655493355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6655496637291102207324473 4991622477968326655493355)
    ·
      refine ⟨7487433716952489983240033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991622477968326655493355 7487433716952489983240033)
      ·
        refine ⟨5615575287714367487430025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487433716952489983240033 5615575287714367487430025)
        ·
          refine ⟨4211681465785775615572519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615575287714367487430025 4211681465785775615572519)
          ·
            refine ⟨6317522198678663423358779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211681465785775615572519 6317522198678663423358779)
            ·
              refine ⟨9476283298017995135038169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317522198678663423358779 9476283298017995135038169)
              ·
                refine ⟨7107212473513496351278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476283298017995135038169 7107212473513496351278627)
                ·
                  refine ⟨10660818710270244526917941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107212473513496351278627 10660818710270244526917941)
                  ·
                    refine ⟨999451754087835424398557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10660818710270244526917941 999451754087835424398557)
                    ·
                      rfl

theorem cell22_2919638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2919638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919638 prefixEnd_2919638 := by exact prefixLift 2919638
  have htrace : WordTrace (prefixWord ++ tailWord_2919638) baseStart_2919638 baseEnd_2919638 := by
    simpa [prefixWord, tailWord_2919638, baseEnd_2919638] using wordTrace_append hprefix tailTrace_2919638
  have hstable : (prefixWord ++ tailWord_2919638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919638).length < 2 ^ (prefixWord ++ tailWord_2919638).sum := by decide
  have hdescent : baseEnd_2919638 < baseStart_2919638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919679 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 5]
def baseStart_2919679 : Nat := 118140960795 + 2919679 * 2 ^ 59
def prefixEnd_2919679 : Nat := 4983230072969 + 3 ^ 40 * 2919679 * 2
def baseEnd_2919679 : Nat := 333155263075241661374477

theorem tailTrace_2919679 : CollatzResearch.WordTrace tailWord_2919679 prefixEnd_2919679 333155263075241661374477 := by
  unfold tailWord_2919679
  simp only [CollatzResearch.WordTrace]
  refine ⟨106489441589509099319434091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70992961059672732879622727 106489441589509099319434091)
  ·
    refine ⟨159734162384263648979151137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106489441589509099319434091 159734162384263648979151137)
    ·
      refine ⟨119800621788197736734363353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159734162384263648979151137 119800621788197736734363353)
      ·
        refine ⟨89850466341148302550772515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119800621788197736734363353 89850466341148302550772515)
        ·
          refine ⟨134775699511722453826158773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89850466341148302550772515 134775699511722453826158773)
          ·
            refine ⟨12635221829223980046202385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134775699511722453826158773 12635221829223980046202385)
            ·
              refine ⟨9476416371917985034651789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12635221829223980046202385 9476416371917985034651789)
              ·
                refine ⟨3553656139469244387994421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476416371917985034651789 3553656139469244387994421)
                ·
                  refine ⟨333155263075241661374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3553656139469244387994421 333155263075241661374477)
                  ·
                    rfl

theorem cell22_2919679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].length) (baseStart_2919679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919679 prefixEnd_2919679 := by exact prefixLift 2919679
  have htrace : WordTrace (prefixWord ++ tailWord_2919679) baseStart_2919679 baseEnd_2919679 := by
    simpa [prefixWord, tailWord_2919679, baseEnd_2919679] using wordTrace_append hprefix tailTrace_2919679
  have hstable : (prefixWord ++ tailWord_2919679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919679).length < 2 ^ (prefixWord ++ tailWord_2919679).sum := by decide
  have hdescent : baseEnd_2919679 < baseStart_2919679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919707 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 10]
def baseStart_2919707 : Nat := 118140960795 + 2919707 * 2 ^ 59
def prefixEnd_2919707 : Nat := 4983230072969 + 3 ^ 40 * 2919707 * 2
def baseEnd_2919707 : Nat := 333158458065980748141115

theorem tailTrace_2919707 : CollatzResearch.WordTrace tailWord_2919707 prefixEnd_2919707 333158458065980748141115 := by
  unfold tailWord_2919707
  simp only [CollatzResearch.WordTrace]
  refine ⟨106490462833407660101453375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70993641888938440067635583 106490462833407660101453375)
  ·
    refine ⟨159735694250111490152180063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106490462833407660101453375 159735694250111490152180063)
    ·
      refine ⟨239603541375167235228270095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159735694250111490152180063 239603541375167235228270095)
      ·
        refine ⟨359405312062750852842405143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239603541375167235228270095 359405312062750852842405143)
        ·
          refine ⟨539107968094126279263607715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359405312062750852842405143 539107968094126279263607715)
          ·
            refine ⟨808661952141189418895411573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539107968094126279263607715 808661952141189418895411573)
            ·
              refine ⟨75812058013236508021444835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 808661952141189418895411573 75812058013236508021444835)
              ·
                refine ⟨113718087019854762032167253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75812058013236508021444835 113718087019854762032167253)
                ·
                  refine ⟨333158458065980748141115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113718087019854762032167253 333158458065980748141115)
                  ·
                    rfl

theorem cell22_2919707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_2919707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919707 prefixEnd_2919707 := by exact prefixLift 2919707
  have htrace : WordTrace (prefixWord ++ tailWord_2919707) baseStart_2919707 baseEnd_2919707 := by
    simpa [prefixWord, tailWord_2919707, baseEnd_2919707] using wordTrace_append hprefix tailTrace_2919707
  have hstable : (prefixWord ++ tailWord_2919707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919707).length < 2 ^ (prefixWord ++ tailWord_2919707).sum := by decide
  have hdescent : baseEnd_2919707 < baseStart_2919707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919754 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2919754 : Nat := 118140960795 + 2919754 * 2 ^ 59
def prefixEnd_2919754 : Nat := 4983230072969 + 3 ^ 40 * 2919754 * 2
def baseEnd_2919754 : Nat := 999491463258449788498201

theorem tailTrace_2919754 : CollatzResearch.WordTrace tailWord_2919754 prefixEnd_2919754 999491463258449788498201 := by
  unfold tailWord_2919754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26623044266059346782103579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70994784709491591418942877 26623044266059346782103579)
  ·
    refine ⟨39934566399089020173155369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26623044266059346782103579 39934566399089020173155369)
    ·
      refine ⟨29950924799316765129866527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39934566399089020173155369 29950924799316765129866527)
      ·
        refine ⟨44926387198975147694799791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29950924799316765129866527 44926387198975147694799791)
        ·
          refine ⟨67389580798462721542199687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926387198975147694799791 67389580798462721542199687)
          ·
            refine ⟨101084371197694082313299531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67389580798462721542199687 101084371197694082313299531)
            ·
              refine ⟨151626556796541123469949297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101084371197694082313299531 151626556796541123469949297)
              ·
                refine ⟨113719917597405842602461973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151626556796541123469949297 113719917597405842602461973)
                ·
                  refine ⟨5330621137378398871990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113719917597405842602461973 5330621137378398871990405)
                  ·
                    refine ⟨999491463258449788498201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330621137378398871990405 999491463258449788498201)
                    ·
                      rfl

theorem cell22_2919754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2919754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919754 prefixEnd_2919754 := by exact prefixLift 2919754
  have htrace : WordTrace (prefixWord ++ tailWord_2919754) baseStart_2919754 baseEnd_2919754 := by
    simpa [prefixWord, tailWord_2919754, baseEnd_2919754] using wordTrace_append hprefix tailTrace_2919754
  have hstable : (prefixWord ++ tailWord_2919754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919754).length < 2 ^ (prefixWord ++ tailWord_2919754).sum := by decide
  have hdescent : baseEnd_2919754 < baseStart_2919754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919756 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_2919756 : Nat := 118140960795 + 2919756 * 2 ^ 59
def prefixEnd_2919756 : Nat := 4983230072969 + 3 ^ 40 * 2919756 * 2
def baseEnd_2919756 : Nat := 999492147899322449948195

theorem tailTrace_2919756 : CollatzResearch.WordTrace tailWord_2919756 prefixEnd_2919756 999492147899322449948195 := by
  unfold tailWord_2919756
  simp only [CollatzResearch.WordTrace]
  refine ⟨53246125005115070734993561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70994833340153427646658081 53246125005115070734993561)
  ·
    refine ⟨39934593753836303051245171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53246125005115070734993561 39934593753836303051245171)
    ·
      refine ⟨59901890630754454576867757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39934593753836303051245171 59901890630754454576867757)
      ·
        refine ⟨22463208986532920466325409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59901890630754454576867757 22463208986532920466325409)
        ·
          refine ⟨16847406739899690349744057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22463208986532920466325409 16847406739899690349744057)
          ·
            refine ⟨12635555054924767762308043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16847406739899690349744057 12635555054924767762308043)
            ·
              refine ⟨18953332582387151643462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12635555054924767762308043 18953332582387151643462065)
              ·
                refine ⟨14214999436790363732596549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18953332582387151643462065 14214999436790363732596549)
                ·
                  refine ⟨2665312394398193199861853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14214999436790363732596549 2665312394398193199861853)
                  ·
                    refine ⟨999492147899322449948195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665312394398193199861853 999492147899322449948195)
                    ·
                      rfl

theorem cell22_2919756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_2919756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919756 prefixEnd_2919756 := by exact prefixLift 2919756
  have htrace : WordTrace (prefixWord ++ tailWord_2919756) baseStart_2919756 baseEnd_2919756 := by
    simpa [prefixWord, tailWord_2919756, baseEnd_2919756] using wordTrace_append hprefix tailTrace_2919756
  have hstable : (prefixWord ++ tailWord_2919756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919756).length < 2 ^ (prefixWord ++ tailWord_2919756).sum := by decide
  have hdescent : baseEnd_2919756 < baseStart_2919756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919801 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_2919801 : Nat := 118140960795 + 2919801 * 2 ^ 59
def prefixEnd_2919801 : Nat := 4983230072969 + 3 ^ 40 * 2919801 * 2
def baseEnd_2919801 : Nat := 999507552318957332573057

theorem tailTrace_2919801 : CollatzResearch.WordTrace tailWord_2919801 prefixEnd_2919801 999507552318957332573057 := by
  unfold tailWord_2919801
  simp only [CollatzResearch.WordTrace]
  refine ⟨106493891295067114155375257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70995927530044742770250171 106493891295067114155375257)
  ·
    refine ⟨79870418471300335616531443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106493891295067114155375257 79870418471300335616531443)
    ·
      refine ⟨119805627706950503424797165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79870418471300335616531443 119805627706950503424797165)
      ·
        refine ⟨44927110390106438784298937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119805627706950503424797165 44927110390106438784298937)
        ·
          refine ⟨33695332792579829088224203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44927110390106438784298937 33695332792579829088224203)
          ·
            refine ⟨50542999188869743632336305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33695332792579829088224203 50542999188869743632336305)
            ·
              refine ⟨37907249391652307724252229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50542999188869743632336305 37907249391652307724252229)
              ·
                refine ⟨7107609260934807698297293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37907249391652307724252229 7107609260934807698297293)
                ·
                  refine ⟨2665353472850552886861485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7107609260934807698297293 2665353472850552886861485)
                  ·
                    refine ⟨999507552318957332573057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665353472850552886861485 999507552318957332573057)
                    ·
                      rfl

theorem cell22_2919801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_2919801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919801 prefixEnd_2919801 := by exact prefixLift 2919801
  have htrace : WordTrace (prefixWord ++ tailWord_2919801) baseStart_2919801 baseEnd_2919801 := by
    simpa [prefixWord, tailWord_2919801, baseEnd_2919801] using wordTrace_append hprefix tailTrace_2919801
  have hstable : (prefixWord ++ tailWord_2919801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919801).length < 2 ^ (prefixWord ++ tailWord_2919801).sum := by decide
  have hdescent : baseEnd_2919801 < baseStart_2919801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919893 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 4]
def baseStart_2919893 : Nat := 118140960795 + 2919893 * 2 ^ 59
def prefixEnd_2919893 : Nat := 4983230072969 + 3 ^ 40 * 2919893 * 2
def baseEnd_2919893 : Nat := 333179681933033253090925

theorem tailTrace_2919893 : CollatzResearch.WordTrace tailWord_2919893 prefixEnd_2919893 333179681933033253090925 := by
  unfold tailWord_2919893
  simp only [CollatzResearch.WordTrace]
  refine ⟨106497246810733813867724333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70998164540489209245149555 106497246810733813867724333)
  ·
    refine ⟨39936467554025180200396625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106497246810733813867724333 39936467554025180200396625)
    ·
      refine ⟨29952350665518885150297469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39936467554025180200396625 29952350665518885150297469)
      ·
        refine ⟨11232131499569581931361551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29952350665518885150297469 11232131499569581931361551)
        ·
          refine ⟨16848197249354372897042327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11232131499569581931361551 16848197249354372897042327)
          ·
            refine ⟨25272295874031559345563491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16848197249354372897042327 25272295874031559345563491)
            ·
              refine ⟨37908443811047339018345237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25272295874031559345563491 37908443811047339018345237)
              ·
                refine ⟨1776958303642844016484933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37908443811047339018345237 1776958303642844016484933)
                ·
                  refine ⟨333179681933033253090925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776958303642844016484933 333179681933033253090925)
                  ·
                    rfl

theorem cell22_2919893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_2919893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919893 prefixEnd_2919893 := by exact prefixLift 2919893
  have htrace : WordTrace (prefixWord ++ tailWord_2919893) baseStart_2919893 baseEnd_2919893 := by
    simpa [prefixWord, tailWord_2919893, baseEnd_2919893] using wordTrace_append hprefix tailTrace_2919893
  have hstable : (prefixWord ++ tailWord_2919893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919893).length < 2 ^ (prefixWord ++ tailWord_2919893).sum := by decide
  have hdescent : baseEnd_2919893 < baseStart_2919893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919908 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2919908 : Nat := 118140960795 + 2919908 * 2 ^ 59
def prefixEnd_2919908 : Nat := 4983230072969 + 3 ^ 40 * 2919908 * 2
def baseEnd_2919908 : Nat := 999544180605644720147729

theorem tailTrace_2919908 : CollatzResearch.WordTrace tailWord_2919908 prefixEnd_2919908 999544180605644720147729 := by
  unfold tailWord_2919908
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248896952839735714760189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70998529270452980953013585 53248896952839735714760189)
  ·
    refine ⟨19968336357314900893035071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53248896952839735714760189 19968336357314900893035071)
    ·
      refine ⟨29952504535972351339552607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19968336357314900893035071 29952504535972351339552607)
      ·
        refine ⟨44928756803958527009328911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29952504535972351339552607 44928756803958527009328911)
        ·
          refine ⟨67393135205937790513993367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44928756803958527009328911 67393135205937790513993367)
          ·
            refine ⟨101089702808906685770990051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67393135205937790513993367 101089702808906685770990051)
            ·
              refine ⟨151634554213360028656485077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101089702808906685770990051 151634554213360028656485077)
              ·
                refine ⟨3553934864375625671636369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151634554213360028656485077 3553934864375625671636369)
                ·
                  refine ⟨2665451148281719253727277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553934864375625671636369 2665451148281719253727277)
                  ·
                    refine ⟨999544180605644720147729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665451148281719253727277 999544180605644720147729)
                    ·
                      rfl

theorem cell22_2919908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2919908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919908 prefixEnd_2919908 := by exact prefixLift 2919908
  have htrace : WordTrace (prefixWord ++ tailWord_2919908) baseStart_2919908 baseEnd_2919908 := by
    simpa [prefixWord, tailWord_2919908, baseEnd_2919908] using wordTrace_append hprefix tailTrace_2919908
  have hstable : (prefixWord ++ tailWord_2919908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919908).length < 2 ^ (prefixWord ++ tailWord_2919908).sum := by decide
  have hdescent : baseEnd_2919908 < baseStart_2919908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919921 : List Nat := [1, 2, 2, 2, 3, 3, 1, 8]
def baseStart_2919921 : Nat := 118140960795 + 2919921 * 2 ^ 59
def prefixEnd_2919921 : Nat := 4983230072969 + 3 ^ 40 * 2919921 * 2
def baseEnd_2919921 : Nat := 111060958974590779952521

theorem tailTrace_2919921 : CollatzResearch.WordTrace tailWord_2919921 prefixEnd_2919921 111060958974590779952521 := by
  unfold tailWord_2919921
  simp only [CollatzResearch.WordTrace]
  refine ⟨106498268054632374649743617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70998845369754916433162411 106498268054632374649743617)
  ·
    refine ⟨79873701040974280987307713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106498268054632374649743617 79873701040974280987307713)
    ·
      refine ⟨59905275780730710740480785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79873701040974280987307713 59905275780730710740480785)
      ·
        refine ⟨44928956835548033055360589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59905275780730710740480785 44928956835548033055360589)
        ·
          refine ⟨16848358813330512395760221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44928956835548033055360589 16848358813330512395760221)
          ·
            refine ⟨6318134554998942148410083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16848358813330512395760221 6318134554998942148410083)
            ·
              refine ⟨9477201832498413222615125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318134554998942148410083 9477201832498413222615125)
              ·
                refine ⟨111060958974590779952521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9477201832498413222615125 111060958974590779952521)
                ·
                  rfl

theorem cell22_2919921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 8].length) (baseStart_2919921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919921 prefixEnd_2919921 := by exact prefixLift 2919921
  have htrace : WordTrace (prefixWord ++ tailWord_2919921) baseStart_2919921 baseEnd_2919921 := by
    simpa [prefixWord, tailWord_2919921, baseEnd_2919921] using wordTrace_append hprefix tailTrace_2919921
  have hstable : (prefixWord ++ tailWord_2919921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919921).length < 2 ^ (prefixWord ++ tailWord_2919921).sum := by decide
  have hdescent : baseEnd_2919921 < baseStart_2919921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919925 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2919925 : Nat := 118140960795 + 2919925 * 2 ^ 59
def prefixEnd_2919925 : Nat := 4983230072969 + 3 ^ 40 * 2919925 * 2
def baseEnd_2919925 : Nat := 999550000053062342472677

theorem tailTrace_2919925 : CollatzResearch.WordTrace tailWord_2919925 prefixEnd_2919925 999550000053062342472677 := by
  unfold tailWord_2919925
  simp only [CollatzResearch.WordTrace]
  refine ⟨106498413946617883332889229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70998942631078588888592819 106498413946617883332889229)
  ·
    refine ⟨39936905229981706249833461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106498413946617883332889229 39936905229981706249833461)
    ·
      refine ⟨3744084865310784960921887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39936905229981706249833461 3744084865310784960921887)
      ·
        refine ⟨5616127297966177441382831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744084865310784960921887 5616127297966177441382831)
        ·
          refine ⟨8424190946949266162074247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616127297966177441382831 8424190946949266162074247)
          ·
            refine ⟨12636286420423899243111371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424190946949266162074247 12636286420423899243111371)
            ·
              refine ⟨18954429630635848864667057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636286420423899243111371 18954429630635848864667057)
              ·
                refine ⟨14215822222976886648500293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18954429630635848864667057 14215822222976886648500293)
                ·
                  refine ⟨2665466666808166246593805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14215822222976886648500293 2665466666808166246593805)
                  ·
                    refine ⟨999550000053062342472677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665466666808166246593805 999550000053062342472677)
                    ·
                      rfl

theorem cell22_2919925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2919925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919925 prefixEnd_2919925 := by exact prefixLift 2919925
  have htrace : WordTrace (prefixWord ++ tailWord_2919925) baseStart_2919925 baseEnd_2919925 := by
    simpa [prefixWord, tailWord_2919925, baseEnd_2919925] using wordTrace_append hprefix tailTrace_2919925
  have hstable : (prefixWord ++ tailWord_2919925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919925).length < 2 ^ (prefixWord ++ tailWord_2919925).sum := by decide
  have hdescent : baseEnd_2919925 < baseStart_2919925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919938 : List Nat := [3, 4, 1, 2, 1, 1, 10]
def baseStart_2919938 : Nat := 118140960795 + 2919938 * 2 ^ 59
def prefixEnd_2919938 : Nat := 4983230072969 + 3 ^ 40 * 2919938 * 2
def baseEnd_2919938 : Nat := 37020535193286468218431

theorem tailTrace_2919938 : CollatzResearch.WordTrace tailWord_2919938 prefixEnd_2919938 37020535193286468218431 := by
  unfold tailWord_2919938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624722023892696638278117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70999258730380524368741645 26624722023892696638278117)
  ·
    refine ⟨4992135379479880619677147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26624722023892696638278117 4992135379479880619677147)
    ·
      refine ⟨7488203069219820929515721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992135379479880619677147 7488203069219820929515721)
      ·
        refine ⟨5616152301914865697136791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7488203069219820929515721 5616152301914865697136791)
        ·
          refine ⟨8424228452872298545705187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616152301914865697136791 8424228452872298545705187)
          ·
            refine ⟨12636342679308447818557781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424228452872298545705187 12636342679308447818557781)
            ·
              refine ⟨37020535193286468218431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12636342679308447818557781 37020535193286468218431)
              ·
                rfl

theorem cell22_2919938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 10].length) (baseStart_2919938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919938 prefixEnd_2919938 := by exact prefixLift 2919938
  have htrace : WordTrace (prefixWord ++ tailWord_2919938) baseStart_2919938 baseEnd_2919938 := by
    simpa [prefixWord, tailWord_2919938, baseEnd_2919938] using wordTrace_append hprefix tailTrace_2919938
  have hstable : (prefixWord ++ tailWord_2919938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919938).length < 2 ^ (prefixWord ++ tailWord_2919938).sum := by decide
  have hdescent : baseEnd_2919938 < baseStart_2919938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919940 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2919940 : Nat := 118140960795 + 2919940 * 2 ^ 59
def prefixEnd_2919940 : Nat := 4983230072969 + 3 ^ 40 * 2919940 * 2
def baseEnd_2919940 : Nat := 999555134859607303347631

theorem tailTrace_2919940 : CollatzResearch.WordTrace tailWord_2919940 prefixEnd_2919940 999555134859607303347631 := by
  unfold tailWord_2919940
  simp only [CollatzResearch.WordTrace]
  refine ⟨53249480520781770447342637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70999307361042360596456849 53249480520781770447342637)
  ·
    refine ⟨19968555195293163917753489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53249480520781770447342637 19968555195293163917753489)
    ·
      refine ⟨14976416396469872938315117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19968555195293163917753489 14976416396469872938315117)
      ·
        refine ⟨5616156148676202351868169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14976416396469872938315117 5616156148676202351868169)
        ·
          refine ⟨4212117111507151763901127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616156148676202351868169 4212117111507151763901127)
          ·
            refine ⟨6318175667260727645851691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212117111507151763901127 6318175667260727645851691)
            ·
              refine ⟨9477263500891091468777537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318175667260727645851691 9477263500891091468777537)
              ·
                refine ⟨7107947625668318601583153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9477263500891091468777537 7107947625668318601583153)
                ·
                  refine ⟨5330960719251238951187365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7107947625668318601583153 5330960719251238951187365)
                  ·
                    refine ⟨999555134859607303347631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330960719251238951187365 999555134859607303347631)
                    ·
                      rfl

theorem cell22_2919940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2919940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2919940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2919940 prefixEnd_2919940 := by exact prefixLift 2919940
  have htrace : WordTrace (prefixWord ++ tailWord_2919940) baseStart_2919940 baseEnd_2919940 := by
    simpa [prefixWord, tailWord_2919940, baseEnd_2919940] using wordTrace_append hprefix tailTrace_2919940
  have hstable : (prefixWord ++ tailWord_2919940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919940).length < 2 ^ (prefixWord ++ tailWord_2919940).sum := by decide
  have hdescent : baseEnd_2919940 < baseStart_2919940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920011 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 6]
def baseStart_2920011 : Nat := 118140960795 + 2920011 * 2 ^ 59
def prefixEnd_2920011 : Nat := 4983230072969 + 3 ^ 40 * 2920011 * 2
def baseEnd_2920011 : Nat := 333193146536862261607471

theorem tailTrace_2920011 : CollatzResearch.WordTrace tailWord_2920011 prefixEnd_2920011 333193146536862261607471 := by
  unfold tailWord_2920011
  simp only [CollatzResearch.WordTrace]
  refine ⟨106501550624306320020519887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71001033749537546680346591 106501550624306320020519887)
  ·
    refine ⟨159752325936459480030779831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106501550624306320020519887 159752325936459480030779831)
    ·
      refine ⟨239628488904689220046169747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159752325936459480030779831 239628488904689220046169747)
      ·
        refine ⟨359442733357033830069254621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239628488904689220046169747 359442733357033830069254621)
        ·
          refine ⟨134791025008887686275970483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359442733357033830069254621 134791025008887686275970483)
          ·
            refine ⟨202186537513331529413955725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134791025008887686275970483 202186537513331529413955725)
            ·
              refine ⟨75819951567499323530233397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202186537513331529413955725 75819951567499323530233397)
              ·
                refine ⟨7108120459453061580959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75819951567499323530233397 7108120459453061580959381)
                ·
                  refine ⟨333193146536862261607471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7108120459453061580959381 333193146536862261607471)
                  ·
                    rfl

theorem cell22_2920011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_2920011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920011 prefixEnd_2920011 := by exact prefixLift 2920011
  have htrace : WordTrace (prefixWord ++ tailWord_2920011) baseStart_2920011 baseEnd_2920011 := by
    simpa [prefixWord, tailWord_2920011, baseEnd_2920011] using wordTrace_append hprefix tailTrace_2920011
  have hstable : (prefixWord ++ tailWord_2920011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920011).length < 2 ^ (prefixWord ++ tailWord_2920011).sum := by decide
  have hdescent : baseEnd_2920011 < baseStart_2920011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920028 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_2920028 : Nat := 118140960795 + 2920028 * 2 ^ 59
def prefixEnd_2920028 : Nat := 4983230072969 + 3 ^ 40 * 2920028 * 2
def baseEnd_2920028 : Nat := 333195086352668135715787

theorem tailTrace_2920028 : CollatzResearch.WordTrace tailWord_2920028 prefixEnd_2920028 333195086352668135715787 := by
  unfold tailWord_2920028
  simp only [CollatzResearch.WordTrace]
  refine ⟨53251085332622365961944369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71001447110163154615925825 53251085332622365961944369)
  ·
    refine ⟨39938313999466774471458277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53251085332622365961944369 39938313999466774471458277)
    ·
      refine ⟨7488433874900020213398427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39938313999466774471458277 7488433874900020213398427)
      ·
        refine ⟨11232650812350030320097641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7488433874900020213398427 11232650812350030320097641)
        ·
          refine ⟨8424488109262522740073231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11232650812350030320097641 8424488109262522740073231)
          ·
            refine ⟨12636732163893784110109847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424488109262522740073231 12636732163893784110109847)
            ·
              refine ⟨18955098245840676165164771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636732163893784110109847 18955098245840676165164771)
              ·
                refine ⟨28432647368761014247747157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18955098245840676165164771 28432647368761014247747157)
                ·
                  refine ⟨333195086352668135715787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28432647368761014247747157 333195086352668135715787)
                  ·
                    rfl

theorem cell22_2920028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_2920028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920028 prefixEnd_2920028 := by exact prefixLift 2920028
  have htrace : WordTrace (prefixWord ++ tailWord_2920028) baseStart_2920028 baseEnd_2920028 := by
    simpa [prefixWord, tailWord_2920028, baseEnd_2920028] using wordTrace_append hprefix tailTrace_2920028
  have hstable : (prefixWord ++ tailWord_2920028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920028).length < 2 ^ (prefixWord ++ tailWord_2920028).sum := by decide
  have hdescent : baseEnd_2920028 < baseStart_2920028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920122 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_2920122 : Nat := 118140960795 + 2920122 * 2 ^ 59
def prefixEnd_2920122 : Nat := 4983230072969 + 3 ^ 40 * 2920122 * 2
def baseEnd_2920122 : Nat := 999617437179019495297073

theorem tailTrace_2920122 : CollatzResearch.WordTrace tailWord_2920122 prefixEnd_2920122 999617437179019495297073 := by
  unfold tailWord_2920122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626399781726046494452655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71003732751269457318540413 26626399781726046494452655)
  ·
    refine ⟨39939599672589069741678983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26626399781726046494452655 39939599672589069741678983)
    ·
      refine ⟨59909399508883604612518475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39939599672589069741678983 59909399508883604612518475)
      ·
        refine ⟨89864099263325406918777713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59909399508883604612518475 89864099263325406918777713)
        ·
          refine ⟨67398074447494055189083285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89864099263325406918777713 67398074447494055189083285)
          ·
            refine ⟨3159284739726283836988279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67398074447494055189083285 3159284739726283836988279)
            ·
              refine ⟨4738927109589425755482419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159284739726283836988279 4738927109589425755482419)
              ·
                refine ⟨7108390664384138633223629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738927109589425755482419 7108390664384138633223629)
                ·
                  refine ⟨2665646499144051987458861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7108390664384138633223629 2665646499144051987458861)
                  ·
                    refine ⟨999617437179019495297073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665646499144051987458861 999617437179019495297073)
                    ·
                      rfl

theorem cell22_2920122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_2920122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920122 prefixEnd_2920122 := by exact prefixLift 2920122
  have htrace : WordTrace (prefixWord ++ tailWord_2920122) baseStart_2920122 baseEnd_2920122 := by
    simpa [prefixWord, tailWord_2920122, baseEnd_2920122] using wordTrace_append hprefix tailTrace_2920122
  have hstable : (prefixWord ++ tailWord_2920122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920122).length < 2 ^ (prefixWord ++ tailWord_2920122).sum := by decide
  have hdescent : baseEnd_2920122 < baseStart_2920122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920229 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_2920229 : Nat := 118140960795 + 2920229 * 2 ^ 59
def prefixEnd_2920229 : Nat := 4983230072969 + 3 ^ 40 * 2920229 * 2
def baseEnd_2920229 : Nat := 999654065465706882871745

theorem tailTrace_2920229 : CollatzResearch.WordTrace tailWord_2920229 prefixEnd_2920229 999654065465706882871745 := by
  unfold tailWord_2920229
  simp only [CollatzResearch.WordTrace]
  refine ⟨106509501737516543251955741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71006334491677695501303827 106509501737516543251955741)
  ·
    refine ⟨39941063151568703719483403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106509501737516543251955741 39941063151568703719483403)
    ·
      refine ⟨59911594727353055579225105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39941063151568703719483403 59911594727353055579225105)
      ·
        refine ⟨44933696045514791684418829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59911594727353055579225105 44933696045514791684418829)
        ·
          refine ⟨16850136017068046881657061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44933696045514791684418829 16850136017068046881657061)
          ·
            refine ⟨3159400503200258790310699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16850136017068046881657061 3159400503200258790310699)
            ·
              refine ⟨4739100754800388185466049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159400503200258790310699 4739100754800388185466049)
              ·
                refine ⟨3554325566100291139099537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739100754800388185466049 3554325566100291139099537)
                ·
                  refine ⟨2665744174575218354324653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554325566100291139099537 2665744174575218354324653)
                  ·
                    refine ⟨999654065465706882871745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665744174575218354324653 999654065465706882871745)
                    ·
                      rfl

theorem cell22_2920229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_2920229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920229 prefixEnd_2920229 := by exact prefixLift 2920229
  have htrace : WordTrace (prefixWord ++ tailWord_2920229) baseStart_2920229 baseEnd_2920229 := by
    simpa [prefixWord, tailWord_2920229, baseEnd_2920229] using wordTrace_append hprefix tailTrace_2920229
  have hstable : (prefixWord ++ tailWord_2920229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920229).length < 2 ^ (prefixWord ++ tailWord_2920229).sum := by decide
  have hdescent : baseEnd_2920229 < baseStart_2920229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920291 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 3, 3]
def baseStart_2920291 : Nat := 118140960795 + 2920291 * 2 ^ 59
def prefixEnd_2920291 : Nat := 4983230072969 + 3 ^ 40 * 2920291 * 2
def baseEnd_2920291 : Nat := 999675289332759387821555

theorem tailTrace_2920291 : CollatzResearch.WordTrace tailWord_2920291 prefixEnd_2920291 999675289332759387821555 := by
  unfold tailWord_2920291
  simp only [CollatzResearch.WordTrace]
  refine ⟨106511763063291927840712727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71007842042194618560475151 106511763063291927840712727)
  ·
    refine ⟨159767644594937891761069091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106511763063291927840712727 159767644594937891761069091)
    ·
      refine ⟨239651466892406837641603637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159767644594937891761069091 239651466892406837641603637)
      ·
        refine ⟨22467325021163141028900341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239651466892406837641603637 22467325021163141028900341)
        ·
          refine ⟨2106311720734044471459407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22467325021163141028900341 2106311720734044471459407)
          ·
            refine ⟨3159467581101066707189111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106311720734044471459407 3159467581101066707189111)
            ·
              refine ⟨4739201371651600060783667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159467581101066707189111 4739201371651600060783667)
              ·
                refine ⟨7108802057477400091175501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739201371651600060783667 7108802057477400091175501)
                ·
                  refine ⟨2665800771554025034190813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7108802057477400091175501 2665800771554025034190813)
                  ·
                    refine ⟨999675289332759387821555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665800771554025034190813 999675289332759387821555)
                    ·
                      rfl

theorem cell22_2920291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 3].length) (baseStart_2920291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920291 prefixEnd_2920291 := by exact prefixLift 2920291
  have htrace : WordTrace (prefixWord ++ tailWord_2920291) baseStart_2920291 baseEnd_2920291 := by
    simpa [prefixWord, tailWord_2920291, baseEnd_2920291] using wordTrace_append hprefix tailTrace_2920291
  have hstable : (prefixWord ++ tailWord_2920291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920291).length < 2 ^ (prefixWord ++ tailWord_2920291).sum := by decide
  have hdescent : baseEnd_2920291 < baseStart_2920291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920332 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_2920332 : Nat := 118140960795 + 2920332 * 2 ^ 59
def prefixEnd_2920332 : Nat := 4983230072969 + 3 ^ 40 * 2920332 * 2
def baseEnd_2920332 : Nat := 333229774823549649182143

theorem tailTrace_2920332 : CollatzResearch.WordTrace tailWord_2920332 prefixEnd_2920332 333229774823549649182143 := by
  unfold tailWord_2920332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53256629228071695921477625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71008838970762261228636833 53256629228071695921477625)
  ·
    refine ⟨39942471921053771941108219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53256629228071695921477625 39942471921053771941108219)
    ·
      refine ⟨59913707881580657911662329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39942471921053771941108219 59913707881580657911662329)
      ·
        refine ⟨44935280911185493433746747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59913707881580657911662329 44935280911185493433746747)
        ·
          refine ⟨67402921366778240150620121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44935280911185493433746747 67402921366778240150620121)
          ·
            refine ⟨50552191025083680112965091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67402921366778240150620121 50552191025083680112965091)
            ·
              refine ⟨75828286537625520169447637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50552191025083680112965091 75828286537625520169447637)
              ·
                refine ⟨1777225465725598128971429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75828286537625520169447637 1777225465725598128971429)
                ·
                  refine ⟨333229774823549649182143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777225465725598128971429 333229774823549649182143)
                  ·
                    rfl

theorem cell22_2920332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_2920332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920332 prefixEnd_2920332 := by exact prefixLift 2920332
  have htrace : WordTrace (prefixWord ++ tailWord_2920332) baseStart_2920332 baseEnd_2920332 := by
    simpa [prefixWord, tailWord_2920332, baseEnd_2920332] using wordTrace_append hprefix tailTrace_2920332
  have hstable : (prefixWord ++ tailWord_2920332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920332).length < 2 ^ (prefixWord ++ tailWord_2920332).sum := by decide
  have hdescent : baseEnd_2920332 < baseStart_2920332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920349 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 4]
def baseStart_2920349 : Nat := 118140960795 + 2920349 * 2 ^ 59
def prefixEnd_2920349 : Nat := 4983230072969 + 3 ^ 40 * 2920349 * 2
def baseEnd_2920349 : Nat := 333231714639355523290459

theorem tailTrace_2920349 : CollatzResearch.WordTrace tailWord_2920349 prefixEnd_2920349 333231714639355523290459 := by
  unfold tailWord_2920349
  simp only [CollatzResearch.WordTrace]
  refine ⟨106513878497081803746324101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71009252331387869164216067 106513878497081803746324101)
  ·
    refine ⟨19971352218202838202435769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106513878497081803746324101 19971352218202838202435769)
    ·
      refine ⟨14978514163652128651826827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971352218202838202435769 14978514163652128651826827)
      ·
        refine ⟨22467771245478192977740241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14978514163652128651826827 22467771245478192977740241)
        ·
          refine ⟨16850828434108644733305181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22467771245478192977740241 16850828434108644733305181)
          ·
            refine ⟨6319060662790741774989443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16850828434108644733305181 6319060662790741774989443)
            ·
              refine ⟨9478590994186112662484165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319060662790741774989443 9478590994186112662484165)
              ·
                refine ⟨1777235811409896124215781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9478590994186112662484165 1777235811409896124215781)
                ·
                  refine ⟨333231714639355523290459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777235811409896124215781 333231714639355523290459)
                  ·
                    rfl

theorem cell22_2920349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_2920349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920349 prefixEnd_2920349 := by exact prefixLift 2920349
  have htrace : WordTrace (prefixWord ++ tailWord_2920349) baseStart_2920349 baseEnd_2920349 := by
    simpa [prefixWord, tailWord_2920349, baseEnd_2920349] using wordTrace_append hprefix tailTrace_2920349
  have hstable : (prefixWord ++ tailWord_2920349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920349).length < 2 ^ (prefixWord ++ tailWord_2920349).sum := by decide
  have hdescent : baseEnd_2920349 < baseStart_2920349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920377 : List Nat := [1, 2, 1, 4, 2, 1, 5, 6]
def baseStart_2920377 : Nat := 118140960795 + 2920377 * 2 ^ 59
def prefixEnd_2920377 : Nat := 4983230072969 + 3 ^ 40 * 2920377 * 2
def baseEnd_2920377 : Nat := 111078303210031536685699

theorem tailTrace_2920377 : CollatzResearch.WordTrace tailWord_2920377 prefixEnd_2920377 111078303210031536685699 := by
  unfold tailWord_2920377
  simp only [CollatzResearch.WordTrace]
  refine ⟨106514899740980364528343385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71009933160653576352228923 106514899740980364528343385)
  ·
    refine ⟨79886174805735273396257539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106514899740980364528343385 79886174805735273396257539)
    ·
      refine ⟨119829262208602910094386309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79886174805735273396257539 119829262208602910094386309)
      ·
        refine ⟨22467986664113045642697433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119829262208602910094386309 22467986664113045642697433)
        ·
          refine ⟨16850989998084784232023075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22467986664113045642697433 16850989998084784232023075)
          ·
            refine ⟨25276484997127176348034613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16850989998084784232023075 25276484997127176348034613)
            ·
              refine ⟨2369670468480672782628245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25276484997127176348034613 2369670468480672782628245)
              ·
                refine ⟨111078303210031536685699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2369670468480672782628245 111078303210031536685699)
                ·
                  rfl

theorem cell22_2920377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 6].length) (baseStart_2920377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920377 prefixEnd_2920377 := by exact prefixLift 2920377
  have htrace : WordTrace (prefixWord ++ tailWord_2920377) baseStart_2920377 baseEnd_2920377 := by
    simpa [prefixWord, tailWord_2920377, baseEnd_2920377] using wordTrace_append hprefix tailTrace_2920377
  have hstable : (prefixWord ++ tailWord_2920377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920377).length < 2 ^ (prefixWord ++ tailWord_2920377).sum := by decide
  have hdescent : baseEnd_2920377 < baseStart_2920377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920435 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_2920435 : Nat := 118140960795 + 2920435 * 2 ^ 59
def prefixEnd_2920435 : Nat := 4983230072969 + 3 ^ 40 * 2920435 * 2
def baseEnd_2920435 : Nat := 999724583475591012221113

theorem tailTrace_2920435 : CollatzResearch.WordTrace tailWord_2920435 prefixEnd_2920435 999724583475591012221113 := by
  unfold tailWord_2920435
  simp only [CollatzResearch.WordTrace]
  refine ⟨106517015174770240433954759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71011343449846826955969839 106517015174770240433954759)
  ·
    refine ⟨159775522762155360650932139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106517015174770240433954759 159775522762155360650932139)
    ·
      refine ⟨239663284143233040976398209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159775522762155360650932139 239663284143233040976398209)
      ·
        refine ⟨179747463107424780732298657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239663284143233040976398209 179747463107424780732298657)
        ·
          refine ⟨134810597330568585549223993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179747463107424780732298657 134810597330568585549223993)
          ·
            refine ⟨101107947997926439161917995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134810597330568585549223993 101107947997926439161917995)
            ·
              refine ⟨151661921996889658742876993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101107947997926439161917995 151661921996889658742876993)
              ·
                refine ⟨113746441497667244057157745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151661921996889658742876993 113746441497667244057157745)
                ·
                  refine ⟨85309831123250433042868309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113746441497667244057157745 85309831123250433042868309)
                  ·
                    refine ⟨999724583475591012221113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85309831123250433042868309 999724583475591012221113)
                    ·
                      rfl

theorem cell22_2920435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_2920435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920435 prefixEnd_2920435 := by exact prefixLift 2920435
  have htrace : WordTrace (prefixWord ++ tailWord_2920435) baseStart_2920435 baseEnd_2920435 := by
    simpa [prefixWord, tailWord_2920435, baseEnd_2920435] using wordTrace_append hprefix tailTrace_2920435
  have hstable : (prefixWord ++ tailWord_2920435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920435).length < 2 ^ (prefixWord ++ tailWord_2920435).sum := by decide
  have hdescent : baseEnd_2920435 < baseStart_2920435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920467 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 6]
def baseStart_2920467 : Nat := 118140960795 + 2920467 * 2 ^ 59
def prefixEnd_2920467 : Nat := 4983230072969 + 3 ^ 40 * 2920467 * 2
def baseEnd_2920467 : Nat := 333245179243184531807005

theorem tailTrace_2920467 : CollatzResearch.WordTrace tailWord_2920467 prefixEnd_2920467 333245179243184531807005 := by
  unfold tailWord_2920467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106518182310654309899119655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71012121540436206599413103 106518182310654309899119655)
  ·
    refine ⟨159777273465981464848679483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106518182310654309899119655 159777273465981464848679483)
    ·
      refine ⟨239665910198972197273019225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159777273465981464848679483 239665910198972197273019225)
      ·
        refine ⟨179749432649229147954764419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239665910198972197273019225 179749432649229147954764419)
        ·
          refine ⟨269624148973843721932146629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179749432649229147954764419 269624148973843721932146629)
          ·
            refine ⟨50554527932595697862277493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269624148973843721932146629 50554527932595697862277493)
            ·
              refine ⟨4739486993680846674588515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50554527932595697862277493 4739486993680846674588515)
              ·
                refine ⟨7109230490521270011882773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739486993680846674588515 7109230490521270011882773)
                ·
                  refine ⟨333245179243184531807005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7109230490521270011882773 333245179243184531807005)
                  ·
                    rfl

theorem cell22_2920467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_2920467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920467 prefixEnd_2920467 := by exact prefixLift 2920467
  have htrace : WordTrace (prefixWord ++ tailWord_2920467) baseStart_2920467 baseEnd_2920467 := by
    simpa [prefixWord, tailWord_2920467, baseEnd_2920467] using wordTrace_append hprefix tailTrace_2920467
  have hstable : (prefixWord ++ tailWord_2920467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920467).length < 2 ^ (prefixWord ++ tailWord_2920467).sum := by decide
  have hdescent : baseEnd_2920467 < baseStart_2920467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920518 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2920518 : Nat := 118140960795 + 2920518 * 2 ^ 59
def prefixEnd_2920518 : Nat := 4983230072969 + 3 ^ 40 * 2920518 * 2
def baseEnd_2920518 : Nat := 333250998690602154131953

theorem tailTrace_2920518 : CollatzResearch.WordTrace tailWord_2920518 prefixEnd_2920518 333250998690602154131953 := by
  unfold tailWord_2920518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328751326045923300288319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71013361622313030406150805 3328751326045923300288319)
  ·
    refine ⟨4993126989068884950432479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3328751326045923300288319 4993126989068884950432479)
    ·
      refine ⟨7489690483603327425648719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993126989068884950432479 7489690483603327425648719)
      ·
        refine ⟨11234535725404991138473079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489690483603327425648719 11234535725404991138473079)
        ·
          refine ⟨16851803588107486707709619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234535725404991138473079 16851803588107486707709619)
          ·
            refine ⟨25277705382161230061564429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16851803588107486707709619 25277705382161230061564429)
            ·
              refine ⟨9479139518310461273086661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25277705382161230061564429 9479139518310461273086661)
              ·
                refine ⟨1777338659683211488703749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9479139518310461273086661 1777338659683211488703749)
                ·
                  refine ⟨333250998690602154131953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777338659683211488703749 333250998690602154131953)
                  ·
                    rfl

theorem cell22_2920518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2920518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920518 prefixEnd_2920518 := by exact prefixLift 2920518
  have htrace : WordTrace (prefixWord ++ tailWord_2920518) baseStart_2920518 baseEnd_2920518 := by
    simpa [prefixWord, tailWord_2920518, baseEnd_2920518] using wordTrace_append hprefix tailTrace_2920518
  have hstable : (prefixWord ++ tailWord_2920518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920518).length < 2 ^ (prefixWord ++ tailWord_2920518).sum := by decide
  have hdescent : baseEnd_2920518 < baseStart_2920518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920544 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_2920544 : Nat := 118140960795 + 2920544 * 2 ^ 59
def prefixEnd_2920544 : Nat := 4983230072969 + 3 ^ 40 * 2920544 * 2
def baseEnd_2920544 : Nat := 999761896403151061245779

theorem tailTrace_2920544 : CollatzResearch.WordTrace tailWord_2920544 prefixEnd_2920544 999761896403151061245779 := by
  unfold tailWord_2920544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53260495365687676024836343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71013993820916901366448457 53260495365687676024836343)
  ·
    refine ⟨79890743048531514037254515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53260495365687676024836343 79890743048531514037254515)
    ·
      refine ⟨119836114572797271055881773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79890743048531514037254515 119836114572797271055881773)
      ·
        refine ⟨44938542964798976645955665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119836114572797271055881773 44938542964798976645955665)
        ·
          refine ⟨33703907223599232484466749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44938542964798976645955665 33703907223599232484466749)
          ·
            refine ⟨12638965208849712181675031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33703907223599232484466749 12638965208849712181675031)
            ·
              refine ⟨18958447813274568272512547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638965208849712181675031 18958447813274568272512547)
              ·
                refine ⟨28437671719911852408768821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18958447813274568272512547 28437671719911852408768821)
                ·
                  refine ⟨2666031723741736163322077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28437671719911852408768821 2666031723741736163322077)
                  ·
                    refine ⟨999761896403151061245779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666031723741736163322077 999761896403151061245779)
                    ·
                      rfl

theorem cell22_2920544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_2920544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920544 prefixEnd_2920544 := by exact prefixLift 2920544
  have htrace : WordTrace (prefixWord ++ tailWord_2920544) baseStart_2920544 baseEnd_2920544 := by
    simpa [prefixWord, tailWord_2920544, baseEnd_2920544] using wordTrace_append hprefix tailTrace_2920544
  have hstable : (prefixWord ++ tailWord_2920544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920544).length < 2 ^ (prefixWord ++ tailWord_2920544).sum := by decide
  have hdescent : baseEnd_2920544 < baseStart_2920544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920612 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_2920612 : Nat := 118140960795 + 2920612 * 2 ^ 59
def prefixEnd_2920612 : Nat := 4983230072969 + 3 ^ 40 * 2920612 * 2
def baseEnd_2920612 : Nat := 999785174192821550545571

theorem tailTrace_2920612 : CollatzResearch.WordTrace tailWord_2920612 prefixEnd_2920612 999785174192821550545571 := by
  unfold tailWord_2920612
  simp only [CollatzResearch.WordTrace]
  refine ⟨53261735447564499831574045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71015647263419333108765393 53261735447564499831574045)
  ·
    refine ⟨19973150792836687436840267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53261735447564499831574045 19973150792836687436840267)
    ·
      refine ⟨29959726189255031155260401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19973150792836687436840267 29959726189255031155260401)
      ·
        refine ⟨22469794641941273366445301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29959726189255031155260401 22469794641941273366445301)
        ·
          refine ⟨2106543247681994378104247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22469794641941273366445301 2106543247681994378104247)
          ·
            refine ⟨3159814871522991567156371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106543247681994378104247 3159814871522991567156371)
            ·
              refine ⟨4739722307284487350734557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159814871522991567156371 4739722307284487350734557)
              ·
                refine ⟨1777395865231682756525459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4739722307284487350734557 1777395865231682756525459)
                ·
                  refine ⟨2666093797847524134788189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777395865231682756525459 2666093797847524134788189)
                  ·
                    refine ⟨999785174192821550545571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666093797847524134788189 999785174192821550545571)
                    ·
                      rfl

theorem cell22_2920612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_2920612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920612 prefixEnd_2920612 := by exact prefixLift 2920612
  have htrace : WordTrace (prefixWord ++ tailWord_2920612) baseStart_2920612 baseEnd_2920612 := by
    simpa [prefixWord, tailWord_2920612, baseEnd_2920612] using wordTrace_append hprefix tailTrace_2920612
  have hstable : (prefixWord ++ tailWord_2920612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920612).length < 2 ^ (prefixWord ++ tailWord_2920612).sum := by decide
  have hdescent : baseEnd_2920612 < baseStart_2920612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920642 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2920642 : Nat := 118140960795 + 2920642 * 2 ^ 59
def prefixEnd_2920642 : Nat := 4983230072969 + 3 ^ 40 * 2920642 * 2
def baseEnd_2920642 : Nat := 333265147935303824098493

theorem tailTrace_2920642 : CollatzResearch.WordTrace tailWord_2920642 prefixEnd_2920642 333265147935303824098493 := by
  unfold tailWord_2920642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26631141271255078696685045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71016376723346876524493453 26631141271255078696685045)
  ·
    refine ⟨2496669494180163627814223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26631141271255078696685045 2496669494180163627814223)
    ·
      refine ⟨3745004241270245441721335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2496669494180163627814223 3745004241270245441721335)
      ·
        refine ⟨5617506361905368162582003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745004241270245441721335 5617506361905368162582003)
        ·
          refine ⟨8426259542858052243873005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617506361905368162582003 8426259542858052243873005)
          ·
            refine ⟨3159847328571769591452377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8426259542858052243873005 3159847328571769591452377)
            ·
              refine ⟨2369885496428827193589283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159847328571769591452377 2369885496428827193589283)
              ·
                refine ⟨3554828244643240790383925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369885496428827193589283 3554828244643240790383925)
                ·
                  refine ⟨333265147935303824098493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554828244643240790383925 333265147935303824098493)
                  ·
                    rfl

theorem cell22_2920642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2920642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920642 prefixEnd_2920642 := by exact prefixLift 2920642
  have htrace : WordTrace (prefixWord ++ tailWord_2920642) baseStart_2920642 baseEnd_2920642 := by
    simpa [prefixWord, tailWord_2920642, baseEnd_2920642] using wordTrace_append hprefix tailTrace_2920642
  have hstable : (prefixWord ++ tailWord_2920642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920642).length < 2 ^ (prefixWord ++ tailWord_2920642).sum := by decide
  have hdescent : baseEnd_2920642 < baseStart_2920642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920651 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 2, 3]
def baseStart_2920651 : Nat := 118140960795 + 2920651 * 2 ^ 59
def prefixEnd_2920651 : Nat := 4983230072969 + 3 ^ 40 * 2920651 * 2
def baseEnd_2920651 : Nat := 999798524689838448820451

theorem tailTrace_2920651 : CollatzResearch.WordTrace tailWord_2920651 prefixEnd_2920651 999798524689838448820451 := by
  unfold tailWord_2920651
  simp only [CollatzResearch.WordTrace]
  refine ⟨106524893341987709323817807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71016595561325139549211871 106524893341987709323817807)
  ·
    refine ⟨159787340012981563985726711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106524893341987709323817807 159787340012981563985726711)
    ·
      refine ⟨239681010019472345978590067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159787340012981563985726711 239681010019472345978590067)
      ·
        refine ⟨359521515029208518967885101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239681010019472345978590067 359521515029208518967885101)
        ·
          refine ⟨134820568135953194612956913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359521515029208518967885101 134820568135953194612956913)
          ·
            refine ⟨101115426101964895959717685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134820568135953194612956913 101115426101964895959717685)
            ·
              refine ⟨9479571197059208996223533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101115426101964895959717685 9479571197059208996223533)
              ·
                refine ⟨3554839198897203373583825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9479571197059208996223533 3554839198897203373583825)
                ·
                  refine ⟨2666129399172902530187869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554839198897203373583825 2666129399172902530187869)
                  ·
                    refine ⟨999798524689838448820451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666129399172902530187869 999798524689838448820451)
                    ·
                      rfl

theorem cell22_2920651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].length) (baseStart_2920651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920651 prefixEnd_2920651 := by exact prefixLift 2920651
  have htrace : WordTrace (prefixWord ++ tailWord_2920651) baseStart_2920651 baseEnd_2920651 := by
    simpa [prefixWord, tailWord_2920651, baseEnd_2920651] using wordTrace_append hprefix tailTrace_2920651
  have hstable : (prefixWord ++ tailWord_2920651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920651).length < 2 ^ (prefixWord ++ tailWord_2920651).sum := by decide
  have hdescent : baseEnd_2920651 < baseStart_2920651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920664 : List Nat := [2, 1, 2, 2, 4, 1, 2, 8]
def baseStart_2920664 : Nat := 118140960795 + 2920664 * 2 ^ 59
def prefixEnd_2920664 : Nat := 4983230072969 + 3 ^ 40 * 2920664 * 2
def baseEnd_2920664 : Nat := 111089219428390083138379

theorem tailTrace_2920664 : CollatzResearch.WordTrace tailWord_2920664 prefixEnd_2920664 111089219428390083138379 := by
  unfold tailWord_2920664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262683745470306272020523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71016911660627075029360697 53262683745470306272020523)
  ·
    refine ⟨79894025618205459408030785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53262683745470306272020523 79894025618205459408030785)
    ·
      refine ⟨59920519213654094556023089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79894025618205459408030785 59920519213654094556023089)
      ·
        refine ⟨44940389410240570917017317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59920519213654094556023089 44940389410240570917017317)
        ·
          refine ⟨8426323014420107046940747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44940389410240570917017317 8426323014420107046940747)
          ·
            refine ⟨12639484521630160570411121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8426323014420107046940747 12639484521630160570411121)
            ·
              refine ⟨9479613391222620427808341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12639484521630160570411121 9479613391222620427808341)
              ·
                refine ⟨111089219428390083138379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9479613391222620427808341 111089219428390083138379)
                ·
                  rfl

theorem cell22_2920664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_2920664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920664 prefixEnd_2920664 := by exact prefixLift 2920664
  have htrace : WordTrace (prefixWord ++ tailWord_2920664) baseStart_2920664 baseEnd_2920664 := by
    simpa [prefixWord, tailWord_2920664, baseEnd_2920664] using wordTrace_append hprefix tailTrace_2920664
  have hstable : (prefixWord ++ tailWord_2920664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920664).length < 2 ^ (prefixWord ++ tailWord_2920664).sum := by decide
  have hdescent : baseEnd_2920664 < baseStart_2920664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920685 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_2920685 : Nat := 118140960795 + 2920685 * 2 ^ 59
def prefixEnd_2920685 : Nat := 4983230072969 + 3 ^ 40 * 2920685 * 2
def baseEnd_2920685 : Nat := 999810163584673693470347

theorem tailTrace_2920685 : CollatzResearch.WordTrace tailWord_2920685 prefixEnd_2920685 999810163584673693470347 := by
  unfold tailWord_2920685
  simp only [CollatzResearch.WordTrace]
  refine ⟨106526133423864533130555509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71017422282576355420370339 106526133423864533130555509)
  ·
    refine ⟨9986825008487299980989579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106526133423864533130555509 9986825008487299980989579)
    ·
      refine ⟨14980237512730949971484369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986825008487299980989579 14980237512730949971484369)
      ·
        refine ⟨11235178134548212478613277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14980237512730949971484369 11235178134548212478613277)
        ·
          refine ⟨4213191800455579679479979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11235178134548212478613277 4213191800455579679479979)
          ·
            refine ⟨6319787700683369519219969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213191800455579679479979 6319787700683369519219969)
            ·
              refine ⟨4739840775512527139414977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319787700683369519219969 4739840775512527139414977)
              ·
                refine ⟨3554880581634395354561233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739840775512527139414977 3554880581634395354561233)
                ·
                  refine ⟨2666160436225796515920925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554880581634395354561233 2666160436225796515920925)
                  ·
                    refine ⟨999810163584673693470347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666160436225796515920925 999810163584673693470347)
                    ·
                      rfl

theorem cell22_2920685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_2920685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920685 prefixEnd_2920685 := by exact prefixLift 2920685
  have htrace : WordTrace (prefixWord ++ tailWord_2920685) baseStart_2920685 baseEnd_2920685 := by
    simpa [prefixWord, tailWord_2920685, baseEnd_2920685] using wordTrace_append hprefix tailTrace_2920685
  have hstable : (prefixWord ++ tailWord_2920685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920685).length < 2 ^ (prefixWord ++ tailWord_2920685).sum := by decide
  have hdescent : baseEnd_2920685 < baseStart_2920685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920786 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2920786 : Nat := 118140960795 + 2920786 * 2 ^ 59
def prefixEnd_2920786 : Nat := 4983230072969 + 3 ^ 40 * 2920786 * 2
def baseEnd_2920786 : Nat := 999844737948743096695037

theorem tailTrace_2920786 : CollatzResearch.WordTrace tailWord_2920786 prefixEnd_2920786 999844737948743096695037 := by
  unfold tailWord_2920786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26632454299124656844995553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71019878130999084919988141 26632454299124656844995553)
  ·
    refine ⟨19974340724343492633746665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26632454299124656844995553 19974340724343492633746665)
    ·
      refine ⟨14980755543257619475309999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19974340724343492633746665 14980755543257619475309999)
      ·
        refine ⟨22471133314886429212964999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14980755543257619475309999 22471133314886429212964999)
        ·
          refine ⟨33706699972329643819447499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471133314886429212964999 33706699972329643819447499)
          ·
            refine ⟨50560049958494465729171249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33706699972329643819447499 50560049958494465729171249)
            ·
              refine ⟨37920037468870849296878437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50560049958494465729171249 37920037468870849296878437)
              ·
                refine ⟨7110007025413284243164707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37920037468870849296878437 7110007025413284243164707)
                ·
                  refine ⟨10665010538119926364747061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110007025413284243164707 10665010538119926364747061)
                  ·
                    refine ⟨999844737948743096695037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10665010538119926364747061 999844737948743096695037)
                    ·
                      rfl

theorem cell22_2920786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2920786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920786 prefixEnd_2920786 := by exact prefixLift 2920786
  have htrace : WordTrace (prefixWord ++ tailWord_2920786) baseStart_2920786 baseEnd_2920786 := by
    simpa [prefixWord, tailWord_2920786, baseEnd_2920786] using wordTrace_append hprefix tailTrace_2920786
  have hstable : (prefixWord ++ tailWord_2920786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920786).length < 2 ^ (prefixWord ++ tailWord_2920786).sum := by decide
  have hdescent : baseEnd_2920786 < baseStart_2920786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920798 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2920798 : Nat := 118140960795 + 2920798 * 2 ^ 59
def prefixEnd_2920798 : Nat := 4983230072969 + 3 ^ 40 * 2920798 * 2
def baseEnd_2920798 : Nat := 999848845793979065395001

theorem tailTrace_2920798 : CollatzResearch.WordTrace tailWord_2920798 prefixEnd_2920798 999848845793979065395001 := by
  unfold tailWord_2920798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316281859056894178677381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71020169914970102286279365 13316281859056894178677381)
  ·
    refine ⟨2496802848573167658502009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13316281859056894178677381 2496802848573167658502009)
    ·
      refine ⟨1872602136429875743876507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496802848573167658502009 1872602136429875743876507)
      ·
        refine ⟨2808903204644813615814761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872602136429875743876507 2808903204644813615814761)
        ·
          refine ⟨2106677403483610211861071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808903204644813615814761 2106677403483610211861071)
          ·
            refine ⟨3160016105225415317791607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106677403483610211861071 3160016105225415317791607)
            ·
              refine ⟨4740024157838122976687411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160016105225415317791607 4740024157838122976687411)
              ·
                refine ⟨7110036236757184465031117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740024157838122976687411 7110036236757184465031117)
                ·
                  refine ⟨2666263588783944174386669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7110036236757184465031117 2666263588783944174386669)
                  ·
                    refine ⟨999848845793979065395001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666263588783944174386669 999848845793979065395001)
                    ·
                      rfl

theorem cell22_2920798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2920798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920798 prefixEnd_2920798 := by exact prefixLift 2920798
  have htrace : WordTrace (prefixWord ++ tailWord_2920798) baseStart_2920798 baseEnd_2920798 := by
    simpa [prefixWord, tailWord_2920798, baseEnd_2920798] using wordTrace_append hprefix tailTrace_2920798
  have hstable : (prefixWord ++ tailWord_2920798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920798).length < 2 ^ (prefixWord ++ tailWord_2920798).sum := by decide
  have hdescent : baseEnd_2920798 < baseStart_2920798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920799 : List Nat := [1, 1, 2, 3, 1, 2, 12]
def baseStart_2920799 : Nat := 118140960795 + 2920799 * 2 ^ 59
def prefixEnd_2920799 : Nat := 4983230072969 + 3 ^ 40 * 2920799 * 2
def baseEnd_2920799 : Nat := 37031451411645014671111

theorem tailTrace_2920799 : CollatzResearch.WordTrace tailWord_2920799 prefixEnd_2920799 37031451411645014671111 := by
  unfold tailWord_2920799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106530291345451530600205451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71020194230301020400136967 106530291345451530600205451)
  ·
    refine ⟨159795437018177295900308177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106530291345451530600205451 159795437018177295900308177)
    ·
      refine ⟨119846577763632971925231133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159795437018177295900308177 119846577763632971925231133)
      ·
        refine ⟨44942466661362364471961675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119846577763632971925231133 44942466661362364471961675)
        ·
          refine ⟨67413699992043546707942513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44942466661362364471961675 67413699992043546707942513)
          ·
            refine ⟨50560274994032660030956885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67413699992043546707942513 50560274994032660030956885)
            ·
              refine ⟨37031451411645014671111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50560274994032660030956885 37031451411645014671111)
              ·
                rfl

theorem cell22_2920799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 12].length) (baseStart_2920799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920799 prefixEnd_2920799 := by exact prefixLift 2920799
  have htrace : WordTrace (prefixWord ++ tailWord_2920799) baseStart_2920799 baseEnd_2920799 := by
    simpa [prefixWord, tailWord_2920799, baseEnd_2920799] using wordTrace_append hprefix tailTrace_2920799
  have hstable : (prefixWord ++ tailWord_2920799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920799).length < 2 ^ (prefixWord ++ tailWord_2920799).sum := by decide
  have hdescent : baseEnd_2920799 < baseStart_2920799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920803 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 2, 3]
def baseStart_2920803 : Nat := 118140960795 + 2920803 * 2 ^ 59
def prefixEnd_2920803 : Nat := 4983230072969 + 3 ^ 40 * 2920803 * 2
def baseEnd_2920803 : Nat := 999850557396160719019985

theorem tailTrace_2920803 : CollatzResearch.WordTrace tailWord_2920803 prefixEnd_2920803 999850557396160719019985 := by
  unfold tailWord_2920803
  simp only [CollatzResearch.WordTrace]
  refine ⟨106530437237437039283351063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71020291491624692855567375 106530437237437039283351063)
  ·
    refine ⟨159795655856155558925026595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106530437237437039283351063 159795655856155558925026595)
    ·
      refine ⟨239693483784233338387539893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159795655856155558925026595 239693483784233338387539893)
      ·
        refine ⟨22471264104771875473831865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239693483784233338387539893 22471264104771875473831865)
        ·
          refine ⟨16853448078578906605373899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22471264104771875473831865 16853448078578906605373899)
          ·
            refine ⟨25280172117868359908060849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16853448078578906605373899 25280172117868359908060849)
            ·
              refine ⟨18960129088401269931045637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25280172117868359908060849 18960129088401269931045637)
              ·
                refine ⟨3555024204075238112071057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18960129088401269931045637 3555024204075238112071057)
                ·
                  refine ⟨2666268153056428584053293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555024204075238112071057 2666268153056428584053293)
                  ·
                    refine ⟨999850557396160719019985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666268153056428584053293 999850557396160719019985)
                    ·
                      rfl

theorem cell22_2920803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].length) (baseStart_2920803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920803 prefixEnd_2920803 := by exact prefixLift 2920803
  have htrace : WordTrace (prefixWord ++ tailWord_2920803) baseStart_2920803 baseEnd_2920803 := by
    simpa [prefixWord, tailWord_2920803, baseEnd_2920803] using wordTrace_append hprefix tailTrace_2920803
  have hstable : (prefixWord ++ tailWord_2920803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920803).length < 2 ^ (prefixWord ++ tailWord_2920803).sum := by decide
  have hdescent : baseEnd_2920803 < baseStart_2920803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920805 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 4]
def baseStart_2920805 : Nat := 118140960795 + 2920805 * 2 ^ 59
def prefixEnd_2920805 : Nat := 4983230072969 + 3 ^ 40 * 2920805 * 2
def baseEnd_2920805 : Nat := 333283747345677793489993

theorem tailTrace_2920805 : CollatzResearch.WordTrace tailWord_2920805 prefixEnd_2920805 333283747345677793489993 := by
  unfold tailWord_2920805
  simp only [CollatzResearch.WordTrace]
  refine ⟨106530510183429793624923869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71020340122286529083282579 106530510183429793624923869)
  ·
    refine ⟨39948941318786172609346451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106530510183429793624923869 39948941318786172609346451)
    ·
      refine ⟨59923411978179258914019677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39948941318786172609346451 59923411978179258914019677)
      ·
        refine ⟨22471279491817222092757379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59923411978179258914019677 22471279491817222092757379)
        ·
          refine ⟨33706919237725833139136069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471279491817222092757379 33706919237725833139136069)
          ·
            refine ⟨6320047357073593713588013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33706919237725833139136069 6320047357073593713588013)
            ·
              refine ⟨2370017758902597642595505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320047357073593713588013 2370017758902597642595505)
              ·
                refine ⟨1777513319176948231946629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370017758902597642595505 1777513319176948231946629)
                ·
                  refine ⟨333283747345677793489993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777513319176948231946629 333283747345677793489993)
                  ·
                    rfl

theorem cell22_2920805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_2920805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920805 prefixEnd_2920805 := by exact prefixLift 2920805
  have htrace : WordTrace (prefixWord ++ tailWord_2920805) baseStart_2920805 baseEnd_2920805 := by
    simpa [prefixWord, tailWord_2920805, baseEnd_2920805] using wordTrace_append hprefix tailTrace_2920805
  have hstable : (prefixWord ++ tailWord_2920805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920805).length < 2 ^ (prefixWord ++ tailWord_2920805).sum := by decide
  have hdescent : baseEnd_2920805 < baseStart_2920805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920816 : List Nat := [2, 1, 1, 1, 4, 4, 2, 7]
def baseStart_2920816 : Nat := 118140960795 + 2920816 * 2 ^ 59
def prefixEnd_2920816 : Nat := 4983230072969 + 3 ^ 40 * 2920816 * 2
def baseEnd_2920816 : Nat := 111095000840203668716105

theorem tailTrace_2920816 : CollatzResearch.WordTrace tailWord_2920816 prefixEnd_2920816 111095000840203668716105 := by
  unfold tailWord_2920816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53265455693194971251787151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71020607590926628335716201 53265455693194971251787151)
  ·
    refine ⟨79898183539792456877680727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53265455693194971251787151 79898183539792456877680727)
    ·
      refine ⟨119847275309688685316521091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79898183539792456877680727 119847275309688685316521091)
      ·
        refine ⟨179770912964533027974781637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119847275309688685316521091 179770912964533027974781637)
        ·
          refine ⟨33707046180849942745271557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179770912964533027974781637 33707046180849942745271557)
          ·
            refine ⟨6320071158909364264738417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33707046180849942745271557 6320071158909364264738417)
            ·
              refine ⟨4740053369182023198553813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320071158909364264738417 4740053369182023198553813)
              ·
                refine ⟨111095000840203668716105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4740053369182023198553813 111095000840203668716105)
                ·
                  rfl

theorem cell22_2920816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_2920816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920816 prefixEnd_2920816 := by exact prefixLift 2920816
  have htrace : WordTrace (prefixWord ++ tailWord_2920816) baseStart_2920816 baseEnd_2920816 := by
    simpa [prefixWord, tailWord_2920816, baseEnd_2920816] using wordTrace_append hprefix tailTrace_2920816
  have hstable : (prefixWord ++ tailWord_2920816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920816).length < 2 ^ (prefixWord ++ tailWord_2920816).sum := by decide
  have hdescent : baseEnd_2920816 < baseStart_2920816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920906 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_2920906 : Nat := 118140960795 + 2920906 * 2 ^ 59
def prefixEnd_2920906 : Nat := 4983230072969 + 3 ^ 40 * 2920906 * 2
def baseEnd_2920906 : Nat := 333295272133700927898223

theorem tailTrace_2920906 : CollatzResearch.WordTrace tailWord_2920906 prefixEnd_2920906 333295272133700927898223 := by
  unfold tailWord_2920906
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633548489015971968587643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71022795970709258582900381 26633548489015971968587643)
  ·
    refine ⟨39950322733523957952881465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26633548489015971968587643 39950322733523957952881465)
    ·
      refine ⟨29962742050142968464661099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39950322733523957952881465 29962742050142968464661099)
      ·
        refine ⟨44944113075214452696991649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29962742050142968464661099 44944113075214452696991649)
        ·
          refine ⟨33708084806410839522743737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44944113075214452696991649 33708084806410839522743737)
          ·
            refine ⟨25281063604808129642057803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33708084806410839522743737 25281063604808129642057803)
            ·
              refine ⟨37921595407212194463086705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25281063604808129642057803 37921595407212194463086705)
              ·
                refine ⟨28441196555409145847315029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37921595407212194463086705 28441196555409145847315029)
                ·
                  refine ⟨333295272133700927898223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28441196555409145847315029 333295272133700927898223)
                  ·
                    rfl

theorem cell22_2920906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_2920906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920906 prefixEnd_2920906 := by exact prefixLift 2920906
  have htrace : WordTrace (prefixWord ++ tailWord_2920906) baseStart_2920906 baseEnd_2920906 := by
    simpa [prefixWord, tailWord_2920906, baseEnd_2920906] using wordTrace_append hprefix tailTrace_2920906
  have hstable : (prefixWord ++ tailWord_2920906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920906).length < 2 ^ (prefixWord ++ tailWord_2920906).sum := by decide
  have hdescent : baseEnd_2920906 < baseStart_2920906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920989 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2920989 : Nat := 118140960795 + 2920989 * 2 ^ 59
def prefixEnd_2920989 : Nat := 4983230072969 + 3 ^ 40 * 2920989 * 2
def baseEnd_2920989 : Nat := 999914228997318233869415

theorem tailTrace_2920989 : CollatzResearch.WordTrace tailWord_2920989 prefixEnd_2920989 999914228997318233869415 := by
  unfold tailWord_2920989
  simp only [CollatzResearch.WordTrace]
  refine ⟨106537221214763193049622021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71024814143175462033081347 106537221214763193049622021)
  ·
    refine ⟨19975728977768098696804129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106537221214763193049622021 19975728977768098696804129)
    ·
      refine ⟨14981796733326074022603097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19975728977768098696804129 14981796733326074022603097)
      ·
        refine ⟨11236347549994555516952323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14981796733326074022603097 11236347549994555516952323)
        ·
          refine ⟨16854521324991833275428485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236347549994555516952323 16854521324991833275428485)
          ·
            refine ⟨3160222748435968739142841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16854521324991833275428485 3160222748435968739142841)
            ·
              refine ⟨2370167061326976554357131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160222748435968739142841 2370167061326976554357131)
              ·
                refine ⟨3555250591990464831535697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370167061326976554357131 3555250591990464831535697)
                ·
                  refine ⟨2666437943992848623651773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555250591990464831535697 2666437943992848623651773)
                  ·
                    refine ⟨999914228997318233869415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666437943992848623651773 999914228997318233869415)
                    ·
                      rfl

theorem cell22_2920989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2920989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2920989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2920989 prefixEnd_2920989 := by exact prefixLift 2920989
  have htrace : WordTrace (prefixWord ++ tailWord_2920989) baseStart_2920989 baseEnd_2920989 := by
    simpa [prefixWord, tailWord_2920989, baseEnd_2920989] using wordTrace_append hprefix tailTrace_2920989
  have hstable : (prefixWord ++ tailWord_2920989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920989).length < 2 ^ (prefixWord ++ tailWord_2920989).sum := by decide
  have hdescent : baseEnd_2920989 < baseStart_2920989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921017 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_2921017 : Nat := 118140960795 + 2921017 * 2 ^ 59
def prefixEnd_2921017 : Nat := 4983230072969 + 3 ^ 40 * 2921017 * 2
def baseEnd_2921017 : Nat := 999923813969535494169329

theorem tailTrace_2921017 : CollatzResearch.WordTrace tailWord_2921017 prefixEnd_2921017 999923813969535494169329 := by
  unfold tailWord_2921017
  simp only [CollatzResearch.WordTrace]
  refine ⟨106538242458661753831641305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71025494972441169221094203 106538242458661753831641305)
  ·
    refine ⟨79903681843996315373730979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106538242458661753831641305 79903681843996315373730979)
    ·
      refine ⟨119855522765994473060596469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79903681843996315373730979 119855522765994473060596469)
      ·
        refine ⟨11236455259311981849430919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119855522765994473060596469 11236455259311981849430919)
        ·
          refine ⟨16854682888967972774146379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236455259311981849430919 16854682888967972774146379)
          ·
            refine ⟨25282024333451959161219569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16854682888967972774146379 25282024333451959161219569)
            ·
              refine ⟨18961518250088969370914677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25282024333451959161219569 18961518250088969370914677)
              ·
                refine ⟨1777642335945840878523251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18961518250088969370914677 1777642335945840878523251)
                ·
                  refine ⟨2666463503918761317784877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777642335945840878523251 2666463503918761317784877)
                  ·
                    refine ⟨999923813969535494169329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666463503918761317784877 999923813969535494169329)
                    ·
                      rfl

theorem cell22_2921017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_2921017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921017 prefixEnd_2921017 := by exact prefixLift 2921017
  have htrace : WordTrace (prefixWord ++ tailWord_2921017) baseStart_2921017 baseEnd_2921017 := by
    simpa [prefixWord, tailWord_2921017, baseEnd_2921017] using wordTrace_append hprefix tailTrace_2921017
  have hstable : (prefixWord ++ tailWord_2921017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921017).length < 2 ^ (prefixWord ++ tailWord_2921017).sum := by decide
  have hdescent : baseEnd_2921017 < baseStart_2921017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921034 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2921034 : Nat := 118140960795 + 2921034 * 2 ^ 59
def prefixEnd_2921034 : Nat := 4983230072969 + 3 ^ 40 * 2921034 * 2
def baseEnd_2921034 : Nat := 999929633416953116494277

theorem tailTrace_2921034 : CollatzResearch.WordTrace tailWord_2921034 prefixEnd_2921034 999929633416953116494277 := by
  unfold tailWord_2921034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26634715624900041433752539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71025908333066777156673437 26634715624900041433752539)
  ·
    refine ⟨39952073437350062150628809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26634715624900041433752539 39952073437350062150628809)
    ·
      refine ⟨29964055078012546612971607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39952073437350062150628809 29964055078012546612971607)
      ·
        refine ⟨44946082617018819919457411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29964055078012546612971607 44946082617018819919457411)
        ·
          refine ⟨67419123925528229879186117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44946082617018819919457411 67419123925528229879186117)
          ·
            refine ⟨12641085736036543102347397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67419123925528229879186117 12641085736036543102347397)
            ·
              refine ⟨2370203575506851831690137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12641085736036543102347397 2370203575506851831690137)
              ·
                refine ⟨1777652681630138873767603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370203575506851831690137 1777652681630138873767603)
                ·
                  refine ⟨2666479022445208310651405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777652681630138873767603 2666479022445208310651405)
                  ·
                    refine ⟨999929633416953116494277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666479022445208310651405 999929633416953116494277)
                    ·
                      rfl

theorem cell22_2921034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2921034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921034 prefixEnd_2921034 := by exact prefixLift 2921034
  have htrace : WordTrace (prefixWord ++ tailWord_2921034) baseStart_2921034 baseEnd_2921034 := by
    simpa [prefixWord, tailWord_2921034, baseEnd_2921034] using wordTrace_append hprefix tailTrace_2921034
  have hstable : (prefixWord ++ tailWord_2921034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921034).length < 2 ^ (prefixWord ++ tailWord_2921034).sum := by decide
  have hdescent : baseEnd_2921034 < baseStart_2921034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921060 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2921060 : Nat := 118140960795 + 2921060 * 2 ^ 59
def prefixEnd_2921060 : Nat := 4983230072969 + 3 ^ 40 * 2921060 * 2
def baseEnd_2921060 : Nat := 999938533748297715344197

theorem tailTrace_2921060 : CollatzResearch.WordTrace tailWord_2921060 prefixEnd_2921060 999938533748297715344197 := by
  unfold tailWord_2921060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53269905398752986087728317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71026540531670648116971089 53269905398752986087728317)
  ·
    refine ⟨19976214524532369782898119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53269905398752986087728317 19976214524532369782898119)
    ·
      refine ⟨29964321786798554674347179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19976214524532369782898119 29964321786798554674347179)
      ·
        refine ⟨44946482680197832011520769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29964321786798554674347179 44946482680197832011520769)
        ·
          refine ⟨33709862010148374008640577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44946482680197832011520769 33709862010148374008640577)
          ·
            refine ⟨25282396507611280506480433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33709862010148374008640577 25282396507611280506480433)
            ·
              refine ⟨18961797380708460379860325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25282396507611280506480433 18961797380708460379860325)
              ·
                refine ⟨3555337008882836321223811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18961797380708460379860325 3555337008882836321223811)
                ·
                  refine ⟨5333005513324254481835717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555337008882836321223811 5333005513324254481835717)
                  ·
                    refine ⟨999938533748297715344197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333005513324254481835717 999938533748297715344197)
                    ·
                      rfl

theorem cell22_2921060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2921060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921060 prefixEnd_2921060 := by exact prefixLift 2921060
  have htrace : WordTrace (prefixWord ++ tailWord_2921060) baseStart_2921060 baseEnd_2921060 := by
    simpa [prefixWord, tailWord_2921060, baseEnd_2921060] using wordTrace_append hprefix tailTrace_2921060
  have hstable : (prefixWord ++ tailWord_2921060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921060).length < 2 ^ (prefixWord ++ tailWord_2921060).sum := by decide
  have hdescent : baseEnd_2921060 < baseStart_2921060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921092 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_2921092 : Nat := 118140960795 + 2921092 * 2 ^ 59
def prefixEnd_2921092 : Nat := 4983230072969 + 3 ^ 40 * 2921092 * 2
def baseEnd_2921092 : Nat := 333316496000753432848033

theorem tailTrace_2921092 : CollatzResearch.WordTrace tailWord_2921092 prefixEnd_2921092 333316496000753432848033 := by
  unfold tailWord_2921092
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270488966695020820310765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71027318622260027760414353 53270488966695020820310765)
  ·
    refine ⟨19976433362510632807616537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53270488966695020820310765 19976433362510632807616537)
    ·
      refine ⟨14982325021882974605712403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19976433362510632807616537 14982325021882974605712403)
      ·
        refine ⟨22473487532824461908568605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982325021882974605712403 22473487532824461908568605)
        ·
          refine ⟨8427557824809173215713227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22473487532824461908568605 8427557824809173215713227)
          ·
            refine ⟨12641336737213759823569841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427557824809173215713227 12641336737213759823569841)
            ·
              refine ⟨9481002552910319867677381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641336737213759823569841 9481002552910319867677381)
              ·
                refine ⟨1777687978670684975189509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9481002552910319867677381 1777687978670684975189509)
                ·
                  refine ⟨333316496000753432848033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777687978670684975189509 333316496000753432848033)
                  ·
                    rfl

theorem cell22_2921092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_2921092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921092 prefixEnd_2921092 := by exact prefixLift 2921092
  have htrace : WordTrace (prefixWord ++ tailWord_2921092) baseStart_2921092 baseEnd_2921092 := by
    simpa [prefixWord, tailWord_2921092, baseEnd_2921092] using wordTrace_append hprefix tailTrace_2921092
  have hstable : (prefixWord ++ tailWord_2921092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921092).length < 2 ^ (prefixWord ++ tailWord_2921092).sum := by decide
  have hdescent : baseEnd_2921092 < baseStart_2921092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921120 : List Nat := [2, 1, 1, 4, 4, 1, 1, 8]
def baseStart_2921120 : Nat := 118140960795 + 2921120 * 2 ^ 59
def prefixEnd_2921120 : Nat := 4983230072969 + 3 ^ 40 * 2921120 * 2
def baseEnd_2921120 : Nat := 111106563663830839871557

theorem tailTrace_2921120 : CollatzResearch.WordTrace tailWord_2921120 prefixEnd_2921120 111106563663830839871557 := by
  unfold tailWord_2921120
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270999588644301211320407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71027999451525734948427209 53270999588644301211320407)
  ·
    refine ⟨79906499382966451816980611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53270999588644301211320407 79906499382966451816980611)
    ·
      refine ⟨119859749074449677725470917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79906499382966451816980611 119859749074449677725470917)
      ·
        refine ⟨22473702951459314573525797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119859749074449677725470917 22473702951459314573525797)
        ·
          refine ⟨4213819303398621482536087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22473702951459314573525797 4213819303398621482536087)
          ·
            refine ⟨6320728955097932223804131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213819303398621482536087 6320728955097932223804131)
            ·
              refine ⟨9481093432646898335706197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320728955097932223804131 9481093432646898335706197)
              ·
                refine ⟨111106563663830839871557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9481093432646898335706197 111106563663830839871557)
                ·
                  rfl

theorem cell22_2921120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_2921120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921120 prefixEnd_2921120 := by exact prefixLift 2921120
  have htrace : WordTrace (prefixWord ++ tailWord_2921120) baseStart_2921120 baseEnd_2921120 := by
    simpa [prefixWord, tailWord_2921120, baseEnd_2921120] using wordTrace_append hprefix tailTrace_2921120
  have hstable : (prefixWord ++ tailWord_2921120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921120).length < 2 ^ (prefixWord ++ tailWord_2921120).sum := by decide
  have hdescent : baseEnd_2921120 < baseStart_2921120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921137 : List Nat := [1, 2, 2, 6, 1, 2, 8]
def baseStart_2921137 : Nat := 118140960795 + 2921137 * 2 ^ 59
def prefixEnd_2921137 : Nat := 4983230072969 + 3 ^ 40 * 2921137 * 2
def baseEnd_2921137 : Nat := 37035736756366488191443

theorem tailTrace_2921137 : CollatzResearch.WordTrace tailWord_2921137 prefixEnd_2921137 37035736756366488191443 := by
  unfold tailWord_2921137
  simp only [CollatzResearch.WordTrace]
  refine ⟨106542619218227014326009665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71028412812151342884006443 106542619218227014326009665)
  ·
    refine ⟨79906964413670260744507249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106542619218227014326009665 79906964413670260744507249)
    ·
      refine ⟨59930223310252695558380437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79906964413670260744507249 59930223310252695558380437)
      ·
        refine ⟨2809229217668095104299083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59930223310252695558380437 2809229217668095104299083)
        ·
          refine ⟨4213843826502142656448625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809229217668095104299083 4213843826502142656448625)
          ·
            refine ⟨3160382869876606992336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213843826502142656448625 3160382869876606992336469)
            ·
              refine ⟨37035736756366488191443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3160382869876606992336469 37035736756366488191443)
              ·
                rfl

theorem cell22_2921137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 8].length) (baseStart_2921137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921137 prefixEnd_2921137 := by exact prefixLift 2921137
  have htrace : WordTrace (prefixWord ++ tailWord_2921137) baseStart_2921137 baseEnd_2921137 := by
    simpa [prefixWord, tailWord_2921137, baseEnd_2921137] using wordTrace_append hprefix tailTrace_2921137
  have hstable : (prefixWord ++ tailWord_2921137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921137).length < 2 ^ (prefixWord ++ tailWord_2921137).sum := by decide
  have hdescent : baseEnd_2921137 < baseStart_2921137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921150 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2921150 : Nat := 118140960795 + 2921150 * 2 ^ 59
def prefixEnd_2921150 : Nat := 4983230072969 + 3 ^ 40 * 2921150 * 2
def baseEnd_2921150 : Nat := 999969342587567480593921

theorem tailTrace_2921150 : CollatzResearch.WordTrace tailWord_2921150 prefixEnd_2921150 999969342587567480593921 := by
  unfold tailWord_2921150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317886670897489693279113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71028728911453278364155269 13317886670897489693279113)
  ·
    refine ⟨9988415003173117269959335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13317886670897489693279113 9988415003173117269959335)
    ·
      refine ⟨14982622504759675904939003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988415003173117269959335 14982622504759675904939003)
      ·
        refine ⟨22473933757139513857408505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982622504759675904939003 22473933757139513857408505)
        ·
          refine ⟨16855450317854635393056379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22473933757139513857408505 16855450317854635393056379)
          ·
            refine ⟨25283175476781953089584569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16855450317854635393056379 25283175476781953089584569)
            ·
              refine ⟨18962381607586464817188427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25283175476781953089584569 18962381607586464817188427)
              ·
                refine ⟨28443572411379697225782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18962381607586464817188427 28443572411379697225782641)
                ·
                  refine ⟨21332679308534772919336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28443572411379697225782641 21332679308534772919336981)
                  ·
                    refine ⟨999969342587567480593921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21332679308534772919336981 999969342587567480593921)
                    ·
                      rfl

theorem cell22_2921150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2921150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921150 prefixEnd_2921150 := by exact prefixLift 2921150
  have htrace : WordTrace (prefixWord ++ tailWord_2921150) baseStart_2921150 baseEnd_2921150 := by
    simpa [prefixWord, tailWord_2921150, baseEnd_2921150] using wordTrace_append hprefix tailTrace_2921150
  have hstable : (prefixWord ++ tailWord_2921150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921150).length < 2 ^ (prefixWord ++ tailWord_2921150).sum := by decide
  have hdescent : baseEnd_2921150 < baseStart_2921150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921152 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_2921152 : Nat := 118140960795 + 2921152 * 2 ^ 59
def prefixEnd_2921152 : Nat := 4983230072969 + 3 ^ 40 * 2921152 * 2
def baseEnd_2921152 : Nat := 999970027228440142043915

theorem tailTrace_2921152 : CollatzResearch.WordTrace tailWord_2921152 prefixEnd_2921152 999970027228440142043915 := by
  unfold tailWord_2921152
  simp only [CollatzResearch.WordTrace]
  refine ⟨53271583156586335943902855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71028777542115114591870473 53271583156586335943902855)
  ·
    refine ⟨79907374734879503915854283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53271583156586335943902855 79907374734879503915854283)
    ·
      refine ⟨119861062102319255873781425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79907374734879503915854283 119861062102319255873781425)
      ·
        refine ⟨89895796576739441905336069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119861062102319255873781425 89895796576739441905336069)
        ·
          refine ⟨16855461858138645357250513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89895796576739441905336069 16855461858138645357250513)
          ·
            refine ⟨12641596393603984017937885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16855461858138645357250513 12641596393603984017937885)
            ·
              refine ⟨4740598647601494006726707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12641596393603984017937885 4740598647601494006726707)
              ·
                refine ⟨7110897971402241010090061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740598647601494006726707 7110897971402241010090061)
                ·
                  refine ⟨2666586739275840378783773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7110897971402241010090061 2666586739275840378783773)
                  ·
                    refine ⟨999970027228440142043915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666586739275840378783773 999970027228440142043915)
                    ·
                      rfl

theorem cell22_2921152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_2921152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921152 prefixEnd_2921152 := by exact prefixLift 2921152
  have htrace : WordTrace (prefixWord ++ tailWord_2921152) baseStart_2921152 baseEnd_2921152 := by
    simpa [prefixWord, tailWord_2921152, baseEnd_2921152] using wordTrace_append hprefix tailTrace_2921152
  have hstable : (prefixWord ++ tailWord_2921152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921152).length < 2 ^ (prefixWord ++ tailWord_2921152).sum := by decide
  have hdescent : baseEnd_2921152 < baseStart_2921152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921158 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2921158 : Nat := 118140960795 + 2921158 * 2 ^ 59
def prefixEnd_2921158 : Nat := 4983230072969 + 3 ^ 40 * 2921158 * 2
def baseEnd_2921158 : Nat := 999972081151058126393897

theorem tailTrace_2921158 : CollatzResearch.WordTrace tailWord_2921158 prefixEnd_2921158 999972081151058126393897 := by
  unfold tailWord_2921158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329480785973466716016379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71028923434100623275016085 3329480785973466716016379)
  ·
    refine ⟨4994221178960200074024569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3329480785973466716016379 4994221178960200074024569)
    ·
      refine ⟨3745665884220150055518427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994221178960200074024569 3745665884220150055518427)
      ·
        refine ⟨5618498826330225083277641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745665884220150055518427 5618498826330225083277641)
        ·
          refine ⟨4213874119747668812458231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618498826330225083277641 4213874119747668812458231)
          ·
            refine ⟨6320811179621503218687347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213874119747668812458231 6320811179621503218687347)
            ·
              refine ⟨9481216769432254828031021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320811179621503218687347 9481216769432254828031021)
              ·
                refine ⟨3555456288537095560511633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9481216769432254828031021 3555456288537095560511633)
                ·
                  refine ⟨2666592216402821670383725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555456288537095560511633 2666592216402821670383725)
                  ·
                    refine ⟨999972081151058126393897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666592216402821670383725 999972081151058126393897)
                    ·
                      rfl

theorem cell22_2921158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2921158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921158 prefixEnd_2921158 := by exact prefixLift 2921158
  have htrace : WordTrace (prefixWord ++ tailWord_2921158) baseStart_2921158 baseEnd_2921158 := by
    simpa [prefixWord, tailWord_2921158, baseEnd_2921158] using wordTrace_append hprefix tailTrace_2921158
  have hstable : (prefixWord ++ tailWord_2921158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921158).length < 2 ^ (prefixWord ++ tailWord_2921158).sum := by decide
  have hdescent : baseEnd_2921158 < baseStart_2921158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921225 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_2921225 : Nat := 118140960795 + 2921225 * 2 ^ 59
def prefixEnd_2921225 : Nat := 4983230072969 + 3 ^ 40 * 2921225 * 2
def baseEnd_2921225 : Nat := 999995016620292284968691

theorem tailTrace_2921225 : CollatzResearch.WordTrace tailWord_2921225 prefixEnd_2921225 999995016620292284968691 := by
  unfold tailWord_2921225
  simp only [CollatzResearch.WordTrace]
  refine ⟨106545828841908205355213129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71030552561272136903475419 106545828841908205355213129)
  ·
    refine ⟨79909371631431154016409847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106545828841908205355213129 79909371631431154016409847)
    ·
      refine ⟨119864057447146731024614771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79909371631431154016409847 119864057447146731024614771)
      ·
        refine ⟨179796086170720096536922157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119864057447146731024614771 179796086170720096536922157)
        ·
          refine ⟨67423532314020036201345809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179796086170720096536922157 67423532314020036201345809)
          ·
            refine ⟨50567649235515027151009357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67423532314020036201345809 50567649235515027151009357)
            ·
              refine ⟨18962868463318135181628509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50567649235515027151009357 18962868463318135181628509)
              ·
                refine ⟨7111075673744300693110691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18962868463318135181628509 7111075673744300693110691)
                ·
                  refine ⟨10666613510616451039666037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7111075673744300693110691 10666613510616451039666037)
                  ·
                    refine ⟨999995016620292284968691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10666613510616451039666037 999995016620292284968691)
                    ·
                      rfl

theorem cell22_2921225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_2921225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921225 prefixEnd_2921225 := by exact prefixLift 2921225
  have htrace : WordTrace (prefixWord ++ tailWord_2921225) baseStart_2921225 baseEnd_2921225 := by
    simpa [prefixWord, tailWord_2921225, baseEnd_2921225] using wordTrace_append hprefix tailTrace_2921225
  have hstable : (prefixWord ++ tailWord_2921225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921225).length < 2 ^ (prefixWord ++ tailWord_2921225).sum := by decide
  have hdescent : baseEnd_2921225 < baseStart_2921225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921242 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_2921242 : Nat := 118140960795 + 2921242 * 2 ^ 59
def prefixEnd_2921242 : Nat := 4983230072969 + 3 ^ 40 * 2921242 * 2
def baseEnd_2921242 : Nat := 1000000836067709907293639

theorem tailTrace_2921242 : CollatzResearch.WordTrace tailWord_2921242 prefixEnd_2921242 1000000836067709907293639 := by
  unfold tailWord_2921242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26636612220711654314645495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71030965921897744839054653 26636612220711654314645495)
  ·
    refine ⟨39954918331067481471968243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26636612220711654314645495 39954918331067481471968243)
    ·
      refine ⟨59932377496601222207952365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39954918331067481471968243 59932377496601222207952365)
      ·
        refine ⟨22474641561225458327982137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59932377496601222207952365 22474641561225458327982137)
        ·
          refine ⟨16855981170919093745986603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22474641561225458327982137 16855981170919093745986603)
          ·
            refine ⟨25283971756378640618979905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16855981170919093745986603 25283971756378640618979905)
            ·
              refine ⟨18962978817283980464234929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25283971756378640618979905 18962978817283980464234929)
              ·
                refine ⟨14222234112962985348176197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18962978817283980464234929 14222234112962985348176197)
                ·
                  refine ⟨2666668896180559752783037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14222234112962985348176197 2666668896180559752783037)
                  ·
                    refine ⟨1000000836067709907293639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666668896180559752783037 1000000836067709907293639)
                    ·
                      rfl

theorem cell22_2921242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_2921242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921242 prefixEnd_2921242 := by exact prefixLift 2921242
  have htrace : WordTrace (prefixWord ++ tailWord_2921242) baseStart_2921242 baseEnd_2921242 := by
    simpa [prefixWord, tailWord_2921242, baseEnd_2921242] using wordTrace_append hprefix tailTrace_2921242
  have hstable : (prefixWord ++ tailWord_2921242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921242).length < 2 ^ (prefixWord ++ tailWord_2921242).sum := by decide
  have hdescent : baseEnd_2921242 < baseStart_2921242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921244 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_2921244 : Nat := 118140960795 + 2921244 * 2 ^ 59
def prefixEnd_2921244 : Nat := 4983230072969 + 3 ^ 40 * 2921244 * 2
def baseEnd_2921244 : Nat := 333333840236194189581211

theorem tailTrace_2921244 : CollatzResearch.WordTrace tailWord_2921244 prefixEnd_2921244 333333840236194189581211 := by
  unfold tailWord_2921244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53273260914419685800077393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71031014552559581066769857 53273260914419685800077393)
  ·
    refine ⟨39954945685814764350058045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53273260914419685800077393 39954945685814764350058045)
    ·
      refine ⟨14983104632180536631271767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39954945685814764350058045 14983104632180536631271767)
      ·
        refine ⟨22474656948270804946907651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14983104632180536631271767 22474656948270804946907651)
        ·
          refine ⟨33711985422406207420361477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22474656948270804946907651 33711985422406207420361477)
          ·
            refine ⟨6320997266701163891317777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33711985422406207420361477 6320997266701163891317777)
            ·
              refine ⟨4740747950025872918488333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320997266701163891317777 4740747950025872918488333)
              ·
                refine ⟨1777780481259702344433125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4740747950025872918488333 1777780481259702344433125)
                ·
                  refine ⟨333333840236194189581211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777780481259702344433125 333333840236194189581211)
                  ·
                    rfl

theorem cell22_2921244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_2921244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921244 prefixEnd_2921244 := by exact prefixLift 2921244
  have htrace : WordTrace (prefixWord ++ tailWord_2921244) baseStart_2921244 baseEnd_2921244 := by
    simpa [prefixWord, tailWord_2921244, baseEnd_2921244] using wordTrace_append hprefix tailTrace_2921244
  have hstable : (prefixWord ++ tailWord_2921244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921244).length < 2 ^ (prefixWord ++ tailWord_2921244).sum := by decide
  have hdescent : baseEnd_2921244 < baseStart_2921244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921261 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2921261 : Nat := 118140960795 + 2921261 * 2 ^ 59
def prefixEnd_2921261 : Nat := 4983230072969 + 3 ^ 40 * 2921261 * 2
def baseEnd_2921261 : Nat := 333335780052000063689527

theorem tailTrace_2921261 : CollatzResearch.WordTrace tailWord_2921261 prefixEnd_2921261 333335780052000063689527 := by
  unfold tailWord_2921261
  simp only [CollatzResearch.WordTrace]
  refine ⟨106547141869777783503523637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71031427913185189002349091 106547141869777783503523637)
  ·
    refine ⟨9988794550291667203455341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106547141869777783503523637 9988794550291667203455341)
    ·
      refine ⟨3745797956359375201295753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9988794550291667203455341 3745797956359375201295753)
      ·
        refine ⟨2809348467269531400971815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745797956359375201295753 2809348467269531400971815)
        ·
          refine ⟨4214022700904297101457723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809348467269531400971815 4214022700904297101457723)
          ·
            refine ⟨6321034051356445652186585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214022700904297101457723 6321034051356445652186585)
            ·
              refine ⟨4740775538517334239139939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6321034051356445652186585 4740775538517334239139939)
              ·
                refine ⟨7111163307776001358709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740775538517334239139939 7111163307776001358709909)
                ·
                  refine ⟨333335780052000063689527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7111163307776001358709909 333335780052000063689527)
                  ·
                    rfl

theorem cell22_2921261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2921261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921261 prefixEnd_2921261 := by exact prefixLift 2921261
  have htrace : WordTrace (prefixWord ++ tailWord_2921261) baseStart_2921261 baseEnd_2921261 := by
    simpa [prefixWord, tailWord_2921261, baseEnd_2921261] using wordTrace_append hprefix tailTrace_2921261
  have hstable : (prefixWord ++ tailWord_2921261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921261).length < 2 ^ (prefixWord ++ tailWord_2921261).sum := by decide
  have hdescent : baseEnd_2921261 < baseStart_2921261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921347 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_2921347 : Nat := 118140960795 + 2921347 * 2 ^ 59
def prefixEnd_2921347 : Nat := 4983230072969 + 3 ^ 40 * 2921347 * 2
def baseEnd_2921347 : Nat := 1000036779713524633418317

theorem tailTrace_2921347 : CollatzResearch.WordTrace tailWord_2921347 prefixEnd_2921347 1000036779713524633418317 := by
  unfold tailWord_2921347
  simp only [CollatzResearch.WordTrace]
  refine ⟨106550278547466220191154295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71033519031644146794102863 106550278547466220191154295)
  ·
    refine ⟨159825417821199330286731443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106550278547466220191154295 159825417821199330286731443)
    ·
      refine ⟨239738126731798995430097165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159825417821199330286731443 239738126731798995430097165)
      ·
        refine ⟨89901797524424623286286437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239738126731798995430097165 89901797524424623286286437)
        ·
          refine ⟨16856587035829616866178707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89901797524424623286286437 16856587035829616866178707)
          ·
            refine ⟨25284880553744425299268061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16856587035829616866178707 25284880553744425299268061)
            ·
              refine ⟨9481830207654159487225523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25284880553744425299268061 9481830207654159487225523)
              ·
                refine ⟨14222745311481239230838285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9481830207654159487225523 14222745311481239230838285)
                ·
                  refine ⟨5333529491805464711564357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14222745311481239230838285 5333529491805464711564357)
                  ·
                    refine ⟨1000036779713524633418317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333529491805464711564357 1000036779713524633418317)
                    ·
                      rfl

theorem cell22_2921347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_2921347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921347 prefixEnd_2921347 := by exact prefixLift 2921347
  have htrace : WordTrace (prefixWord ++ tailWord_2921347) baseStart_2921347 baseEnd_2921347 := by
    simpa [prefixWord, tailWord_2921347, baseEnd_2921347] using wordTrace_append hprefix tailTrace_2921347
  have hstable : (prefixWord ++ tailWord_2921347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921347).length < 2 ^ (prefixWord ++ tailWord_2921347).sum := by decide
  have hdescent : baseEnd_2921347 < baseStart_2921347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921360 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2921360 : Nat := 118140960795 + 2921360 * 2 ^ 59
def prefixEnd_2921360 : Nat := 4983230072969 + 3 ^ 40 * 2921360 * 2
def baseEnd_2921360 : Nat := 1000041229879196932843277

theorem tailTrace_2921360 : CollatzResearch.WordTrace tailWord_2921360 prefixEnd_2921360 1000041229879196932843277 := by
  unfold tailWord_2921360
  simp only [CollatzResearch.WordTrace]
  refine ⟨53275376348209561705688767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71033835130946082274251689 53275376348209561705688767)
  ·
    refine ⟨79913064522314342558533151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53275376348209561705688767 79913064522314342558533151)
    ·
      refine ⟨119869596783471513837799727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79913064522314342558533151 119869596783471513837799727)
      ·
        refine ⟨179804395175207270756699591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119869596783471513837799727 179804395175207270756699591)
        ·
          refine ⟨269706592762810906135049387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179804395175207270756699591 269706592762810906135049387)
          ·
            refine ⟨404559889144216359202574081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269706592762810906135049387 404559889144216359202574081)
            ·
              refine ⟨303419916858162269401930561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404559889144216359202574081 303419916858162269401930561)
              ·
                refine ⟨227564937643621702051447921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303419916858162269401930561 227564937643621702051447921)
                ·
                  refine ⟨170673703232716276538585941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227564937643621702051447921 170673703232716276538585941)
                  ·
                    refine ⟨1000041229879196932843277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170673703232716276538585941 1000041229879196932843277)
                    ·
                      rfl

theorem cell22_2921360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2921360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921360 prefixEnd_2921360 := by exact prefixLift 2921360
  have htrace : WordTrace (prefixWord ++ tailWord_2921360) baseStart_2921360 baseEnd_2921360 := by
    simpa [prefixWord, tailWord_2921360, baseEnd_2921360] using wordTrace_append hprefix tailTrace_2921360
  have hstable : (prefixWord ++ tailWord_2921360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921360).length < 2 ^ (prefixWord ++ tailWord_2921360).sum := by decide
  have hdescent : baseEnd_2921360 < baseStart_2921360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921372 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2921372 : Nat := 118140960795 + 2921372 * 2 ^ 59
def prefixEnd_2921372 : Nat := 4983230072969 + 3 ^ 40 * 2921372 * 2
def baseEnd_2921372 : Nat := 1000045337724432901543241

theorem tailTrace_2921372 : CollatzResearch.WordTrace tailWord_2921372 prefixEnd_2921372 1000045337724432901543241 := by
  unfold tailWord_2921372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53275595186187824730407185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71034126914917099640542913 53275595186187824730407185)
  ·
    refine ⟨39956696389640868547805389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53275595186187824730407185 39956696389640868547805389)
    ·
      refine ⟨14983761146115325705427021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39956696389640868547805389 14983761146115325705427021)
      ·
        refine ⟨5618910429793247139535133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14983761146115325705427021 5618910429793247139535133)
        ·
          refine ⟨2107091411172467677325675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5618910429793247139535133 2107091411172467677325675)
          ·
            refine ⟨3160637116758701515988513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107091411172467677325675 3160637116758701515988513)
            ·
              refine ⟨2370477837569026136991385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160637116758701515988513 2370477837569026136991385)
              ·
                refine ⟨1777858378176769602743539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370477837569026136991385 1777858378176769602743539)
                ·
                  refine ⟨2666787567265154404115309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777858378176769602743539 2666787567265154404115309)
                  ·
                    refine ⟨1000045337724432901543241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666787567265154404115309 1000045337724432901543241)
                    ·
                      rfl

theorem cell22_2921372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2921372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921372 prefixEnd_2921372 := by exact prefixLift 2921372
  have htrace : WordTrace (prefixWord ++ tailWord_2921372) baseStart_2921372 baseEnd_2921372 := by
    simpa [prefixWord, tailWord_2921372, baseEnd_2921372] using wordTrace_append hprefix tailTrace_2921372
  have hstable : (prefixWord ++ tailWord_2921372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921372).length < 2 ^ (prefixWord ++ tailWord_2921372).sum := by decide
  have hdescent : baseEnd_2921372 < baseStart_2921372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921396 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2921396 : Nat := 118140960795 + 2921396 * 2 ^ 59
def prefixEnd_2921396 : Nat := 4983230072969 + 3 ^ 40 * 2921396 * 2
def baseEnd_2921396 : Nat := 333351184471634946314389

theorem tailTrace_2921396 : CollatzResearch.WordTrace tailWord_2921396 prefixEnd_2921396 333351184471634946314389 := by
  unfold tailWord_2921396
  simp only [CollatzResearch.WordTrace]
  refine ⟨53276032862144350779844021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71034710482859134373125361 53276032862144350779844021)
  ·
    refine ⟨4994628080826032885610377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53276032862144350779844021 4994628080826032885610377)
    ·
      refine ⟨3745971060619524664207783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994628080826032885610377 3745971060619524664207783)
      ·
        refine ⟨5618956590929286996311675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745971060619524664207783 5618956590929286996311675)
        ·
          refine ⟨8428434886393930494467513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618956590929286996311675 8428434886393930494467513)
          ·
            refine ⟨6321326164795447870850635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8428434886393930494467513 6321326164795447870850635)
            ·
              refine ⟨9481989247193171806275953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321326164795447870850635 9481989247193171806275953)
              ·
                refine ⟨7111491935394878854706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9481989247193171806275953 7111491935394878854706965)
                ·
                  refine ⟨333351184471634946314389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7111491935394878854706965 333351184471634946314389)
                  ·
                    rfl

theorem cell22_2921396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2921396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921396 prefixEnd_2921396 := by exact prefixLift 2921396
  have htrace : WordTrace (prefixWord ++ tailWord_2921396) baseStart_2921396 baseEnd_2921396 := by
    simpa [prefixWord, tailWord_2921396, baseEnd_2921396] using wordTrace_append hprefix tailTrace_2921396
  have hstable : (prefixWord ++ tailWord_2921396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921396).length < 2 ^ (prefixWord ++ tailWord_2921396).sum := by decide
  have hdescent : baseEnd_2921396 < baseStart_2921396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921428 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2921428 : Nat := 118140960795 + 2921428 * 2 ^ 59
def prefixEnd_2921428 : Nat := 4983230072969 + 3 ^ 40 * 2921428 * 2
def baseEnd_2921428 : Nat := 1000064507668867422143069

theorem tailTrace_2921428 : CollatzResearch.WordTrace tailWord_2921428 prefixEnd_2921428 1000064507668867422143069 := by
  unfold tailWord_2921428
  simp only [CollatzResearch.WordTrace]
  refine ⟨53276616430086385512426469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71035488573448514016568625 53276616430086385512426469)
  ·
    refine ⟨9989365580641197283579963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53276616430086385512426469 9989365580641197283579963)
    ·
      refine ⟨14984048370961795925369945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9989365580641197283579963 14984048370961795925369945)
      ·
        refine ⟨11238036278221346944027459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14984048370961795925369945 11238036278221346944027459)
        ·
          refine ⟨16857054417332020416041189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238036278221346944027459 16857054417332020416041189)
          ·
            refine ⟨3160697703249753828007723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16857054417332020416041189 3160697703249753828007723)
            ·
              refine ⟨4741046554874630742011585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160697703249753828007723 4741046554874630742011585)
              ·
                refine ⟨3555784916155973056508689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741046554874630742011585 3555784916155973056508689)
                ·
                  refine ⟨2666838687116979792381517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555784916155973056508689 2666838687116979792381517)
                  ·
                    refine ⟨1000064507668867422143069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666838687116979792381517 1000064507668867422143069)
                    ·
                      rfl

theorem cell22_2921428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2921428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921428 prefixEnd_2921428 := by exact prefixLift 2921428
  have htrace : WordTrace (prefixWord ++ tailWord_2921428) baseStart_2921428 baseEnd_2921428 := by
    simpa [prefixWord, tailWord_2921428, baseEnd_2921428] using wordTrace_append hprefix tailTrace_2921428
  have hstable : (prefixWord ++ tailWord_2921428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921428).length < 2 ^ (prefixWord ++ tailWord_2921428).sum := by decide
  have hdescent : baseEnd_2921428 < baseStart_2921428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921445 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_2921445 : Nat := 118140960795 + 2921445 * 2 ^ 59
def prefixEnd_2921445 : Nat := 4983230072969 + 3 ^ 40 * 2921445 * 2
def baseEnd_2921445 : Nat := 1000070327116285044468017

theorem tailTrace_2921445 : CollatzResearch.WordTrace tailWord_2921445 prefixEnd_2921445 1000070327116285044468017 := by
  unfold tailWord_2921445
  simp only [CollatzResearch.WordTrace]
  refine ⟨106553852901111182928221789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71035901934074121952147859 106553852901111182928221789)
  ·
    refine ⟨39957694837916693598083171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106553852901111182928221789 39957694837916693598083171)
    ·
      refine ⟨59936542256875040397124757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39957694837916693598083171 59936542256875040397124757)
      ·
        refine ⟨2809525418291017518615223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59936542256875040397124757 2809525418291017518615223)
        ·
          refine ⟨4214288127436526277922835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809525418291017518615223 4214288127436526277922835)
          ·
            refine ⟨6321432191154789416884253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214288127436526277922835 6321432191154789416884253)
            ·
              refine ⟨2370537071683046031331595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6321432191154789416884253 2370537071683046031331595)
              ·
                refine ⟨3555805607524569046997393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370537071683046031331595 3555805607524569046997393)
                ·
                  refine ⟨2666854205643426785248045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555805607524569046997393 2666854205643426785248045)
                  ·
                    refine ⟨1000070327116285044468017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666854205643426785248045 1000070327116285044468017)
                    ·
                      rfl

theorem cell22_2921445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_2921445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921445 prefixEnd_2921445 := by exact prefixLift 2921445
  have htrace : WordTrace (prefixWord ++ tailWord_2921445) baseStart_2921445 baseEnd_2921445 := by
    simpa [prefixWord, tailWord_2921445, baseEnd_2921445] using wordTrace_append hprefix tailTrace_2921445
  have hstable : (prefixWord ++ tailWord_2921445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921445).length < 2 ^ (prefixWord ++ tailWord_2921445).sum := by decide
  have hdescent : baseEnd_2921445 < baseStart_2921445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921458 : List Nat := [3, 2, 1, 5, 1, 2, 2, 6]
def baseStart_2921458 : Nat := 118140960795 + 2921458 * 2 ^ 59
def prefixEnd_2921458 : Nat := 4983230072969 + 3 ^ 40 * 2921458 * 2
def baseEnd_2921458 : Nat := 111119419697995260432553

theorem tailTrace_2921458 : CollatzResearch.WordTrace tailWord_2921458 prefixEnd_2921458 111119419697995260432553 := by
  unfold tailWord_2921458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26638581762516021537111257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71036218033376057432296685 26638581762516021537111257)
  ·
    refine ⟨19978936321887016152833443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26638581762516021537111257 19978936321887016152833443)
    ·
      refine ⟨29968404482830524229250165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19978936321887016152833443 29968404482830524229250165)
      ·
        refine ⟨2809537920265361646492203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29968404482830524229250165 2809537920265361646492203)
        ·
          refine ⟨4214306880398042469738305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809537920265361646492203 4214306880398042469738305)
          ·
            refine ⟨3160730160298531852303729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214306880398042469738305 3160730160298531852303729)
            ·
              refine ⟨2370547620223898889227797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160730160298531852303729 2370547620223898889227797)
              ·
                refine ⟨111119419697995260432553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2370547620223898889227797 111119419697995260432553)
                ·
                  rfl

theorem cell22_2921458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_2921458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921458 prefixEnd_2921458 := by exact prefixLift 2921458
  have htrace : WordTrace (prefixWord ++ tailWord_2921458) baseStart_2921458 baseEnd_2921458 := by
    simpa [prefixWord, tailWord_2921458, baseEnd_2921458] using wordTrace_append hprefix tailTrace_2921458
  have hstable : (prefixWord ++ tailWord_2921458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921458).length < 2 ^ (prefixWord ++ tailWord_2921458).sum := by decide
  have hdescent : baseEnd_2921458 < baseStart_2921458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921473 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2921473 : Nat := 118140960795 + 2921473 * 2 ^ 59
def prefixEnd_2921473 : Nat := 4983230072969 + 3 ^ 40 * 2921473 * 2
def baseEnd_2921473 : Nat := 1000079912088502304767931

theorem tailTrace_2921473 : CollatzResearch.WordTrace tailWord_2921473 prefixEnd_2921473 1000079912088502304767931 := by
  unfold tailWord_2921473
  simp only [CollatzResearch.WordTrace]
  refine ⟨106554874145009743710241073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71036582763339829140160715 106554874145009743710241073)
  ·
    refine ⟨79916155608757307782680805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106554874145009743710241073 79916155608757307782680805)
    ·
      refine ⟨14984279176641995209252651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79916155608757307782680805 14984279176641995209252651)
      ·
        refine ⟨22476418764962992813878977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14984279176641995209252651 22476418764962992813878977)
        ·
          refine ⟨16857314073722244610409233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22476418764962992813878977 16857314073722244610409233)
          ·
            refine ⟨12642985555291683457806925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16857314073722244610409233 12642985555291683457806925)
            ·
              refine ⟨4741119583234381296677597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12642985555291683457806925 4741119583234381296677597)
              ·
                refine ⟨1777919843712892986254099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741119583234381296677597 1777919843712892986254099)
                ·
                  refine ⟨2666879765569339479381149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777919843712892986254099 2666879765569339479381149)
                  ·
                    refine ⟨1000079912088502304767931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666879765569339479381149 1000079912088502304767931)
                    ·
                      rfl

theorem cell22_2921473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2921473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921473 prefixEnd_2921473 := by exact prefixLift 2921473
  have htrace : WordTrace (prefixWord ++ tailWord_2921473) baseStart_2921473 baseEnd_2921473 := by
    simpa [prefixWord, tailWord_2921473, baseEnd_2921473] using wordTrace_append hprefix tailTrace_2921473
  have hstable : (prefixWord ++ tailWord_2921473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921473).length < 2 ^ (prefixWord ++ tailWord_2921473).sum := by decide
  have hdescent : baseEnd_2921473 < baseStart_2921473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921529 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_2921529 : Nat := 118140960795 + 2921529 * 2 ^ 59
def prefixEnd_2921529 : Nat := 4983230072969 + 3 ^ 40 * 2921529 * 2
def baseEnd_2921529 : Nat := 1000099082032936825367759

theorem tailTrace_2921529 : CollatzResearch.WordTrace tailWord_2921529 prefixEnd_2921529 1000099082032936825367759 := by
  unfold tailWord_2921529
  simp only [CollatzResearch.WordTrace]
  refine ⟨106556916632806865274279641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71037944421871243516186427 106556916632806865274279641)
  ·
    refine ⟨79917687474605148955709731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106556916632806865274279641 79917687474605148955709731)
    ·
      refine ⟨119876531211907723433564597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79917687474605148955709731 119876531211907723433564597)
      ·
        refine ⟨11238424801116349071896681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119876531211907723433564597 11238424801116349071896681)
        ·
          refine ⟨8428818600837261803922511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11238424801116349071896681 8428818600837261803922511)
          ·
            refine ⟨12643227901255892705883767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428818600837261803922511 12643227901255892705883767)
            ·
              refine ⟨18964841851883839058825651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643227901255892705883767 18964841851883839058825651)
              ·
                refine ⟨28447262777825758588238477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18964841851883839058825651 28447262777825758588238477)
                ·
                  refine ⟨10667723541684659470589429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28447262777825758588238477 10667723541684659470589429)
                  ·
                    refine ⟨1000099082032936825367759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10667723541684659470589429 1000099082032936825367759)
                    ·
                      rfl

theorem cell22_2921529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_2921529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921529 prefixEnd_2921529 := by exact prefixLift 2921529
  have htrace : WordTrace (prefixWord ++ tailWord_2921529) baseStart_2921529 baseEnd_2921529 := by
    simpa [prefixWord, tailWord_2921529, baseEnd_2921529] using wordTrace_append hprefix tailTrace_2921529
  have hstable : (prefixWord ++ tailWord_2921529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921529).length < 2 ^ (prefixWord ++ tailWord_2921529).sum := by decide
  have hdescent : baseEnd_2921529 < baseStart_2921529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921533 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2921533 : Nat := 118140960795 + 2921533 * 2 ^ 59
def prefixEnd_2921533 : Nat := 4983230072969 + 3 ^ 40 * 2921533 * 2
def baseEnd_2921533 : Nat := 1000100451314682148267747

theorem tailTrace_2921533 : CollatzResearch.WordTrace tailWord_2921533 prefixEnd_2921533 1000100451314682148267747 := by
  unfold tailWord_2921533
  simp only [CollatzResearch.WordTrace]
  refine ⟨106557062524792373957425253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71038041683194915971616835 106557062524792373957425253)
  ·
    refine ⟨19979449223398570117017235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106557062524792373957425253 19979449223398570117017235)
    ·
      refine ⟨29969173835097855175525853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19979449223398570117017235 29969173835097855175525853)
      ·
        refine ⟨11238440188161695690822195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29969173835097855175525853 11238440188161695690822195)
        ·
          refine ⟨16857660282242543536233293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238440188161695690822195 16857660282242543536233293)
          ·
            refine ⟨6321622605840953826087485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16857660282242543536233293 6321622605840953826087485)
            ·
              refine ⟨2370608477190357684782807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6321622605840953826087485 2370608477190357684782807)
              ·
                refine ⟨3555912715785536527174211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370608477190357684782807 3555912715785536527174211)
                ·
                  refine ⟨5333869073678304790761317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555912715785536527174211 5333869073678304790761317)
                  ·
                    refine ⟨1000100451314682148267747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333869073678304790761317 1000100451314682148267747)
                    ·
                      rfl

theorem cell22_2921533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2921533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921533 prefixEnd_2921533 := by exact prefixLift 2921533
  have htrace : WordTrace (prefixWord ++ tailWord_2921533) baseStart_2921533 baseEnd_2921533 := by
    simpa [prefixWord, tailWord_2921533, baseEnd_2921533] using wordTrace_append hprefix tailTrace_2921533
  have hstable : (prefixWord ++ tailWord_2921533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921533).length < 2 ^ (prefixWord ++ tailWord_2921533).sum := by decide
  have hdescent : baseEnd_2921533 < baseStart_2921533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921544 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2921544 : Nat := 118140960795 + 2921544 * 2 ^ 59
def prefixEnd_2921544 : Nat := 4983230072969 + 3 ^ 40 * 2921544 * 2
def baseEnd_2921544 : Nat := 1000104216839481786242713

theorem tailTrace_2921544 : CollatzResearch.WordTrace tailWord_2921544 prefixEnd_2921544 1000104216839481786242713 := by
  unfold tailWord_2921544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53278731863876261418037843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71038309151835015224050457 53278731863876261418037843)
  ·
    refine ⟨79918097795814392127056765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53278731863876261418037843 79918097795814392127056765)
    ·
      refine ⟨29969286673430397047646287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79918097795814392127056765 29969286673430397047646287)
      ·
        refine ⟨44953930010145595571469431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29969286673430397047646287 44953930010145595571469431)
        ·
          refine ⟨67430895015218393357204147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44953930010145595571469431 67430895015218393357204147)
          ·
            refine ⟨101146342522827590035806221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67430895015218393357204147 101146342522827590035806221)
            ·
              refine ⟨37929878446060346263427333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101146342522827590035806221 37929878446060346263427333)
              ·
                refine ⟨7111852208636314924392625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37929878446060346263427333 7111852208636314924392625)
                ·
                  refine ⟨5333889156477236193294469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111852208636314924392625 5333889156477236193294469)
                  ·
                    refine ⟨1000104216839481786242713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333889156477236193294469 1000104216839481786242713)
                    ·
                      rfl

theorem cell22_2921544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2921544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921544 prefixEnd_2921544 := by exact prefixLift 2921544
  have htrace : WordTrace (prefixWord ++ tailWord_2921544) baseStart_2921544 baseEnd_2921544 := by
    simpa [prefixWord, tailWord_2921544, baseEnd_2921544] using wordTrace_append hprefix tailTrace_2921544
  have hstable : (prefixWord ++ tailWord_2921544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921544).length < 2 ^ (prefixWord ++ tailWord_2921544).sum := by decide
  have hdescent : baseEnd_2921544 < baseStart_2921544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921546 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_2921546 : Nat := 118140960795 + 2921546 * 2 ^ 59
def prefixEnd_2921546 : Nat := 4983230072969 + 3 ^ 40 * 2921546 * 2
def baseEnd_2921546 : Nat := 1000104901480354447692707

theorem tailTrace_2921546 : CollatzResearch.WordTrace tailWord_2921546 prefixEnd_2921546 1000104901480354447692707 := by
  unfold tailWord_2921546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639384168436319294412123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71038357782496851451765661 26639384168436319294412123)
  ·
    refine ⟨39959076252654478941618185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26639384168436319294412123 39959076252654478941618185)
    ·
      refine ⟨29969307189490859206213639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39959076252654478941618185 29969307189490859206213639)
      ·
        refine ⟨44953960784236288809320459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29969307189490859206213639 44953960784236288809320459)
        ·
          refine ⟨67430941176354433213980689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44953960784236288809320459 67430941176354433213980689)
          ·
            refine ⟨50573205882265824910485517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67430941176354433213980689 50573205882265824910485517)
            ·
              refine ⟨18964952205849684341432069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50573205882265824910485517 18964952205849684341432069)
              ·
                refine ⟨3555928538596815814018513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18964952205849684341432069 3555928538596815814018513)
                ·
                  refine ⟨2666946403947611860513885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555928538596815814018513 2666946403947611860513885)
                  ·
                    refine ⟨1000104901480354447692707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666946403947611860513885 1000104901480354447692707)
                    ·
                      rfl

theorem cell22_2921546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_2921546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921546 prefixEnd_2921546 := by exact prefixLift 2921546
  have htrace : WordTrace (prefixWord ++ tailWord_2921546) baseStart_2921546 baseEnd_2921546 := by
    simpa [prefixWord, tailWord_2921546, baseEnd_2921546] using wordTrace_append hprefix tailTrace_2921546
  have hstable : (prefixWord ++ tailWord_2921546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921546).length < 2 ^ (prefixWord ++ tailWord_2921546).sum := by decide
  have hdescent : baseEnd_2921546 < baseStart_2921546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921578 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2921578 : Nat := 118140960795 + 2921578 * 2 ^ 59
def prefixEnd_2921578 : Nat := 4983230072969 + 3 ^ 40 * 2921578 * 2
def baseEnd_2921578 : Nat := 1000115855734317030892609

theorem tailTrace_2921578 : CollatzResearch.WordTrace tailWord_2921578 prefixEnd_2921578 1000115855734317030892609 := by
  unfold tailWord_2921578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639675952407336660703347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71039135873086231095208925 26639675952407336660703347)
  ·
    refine ⟨39959513928611004991055021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26639675952407336660703347 39959513928611004991055021)
    ·
      refine ⟨14984817723229126871645633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39959513928611004991055021 14984817723229126871645633)
      ·
        refine ⟨11238613292421845153734225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14984817723229126871645633 11238613292421845153734225)
        ·
          refine ⟨8428959969316383865300669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11238613292421845153734225 8428959969316383865300669)
          ·
            refine ⟨3160859988493643949487751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8428959969316383865300669 3160859988493643949487751)
            ·
              refine ⟨4741289982740465924231627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160859988493643949487751 4741289982740465924231627)
              ·
                refine ⟨7111934974110698886347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741289982740465924231627 7111934974110698886347441)
                ·
                  refine ⟨5333951230583024164760581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111934974110698886347441 5333951230583024164760581)
                  ·
                    refine ⟨1000115855734317030892609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333951230583024164760581 1000115855734317030892609)
                    ·
                      rfl

theorem cell22_2921578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2921578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921578 prefixEnd_2921578 := by exact prefixLift 2921578
  have htrace : WordTrace (prefixWord ++ tailWord_2921578) baseStart_2921578 baseEnd_2921578 := by
    simpa [prefixWord, tailWord_2921578, baseEnd_2921578] using wordTrace_append hprefix tailTrace_2921578
  have hstable : (prefixWord ++ tailWord_2921578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921578).length < 2 ^ (prefixWord ++ tailWord_2921578).sum := by decide
  have hdescent : baseEnd_2921578 < baseStart_2921578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921619 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_2921619 : Nat := 118140960795 + 2921619 * 2 ^ 59
def prefixEnd_2921619 : Nat := 4983230072969 + 3 ^ 40 * 2921619 * 2
def baseEnd_2921619 : Nat := 1000129890872206590617483

theorem tailTrace_2921619 : CollatzResearch.WordTrace tailWord_2921619 prefixEnd_2921619 1000129890872206590617483 := by
  unfold tailWord_2921619
  simp only [CollatzResearch.WordTrace]
  refine ⟨106560199202480810645055911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71040132801653873763370607 106560199202480810645055911)
  ·
    refine ⟨159840298803721215967583867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106560199202480810645055911 159840298803721215967583867)
    ·
      refine ⟨239760448205581823951375801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159840298803721215967583867 239760448205581823951375801)
      ·
        refine ⟨179820336154186367963531851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239760448205581823951375801 179820336154186367963531851)
        ·
          refine ⟨269730504231279551945297777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179820336154186367963531851 269730504231279551945297777)
          ·
            refine ⟨202297878173459663958973333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269730504231279551945297777 202297878173459663958973333)
            ·
              refine ⟨9482713039380921748076875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202297878173459663958973333 9482713039380921748076875)
              ·
                refine ⟨14224069559071382622115313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482713039380921748076875 14224069559071382622115313)
                ·
                  refine ⟨10668052169303536966586485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14224069559071382622115313 10668052169303536966586485)
                  ·
                    refine ⟨1000129890872206590617483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10668052169303536966586485 1000129890872206590617483)
                    ·
                      rfl

theorem cell22_2921619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_2921619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921619 prefixEnd_2921619 := by exact prefixLift 2921619
  have htrace : WordTrace (prefixWord ++ tailWord_2921619) baseStart_2921619 baseEnd_2921619 := by
    simpa [prefixWord, tailWord_2921619, baseEnd_2921619] using wordTrace_append hprefix tailTrace_2921619
  have hstable : (prefixWord ++ tailWord_2921619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921619).length < 2 ^ (prefixWord ++ tailWord_2921619).sum := by decide
  have hdescent : baseEnd_2921619 < baseStart_2921619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921642 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2921642 : Nat := 118140960795 + 2921642 * 2 ^ 59
def prefixEnd_2921642 : Nat := 4983230072969 + 3 ^ 40 * 2921642 * 2
def baseEnd_2921642 : Nat := 1000137764242242197292413

theorem tailTrace_2921642 : CollatzResearch.WordTrace tailWord_2921642 prefixEnd_2921642 1000137764242242197292413 := by
  unfold tailWord_2921642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26640259520349371393285795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71040692054264990382095453 26640259520349371393285795)
  ·
    refine ⟨39960389280524057089928693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26640259520349371393285795 39960389280524057089928693)
    ·
      refine ⟨3746286495049130352180815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39960389280524057089928693 3746286495049130352180815)
      ·
        refine ⟨5619429742573695528271223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746286495049130352180815 5619429742573695528271223)
        ·
          refine ⟨8429144613860543292406835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619429742573695528271223 8429144613860543292406835)
          ·
            refine ⟨12643716920790814938610253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429144613860543292406835 12643716920790814938610253)
            ·
              refine ⟨4741393845296555601978845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12643716920790814938610253 4741393845296555601978845)
              ·
                refine ⟨1778022691986208350742067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741393845296555601978845 1778022691986208350742067)
                ·
                  refine ⟨2667034037979312526113101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778022691986208350742067 2667034037979312526113101)
                  ·
                    refine ⟨1000137764242242197292413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667034037979312526113101 1000137764242242197292413)
                    ·
                      rfl

theorem cell22_2921642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2921642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921642 prefixEnd_2921642 := by exact prefixLift 2921642
  have htrace : WordTrace (prefixWord ++ tailWord_2921642) baseStart_2921642 baseEnd_2921642 := by
    simpa [prefixWord, tailWord_2921642, baseEnd_2921642] using wordTrace_append hprefix tailTrace_2921642
  have hstable : (prefixWord ++ tailWord_2921642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921642).length < 2 ^ (prefixWord ++ tailWord_2921642).sum := by decide
  have hdescent : baseEnd_2921642 < baseStart_2921642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921651 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 1, 4]
def baseStart_2921651 : Nat := 118140960795 + 2921651 * 2 ^ 59
def prefixEnd_2921651 : Nat := 4983230072969 + 3 ^ 40 * 2921651 * 2
def baseEnd_2921651 : Nat := 1000140845126169173817385

theorem tailTrace_2921651 : CollatzResearch.WordTrace tailWord_2921651 prefixEnd_2921651 1000140845126169173817385 := by
  unfold tailWord_2921651
  simp only [CollatzResearch.WordTrace]
  refine ⟨106561366338364880110220807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71040910892243253406813871 106561366338364880110220807)
  ·
    refine ⟨159842049507547320165331211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106561366338364880110220807 159842049507547320165331211)
    ·
      refine ⟨239763074261320980247996817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159842049507547320165331211 239763074261320980247996817)
      ·
        refine ⟨179822305695990735185997613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239763074261320980247996817 179822305695990735185997613)
        ·
          refine ⟨67433364635996525694749105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179822305695990735185997613 67433364635996525694749105)
          ·
            refine ⟨50575023476997394271061829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67433364635996525694749105 50575023476997394271061829)
            ·
              refine ⟨9482816901937011425824093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50575023476997394271061829 9482816901937011425824093)
              ·
                refine ⟨3556056338226379284684035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9482816901937011425824093 3556056338226379284684035)
                ·
                  refine ⟨5334084507339568927026053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556056338226379284684035 5334084507339568927026053)
                  ·
                    refine ⟨1000140845126169173817385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334084507339568927026053 1000140845126169173817385)
                    ·
                      rfl

theorem cell22_2921651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_2921651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921651 prefixEnd_2921651 := by exact prefixLift 2921651
  have htrace : WordTrace (prefixWord ++ tailWord_2921651) baseStart_2921651 baseEnd_2921651 := by
    simpa [prefixWord, tailWord_2921651, baseEnd_2921651] using wordTrace_append hprefix tailTrace_2921651
  have hstable : (prefixWord ++ tailWord_2921651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921651).length < 2 ^ (prefixWord ++ tailWord_2921651).sum := by decide
  have hdescent : baseEnd_2921651 < baseStart_2921651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921679 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_2921679 : Nat := 118140960795 + 2921679 * 2 ^ 59
def prefixEnd_2921679 : Nat := 4983230072969 + 3 ^ 40 * 2921679 * 2
def baseEnd_2921679 : Nat := 1000150430098386434117299

theorem tailTrace_2921679 : CollatzResearch.WordTrace tailWord_2921679 prefixEnd_2921679 1000150430098386434117299 := by
  unfold tailWord_2921679
  simp only [CollatzResearch.WordTrace]
  refine ⟨106562387582263440892240091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71041591721508960594826727 106562387582263440892240091)
  ·
    refine ⟨159843581373395161338360137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106562387582263440892240091 159843581373395161338360137)
    ·
      refine ⟨119882686030046371003770103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159843581373395161338360137 119882686030046371003770103)
      ·
        refine ⟨179824029045069556505655155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119882686030046371003770103 179824029045069556505655155)
        ·
          refine ⟨269736043567604334758482733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179824029045069556505655155 269736043567604334758482733)
          ·
            refine ⟨101151016337851625534431025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269736043567604334758482733 101151016337851625534431025)
            ·
              refine ⟨75863262253388719150823269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101151016337851625534431025 75863262253388719150823269)
              ·
                refine ⟨14224361672510384840779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75863262253388719150823269 14224361672510384840779363)
                ·
                  refine ⟨21336542508765577261169045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14224361672510384840779363 21336542508765577261169045)
                  ·
                    refine ⟨1000150430098386434117299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21336542508765577261169045 1000150430098386434117299)
                    ·
                      rfl

theorem cell22_2921679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_2921679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921679 prefixEnd_2921679 := by exact prefixLift 2921679
  have htrace : WordTrace (prefixWord ++ tailWord_2921679) baseStart_2921679 baseEnd_2921679 := by
    simpa [prefixWord, tailWord_2921679, baseEnd_2921679] using wordTrace_append hprefix tailTrace_2921679
  have hstable : (prefixWord ++ tailWord_2921679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921679).length < 2 ^ (prefixWord ++ tailWord_2921679).sum := by decide
  have hdescent : baseEnd_2921679 < baseStart_2921679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921685 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_2921685 : Nat := 118140960795 + 2921685 * 2 ^ 59
def prefixEnd_2921685 : Nat := 4983230072969 + 3 ^ 40 * 2921685 * 2
def baseEnd_2921685 : Nat := 1000152484021004418467281

theorem tailTrace_2921685 : CollatzResearch.WordTrace tailWord_2921685 prefixEnd_2921685 1000152484021004418467281 := by
  unfold tailWord_2921685
  simp only [CollatzResearch.WordTrace]
  refine ⟨106562606420241703916958509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71041737613494469277972339 106562606420241703916958509)
  ·
    refine ⟨39960977407590638968859441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106562606420241703916958509 39960977407590638968859441)
    ·
      refine ⟨29970733055692979226644581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39960977407590638968859441 29970733055692979226644581)
      ·
        refine ⟨5619512447942433604995859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29970733055692979226644581 5619512447942433604995859)
        ·
          refine ⟨8429268671913650407493789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619512447942433604995859 8429268671913650407493789)
          ·
            refine ⟨3160975751967618902810171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8429268671913650407493789 3160975751967618902810171)
            ·
              refine ⟨4741463627951428354215257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160975751967618902810171 4741463627951428354215257)
              ·
                refine ⟨3556097720963571265661443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741463627951428354215257 3556097720963571265661443)
                ·
                  refine ⟨5334146581445356898492165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556097720963571265661443 5334146581445356898492165)
                  ·
                    refine ⟨1000152484021004418467281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334146581445356898492165 1000152484021004418467281)
                    ·
                      rfl

theorem cell22_2921685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_2921685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921685 prefixEnd_2921685 := by exact prefixLift 2921685
  have htrace : WordTrace (prefixWord ++ tailWord_2921685) baseStart_2921685 baseEnd_2921685 := by
    simpa [prefixWord, tailWord_2921685, baseEnd_2921685] using wordTrace_append hprefix tailTrace_2921685
  have hstable : (prefixWord ++ tailWord_2921685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921685).length < 2 ^ (prefixWord ++ tailWord_2921685).sum := by decide
  have hdescent : baseEnd_2921685 < baseStart_2921685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921696 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_2921696 : Nat := 118140960795 + 2921696 * 2 ^ 59
def prefixEnd_2921696 : Nat := 4983230072969 + 3 ^ 40 * 2921696 * 2
def baseEnd_2921696 : Nat := 1000156249545804056442247

theorem tailTrace_2921696 : CollatzResearch.WordTrace tailWord_2921696 prefixEnd_2921696 1000156249545804056442247 := by
  unfold tailWord_2921696
  simp only [CollatzResearch.WordTrace]
  refine ⟨53281503811600926397804471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71042005082134568530405961 53281503811600926397804471)
  ·
    refine ⟨79922255717401389596706707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53281503811600926397804471 79922255717401389596706707)
    ·
      refine ⟨119883383576102084395060061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79922255717401389596706707 119883383576102084395060061)
      ·
        refine ⟨44956268841038281648147523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119883383576102084395060061 44956268841038281648147523)
        ·
          refine ⟨67434403261557422472221285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44956268841038281648147523 67434403261557422472221285)
          ·
            refine ⟨12643950611542016713541491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67434403261557422472221285 12643950611542016713541491)
            ·
              refine ⟨18965925917313025070312237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643950611542016713541491 18965925917313025070312237)
              ·
                refine ⟨7112222218992384401367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18965925917313025070312237 7112222218992384401367089)
                ·
                  refine ⟨5334166664244288301025317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112222218992384401367089 5334166664244288301025317)
                  ·
                    refine ⟨1000156249545804056442247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334166664244288301025317 1000156249545804056442247)
                    ·
                      rfl

theorem cell22_2921696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_2921696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921696 prefixEnd_2921696 := by exact prefixLift 2921696
  have htrace : WordTrace (prefixWord ++ tailWord_2921696) baseStart_2921696 baseEnd_2921696 := by
    simpa [prefixWord, tailWord_2921696, baseEnd_2921696] using wordTrace_append hprefix tailTrace_2921696
  have hstable : (prefixWord ++ tailWord_2921696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921696).length < 2 ^ (prefixWord ++ tailWord_2921696).sum := by decide
  have hdescent : baseEnd_2921696 < baseStart_2921696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921711 : List Nat := [1, 1, 2, 1, 8, 9]
def baseStart_2921711 : Nat := 118140960795 + 2921711 * 2 ^ 59
def prefixEnd_2921711 : Nat := 4983230072969 + 3 ^ 40 * 2921711 * 2
def baseEnd_2921711 : Nat := 12347671411757395275521

theorem tailTrace_2921711 : CollatzResearch.WordTrace tailWord_2921711 prefixEnd_2921711 12347671411757395275521 := by
  unfold tailWord_2921711
  simp only [CollatzResearch.WordTrace]
  refine ⟨106563554718147510357404987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71042369812098340238269991 106563554718147510357404987)
  ·
    refine ⟨159845332077221265536107481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106563554718147510357404987 159845332077221265536107481)
    ·
      refine ⟨119883999057915949152080611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159845332077221265536107481 119883999057915949152080611)
      ·
        refine ⟨179825998586873923728120917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119883999057915949152080611 179825998586873923728120917)
        ·
          refine ⟨2107335920939928793688917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 179825998586873923728120917 2107335920939928793688917)
          ·
            refine ⟨12347671411757395275521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2107335920939928793688917 12347671411757395275521)
            ·
              rfl

theorem cell22_2921711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 9].length) (baseStart_2921711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921711 prefixEnd_2921711 := by exact prefixLift 2921711
  have htrace : WordTrace (prefixWord ++ tailWord_2921711) baseStart_2921711 baseEnd_2921711 := by
    simpa [prefixWord, tailWord_2921711, baseEnd_2921711] using wordTrace_append hprefix tailTrace_2921711
  have hstable : (prefixWord ++ tailWord_2921711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921711).length < 2 ^ (prefixWord ++ tailWord_2921711).sum := by decide
  have hdescent : baseEnd_2921711 < baseStart_2921711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921790 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2921790 : Nat := 118140960795 + 2921790 * 2 ^ 59
def prefixEnd_2921790 : Nat := 4983230072969 + 3 ^ 40 * 2921790 * 2
def baseEnd_2921790 : Nat := 333396142555606381530653

theorem tailTrace_2921790 : CollatzResearch.WordTrace tailWord_2921790 prefixEnd_2921790 333396142555606381530653 := by
  unfold tailWord_2921790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320804510607663356191353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71044290723240871233020549 13320804510607663356191353)
  ·
    refine ⟨9990603382955747517143515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13320804510607663356191353 9990603382955747517143515)
    ·
      refine ⟨14985905074433621275715273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9990603382955747517143515 14985905074433621275715273)
      ·
        refine ⟨11239428805825215956786455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14985905074433621275715273 11239428805825215956786455)
        ·
          refine ⟨16859143208737823935179683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239428805825215956786455 16859143208737823935179683)
          ·
            refine ⟨25288714813106735902769525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16859143208737823935179683 25288714813106735902769525)
            ·
              refine ⟨2370817013728756490884643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25288714813106735902769525 2370817013728756490884643)
              ·
                refine ⟨3556225520593134736326965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370817013728756490884643 3556225520593134736326965)
                ·
                  refine ⟨333396142555606381530653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556225520593134736326965 333396142555606381530653)
                  ·
                    rfl

theorem cell22_2921790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2921790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921790 prefixEnd_2921790 := by exact prefixLift 2921790
  have htrace : WordTrace (prefixWord ++ tailWord_2921790) baseStart_2921790 baseEnd_2921790 := by
    simpa [prefixWord, tailWord_2921790, baseEnd_2921790] using wordTrace_append hprefix tailTrace_2921790
  have hstable : (prefixWord ++ tailWord_2921790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921790).length < 2 ^ (prefixWord ++ tailWord_2921790).sum := by decide
  have hdescent : baseEnd_2921790 < baseStart_2921790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921801 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 6]
def baseStart_2921801 : Nat := 118140960795 + 2921801 * 2 ^ 59
def prefixEnd_2921801 : Nat := 4983230072969 + 3 ^ 40 * 2921801 * 2
def baseEnd_2921801 : Nat := 333397397730539594188975

theorem tailTrace_2921801 : CollatzResearch.WordTrace tailWord_2921801 prefixEnd_2921801 333397397730539594188975 := by
  unfold tailWord_2921801
  simp only [CollatzResearch.WordTrace]
  refine ⟨106566837287821455728181257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71044558191880970485454171 106566837287821455728181257)
  ·
    refine ⟨79925127965866091796135943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106566837287821455728181257 79925127965866091796135943)
    ·
      refine ⟨119887691948799137694203915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79925127965866091796135943 119887691948799137694203915)
      ·
        refine ⟨179831537923198706541305873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119887691948799137694203915 179831537923198706541305873)
        ·
          refine ⟨134873653442399029905979405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179831537923198706541305873 134873653442399029905979405)
          ·
            refine ⟨50577620040899636214742277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134873653442399029905979405 50577620040899636214742277)
            ·
              refine ⟨9483303757668681790264177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50577620040899636214742277 9483303757668681790264177)
              ·
                refine ⟨7112477818251511342698133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483303757668681790264177 7112477818251511342698133)
                ·
                  refine ⟨333397397730539594188975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7112477818251511342698133 333397397730539594188975)
                  ·
                    rfl

theorem cell22_2921801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_2921801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921801 prefixEnd_2921801 := by exact prefixLift 2921801
  have htrace : WordTrace (prefixWord ++ tailWord_2921801) baseStart_2921801 baseEnd_2921801 := by
    simpa [prefixWord, tailWord_2921801, baseEnd_2921801] using wordTrace_append hprefix tailTrace_2921801
  have hstable : (prefixWord ++ tailWord_2921801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921801).length < 2 ^ (prefixWord ++ tailWord_2921801).sum := by decide
  have hdescent : baseEnd_2921801 < baseStart_2921801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921816 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2921816 : Nat := 118140960795 + 2921816 * 2 ^ 59
def prefixEnd_2921816 : Nat := 4983230072969 + 3 ^ 40 * 2921816 * 2
def baseEnd_2921816 : Nat := 1000197327998163743441879

theorem tailTrace_2921816 : CollatzResearch.WordTrace tailWord_2921816 prefixEnd_2921816 1000197327998163743441879 := by
  unfold tailWord_2921816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53283692191383556644988651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71044922921844742193318201 53283692191383556644988651)
  ·
    refine ⟨79925538287075334967482977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53283692191383556644988651 79925538287075334967482977)
    ·
      refine ⟨59944153715306501225612233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79925538287075334967482977 59944153715306501225612233)
      ·
        refine ⟨44958115286479875919209175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59944153715306501225612233 44958115286479875919209175)
        ·
          refine ⟨67437172929719813878813763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44958115286479875919209175 67437172929719813878813763)
          ·
            refine ⟨101155759394579720818220645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67437172929719813878813763 101155759394579720818220645)
            ·
              refine ⟨18966704886483697653416371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101155759394579720818220645 18966704886483697653416371)
              ·
                refine ⟨28450057329725546480124557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18966704886483697653416371 28450057329725546480124557)
                ·
                  refine ⟨10668771498647079930046709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28450057329725546480124557 10668771498647079930046709)
                  ·
                    refine ⟨1000197327998163743441879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10668771498647079930046709 1000197327998163743441879)
                    ·
                      rfl

theorem cell22_2921816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2921816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921816 prefixEnd_2921816 := by exact prefixLift 2921816
  have htrace : WordTrace (prefixWord ++ tailWord_2921816) baseStart_2921816 baseEnd_2921816 := by
    simpa [prefixWord, tailWord_2921816, baseEnd_2921816] using wordTrace_append hprefix tailTrace_2921816
  have hstable : (prefixWord ++ tailWord_2921816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921816).length < 2 ^ (prefixWord ++ tailWord_2921816).sum := by decide
  have hdescent : baseEnd_2921816 < baseStart_2921816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921861 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2921861 : Nat := 118140960795 + 2921861 * 2 ^ 59
def prefixEnd_2921861 : Nat := 4983230072969 + 3 ^ 40 * 2921861 * 2
def baseEnd_2921861 : Nat := 1000212732417798626066741

theorem tailTrace_2921861 : CollatzResearch.WordTrace tailWord_2921861 prefixEnd_2921861 1000212732417798626066741 := by
  unfold tailWord_2921861
  simp only [CollatzResearch.WordTrace]
  refine ⟨106569025667604085975365437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71046017111736057316910291 106569025667604085975365437)
  ·
    refine ⟨39963384625351532240762039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106569025667604085975365437 39963384625351532240762039)
    ·
      refine ⟨59945076938027298361143059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39963384625351532240762039 59945076938027298361143059)
      ·
        refine ⟨89917615407040947541714589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59945076938027298361143059 89917615407040947541714589)
        ·
          refine ⟨33719105777640355328142971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89917615407040947541714589 33719105777640355328142971)
          ·
            refine ⟨50578658666460532992214457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33719105777640355328142971 50578658666460532992214457)
            ·
              refine ⟨37933993999845399744160843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50578658666460532992214457 37933993999845399744160843)
              ·
                refine ⟨56900990999768099616241265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37933993999845399744160843 56900990999768099616241265)
                ·
                  refine ⟨42675743249826074712180949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56900990999768099616241265 42675743249826074712180949)
                  ·
                    refine ⟨1000212732417798626066741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42675743249826074712180949 1000212732417798626066741)
                    ·
                      rfl

theorem cell22_2921861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2921861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921861 prefixEnd_2921861 := by exact prefixLift 2921861
  have htrace : WordTrace (prefixWord ++ tailWord_2921861) baseStart_2921861 baseEnd_2921861 := by
    simpa [prefixWord, tailWord_2921861, baseEnd_2921861] using wordTrace_append hprefix tailTrace_2921861
  have hstable : (prefixWord ++ tailWord_2921861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921861).length < 2 ^ (prefixWord ++ tailWord_2921861).sum := by decide
  have hdescent : baseEnd_2921861 < baseStart_2921861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921865 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_2921865 : Nat := 118140960795 + 2921865 * 2 ^ 59
def prefixEnd_2921865 : Nat := 4983230072969 + 3 ^ 40 * 2921865 * 2
def baseEnd_2921865 : Nat := 1000214101699543948966729

theorem tailTrace_2921865 : CollatzResearch.WordTrace tailWord_2921865 prefixEnd_2921865 1000214101699543948966729 := by
  unfold tailWord_2921865
  simp only [CollatzResearch.WordTrace]
  refine ⟨106569171559589594658511049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71046114373059729772340699 106569171559589594658511049)
  ·
    refine ⟨79926878669692195993883287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106569171559589594658511049 79926878669692195993883287)
    ·
      refine ⟨119890318004538293990824931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79926878669692195993883287 119890318004538293990824931)
      ·
        refine ⟨179835477006807440986237397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119890318004538293990824931 179835477006807440986237397)
        ·
          refine ⟨4214893992347049398114939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 179835477006807440986237397 4214893992347049398114939)
          ·
            refine ⟨6322340988520574097172409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214893992347049398114939 6322340988520574097172409)
            ·
              refine ⟨4741755741390430572879307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322340988520574097172409 4741755741390430572879307)
              ·
                refine ⟨7112633612085645859318961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741755741390430572879307 7112633612085645859318961)
                ·
                  refine ⟨5334475209064234394489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112633612085645859318961 5334475209064234394489221)
                  ·
                    refine ⟨1000214101699543948966729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334475209064234394489221 1000214101699543948966729)
                    ·
                      rfl

theorem cell22_2921865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_2921865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921865 prefixEnd_2921865 := by exact prefixLift 2921865
  have htrace : WordTrace (prefixWord ++ tailWord_2921865) baseStart_2921865 baseEnd_2921865 := by
    simpa [prefixWord, tailWord_2921865, baseEnd_2921865] using wordTrace_append hprefix tailTrace_2921865
  have hstable : (prefixWord ++ tailWord_2921865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921865).length < 2 ^ (prefixWord ++ tailWord_2921865).sum := by decide
  have hdescent : baseEnd_2921865 < baseStart_2921865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921884 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_2921884 : Nat := 118140960795 + 2921884 * 2 ^ 59
def prefixEnd_2921884 : Nat := 4983230072969 + 3 ^ 40 * 2921884 * 2
def baseEnd_2921884 : Nat := 1000220605787834232741671

theorem tailTrace_2921884 : CollatzResearch.WordTrace tailWord_2921884 prefixEnd_2921884 1000220605787834232741671 := by
  unfold tailWord_2921884
  simp only [CollatzResearch.WordTrace]
  refine ⟨53284932273260380451726353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71046576364347173935635137 53284932273260380451726353)
  ·
    refine ⟨39963699204945285338794765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53284932273260380451726353 39963699204945285338794765)
    ·
      refine ⟨14986387201854482002048037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39963699204945285338794765 14986387201854482002048037)
      ·
        refine ⟨2809947600347715375384007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14986387201854482002048037 2809947600347715375384007)
        ·
          refine ⟨4214921400521573063076011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809947600347715375384007 4214921400521573063076011)
          ·
            refine ⟨6322382100782359594614017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214921400521573063076011 6322382100782359594614017)
            ·
              refine ⟨4741786575586769695960513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322382100782359594614017 4741786575586769695960513)
              ·
                refine ⟨3556339931690077271970385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741786575586769695960513 3556339931690077271970385)
                ·
                  refine ⟨2667254948767557953977789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556339931690077271970385 2667254948767557953977789)
                  ·
                    refine ⟨1000220605787834232741671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667254948767557953977789 1000220605787834232741671)
                    ·
                      rfl

theorem cell22_2921884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_2921884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921884 prefixEnd_2921884 := by exact prefixLift 2921884
  have htrace : WordTrace (prefixWord ++ tailWord_2921884) baseStart_2921884 baseEnd_2921884 := by
    simpa [prefixWord, tailWord_2921884, baseEnd_2921884] using wordTrace_append hprefix tailTrace_2921884
  have hstable : (prefixWord ++ tailWord_2921884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921884).length < 2 ^ (prefixWord ++ tailWord_2921884).sum := by decide
  have hdescent : baseEnd_2921884 < baseStart_2921884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921886 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2921886 : Nat := 118140960795 + 2921886 * 2 ^ 59
def prefixEnd_2921886 : Nat := 4983230072969 + 3 ^ 40 * 2921886 * 2
def baseEnd_2921886 : Nat := 333407096809568964730555

theorem tailTrace_2921886 : CollatzResearch.WordTrace tailWord_2921886 prefixEnd_2921886 333407096809568964730555 := by
  unfold tailWord_2921886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13321242186564189405628189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71046624995009010163350341 13321242186564189405628189)
  ·
    refine ⟨4995465819961571027110571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13321242186564189405628189 4995465819961571027110571)
    ·
      refine ⟨7493198729942356540665857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995465819961571027110571 7493198729942356540665857)
      ·
        refine ⟨5619899047456767405499393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7493198729942356540665857 5619899047456767405499393)
        ·
          refine ⟨4214924285592575554124545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5619899047456767405499393 4214924285592575554124545)
          ·
            refine ⟨3161193214194431665593409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214924285592575554124545 3161193214194431665593409)
            ·
              refine ⟨2370894910645823749195057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161193214194431665593409 2370894910645823749195057)
              ·
                refine ⟨1778171182984367811896293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370894910645823749195057 1778171182984367811896293)
                ·
                  refine ⟨333407096809568964730555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778171182984367811896293 333407096809568964730555)
                  ·
                    rfl

theorem cell22_2921886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2921886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921886 prefixEnd_2921886 := by exact prefixLift 2921886
  have htrace : WordTrace (prefixWord ++ tailWord_2921886) baseStart_2921886 baseEnd_2921886 := by
    simpa [prefixWord, tailWord_2921886, baseEnd_2921886] using wordTrace_append hprefix tailTrace_2921886
  have hstable : (prefixWord ++ tailWord_2921886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921886).length < 2 ^ (prefixWord ++ tailWord_2921886).sum := by decide
  have hdescent : baseEnd_2921886 < baseStart_2921886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921895 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2921895 : Nat := 118140960795 + 2921895 * 2 ^ 59
def prefixEnd_2921895 : Nat := 4983230072969 + 3 ^ 40 * 2921895 * 2
def baseEnd_2921895 : Nat := 1000224371312633870716637

theorem tailTrace_2921895 : CollatzResearch.WordTrace tailWord_2921895 prefixEnd_2921895 1000224371312633870716637 := by
  unfold tailWord_2921895
  simp only [CollatzResearch.WordTrace]
  refine ⟨106570265749480909782103139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71046843832987273188068759 106570265749480909782103139)
  ·
    refine ⟨159855398624221364673154709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106570265749480909782103139 159855398624221364673154709)
    ·
      refine ⟨7493221810510376469054127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159855398624221364673154709 7493221810510376469054127)
      ·
        refine ⟨11239832715765564703581191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493221810510376469054127 11239832715765564703581191)
        ·
          refine ⟨16859749073648347055371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239832715765564703581191 16859749073648347055371787)
          ·
            refine ⟨25289623610472520583057681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16859749073648347055371787 25289623610472520583057681)
            ·
              refine ⟨18967217707854390437293261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25289623610472520583057681 18967217707854390437293261)
              ·
                refine ⟨7112706640445396413984973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18967217707854390437293261 7112706640445396413984973)
                ·
                  refine ⟨2667264990167023655244365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7112706640445396413984973 2667264990167023655244365)
                  ·
                    refine ⟨1000224371312633870716637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667264990167023655244365 1000224371312633870716637)
                    ·
                      rfl

theorem cell22_2921895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2921895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921895 prefixEnd_2921895 := by exact prefixLift 2921895
  have htrace : WordTrace (prefixWord ++ tailWord_2921895) baseStart_2921895 baseEnd_2921895 := by
    simpa [prefixWord, tailWord_2921895, baseEnd_2921895] using wordTrace_append hprefix tailTrace_2921895
  have hstable : (prefixWord ++ tailWord_2921895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921895).length < 2 ^ (prefixWord ++ tailWord_2921895).sum := by decide
  have hdescent : baseEnd_2921895 < baseStart_2921895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921942 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2921942 : Nat := 118140960795 + 2921942 * 2 ^ 59
def prefixEnd_2921942 : Nat := 4983230072969 + 3 ^ 40 * 2921942 * 2
def baseEnd_2921942 : Nat := 333413486791047138263831

theorem tailTrace_2921942 : CollatzResearch.WordTrace tailWord_2921942 prefixEnd_2921942 333413486791047138263831 := by
  unfold tailWord_2921942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6660748748769414800566505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71047986653540424539376053 6660748748769414800566505)
  ·
    refine ⟨4995561561577061100424879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6660748748769414800566505 4995561561577061100424879)
    ·
      refine ⟨7493342342365591650637319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995561561577061100424879 7493342342365591650637319)
      ·
        refine ⟨11240013513548387475955979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493342342365591650637319 11240013513548387475955979)
        ·
          refine ⟨16860020270322581213933969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240013513548387475955979 16860020270322581213933969)
          ·
            refine ⟨12645015202741935910450477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16860020270322581213933969 12645015202741935910450477)
            ·
              refine ⟨4741880701028225966418929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12645015202741935910450477 4741880701028225966418929)
              ·
                refine ⟨3556410525771169474814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741880701028225966418929 3556410525771169474814197)
                ·
                  refine ⟨333413486791047138263831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556410525771169474814197 333413486791047138263831)
                  ·
                    rfl

theorem cell22_2921942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2921942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921942 prefixEnd_2921942 := by exact prefixLift 2921942
  have htrace : WordTrace (prefixWord ++ tailWord_2921942) baseStart_2921942 baseEnd_2921942 := by
    simpa [prefixWord, tailWord_2921942, baseEnd_2921942] using wordTrace_append hprefix tailTrace_2921942
  have hstable : (prefixWord ++ tailWord_2921942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921942).length < 2 ^ (prefixWord ++ tailWord_2921942).sum := by decide
  have hdescent : baseEnd_2921942 < baseStart_2921942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921953 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 6]
def baseStart_2921953 : Nat := 118140960795 + 2921953 * 2 ^ 59
def prefixEnd_2921953 : Nat := 4983230072969 + 3 ^ 40 * 2921953 * 2
def baseEnd_2921953 : Nat := 333414741965980350922153

theorem tailTrace_2921953 : CollatzResearch.WordTrace tailWord_2921953 prefixEnd_2921953 333414741965980350922153 := by
  unfold tailWord_2921953
  simp only [CollatzResearch.WordTrace]
  refine ⟨106572381183270785687714513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71048254122180523791809675 106572381183270785687714513)
  ·
    refine ⟨79929285887453089265785885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106572381183270785687714513 79929285887453089265785885)
    ·
      refine ⟨29973482207794908474669707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79929285887453089265785885 29973482207794908474669707)
      ·
        refine ⟨44960223311692362712004561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29973482207794908474669707 44960223311692362712004561)
        ·
          refine ⟨33720167483769272034003421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44960223311692362712004561 33720167483769272034003421)
          ·
            refine ⟨12645062806413477012751283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33720167483769272034003421 12645062806413477012751283)
            ·
              refine ⟨18967594209620215519126925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645062806413477012751283 18967594209620215519126925)
              ·
                refine ⟨7112847828607580819672597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18967594209620215519126925 7112847828607580819672597)
                ·
                  refine ⟨333414741965980350922153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7112847828607580819672597 333414741965980350922153)
                  ·
                    rfl

theorem cell22_2921953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_2921953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921953 prefixEnd_2921953 := by exact prefixLift 2921953
  have htrace : WordTrace (prefixWord ++ tailWord_2921953) baseStart_2921953 baseEnd_2921953 := by
    simpa [prefixWord, tailWord_2921953, baseEnd_2921953] using wordTrace_append hprefix tailTrace_2921953
  have hstable : (prefixWord ++ tailWord_2921953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921953).length < 2 ^ (prefixWord ++ tailWord_2921953).sum := by decide
  have hdescent : baseEnd_2921953 < baseStart_2921953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921970 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_2921970 : Nat := 118140960795 + 2921970 * 2 ^ 59
def prefixEnd_2921970 : Nat := 4983230072969 + 3 ^ 40 * 2921970 * 2
def baseEnd_2921970 : Nat := 333416681781786225030469

theorem tailTrace_2921970 : CollatzResearch.WordTrace tailWord_2921970 prefixEnd_2921970 333416681781786225030469 := by
  unfold tailWord_2921970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26643250306052299397770841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71048667482806131727388909 26643250306052299397770841)
  ·
    refine ⟨19982437729539224548328131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26643250306052299397770841 19982437729539224548328131)
    ·
      refine ⟨29973656594308836822492197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19982437729539224548328131 29973656594308836822492197)
      ·
        refine ⟨5620060611432906904217287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29973656594308836822492197 5620060611432906904217287)
        ·
          refine ⟨8430090917149360356325931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620060611432906904217287 8430090917149360356325931)
          ·
            refine ⟨12645136375724040534488897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430090917149360356325931 12645136375724040534488897)
            ·
              refine ⟨9483852281793030400866673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645136375724040534488897 9483852281793030400866673)
              ·
                refine ⟨7112889211344772800650005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483852281793030400866673 7112889211344772800650005)
                ·
                  refine ⟨333416681781786225030469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7112889211344772800650005 333416681781786225030469)
                  ·
                    rfl

theorem cell22_2921970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_2921970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2921970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2921970 prefixEnd_2921970 := by exact prefixLift 2921970
  have htrace : WordTrace (prefixWord ++ tailWord_2921970) baseStart_2921970 baseEnd_2921970 := by
    simpa [prefixWord, tailWord_2921970, baseEnd_2921970] using wordTrace_append hprefix tailTrace_2921970
  have hstable : (prefixWord ++ tailWord_2921970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921970).length < 2 ^ (prefixWord ++ tailWord_2921970).sum := by decide
  have hdescent : baseEnd_2921970 < baseStart_2921970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922004 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2922004 : Nat := 118140960795 + 2922004 * 2 ^ 59
def prefixEnd_2922004 : Nat := 4983230072969 + 3 ^ 40 * 2922004 * 2
def baseEnd_2922004 : Nat := 333420561413397973247101

theorem tailTrace_2922004 : CollatzResearch.WordTrace tailWord_2922004 prefixEnd_2922004 333420561413397973247101 := by
  unfold tailWord_2922004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53287120653043010698910533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71049494204057347598547377 53287120653043010698910533)
  ·
    refine ⟨9991335122445564506045725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53287120653043010698910533 9991335122445564506045725)
    ·
      refine ⟨3746750670917086689767147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9991335122445564506045725 3746750670917086689767147)
      ·
        refine ⟨5620126006375630034650721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746750670917086689767147 5620126006375630034650721)
        ·
          refine ⟨4215094504781722525988041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620126006375630034650721 4215094504781722525988041)
          ·
            refine ⟨3161320878586291894491031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215094504781722525988041 3161320878586291894491031)
            ·
              refine ⟨4741981317879437841736547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161320878586291894491031 4741981317879437841736547)
              ·
                refine ⟨7112971976819156762604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741981317879437841736547 7112971976819156762604821)
                ·
                  refine ⟨333420561413397973247101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7112971976819156762604821 333420561413397973247101)
                  ·
                    rfl

theorem cell22_2922004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2922004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922004 prefixEnd_2922004 := by exact prefixLift 2922004
  have htrace : WordTrace (prefixWord ++ tailWord_2922004) baseStart_2922004 baseEnd_2922004 := by
    simpa [prefixWord, tailWord_2922004, baseEnd_2922004] using wordTrace_append hprefix tailTrace_2922004
  have hstable : (prefixWord ++ tailWord_2922004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922004).length < 2 ^ (prefixWord ++ tailWord_2922004).sum := by decide
  have hdescent : baseEnd_2922004 < baseStart_2922004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922060 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_2922060 : Nat := 118140960795 + 2922060 * 2 ^ 59
def prefixEnd_2922060 : Nat := 4983230072969 + 3 ^ 40 * 2922060 * 2
def baseEnd_2922060 : Nat := 333426951394876146780377

theorem tailTrace_2922060 : CollatzResearch.WordTrace tailWord_2922060 prefixEnd_2922060 333426951394876146780377 := by
  unfold tailWord_2922060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53288141896941571480929817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71050855862588761974573089 53288141896941571480929817)
  ·
    refine ⟨39966106422706178610697363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53288141896941571480929817 39966106422706178610697363)
    ·
      refine ⟨59949159634059267916046045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39966106422706178610697363 59949159634059267916046045)
      ·
        refine ⟨22480934862772225468517267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59949159634059267916046045 22480934862772225468517267)
        ·
          refine ⟨33721402294158338202775901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22480934862772225468517267 33721402294158338202775901)
          ·
            refine ⟨12645525860309376826040963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33721402294158338202775901 12645525860309376826040963)
            ·
              refine ⟨18968288790464065239061445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645525860309376826040963 18968288790464065239061445)
              ·
                refine ⟨3556554148212012232324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18968288790464065239061445 3556554148212012232324021)
                ·
                  refine ⟨333426951394876146780377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556554148212012232324021 333426951394876146780377)
                  ·
                    rfl

theorem cell22_2922060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_2922060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922060 prefixEnd_2922060 := by exact prefixLift 2922060
  have htrace : WordTrace (prefixWord ++ tailWord_2922060) baseStart_2922060 baseEnd_2922060 := by
    simpa [prefixWord, tailWord_2922060, baseEnd_2922060] using wordTrace_append hprefix tailTrace_2922060
  have hstable : (prefixWord ++ tailWord_2922060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922060).length < 2 ^ (prefixWord ++ tailWord_2922060).sum := by decide
  have hdescent : baseEnd_2922060 < baseStart_2922060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922122 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_2922122 : Nat := 118140960795 + 2922122 * 2 ^ 59
def prefixEnd_2922122 : Nat := 4983230072969 + 3 ^ 40 * 2922122 * 2
def baseEnd_2922122 : Nat := 333434026017226981763647

theorem tailTrace_2922122 : CollatzResearch.WordTrace tailWord_2922122 prefixEnd_2922122 333434026017226981763647 := by
  unfold tailWord_2922122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644636279914631887654155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71052363413105685033744413 26644636279914631887654155)
  ·
    refine ⟨39966954419871947831481233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26644636279914631887654155 39966954419871947831481233)
    ·
      refine ⟨29975215814903960873610925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39966954419871947831481233 29975215814903960873610925)
      ·
        refine ⟨11240705930588985327604097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29975215814903960873610925 11240705930588985327604097)
        ·
          refine ⟨8430529447941738995703073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11240705930588985327604097 8430529447941738995703073)
          ·
            refine ⟨6322897085956304246777305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8430529447941738995703073 6322897085956304246777305)
            ·
              refine ⟨4742172814467228185082979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322897085956304246777305 4742172814467228185082979)
              ·
                refine ⟨7113259221700842277624469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742172814467228185082979 7113259221700842277624469)
                ·
                  refine ⟨333434026017226981763647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7113259221700842277624469 333434026017226981763647)
                  ·
                    rfl

theorem cell22_2922122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_2922122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922122 prefixEnd_2922122 := by exact prefixLift 2922122
  have htrace : WordTrace (prefixWord ++ tailWord_2922122) baseStart_2922122 baseEnd_2922122 := by
    simpa [prefixWord, tailWord_2922122, baseEnd_2922122] using wordTrace_append hprefix tailTrace_2922122
  have hstable : (prefixWord ++ tailWord_2922122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922122).length < 2 ^ (prefixWord ++ tailWord_2922122).sum := by decide
  have hdescent : baseEnd_2922122 < baseStart_2922122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922135 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2922135 : Nat := 118140960795 + 2922135 * 2 ^ 59
def prefixEnd_2922135 : Nat := 4983230072969 + 3 ^ 40 * 2922135 * 2
def baseEnd_2922135 : Nat := 1000306528217353244715901

theorem tailTrace_2922135 : CollatzResearch.WordTrace tailWord_2922135 prefixEnd_2922135 1000306528217353244715901 := by
  unfold tailWord_2922135
  simp only [CollatzResearch.WordTrace]
  refine ⟨106579019268611430770839859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71052679512407620513893239 106579019268611430770839859)
  ·
    refine ⟨159868528902917146156259789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106579019268611430770839859 159868528902917146156259789)
    ·
      refine ⟨59950698338593929808597421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159868528902917146156259789 59950698338593929808597421)
      ·
        refine ⟨22481511876972723678224033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59950698338593929808597421 22481511876972723678224033)
        ·
          refine ⟨16861133907729542758668025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22481511876972723678224033 16861133907729542758668025)
          ·
            refine ⟨12645850430797157069001019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16861133907729542758668025 12645850430797157069001019)
            ·
              refine ⟨18968775646195735603501529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645850430797157069001019 18968775646195735603501529)
              ·
                refine ⟨14226581734646801702626147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18968775646195735603501529 14226581734646801702626147)
                ·
                  refine ⟨21339872601970202553939221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14226581734646801702626147 21339872601970202553939221)
                  ·
                    refine ⟨1000306528217353244715901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21339872601970202553939221 1000306528217353244715901)
                    ·
                      rfl

theorem cell22_2922135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2922135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922135 prefixEnd_2922135 := by exact prefixLift 2922135
  have htrace : WordTrace (prefixWord ++ tailWord_2922135) baseStart_2922135 baseEnd_2922135 := by
    simpa [prefixWord, tailWord_2922135, baseEnd_2922135] using wordTrace_append hprefix tailTrace_2922135
  have hstable : (prefixWord ++ tailWord_2922135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922135).length < 2 ^ (prefixWord ++ tailWord_2922135).sum := by decide
  have hdescent : baseEnd_2922135 < baseStart_2922135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922188 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_2922188 : Nat := 118140960795 + 2922188 * 2 ^ 59
def prefixEnd_2922188 : Nat := 4983230072969 + 3 ^ 40 * 2922188 * 2
def baseEnd_2922188 : Nat := 1000324671200478773140739

theorem tailTrace_2922188 : CollatzResearch.WordTrace tailWord_2922188 prefixEnd_2922188 1000324671200478773140739 := by
  unfold tailWord_2922188
  simp only [CollatzResearch.WordTrace]
  refine ⟨53290476168709710411259609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71053968224946280548346145 53290476168709710411259609)
  ·
    refine ⟨39967857126532282808444707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53290476168709710411259609 39967857126532282808444707)
    ·
      refine ⟨59951785689798424212667061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39967857126532282808444707 59951785689798424212667061)
      ·
        refine ⟨5620479908418602269937537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59951785689798424212667061 5620479908418602269937537)
        ·
          refine ⟨4215359931313951702453153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620479908418602269937537 4215359931313951702453153)
          ·
            refine ⟨3161519948485463776839865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215359931313951702453153 3161519948485463776839865)
            ·
              refine ⟨2371139961364097832629899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161519948485463776839865 2371139961364097832629899)
              ·
                refine ⟨3556709942046146748944849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371139961364097832629899 3556709942046146748944849)
                ·
                  refine ⟨2667532456534610061708637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556709942046146748944849 2667532456534610061708637)
                  ·
                    refine ⟨1000324671200478773140739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667532456534610061708637 1000324671200478773140739)
                    ·
                      rfl

theorem cell22_2922188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_2922188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922188 prefixEnd_2922188 := by exact prefixLift 2922188
  have htrace : WordTrace (prefixWord ++ tailWord_2922188) baseStart_2922188 baseEnd_2922188 := by
    simpa [prefixWord, tailWord_2922188, baseEnd_2922188] using wordTrace_append hprefix tailTrace_2922188
  have hstable : (prefixWord ++ tailWord_2922188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922188).length < 2 ^ (prefixWord ++ tailWord_2922188).sum := by decide
  have hdescent : baseEnd_2922188 < baseStart_2922188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922272 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_2922272 : Nat := 118140960795 + 2922272 * 2 ^ 59
def prefixEnd_2922272 : Nat := 4983230072969 + 3 ^ 40 * 2922272 * 2
def baseEnd_2922272 : Nat := 1000353426117130554040481

theorem tailTrace_2922272 : CollatzResearch.WordTrace tailWord_2922272 prefixEnd_2922272 1000353426117130554040481 := by
  unfold tailWord_2922272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53292008034557551584288535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71056010712743402112384713 53292008034557551584288535)
  ·
    refine ⟨79938012051836327376432803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53292008034557551584288535 79938012051836327376432803)
    ·
      refine ⟨119907018077754491064649205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79938012051836327376432803 119907018077754491064649205)
      ·
        refine ⟨11241282944789483537310863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119907018077754491064649205 11241282944789483537310863)
        ·
          refine ⟨16861924417184225305966295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241282944789483537310863 16861924417184225305966295)
          ·
            refine ⟨25292886625776337958949443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16861924417184225305966295 25292886625776337958949443)
            ·
              refine ⟨37939329938664506938424165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25292886625776337958949443 37939329938664506938424165)
              ·
                refine ⟨7113624363499595050954531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37939329938664506938424165 7113624363499595050954531)
                ·
                  refine ⟨10670436545249392576431797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113624363499595050954531 10670436545249392576431797)
                  ·
                    refine ⟨1000353426117130554040481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10670436545249392576431797 1000353426117130554040481)
                    ·
                      rfl

theorem cell22_2922272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_2922272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922272 prefixEnd_2922272 := by exact prefixLift 2922272
  have htrace : WordTrace (prefixWord ++ tailWord_2922272) baseStart_2922272 baseEnd_2922272 := by
    simpa [prefixWord, tailWord_2922272, baseEnd_2922272] using wordTrace_append hprefix tailTrace_2922272
  have hstable : (prefixWord ++ tailWord_2922272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922272).length < 2 ^ (prefixWord ++ tailWord_2922272).sum := by decide
  have hdescent : baseEnd_2922272 < baseStart_2922272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922276 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2922276 : Nat := 118140960795 + 2922276 * 2 ^ 59
def prefixEnd_2922276 : Nat := 4983230072969 + 3 ^ 40 * 2922276 * 2
def baseEnd_2922276 : Nat := 1000354795398875876940469

theorem tailTrace_2922276 : CollatzResearch.WordTrace tailWord_2922276 prefixEnd_2922276 1000354795398875876940469 := by
  unfold tailWord_2922276
  simp only [CollatzResearch.WordTrace]
  refine ⟨53292080980550305925861341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71056107974067074567815121 53292080980550305925861341)
  ·
    refine ⟨19984530367706364722198003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53292080980550305925861341 19984530367706364722198003)
    ·
      refine ⟨29976795551559547083297005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19984530367706364722198003 29976795551559547083297005)
      ·
        refine ⟨11241298331834830156236377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29976795551559547083297005 11241298331834830156236377)
        ·
          refine ⟨8430973748876122617177283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11241298331834830156236377 8430973748876122617177283)
          ·
            refine ⟨12646460623314183925765925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430973748876122617177283 12646460623314183925765925)
            ·
              refine ⟨2371211366871409486081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12646460623314183925765925 2371211366871409486081111)
              ·
                refine ⟨3556817050307114229121667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371211366871409486081111 3556817050307114229121667)
                ·
                  refine ⟨5335225575460671343682501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556817050307114229121667 5335225575460671343682501)
                  ·
                    refine ⟨1000354795398875876940469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335225575460671343682501 1000354795398875876940469)
                    ·
                      rfl

theorem cell22_2922276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2922276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922276 prefixEnd_2922276 := by exact prefixLift 2922276
  have htrace : WordTrace (prefixWord ++ tailWord_2922276) baseStart_2922276 baseEnd_2922276 := by
    simpa [prefixWord, tailWord_2922276, baseEnd_2922276] using wordTrace_append hprefix tailTrace_2922276
  have hstable : (prefixWord ++ tailWord_2922276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922276).length < 2 ^ (prefixWord ++ tailWord_2922276).sum := by decide
  have hdescent : baseEnd_2922276 < baseStart_2922276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922289 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_2922289 : Nat := 118140960795 + 2922289 * 2 ^ 59
def prefixEnd_2922289 : Nat := 4983230072969 + 3 ^ 40 * 2922289 * 2
def baseEnd_2922289 : Nat := 1000359245564548176365429

theorem tailTrace_2922289 : CollatzResearch.WordTrace tailWord_2922289 prefixEnd_2922289 1000359245564548176365429 := by
  unfold tailWord_2922289
  simp only [CollatzResearch.WordTrace]
  refine ⟨106584636110053515071945921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71056424073369010047963947 106584636110053515071945921)
  ·
    refine ⟨79938477082540136303959441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106584636110053515071945921 79938477082540136303959441)
    ·
      refine ⟨59953857811905102227969581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79938477082540136303959441 59953857811905102227969581)
      ·
        refine ⟨22482696679464413335488593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59953857811905102227969581 22482696679464413335488593)
        ·
          refine ⟨16862022509598310001616445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22482696679464413335488593 16862022509598310001616445)
          ·
            refine ⟨6323258441099366250606167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16862022509598310001616445 6323258441099366250606167)
            ·
              refine ⟨9484887661649049375909251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323258441099366250606167 9484887661649049375909251)
              ·
                refine ⟨14227331492473574063863877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9484887661649049375909251 14227331492473574063863877)
                ·
                  refine ⟨2667624654838795136974477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14227331492473574063863877 2667624654838795136974477)
                  ·
                    refine ⟨1000359245564548176365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667624654838795136974477 1000359245564548176365429)
                    ·
                      rfl

theorem cell22_2922289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_2922289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922289 prefixEnd_2922289 := by exact prefixLift 2922289
  have htrace : WordTrace (prefixWord ++ tailWord_2922289) baseStart_2922289 baseEnd_2922289 := by
    simpa [prefixWord, tailWord_2922289, baseEnd_2922289] using wordTrace_append hprefix tailTrace_2922289
  have hstable : (prefixWord ++ tailWord_2922289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922289).length < 2 ^ (prefixWord ++ tailWord_2922289).sum := by decide
  have hdescent : baseEnd_2922289 < baseStart_2922289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922347 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 5]
def baseStart_2922347 : Nat := 118140960795 + 2922347 * 2 ^ 59
def prefixEnd_2922347 : Nat := 4983230072969 + 3 ^ 40 * 2922347 * 2
def baseEnd_2922347 : Nat := 333459700049951786138417

theorem tailTrace_2922347 : CollatzResearch.WordTrace tailWord_2922347 prefixEnd_2922347 333459700049951786138417 := by
  unfold tailWord_2922347
  simp only [CollatzResearch.WordTrace]
  refine ⟨106586751543843390977557295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71057834362562260651704863 106586751543843390977557295)
  ·
    refine ⟨159880127315765086466335943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106586751543843390977557295 159880127315765086466335943)
    ·
      refine ⟨239820190973647629699503915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159880127315765086466335943 239820190973647629699503915)
      ·
        refine ⟨359730286460471444549255873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239820190973647629699503915 359730286460471444549255873)
        ·
          refine ⟨269797714845353583411941905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359730286460471444549255873 269797714845353583411941905)
          ·
            refine ⟨202348286134015187558956429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269797714845353583411941905 202348286134015187558956429)
            ·
              refine ⟨75880607300255695334608661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202348286134015187558956429 75880607300255695334608661)
              ·
                refine ⟨3556903467199485718809781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75880607300255695334608661 3556903467199485718809781)
                ·
                  refine ⟨333459700049951786138417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556903467199485718809781 333459700049951786138417)
                  ·
                    rfl

theorem cell22_2922347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].length) (baseStart_2922347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922347 prefixEnd_2922347 := by exact prefixLift 2922347
  have htrace : WordTrace (prefixWord ++ tailWord_2922347) baseStart_2922347 baseEnd_2922347 := by
    simpa [prefixWord, tailWord_2922347, baseEnd_2922347] using wordTrace_append hprefix tailTrace_2922347
  have hstable : (prefixWord ++ tailWord_2922347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922347).length < 2 ^ (prefixWord ++ tailWord_2922347).sum := by decide
  have hdescent : baseEnd_2922347 < baseStart_2922347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922362 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2922362 : Nat := 118140960795 + 2922362 * 2 ^ 59
def prefixEnd_2922362 : Nat := 4983230072969 + 3 ^ 40 * 2922362 * 2
def baseEnd_2922362 : Nat := 1000384234956400319290205

theorem tailTrace_2922362 : CollatzResearch.WordTrace tailWord_2922362 prefixEnd_2922362 1000384234956400319290205 := by
  unfold tailWord_2922362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26646824659697262134838335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71058199092526032359568893 26646824659697262134838335)
  ·
    refine ⟨39970236989545893202257503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26646824659697262134838335 39970236989545893202257503)
    ·
      refine ⟨59955355484318839803386255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39970236989545893202257503 59955355484318839803386255)
      ·
        refine ⟨89933033226478259705079383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59955355484318839803386255 89933033226478259705079383)
        ·
          refine ⟨134899549839717389557619075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89933033226478259705079383 134899549839717389557619075)
          ·
            refine ⟨202349324759576084336428613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134899549839717389557619075 202349324759576084336428613)
            ·
              refine ⟨37940498392420515813080365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202349324759576084336428613 37940498392420515813080365)
              ·
                refine ⟨14227686897157693429905137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37940498392420515813080365 14227686897157693429905137)
                ·
                  refine ⟨10670765172868270072428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14227686897157693429905137 10670765172868270072428853)
                  ·
                    refine ⟨1000384234956400319290205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10670765172868270072428853 1000384234956400319290205)
                    ·
                      rfl

theorem cell22_2922362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2922362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922362 prefixEnd_2922362 := by exact prefixLift 2922362
  have htrace : WordTrace (prefixWord ++ tailWord_2922362) baseStart_2922362 baseEnd_2922362 := by
    simpa [prefixWord, tailWord_2922362, baseEnd_2922362] using wordTrace_append hprefix tailTrace_2922362
  have hstable : (prefixWord ++ tailWord_2922362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922362).length < 2 ^ (prefixWord ++ tailWord_2922362).sum := by decide
  have hdescent : baseEnd_2922362 < baseStart_2922362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922402 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2922402 : Nat := 118140960795 + 2922402 * 2 ^ 59
def prefixEnd_2922402 : Nat := 4983230072969 + 3 ^ 40 * 2922402 * 2
def baseEnd_2922402 : Nat := 1000397927773853548290083

theorem tailTrace_2922402 : CollatzResearch.WordTrace tailWord_2922402 prefixEnd_2922402 1000397927773853548290083 := by
  unfold tailWord_2922402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647189389661033842702365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71059171705762756913872973 26647189389661033842702365)
  ·
    refine ⟨9992696021122887691013387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26647189389661033842702365 9992696021122887691013387)
    ·
      refine ⟨14989044031684331536520081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992696021122887691013387 14989044031684331536520081)
      ·
        refine ⟨11241783023763248652390061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14989044031684331536520081 11241783023763248652390061)
        ·
          refine ⟨4215668633911218244646273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11241783023763248652390061 4215668633911218244646273)
          ·
            refine ⟨3161751475433413683484705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215668633911218244646273 3161751475433413683484705)
            ·
              refine ⟨2371313606575060262613529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161751475433413683484705 2371313606575060262613529)
              ·
                refine ⟨1778485204931295196960147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371313606575060262613529 1778485204931295196960147)
                ·
                  refine ⟨2667727807396942795440221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778485204931295196960147 2667727807396942795440221)
                  ·
                    refine ⟨1000397927773853548290083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667727807396942795440221 1000397927773853548290083)
                    ·
                      rfl

theorem cell22_2922402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2922402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922402 prefixEnd_2922402 := by exact prefixLift 2922402
  have htrace : WordTrace (prefixWord ++ tailWord_2922402) baseStart_2922402 baseEnd_2922402 := by
    simpa [prefixWord, tailWord_2922402, baseEnd_2922402] using wordTrace_append hprefix tailTrace_2922402
  have hstable : (prefixWord ++ tailWord_2922402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922402).length < 2 ^ (prefixWord ++ tailWord_2922402).sum := by decide
  have hdescent : baseEnd_2922402 < baseStart_2922402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922424 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_2922424 : Nat := 118140960795 + 2922424 * 2 ^ 59
def prefixEnd_2922424 : Nat := 4983230072969 + 3 ^ 40 * 2922424 * 2
def baseEnd_2922424 : Nat := 1000405458823452824240015

theorem tailTrace_2922424 : CollatzResearch.WordTrace tailWord_2922424 prefixEnd_2922424 1000405458823452824240015 := by
  unfold tailWord_2922424
  simp only [CollatzResearch.WordTrace]
  refine ⟨53294779982282216564055163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71059706643042955418740217 53294779982282216564055163)
  ·
    refine ⟨79942169973423324846082745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53294779982282216564055163 79942169973423324846082745)
    ·
      refine ⟨59956627480067493634562059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79942169973423324846082745 59956627480067493634562059)
      ·
        refine ⟨89934941220101240451843089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59956627480067493634562059 89934941220101240451843089)
        ·
          refine ⟨67451205915075930338882317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89934941220101240451843089 67451205915075930338882317)
          ·
            refine ⟨25294202218153473877080869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67451205915075930338882317 25294202218153473877080869)
            ·
              refine ⟨4742662915903776351952663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25294202218153473877080869 4742662915903776351952663)
              ·
                refine ⟨7113994373855664527928995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742662915903776351952663 7113994373855664527928995)
                ·
                  refine ⟨10670991560783496791893493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113994373855664527928995 10670991560783496791893493)
                  ·
                    refine ⟨1000405458823452824240015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10670991560783496791893493 1000405458823452824240015)
                    ·
                      rfl

theorem cell22_2922424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_2922424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922424 prefixEnd_2922424 := by exact prefixLift 2922424
  have htrace : WordTrace (prefixWord ++ tailWord_2922424) baseStart_2922424 baseEnd_2922424 := by
    simpa [prefixWord, tailWord_2922424, baseEnd_2922424] using wordTrace_append hprefix tailTrace_2922424
  have hstable : (prefixWord ++ tailWord_2922424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922424).length < 2 ^ (prefixWord ++ tailWord_2922424).sum := by decide
  have hdescent : baseEnd_2922424 < baseStart_2922424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922460 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_2922460 : Nat := 118140960795 + 2922460 * 2 ^ 59
def prefixEnd_2922460 : Nat := 4983230072969 + 3 ^ 40 * 2922460 * 2
def baseEnd_2922460 : Nat := 333472594119720243446635

theorem tailTrace_2922460 : CollatzResearch.WordTrace tailWord_2922460 prefixEnd_2922460 333472594119720243446635 := by
  unfold tailWord_2922460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53295436496217005638210417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71060581994956007517613889 53295436496217005638210417)
  ·
    refine ⟨39971577372162754228657813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53295436496217005638210417 39971577372162754228657813)
    ·
      refine ⟨1873667689320129104468335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39971577372162754228657813 1873667689320129104468335)
      ·
        refine ⟨2810501533980193656702503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873667689320129104468335 2810501533980193656702503)
        ·
          refine ⟨4215752300970290485053755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810501533980193656702503 4215752300970290485053755)
          ·
            refine ⟨6323628451455435727580633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215752300970290485053755 6323628451455435727580633)
            ·
              refine ⟨4742721338591576795685475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6323628451455435727580633 4742721338591576795685475)
              ·
                refine ⟨7114082007887365193528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742721338591576795685475 7114082007887365193528213)
                ·
                  refine ⟨333472594119720243446635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7114082007887365193528213 333472594119720243446635)
                  ·
                    rfl

theorem cell22_2922460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_2922460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922460 prefixEnd_2922460 := by exact prefixLift 2922460
  have htrace : WordTrace (prefixWord ++ tailWord_2922460) baseStart_2922460 baseEnd_2922460 := by
    simpa [prefixWord, tailWord_2922460, baseEnd_2922460] using wordTrace_append hprefix tailTrace_2922460
  have hstable : (prefixWord ++ tailWord_2922460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922460).length < 2 ^ (prefixWord ++ tailWord_2922460).sum := by decide
  have hdescent : baseEnd_2922460 < baseStart_2922460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922520 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_2922520 : Nat := 118140960795 + 2922520 * 2 ^ 59
def prefixEnd_2922520 : Nat := 4983230072969 + 3 ^ 40 * 2922520 * 2
def baseEnd_2922520 : Nat := 1000438321585340573839721

theorem tailTrace_2922520 : CollatzResearch.WordTrace tailWord_2922520 prefixEnd_2922520 1000438321585340573839721 := by
  unfold tailWord_2922520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53296530686108320761802507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71062040914811094349070009 53296530686108320761802507)
  ·
    refine ⟨79944796029162481142703761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53296530686108320761802507 79944796029162481142703761)
    ·
      refine ⟨59958597021871860857027821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79944796029162481142703761 59958597021871860857027821)
      ·
        refine ⟨22484473883201947821385433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59958597021871860857027821 22484473883201947821385433)
        ·
          refine ⟨16863355412401460866039075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22484473883201947821385433 16863355412401460866039075)
          ·
            refine ⟨25295033118602191299058613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16863355412401460866039075 25295033118602191299058613)
            ·
              refine ⟨2371409354868955434286745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25295033118602191299058613 2371409354868955434286745)
              ·
                refine ⟨1778557016151716575715059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371409354868955434286745 1778557016151716575715059)
                ·
                  refine ⟨2667835524227574863572589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778557016151716575715059 2667835524227574863572589)
                  ·
                    refine ⟨1000438321585340573839721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667835524227574863572589 1000438321585340573839721)
                    ·
                      rfl

theorem cell22_2922520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_2922520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922520 prefixEnd_2922520 := by exact prefixLift 2922520
  have htrace : WordTrace (prefixWord ++ tailWord_2922520) baseStart_2922520 baseEnd_2922520 := by
    simpa [prefixWord, tailWord_2922520, baseEnd_2922520] using wordTrace_append hprefix tailTrace_2922520
  have hstable : (prefixWord ++ tailWord_2922520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922520).length < 2 ^ (prefixWord ++ tailWord_2922520).sum := by decide
  have hdescent : baseEnd_2922520 < baseStart_2922520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922533 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 5]
def baseStart_2922533 : Nat := 118140960795 + 2922533 * 2 ^ 59
def prefixEnd_2922533 : Nat := 4983230072969 + 3 ^ 40 * 2922533 * 2
def baseEnd_2922533 : Nat := 333480923917004291088227

theorem tailTrace_2922533 : CollatzResearch.WordTrace tailWord_2922533 prefixEnd_2922533 333480923917004291088227 := by
  unfold tailWord_2922533
  simp only [CollatzResearch.WordTrace]
  refine ⟨106593535521169544743828253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71062357014113029829218835 106593535521169544743828253)
  ·
    refine ⟨39972575820438579278935595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106593535521169544743828253 39972575820438579278935595)
    ·
      refine ⟨59958863730657868918403393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39972575820438579278935595 59958863730657868918403393)
      ·
        refine ⟨44969147797993401688802545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59958863730657868918403393 44969147797993401688802545)
        ·
          refine ⟨33726860848495051266601909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44969147797993401688802545 33726860848495051266601909)
          ·
            refine ⟨3161893204546411056243929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33726860848495051266601909 3161893204546411056243929)
            ·
              refine ⟨2371419903409808292182947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161893204546411056243929 2371419903409808292182947)
              ·
                refine ⟨3557129855114712438274421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371419903409808292182947 3557129855114712438274421)
                ·
                  refine ⟨333480923917004291088227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557129855114712438274421 333480923917004291088227)
                  ·
                    rfl

theorem cell22_2922533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_2922533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922533 prefixEnd_2922533 := by exact prefixLift 2922533
  have htrace : WordTrace (prefixWord ++ tailWord_2922533) baseStart_2922533 baseEnd_2922533 := by
    simpa [prefixWord, tailWord_2922533, baseEnd_2922533] using wordTrace_append hprefix tailTrace_2922533
  have hstable : (prefixWord ++ tailWord_2922533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922533).length < 2 ^ (prefixWord ++ tailWord_2922533).sum := by decide
  have hdescent : baseEnd_2922533 < baseStart_2922533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922546 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2922546 : Nat := 118140960795 + 2922546 * 2 ^ 59
def prefixEnd_2922546 : Nat := 4983230072969 + 3 ^ 40 * 2922546 * 2
def baseEnd_2922546 : Nat := 1000447221916685172689641

theorem tailTrace_2922546 : CollatzResearch.WordTrace tailWord_2922546 prefixEnd_2922546 1000447221916685172689641 := by
  unfold tailWord_2922546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648502417530611991012873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71062673113414965309367661 26648502417530611991012873)
  ·
    refine ⟨19986376813147958993259655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26648502417530611991012873 19986376813147958993259655)
    ·
      refine ⟨29979565219721938489889483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19986376813147958993259655 29979565219721938489889483)
      ·
        refine ⟨44969347829582907734834225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29979565219721938489889483 44969347829582907734834225)
        ·
          refine ⟨33727010872187180801125669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44969347829582907734834225 33727010872187180801125669)
          ·
            refine ⟨6323814538535096400211063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33727010872187180801125669 6323814538535096400211063)
            ·
              refine ⟨9485721807802644600316595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323814538535096400211063 9485721807802644600316595)
              ·
                refine ⟨14228582711703966900474893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485721807802644600316595 14228582711703966900474893)
                ·
                  refine ⟨5335718516888987587678085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14228582711703966900474893 5335718516888987587678085)
                  ·
                    refine ⟨1000447221916685172689641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335718516888987587678085 1000447221916685172689641)
                    ·
                      rfl

theorem cell22_2922546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2922546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922546 prefixEnd_2922546 := by exact prefixLift 2922546
  have htrace : WordTrace (prefixWord ++ tailWord_2922546) baseStart_2922546 baseEnd_2922546 := by
    simpa [prefixWord, tailWord_2922546, baseEnd_2922546] using wordTrace_append hprefix tailTrace_2922546
  have hstable : (prefixWord ++ tailWord_2922546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922546).length < 2 ^ (prefixWord ++ tailWord_2922546).sum := by decide
  have hdescent : baseEnd_2922546 < baseStart_2922546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922559 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_2922559 : Nat := 118140960795 + 2922559 * 2 ^ 59
def prefixEnd_2922559 : Nat := 4983230072969 + 3 ^ 40 * 2922559 * 2
def baseEnd_2922559 : Nat := 1000451672082357472114601

theorem tailTrace_2922559 : CollatzResearch.WordTrace tailWord_2922559 prefixEnd_2922559 1000451672082357472114601 := by
  unfold tailWord_2922559
  simp only [CollatzResearch.WordTrace]
  refine ⟨106594483819075351184274731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71062989212716900789516487 106594483819075351184274731)
  ·
    refine ⟨159891725728613026776412097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106594483819075351184274731 159891725728613026776412097)
    ·
      refine ⟨119918794296459770082309073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159891725728613026776412097 119918794296459770082309073)
      ·
        refine ⟨89939095722344827561731805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119918794296459770082309073 89939095722344827561731805)
        ·
          refine ⟨33727160895879310335649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89939095722344827561731805 33727160895879310335649427)
          ·
            refine ⟨50590741343818965503474141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33727160895879310335649427 50590741343818965503474141)
            ·
              refine ⟨18971528003932112063802803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50590741343818965503474141 18971528003932112063802803)
              ·
                refine ⟨28457292005898168095704205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18971528003932112063802803 28457292005898168095704205)
                ·
                  refine ⟨10671484502211813035889077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28457292005898168095704205 10671484502211813035889077)
                  ·
                    refine ⟨1000451672082357472114601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10671484502211813035889077 1000451672082357472114601)
                    ·
                      rfl

theorem cell22_2922559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_2922559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922559 prefixEnd_2922559 := by exact prefixLift 2922559
  have htrace : WordTrace (prefixWord ++ tailWord_2922559) baseStart_2922559 baseEnd_2922559 := by
    simpa [prefixWord, tailWord_2922559, baseEnd_2922559] using wordTrace_append hprefix tailTrace_2922559
  have hstable : (prefixWord ++ tailWord_2922559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922559).length < 2 ^ (prefixWord ++ tailWord_2922559).sum := by decide
  have hdescent : baseEnd_2922559 < baseStart_2922559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922608 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_2922608 : Nat := 118140960795 + 2922608 * 2 ^ 59
def prefixEnd_2922608 : Nat := 4983230072969 + 3 ^ 40 * 2922608 * 2
def baseEnd_2922608 : Nat := 1000468445783737677639451

theorem tailTrace_2922608 : CollatzResearch.WordTrace tailWord_2922608 prefixEnd_2922608 1000468445783737677639451 := by
  unfold tailWord_2922608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298135497948916276404239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71064180663931888368538985 53298135497948916276404239)
  ·
    refine ⟨79947203246923374414606359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53298135497948916276404239 79947203246923374414606359)
    ·
      refine ⟨119920804870385061621909539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79947203246923374414606359 119920804870385061621909539)
      ·
        refine ⟨179881207305577592432864309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119920804870385061621909539 179881207305577592432864309)
        ·
          refine ⟨16863863184897899290581029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179881207305577592432864309 16863863184897899290581029)
          ·
            refine ⟨3161974347168356116983943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16863863184897899290581029 3161974347168356116983943)
            ·
              refine ⟨4742961520752534175475915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161974347168356116983943 4742961520752534175475915)
              ·
                refine ⟨7114442281128801263213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742961520752534175475915 7114442281128801263213873)
                ·
                  refine ⟨5335831710846600947410405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7114442281128801263213873 5335831710846600947410405)
                  ·
                    refine ⟨1000468445783737677639451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335831710846600947410405 1000468445783737677639451)
                    ·
                      rfl

theorem cell22_2922608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_2922608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922608 prefixEnd_2922608 := by exact prefixLift 2922608
  have htrace : WordTrace (prefixWord ++ tailWord_2922608) baseStart_2922608 baseEnd_2922608 := by
    simpa [prefixWord, tailWord_2922608, baseEnd_2922608] using wordTrace_append hprefix tailTrace_2922608
  have hstable : (prefixWord ++ tailWord_2922608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922608).length < 2 ^ (prefixWord ++ tailWord_2922608).sum := by decide
  have hdescent : baseEnd_2922608 < baseStart_2922608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922644 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2922644 : Nat := 118140960795 + 2922644 * 2 ^ 59
def prefixEnd_2922644 : Nat := 4983230072969 + 3 ^ 40 * 2922644 * 2
def baseEnd_2922644 : Nat := 1000480769319445583739341

theorem tailTrace_2922644 : CollatzResearch.WordTrace tailWord_2922644 prefixEnd_2922644 1000480769319445583739341 := by
  unfold tailWord_2922644
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298792011883705350559493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71065056015844940467412657 53298792011883705350559493)
  ·
    refine ⟨9993523502228194753229905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53298792011883705350559493 9993523502228194753229905)
    ·
      refine ⟨7495142626671146064922429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9993523502228194753229905 7495142626671146064922429)
      ·
        refine ⟨2810678485001679774345911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7495142626671146064922429 2810678485001679774345911)
        ·
          refine ⟨4216017727502519661518867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810678485001679774345911 4216017727502519661518867)
          ·
            refine ⟨6324026591253779492278301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216017727502519661518867 6324026591253779492278301)
            ·
              refine ⟨2371509971720167309604363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6324026591253779492278301 2371509971720167309604363)
              ·
                refine ⟨3557264957580250964406545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371509971720167309604363 3557264957580250964406545)
                ·
                  refine ⟨2667948718185188223304909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557264957580250964406545 2667948718185188223304909)
                  ·
                    refine ⟨1000480769319445583739341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667948718185188223304909 1000480769319445583739341)
                    ·
                      rfl

theorem cell22_2922644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2922644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922644 prefixEnd_2922644 := by exact prefixLift 2922644
  have htrace : WordTrace (prefixWord ++ tailWord_2922644) baseStart_2922644 baseEnd_2922644 := by
    simpa [prefixWord, tailWord_2922644, baseEnd_2922644] using wordTrace_append hprefix tailTrace_2922644
  have hstable : (prefixWord ++ tailWord_2922644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922644).length < 2 ^ (prefixWord ++ tailWord_2922644).sum := by decide
  have hdescent : baseEnd_2922644 < baseStart_2922644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922689 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2922689 : Nat := 118140960795 + 2922689 * 2 ^ 59
def prefixEnd_2922689 : Nat := 4983230072969 + 3 ^ 40 * 2922689 * 2
def baseEnd_2922689 : Nat := 1000496173739080466364203

theorem tailTrace_2922689 : CollatzResearch.WordTrace tailWord_2922689 prefixEnd_2922689 1000496173739080466364203 := by
  unfold tailWord_2922689
  simp only [CollatzResearch.WordTrace]
  refine ⟨106599225308604383386507121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71066150205736255591004747 106599225308604383386507121)
  ·
    refine ⟨79949418981453287539880341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106599225308604383386507121 79949418981453287539880341)
    ·
      refine ⟨3747629014755622853431891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79949418981453287539880341 3747629014755622853431891)
      ·
        refine ⟨5621443522133434280147837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747629014755622853431891 5621443522133434280147837)
        ·
          refine ⟨2108041320800037855055439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5621443522133434280147837 2108041320800037855055439)
          ·
            refine ⟨3162061981200056782583159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108041320800037855055439 3162061981200056782583159)
            ·
              refine ⟨4743092971800085173874739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162061981200056782583159 4743092971800085173874739)
              ·
                refine ⟨7114639457700127760812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743092971800085173874739 7114639457700127760812109)
                ·
                  refine ⟨2667989796637547910304541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7114639457700127760812109 2667989796637547910304541)
                  ·
                    refine ⟨1000496173739080466364203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667989796637547910304541 1000496173739080466364203)
                    ·
                      rfl

theorem cell22_2922689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2922689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922689 prefixEnd_2922689 := by exact prefixLift 2922689
  have htrace : WordTrace (prefixWord ++ tailWord_2922689) baseStart_2922689 baseEnd_2922689 := by
    simpa [prefixWord, tailWord_2922689, baseEnd_2922689] using wordTrace_append hprefix tailTrace_2922689
  have hstable : (prefixWord ++ tailWord_2922689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922689).length < 2 ^ (prefixWord ++ tailWord_2922689).sum := by decide
  have hdescent : baseEnd_2922689 < baseStart_2922689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922711 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_2922711 : Nat := 118140960795 + 2922711 * 2 ^ 59
def prefixEnd_2922711 : Nat := 4983230072969 + 3 ^ 40 * 2922711 * 2
def baseEnd_2922711 : Nat := 1000503704788679742314135

theorem tailTrace_2922711 : CollatzResearch.WordTrace tailWord_2922711 prefixEnd_2922711 1000503704788679742314135 := by
  unfold tailWord_2922711
  simp only [CollatzResearch.WordTrace]
  refine ⟨106600027714524681143807987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71066685143016454095871991 106600027714524681143807987)
  ·
    refine ⟨159900041571787021715711981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106600027714524681143807987 159900041571787021715711981)
    ·
      refine ⟨59962515589420133143391993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159900041571787021715711981 59962515589420133143391993)
      ·
        refine ⟨44971886692065099857543995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59962515589420133143391993 44971886692065099857543995)
        ·
          refine ⟨67457830038097649786315993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44971886692065099857543995 67457830038097649786315993)
          ·
            refine ⟨50593372528573237339736995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67457830038097649786315993 50593372528573237339736995)
            ·
              refine ⟨75890058792859856009605493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50593372528573237339736995 75890058792859856009605493)
              ·
                refine ⟨7114693011830611500900515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75890058792859856009605493 7114693011830611500900515)
                ·
                  refine ⟨10672039517745917251350773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114693011830611500900515 10672039517745917251350773)
                  ·
                    refine ⟨1000503704788679742314135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10672039517745917251350773 1000503704788679742314135)
                    ·
                      rfl

theorem cell22_2922711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_2922711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922711 prefixEnd_2922711 := by exact prefixLift 2922711
  have htrace : WordTrace (prefixWord ++ tailWord_2922711) baseStart_2922711 baseEnd_2922711 := by
    simpa [prefixWord, tailWord_2922711, baseEnd_2922711] using wordTrace_append hprefix tailTrace_2922711
  have hstable : (prefixWord ++ tailWord_2922711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922711).length < 2 ^ (prefixWord ++ tailWord_2922711).sum := by decide
  have hdescent : baseEnd_2922711 < baseStart_2922711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922728 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2922728 : Nat := 118140960795 + 2922728 * 2 ^ 59
def prefixEnd_2922728 : Nat := 4983230072969 + 3 ^ 40 * 2922728 * 2
def baseEnd_2922728 : Nat := 1000509524236097364639083

theorem tailTrace_2922728 : CollatzResearch.WordTrace tailWord_2922728 prefixEnd_2922728 1000509524236097364639083 := by
  unfold tailWord_2922728
  simp only [CollatzResearch.WordTrace]
  refine ⟨53300323877731546523588419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71067098503642062031451225 53300323877731546523588419)
  ·
    refine ⟨79950485816597319785382629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53300323877731546523588419 79950485816597319785382629)
    ·
      refine ⟨14990716090611997459759243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79950485816597319785382629 14990716090611997459759243)
      ·
        refine ⟨22486074135917996189638865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14990716090611997459759243 22486074135917996189638865)
        ·
          refine ⟨16864555601938497142229149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22486074135917996189638865 16864555601938497142229149)
          ·
            refine ⟨6324208350726936428335931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16864555601938497142229149 6324208350726936428335931)
            ·
              refine ⟨9486312526090404642503897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324208350726936428335931 9486312526090404642503897)
              ·
                refine ⟨7114734394567803481877923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9486312526090404642503897 7114734394567803481877923)
                ·
                  refine ⟨10672101591851705222816885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114734394567803481877923 10672101591851705222816885)
                  ·
                    refine ⟨1000509524236097364639083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10672101591851705222816885 1000509524236097364639083)
                    ·
                      rfl

theorem cell22_2922728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2922728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922728 prefixEnd_2922728 := by exact prefixLift 2922728
  have htrace : WordTrace (prefixWord ++ tailWord_2922728) baseStart_2922728 baseEnd_2922728 := by
    simpa [prefixWord, tailWord_2922728, baseEnd_2922728] using wordTrace_append hprefix tailTrace_2922728
  have hstable : (prefixWord ++ tailWord_2922728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922728).length < 2 ^ (prefixWord ++ tailWord_2922728).sum := by decide
  have hdescent : baseEnd_2922728 < baseStart_2922728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922773 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2922773 : Nat := 118140960795 + 2922773 * 2 ^ 59
def prefixEnd_2922773 : Nat := 4983230072969 + 3 ^ 40 * 2922773 * 2
def baseEnd_2922773 : Nat := 1000524928655732247263945

theorem tailTrace_2922773 : CollatzResearch.WordTrace tailWord_2922773 prefixEnd_2922773 1000524928655732247263945 := by
  unfold tailWord_2922773
  simp only [CollatzResearch.WordTrace]
  refine ⟨106602289040300065732564973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71068192693533377155043315 106602289040300065732564973)
  ·
    refine ⟨39975858390112524649711865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106602289040300065732564973 39975858390112524649711865)
    ·
      refine ⟨29981893792584393487283899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39975858390112524649711865 29981893792584393487283899)
      ·
        refine ⟨44972840688876590230925849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29981893792584393487283899 44972840688876590230925849)
        ·
          refine ⟨33729630516657442673194387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44972840688876590230925849 33729630516657442673194387)
          ·
            refine ⟨50594445774986164009791581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33729630516657442673194387 50594445774986164009791581)
            ·
              refine ⟨18972917165619811503671843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50594445774986164009791581 18972917165619811503671843)
              ·
                refine ⟨28459375748429717255507765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18972917165619811503671843 28459375748429717255507765)
                ·
                  refine ⟨2668066476415285992703853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28459375748429717255507765 2668066476415285992703853)
                  ·
                    refine ⟨1000524928655732247263945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668066476415285992703853 1000524928655732247263945)
                    ·
                      rfl

theorem cell22_2922773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2922773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922773 prefixEnd_2922773 := by exact prefixLift 2922773
  have htrace : WordTrace (prefixWord ++ tailWord_2922773) baseStart_2922773 baseEnd_2922773 := by
    simpa [prefixWord, tailWord_2922773, baseEnd_2922773] using wordTrace_append hprefix tailTrace_2922773
  have hstable : (prefixWord ++ tailWord_2922773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922773).length < 2 ^ (prefixWord ++ tailWord_2922773).sum := by decide
  have hdescent : baseEnd_2922773 < baseStart_2922773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922816 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2922816 : Nat := 118140960795 + 2922816 * 2 ^ 59
def prefixEnd_2922816 : Nat := 4983230072969 + 3 ^ 40 * 2922816 * 2
def baseEnd_2922816 : Nat := 1000539648434494468438813

theorem tailTrace_2922816 : CollatzResearch.WordTrace tailWord_2922816 prefixEnd_2922816 1000539648434494468438813 := by
  unfold tailWord_2922816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53301928689572142038190151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71069238252762856050920201 53301928689572142038190151)
  ·
    refine ⟨79952893034358213057285227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53301928689572142038190151 79952893034358213057285227)
    ·
      refine ⟨119929339551537319585927841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79952893034358213057285227 119929339551537319585927841)
      ·
        refine ⟨89947004663652989689445881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119929339551537319585927841 89947004663652989689445881)
        ·
          refine ⟨67460253497739742267084411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89947004663652989689445881 67460253497739742267084411)
          ·
            refine ⟨101190380246609613400626617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67460253497739742267084411 101190380246609613400626617)
            ·
              refine ⟨75892785184957210050469963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101190380246609613400626617 75892785184957210050469963)
              ·
                refine ⟨113839177777435815075704945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75892785184957210050469963 113839177777435815075704945)
                ·
                  refine ⟨85379383333076861306778709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113839177777435815075704945 85379383333076861306778709)
                  ·
                    refine ⟨1000539648434494468438813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85379383333076861306778709 1000539648434494468438813)
                    ·
                      rfl

theorem cell22_2922816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2922816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922816 prefixEnd_2922816 := by exact prefixLift 2922816
  have htrace : WordTrace (prefixWord ++ tailWord_2922816) baseStart_2922816 baseEnd_2922816 := by
    simpa [prefixWord, tailWord_2922816, baseEnd_2922816] using wordTrace_append hprefix tailTrace_2922816
  have hstable : (prefixWord ++ tailWord_2922816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922816).length < 2 ^ (prefixWord ++ tailWord_2922816).sum := by decide
  have hdescent : baseEnd_2922816 < baseStart_2922816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922831 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 8]
def baseStart_2922831 : Nat := 118140960795 + 2922831 * 2 ^ 59
def prefixEnd_2922831 : Nat := 4983230072969 + 3 ^ 40 * 2922831 * 2
def baseEnd_2922831 : Nat := 333514927747013143104589

theorem tailTrace_2922831 : CollatzResearch.WordTrace tailWord_2922831 prefixEnd_2922831 333514927747013143104589 := by
  unfold tailWord_2922831
  simp only [CollatzResearch.WordTrace]
  refine ⟨106604404474089941638176347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71069602982726627758784231 106604404474089941638176347)
  ·
    refine ⟨159906606711134912457264521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106604404474089941638176347 159906606711134912457264521)
    ·
      refine ⟨119929955033351184342948391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159906606711134912457264521 119929955033351184342948391)
      ·
        refine ⟨179894932550026776514422587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119929955033351184342948391 179894932550026776514422587)
        ·
          refine ⟨269842398825040164771633881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179894932550026776514422587 269842398825040164771633881)
          ·
            refine ⟨202381799118780123578725411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269842398825040164771633881 202381799118780123578725411)
            ·
              refine ⟨303572698678170185368088117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202381799118780123578725411 303572698678170185368088117)
              ·
                refine ⟨28459940501078454878258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303572698678170185368088117 28459940501078454878258261)
                ·
                  refine ⟨333514927747013143104589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28459940501078454878258261 333514927747013143104589)
                  ·
                    rfl

theorem cell22_2922831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_2922831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922831 prefixEnd_2922831 := by exact prefixLift 2922831
  have htrace : WordTrace (prefixWord ++ tailWord_2922831) baseStart_2922831 baseEnd_2922831 := by
    simpa [prefixWord, tailWord_2922831, baseEnd_2922831] using wordTrace_append hprefix tailTrace_2922831
  have hstable : (prefixWord ++ tailWord_2922831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922831).length < 2 ^ (prefixWord ++ tailWord_2922831).sum := by decide
  have hdescent : baseEnd_2922831 < baseStart_2922831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922910 : List Nat := [4, 3, 1, 2, 1, 11]
def baseStart_2922910 : Nat := 118140960795 + 2922910 * 2 ^ 59
def prefixEnd_2922910 : Nat := 4983230072969 + 3 ^ 40 * 2922910 * 2
def baseEnd_2922910 : Nat := 12352738599450735266525

theorem tailTrace_2922910 : CollatzResearch.WordTrace tailWord_2922910 prefixEnd_2922910 12352738599450735266525 := by
  unfold tailWord_2922910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325910730100467266287773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71071523893869158753534789 13325910730100467266287773)
  ·
    refine ⟨4997216523787675224857915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13325910730100467266287773 4997216523787675224857915)
    ·
      refine ⟨7495824785681512837286873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997216523787675224857915 7495824785681512837286873)
      ·
        refine ⟨5621868589261134627965155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7495824785681512837286873 5621868589261134627965155)
        ·
          refine ⟨8432802883891701941947733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621868589261134627965155 8432802883891701941947733)
          ·
            refine ⟨12352738599450735266525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8432802883891701941947733 12352738599450735266525)
            ·
              rfl

theorem cell22_2922910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 11].length) (baseStart_2922910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922910 prefixEnd_2922910 := by exact prefixLift 2922910
  have htrace : WordTrace (prefixWord ++ tailWord_2922910) baseStart_2922910 baseEnd_2922910 := by
    simpa [prefixWord, tailWord_2922910, baseEnd_2922910] using wordTrace_append hprefix tailTrace_2922910
  have hstable : (prefixWord ++ tailWord_2922910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922910).length < 2 ^ (prefixWord ++ tailWord_2922910).sum := by decide
  have hdescent : baseEnd_2922910 < baseStart_2922910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922989 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2922989 : Nat := 118140960795 + 2922989 * 2 ^ 59
def prefixEnd_2922989 : Nat := 4983230072969 + 3 ^ 40 * 2922989 * 2
def baseEnd_2922989 : Nat := 333532956623326561287761

theorem tailTrace_2922989 : CollatzResearch.WordTrace tailWord_2922989 prefixEnd_2922989 333532956623326561287761 := by
  unfold tailWord_2922989
  simp only [CollatzResearch.WordTrace]
  refine ⟨106610167207517534622428021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71073444805011689748285347 106610167207517534622428021)
  ·
    refine ⟨9994703175704768870852627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106610167207517534622428021 9994703175704768870852627)
    ·
      refine ⟨14992054763557153306278941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994703175704768870852627 14992054763557153306278941)
      ·
        refine ⟨5622020536333932489854603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14992054763557153306278941 5622020536333932489854603)
        ·
          refine ⟨8433030804500898734781905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622020536333932489854603 8433030804500898734781905)
          ·
            refine ⟨6324773103375674051086429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433030804500898734781905 6324773103375674051086429)
            ·
              refine ⟨2371789913765877769157411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6324773103375674051086429 2371789913765877769157411)
              ·
                refine ⟨3557684870648816653736117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371789913765877769157411 3557684870648816653736117)
                ·
                  refine ⟨333532956623326561287761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557684870648816653736117 333532956623326561287761)
                  ·
                    rfl

theorem cell22_2922989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2922989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2922989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2922989 prefixEnd_2922989 := by exact prefixLift 2922989
  have htrace : WordTrace (prefixWord ++ tailWord_2922989) baseStart_2922989 baseEnd_2922989 := by
    simpa [prefixWord, tailWord_2922989, baseEnd_2922989] using wordTrace_append hprefix tailTrace_2922989
  have hstable : (prefixWord ++ tailWord_2922989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922989).length < 2 ^ (prefixWord ++ tailWord_2922989).sum := by decide
  have hdescent : baseEnd_2922989 < baseStart_2922989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923010 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2923010 : Nat := 118140960795 + 2923010 * 2 ^ 59
def prefixEnd_2923010 : Nat := 4983230072969 + 3 ^ 40 * 2923010 * 2
def baseEnd_2923010 : Nat := 1000606058599142629088219

theorem tailTrace_2923010 : CollatzResearch.WordTrace tailWord_2923010 prefixEnd_2923010 1000606058599142629088219 := by
  unfold tailWord_2923010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652733285110363802235621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71073955426960970139294989 26652733285110363802235621)
  ·
    refine ⟨4997387490958193212919179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26652733285110363802235621 4997387490958193212919179)
    ·
      refine ⟨7496081236437289819378769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997387490958193212919179 7496081236437289819378769)
      ·
        refine ⟨5622060927327967364534077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496081236437289819378769 5622060927327967364534077)
        ·
          refine ⟨2108272847747987761700279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5622060927327967364534077 2108272847747987761700279)
          ·
            refine ⟨3162409271621981642550419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108272847747987761700279 3162409271621981642550419)
            ·
              refine ⟨4743613907432972463825629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162409271621981642550419 4743613907432972463825629)
              ·
                refine ⟨1778855215287364673934611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4743613907432972463825629 1778855215287364673934611)
                ·
                  refine ⟨2668282822931047010901917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778855215287364673934611 2668282822931047010901917)
                  ·
                    refine ⟨1000606058599142629088219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668282822931047010901917 1000606058599142629088219)
                    ·
                      rfl

theorem cell22_2923010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2923010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923010 prefixEnd_2923010 := by exact prefixLift 2923010
  have htrace : WordTrace (prefixWord ++ tailWord_2923010) baseStart_2923010 baseEnd_2923010 := by
    simpa [prefixWord, tailWord_2923010, baseEnd_2923010] using wordTrace_append hprefix tailTrace_2923010
  have hstable : (prefixWord ++ tailWord_2923010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923010).length < 2 ^ (prefixWord ++ tailWord_2923010).sum := by decide
  have hdescent : baseEnd_2923010 < baseStart_2923010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923032 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_2923032 : Nat := 118140960795 + 2923032 * 2 ^ 59
def prefixEnd_2923032 : Nat := 4983230072969 + 3 ^ 40 * 2923032 * 2
def baseEnd_2923032 : Nat := 1000613589648741905038151

theorem tailTrace_2923032 : CollatzResearch.WordTrace tailWord_2923032 prefixEnd_2923032 1000613589648741905038151 := by
  unfold tailWord_2923032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53305867773180876483121675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71074490364241168644162233 53305867773180876483121675)
  ·
    refine ⟨79958801659771314724682513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53305867773180876483121675 79958801659771314724682513)
    ·
      refine ⟨59969101244828486043511885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79958801659771314724682513 59969101244828486043511885)
      ·
        refine ⟨22488412966810682266316957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59969101244828486043511885 22488412966810682266316957)
        ·
          refine ⟨8433154862554005849868859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22488412966810682266316957 8433154862554005849868859)
          ·
            refine ⟨12649732293831008774803289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433154862554005849868859 12649732293831008774803289)
            ·
              refine ⟨9487299220373256581102467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649732293831008774803289 9487299220373256581102467)
              ·
                refine ⟨14230948830559884871653701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487299220373256581102467 14230948830559884871653701)
                ·
                  refine ⟨2668302905729978413435069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14230948830559884871653701 2668302905729978413435069)
                  ·
                    refine ⟨1000613589648741905038151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668302905729978413435069 1000613589648741905038151)
                    ·
                      rfl

theorem cell22_2923032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_2923032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923032 prefixEnd_2923032 := by exact prefixLift 2923032
  have htrace : WordTrace (prefixWord ++ tailWord_2923032) baseStart_2923032 baseEnd_2923032 := by
    simpa [prefixWord, tailWord_2923032, baseEnd_2923032] using wordTrace_append hprefix tailTrace_2923032
  have hstable : (prefixWord ++ tailWord_2923032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923032).length < 2 ^ (prefixWord ++ tailWord_2923032).sum := by decide
  have hdescent : baseEnd_2923032 < baseStart_2923032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923062 : List Nat := [5, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2923062 : Nat := 118140960795 + 2923062 * 2 ^ 59
def prefixEnd_2923062 : Nat := 4983230072969 + 3 ^ 40 * 2923062 * 2
def baseEnd_2923062 : Nat := 111180428806870202976451

theorem tailTrace_2923062 : CollatzResearch.WordTrace tailWord_2923062 prefixEnd_2923062 111180428806870202976451 := by
  unfold tailWord_2923062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663301858515816755614715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71075219824168712059890293 6663301858515816755614715)
  ·
    refine ⟨9994952787773725133422073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663301858515816755614715 9994952787773725133422073)
    ·
      refine ⟨7496214590830293850066555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994952787773725133422073 7496214590830293850066555)
      ·
        refine ⟨11244321886245440775099833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496214590830293850066555 11244321886245440775099833)
        ·
          refine ⟨8433241414684080581324875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11244321886245440775099833 8433241414684080581324875)
          ·
            refine ⟨12649862122026120871987313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433241414684080581324875 12649862122026120871987313)
            ·
              refine ⟨9487396591519590653990485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649862122026120871987313 9487396591519590653990485)
              ·
                refine ⟨111180428806870202976451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9487396591519590653990485 111180428806870202976451)
                ·
                  rfl

theorem cell22_2923062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2923062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923062 prefixEnd_2923062 := by exact prefixLift 2923062
  have htrace : WordTrace (prefixWord ++ tailWord_2923062) baseStart_2923062 baseEnd_2923062 := by
    simpa [prefixWord, tailWord_2923062, baseEnd_2923062] using wordTrace_append hprefix tailTrace_2923062
  have hstable : (prefixWord ++ tailWord_2923062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923062).length < 2 ^ (prefixWord ++ tailWord_2923062).sum := by decide
  have hdescent : baseEnd_2923062 < baseStart_2923062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923105 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2923105 : Nat := 118140960795 + 2923105 * 2 ^ 59
def prefixEnd_2923105 : Nat := 4983230072969 + 3 ^ 40 * 2923105 * 2
def baseEnd_2923105 : Nat := 1000638579040594047962927

theorem tailTrace_2923105 : CollatzResearch.WordTrace tailWord_2923105 prefixEnd_2923105 1000638579040594047962927 := by
  unfold tailWord_2923105
  simp only [CollatzResearch.WordTrace]
  refine ⟨106614398075097286433650769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71076265383398190955767179 106614398075097286433650769)
  ·
    refine ⟨79960798556322964825238077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106614398075097286433650769 79960798556322964825238077)
    ·
      refine ⟨29985299458621111809464279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79960798556322964825238077 29985299458621111809464279)
      ·
        refine ⟨44977949187931667714196419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29985299458621111809464279 44977949187931667714196419)
        ·
          refine ⟨67466923781897501571294629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44977949187931667714196419 67466923781897501571294629)
          ·
            refine ⟨12650048209105781544617743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67466923781897501571294629 12650048209105781544617743)
            ·
              refine ⟨18975072313658672316926615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650048209105781544617743 18975072313658672316926615)
              ·
                refine ⟨28462608470488008475389923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18975072313658672316926615 28462608470488008475389923)
                ·
                  refine ⟨42693912705732012713084885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28462608470488008475389923 42693912705732012713084885)
                  ·
                    refine ⟨1000638579040594047962927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42693912705732012713084885 1000638579040594047962927)
                    ·
                      rfl

theorem cell22_2923105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2923105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923105 prefixEnd_2923105 := by exact prefixLift 2923105
  have htrace : WordTrace (prefixWord ++ tailWord_2923105) baseStart_2923105 baseEnd_2923105 := by
    simpa [prefixWord, tailWord_2923105, baseEnd_2923105] using wordTrace_append hprefix tailTrace_2923105
  have hstable : (prefixWord ++ tailWord_2923105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923105).length < 2 ^ (prefixWord ++ tailWord_2923105).sum := by decide
  have hdescent : baseEnd_2923105 < baseStart_2923105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923197 : List Nat := [1, 4, 1, 2, 1, 5, 8]
def baseStart_2923197 : Nat := 118140960795 + 2923197 * 2 ^ 59
def prefixEnd_2923197 : Nat := 4983230072969 + 3 ^ 40 * 2923197 * 2
def baseEnd_2923197 : Nat := 37061854537805054617135

theorem tailTrace_2923197 : CollatzResearch.WordTrace tailWord_2923197 prefixEnd_2923197 37061854537805054617135 := by
  unfold tailWord_2923197
  simp only [CollatzResearch.WordTrace]
  refine ⟨106617753590763986145999845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71078502393842657430666563 106617753590763986145999845)
  ·
    refine ⟨19990828798268247402374971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106617753590763986145999845 19990828798268247402374971)
    ·
      refine ⟨29986243197402371103562457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19990828798268247402374971 29986243197402371103562457)
      ·
        refine ⟨22489682398051778327671843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29986243197402371103562457 22489682398051778327671843)
        ·
          refine ⟨33734523597077667491507765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22489682398051778327671843 33734523597077667491507765)
          ·
            refine ⟨3162611587226031327328853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33734523597077667491507765 3162611587226031327328853)
            ·
              refine ⟨37061854537805054617135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3162611587226031327328853 37061854537805054617135)
              ·
                rfl

theorem cell22_2923197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 8].length) (baseStart_2923197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923197 prefixEnd_2923197 := by exact prefixLift 2923197
  have htrace : WordTrace (prefixWord ++ tailWord_2923197) baseStart_2923197 baseEnd_2923197 := by
    simpa [prefixWord, tailWord_2923197, baseEnd_2923197] using wordTrace_append hprefix tailTrace_2923197
  have hstable : (prefixWord ++ tailWord_2923197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923197).length < 2 ^ (prefixWord ++ tailWord_2923197).sum := by decide
  have hdescent : baseEnd_2923197 < baseStart_2923197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923319 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 4, 3]
def baseStart_2923319 : Nat := 118140960795 + 2923319 * 2 ^ 59
def prefixEnd_2923319 : Nat := 4983230072969 + 3 ^ 40 * 2923319 * 2
def baseEnd_2923319 : Nat := 1000711835613968823112271

theorem tailTrace_2923319 : CollatzResearch.WordTrace tailWord_2923319 prefixEnd_2923319 1000711835613968823112271 := by
  unfold tailWord_2923319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106622203296322000981941011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71081468864214667321294007 106622203296322000981941011)
  ·
    refine ⟨159933304944483001472911517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106622203296322000981941011 159933304944483001472911517)
    ·
      refine ⟨59974989354181125552341819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159933304944483001472911517 59974989354181125552341819)
      ·
        refine ⟨89962484031271688328512729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59974989354181125552341819 89962484031271688328512729)
        ·
          refine ⟨67471863023453766246384547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89962484031271688328512729 67471863023453766246384547)
          ·
            refine ⟨101207794535180649369576821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67471863023453766246384547 101207794535180649369576821)
            ·
              refine ⟨9488230737673185878397827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101207794535180649369576821 9488230737673185878397827)
              ·
                refine ⟨14232346106509778817596741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488230737673185878397827 14232346106509778817596741)
                ·
                  refine ⟨2668564894970583528299389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14232346106509778817596741 2668564894970583528299389)
                  ·
                    refine ⟨1000711835613968823112271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668564894970583528299389 1000711835613968823112271)
                    ·
                      rfl

theorem cell22_2923319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_2923319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923319 prefixEnd_2923319 := by exact prefixLift 2923319
  have htrace : WordTrace (prefixWord ++ tailWord_2923319) baseStart_2923319 baseEnd_2923319 := by
    simpa [prefixWord, tailWord_2923319, baseEnd_2923319] using wordTrace_append hprefix tailTrace_2923319
  have hstable : (prefixWord ++ tailWord_2923319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923319).length < 2 ^ (prefixWord ++ tailWord_2923319).sum := by decide
  have hdescent : baseEnd_2923319 < baseStart_2923319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923490 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2923490 : Nat := 118140960795 + 2923490 * 2 ^ 59
def prefixEnd_2923490 : Nat := 4983230072969 + 3 ^ 40 * 2923490 * 2
def baseEnd_2923490 : Nat := 333590124136193792362249

theorem tailTrace_2923490 : CollatzResearch.WordTrace tailWord_2923490 prefixEnd_2923490 333590124136193792362249 := by
  unfold tailWord_2923490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657110044675624296603981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71085626785801664790943949 26657110044675624296603981)
  ·
    refine ⟨9996416266753359111226493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26657110044675624296603981 9996416266753359111226493)
    ·
      refine ⟨3748656100032509666709935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9996416266753359111226493 3748656100032509666709935)
      ·
        refine ⟨5622984150048764500064903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748656100032509666709935 5622984150048764500064903)
        ·
          refine ⟨8434476225073146750097355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622984150048764500064903 8434476225073146750097355)
          ·
            refine ⟨12651714337609720125146033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434476225073146750097355 12651714337609720125146033)
            ·
              refine ⟨9488785753207290093859525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12651714337609720125146033 9488785753207290093859525)
              ·
                refine ⟨1779147328726366892598661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9488785753207290093859525 1779147328726366892598661)
                ·
                  refine ⟨333590124136193792362249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779147328726366892598661 333590124136193792362249)
                  ·
                    rfl

theorem cell22_2923490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2923490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923490 prefixEnd_2923490 := by exact prefixLift 2923490
  have htrace : WordTrace (prefixWord ++ tailWord_2923490) baseStart_2923490 baseEnd_2923490 := by
    simpa [prefixWord, tailWord_2923490, baseEnd_2923490] using wordTrace_append hprefix tailTrace_2923490
  have hstable : (prefixWord ++ tailWord_2923490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923490).length < 2 ^ (prefixWord ++ tailWord_2923490).sum := by decide
  have hdescent : baseEnd_2923490 < baseStart_2923490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923505 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_2923505 : Nat := 118140960795 + 2923505 * 2 ^ 59
def prefixEnd_2923505 : Nat := 4983230072969 + 3 ^ 40 * 2923505 * 2
def baseEnd_2923505 : Nat := 1000775507215126337961701

theorem tailTrace_2923505 : CollatzResearch.WordTrace tailWord_2923505 prefixEnd_2923505 1000775507215126337961701 := by
  unfold tailWord_2923505
  simp only [CollatzResearch.WordTrace]
  refine ⟨106628987273648154748211969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71085991515765436498807979 106628987273648154748211969)
  ·
    refine ⟨79971740455236116061158977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106628987273648154748211969 79971740455236116061158977)
    ·
      refine ⟨59978805341427087045869233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79971740455236116061158977 59978805341427087045869233)
      ·
        refine ⟨44984104006070315284401925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59978805341427087045869233 44984104006070315284401925)
        ·
          refine ⟨8434519501138184115825361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44984104006070315284401925 8434519501138184115825361)
          ·
            refine ⟨6325889625853638086869021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8434519501138184115825361 6325889625853638086869021)
            ·
              refine ⟨2372208609695114282575883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6325889625853638086869021 2372208609695114282575883)
              ·
                refine ⟨3558312914542671423863825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372208609695114282575883 3558312914542671423863825)
                ·
                  refine ⟨2668734685907003567897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558312914542671423863825 2668734685907003567897869)
                  ·
                    refine ⟨1000775507215126337961701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668734685907003567897869 1000775507215126337961701)
                    ·
                      rfl

theorem cell22_2923505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_2923505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923505 prefixEnd_2923505 := by exact prefixLift 2923505
  have htrace : WordTrace (prefixWord ++ tailWord_2923505) baseStart_2923505 baseEnd_2923505 := by
    simpa [prefixWord, tailWord_2923505, baseEnd_2923505] using wordTrace_append hprefix tailTrace_2923505
  have hstable : (prefixWord ++ tailWord_2923505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923505).length < 2 ^ (prefixWord ++ tailWord_2923505).sum := by decide
  have hdescent : baseEnd_2923505 < baseStart_2923505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923514 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_2923514 : Nat := 118140960795 + 2923514 * 2 ^ 59
def prefixEnd_2923514 : Nat := 4983230072969 + 3 ^ 40 * 2923514 * 2
def baseEnd_2923514 : Nat := 1000778588099053314486673

theorem tailTrace_2923514 : CollatzResearch.WordTrace tailWord_2923514 prefixEnd_2923514 1000778588099053314486673 := by
  unfold tailWord_2923514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657328882653887321322399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71086210353743699523526397 26657328882653887321322399)
  ·
    refine ⟨39985993323980830981983599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26657328882653887321322399 39985993323980830981983599)
    ·
      refine ⟨59978989985971246472975399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39985993323980830981983599 59978989985971246472975399)
      ·
        refine ⟨89968484978956869709463099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59978989985971246472975399 89968484978956869709463099)
        ·
          refine ⟨134952727468435304564194649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89968484978956869709463099 134952727468435304564194649)
          ·
            refine ⟨101214545601326478423145987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134952727468435304564194649 101214545601326478423145987)
            ·
              refine ⟨151821818401989717634718981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101214545601326478423145987 151821818401989717634718981)
              ·
                refine ⟨28466590950373072056509809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151821818401989717634718981 28466590950373072056509809)
                ·
                  refine ⟨21349943212779804042382357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28466590950373072056509809 21349943212779804042382357)
                  ·
                    refine ⟨1000778588099053314486673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21349943212779804042382357 1000778588099053314486673)
                    ·
                      rfl

theorem cell22_2923514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_2923514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923514 prefixEnd_2923514 := by exact prefixLift 2923514
  have htrace : WordTrace (prefixWord ++ tailWord_2923514) baseStart_2923514 baseEnd_2923514 := by
    simpa [prefixWord, tailWord_2923514, baseEnd_2923514] using wordTrace_append hprefix tailTrace_2923514
  have hstable : (prefixWord ++ tailWord_2923514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923514).length < 2 ^ (prefixWord ++ tailWord_2923514).sum := by decide
  have hdescent : baseEnd_2923514 < baseStart_2923514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923518 : List Nat := [4, 2, 2, 2, 2, 1, 1, 8]
def baseStart_2923518 : Nat := 118140960795 + 2923518 * 2 ^ 59
def prefixEnd_2923518 : Nat := 4983230072969 + 3 ^ 40 * 2923518 * 2
def baseEnd_2923518 : Nat := 111197773042310959709629

theorem tailTrace_2923518 : CollatzResearch.WordTrace tailWord_2923518 prefixEnd_2923518 111197773042310959709629 := by
  unfold tailWord_2923518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328682677825132246054401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71086307615067371978956805 13328682677825132246054401)
  ·
    refine ⟨9996512008368849184540801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13328682677825132246054401 9996512008368849184540801)
    ·
      refine ⟨7497384006276636888405601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9996512008368849184540801 7497384006276636888405601)
      ·
        refine ⟨5623038004707477666304201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7497384006276636888405601 5623038004707477666304201)
        ·
          refine ⟨4217278503530608249728151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623038004707477666304201 4217278503530608249728151)
          ·
            refine ⟨6325917755295912374592227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217278503530608249728151 6325917755295912374592227)
            ·
              refine ⟨9488876632943868561888341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325917755295912374592227 9488876632943868561888341)
              ·
                refine ⟨111197773042310959709629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9488876632943868561888341 111197773042310959709629)
                ·
                  rfl

theorem cell22_2923518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_2923518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923518 prefixEnd_2923518 := by exact prefixLift 2923518
  have htrace : WordTrace (prefixWord ++ tailWord_2923518) baseStart_2923518 baseEnd_2923518 := by
    simpa [prefixWord, tailWord_2923518, baseEnd_2923518] using wordTrace_append hprefix tailTrace_2923518
  have hstable : (prefixWord ++ tailWord_2923518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923518).length < 2 ^ (prefixWord ++ tailWord_2923518).sum := by decide
  have hdescent : baseEnd_2923518 < baseStart_2923518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923546 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_2923546 : Nat := 118140960795 + 2923546 * 2 ^ 59
def prefixEnd_2923546 : Nat := 4983230072969 + 3 ^ 40 * 2923546 * 2
def baseEnd_2923546 : Nat := 333596514117671965895525

theorem tailTrace_2923546 : CollatzResearch.WordTrace tailWord_2923546 prefixEnd_2923546 333596514117671965895525 := by
  unfold tailWord_2923546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657620666624904687613623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71086988444333079166969661 26657620666624904687613623)
  ·
    refine ⟨39986430999937357031420435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26657620666624904687613623 39986430999937357031420435)
    ·
      refine ⟨59979646499906035547130653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39986430999937357031420435 59979646499906035547130653)
      ·
        refine ⟨22492367437464763330173995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59979646499906035547130653 22492367437464763330173995)
        ·
          refine ⟨33738551156197144995260993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22492367437464763330173995 33738551156197144995260993)
          ·
            refine ⟨25303913367147858746445745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33738551156197144995260993 25303913367147858746445745)
            ·
              refine ⟨18977935025360894059834309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25303913367147858746445745 18977935025360894059834309)
              ·
                refine ⟨3558362817255167636218933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18977935025360894059834309 3558362817255167636218933)
                ·
                  refine ⟨333596514117671965895525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558362817255167636218933 333596514117671965895525)
                  ·
                    rfl

theorem cell22_2923546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_2923546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923546 prefixEnd_2923546 := by exact prefixLift 2923546
  have htrace : WordTrace (prefixWord ++ tailWord_2923546) baseStart_2923546 baseEnd_2923546 := by
    simpa [prefixWord, tailWord_2923546, baseEnd_2923546] using wordTrace_append hprefix tailTrace_2923546
  have hstable : (prefixWord ++ tailWord_2923546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923546).length < 2 ^ (prefixWord ++ tailWord_2923546).sum := by decide
  have hdescent : baseEnd_2923546 < baseStart_2923546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923608 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_2923608 : Nat := 118140960795 + 2923608 * 2 ^ 59
def prefixEnd_2923608 : Nat := 4983230072969 + 3 ^ 40 * 2923608 * 2
def baseEnd_2923608 : Nat := 333603588740022800878795

theorem tailTrace_2923608 : CollatzResearch.WordTrace tailWord_2923608 prefixEnd_2923608 333603588740022800878795 := by
  unfold tailWord_2923608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53316371996137501669605739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71088495994850002226140985 53316371996137501669605739)
  ·
    refine ⟨79974557994206252504408609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53316371996137501669605739 79974557994206252504408609)
    ·
      refine ⟨59980918495654689378306457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79974557994206252504408609 59980918495654689378306457)
      ·
        refine ⟨44985688871741017033729843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59980918495654689378306457 44985688871741017033729843)
        ·
          refine ⟨67478533307611525550594765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44985688871741017033729843 67478533307611525550594765)
          ·
            refine ⟨25304449990354322081473037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67478533307611525550594765 25304449990354322081473037)
            ·
              refine ⟨9489168746382870780552389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25304449990354322081473037 9489168746382870780552389)
              ·
                refine ⟨1779219139946788271353573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9489168746382870780552389 1779219139946788271353573)
                ·
                  refine ⟨333603588740022800878795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779219139946788271353573 333603588740022800878795)
                  ·
                    rfl

theorem cell22_2923608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_2923608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923608 prefixEnd_2923608 := by exact prefixLift 2923608
  have htrace : WordTrace (prefixWord ++ tailWord_2923608) baseStart_2923608 baseEnd_2923608 := by
    simpa [prefixWord, tailWord_2923608, baseEnd_2923608] using wordTrace_append hprefix tailTrace_2923608
  have hstable : (prefixWord ++ tailWord_2923608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923608).length < 2 ^ (prefixWord ++ tailWord_2923608).sum := by decide
  have hdescent : baseEnd_2923608 < baseStart_2923608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923621 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2923621 : Nat := 118140960795 + 2923621 * 2 ^ 59
def prefixEnd_2923621 : Nat := 4983230072969 + 3 ^ 40 * 2923621 * 2
def baseEnd_2923621 : Nat := 1000815216385740702061345

theorem tailTrace_2923621 : CollatzResearch.WordTrace tailWord_2923621 prefixEnd_2923621 1000815216385740702061345 := by
  unfold tailWord_2923621
  simp only [CollatzResearch.WordTrace]
  refine ⟨106633218141227906559434717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71088812094151937706289811 106633218141227906559434717)
  ·
    refine ⟨39987456802960464959788019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106633218141227906559434717 39987456802960464959788019)
    ·
      refine ⟨59981185204440697439682029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39987456802960464959788019 59981185204440697439682029)
      ·
        refine ⟨22492944451665261539880761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59981185204440697439682029 22492944451665261539880761)
        ·
          refine ⟨16869708338748946154910571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22492944451665261539880761 16869708338748946154910571)
          ·
            refine ⟨25304562508123419232365857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16869708338748946154910571 25304562508123419232365857)
            ·
              refine ⟨18978421881092564424274393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25304562508123419232365857 18978421881092564424274393)
              ·
                refine ⟨14233816410819423318205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18978421881092564424274393 14233816410819423318205795)
                ·
                  refine ⟨21350724616229134977308693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14233816410819423318205795 21350724616229134977308693)
                  ·
                    refine ⟨1000815216385740702061345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21350724616229134977308693 1000815216385740702061345)
                    ·
                      rfl

theorem cell22_2923621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2923621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923621 prefixEnd_2923621 := by exact prefixLift 2923621
  have htrace : WordTrace (prefixWord ++ tailWord_2923621) baseStart_2923621 baseEnd_2923621 := by
    simpa [prefixWord, tailWord_2923621, baseEnd_2923621] using wordTrace_append hprefix tailTrace_2923621
  have hstable : (prefixWord ++ tailWord_2923621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923621).length < 2 ^ (prefixWord ++ tailWord_2923621).sum := by decide
  have hdescent : baseEnd_2923621 < baseStart_2923621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923623 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2923623 : Nat := 118140960795 + 2923623 * 2 ^ 59
def prefixEnd_2923623 : Nat := 4983230072969 + 3 ^ 40 * 2923623 * 2
def baseEnd_2923623 : Nat := 1000815901026613363511339

theorem tailTrace_2923623 : CollatzResearch.WordTrace tailWord_2923623 prefixEnd_2923623 1000815901026613363511339 := by
  unfold tailWord_2923623
  simp only [CollatzResearch.WordTrace]
  refine ⟨106633291087220660901007523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71088860724813773934005015 106633291087220660901007523)
  ·
    refine ⟨159949936630830991351511285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106633291087220660901007523 159949936630830991351511285)
    ·
      refine ⟨14995306559140405439204183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159949936630830991351511285 14995306559140405439204183)
      ·
        refine ⟨22492959838710608158806275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14995306559140405439204183 22492959838710608158806275)
        ·
          refine ⟨33739439758065912238209413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22492959838710608158806275 33739439758065912238209413)
          ·
            refine ⟨6326144954637358544664265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33739439758065912238209413 6326144954637358544664265)
            ·
              refine ⟨4744608715978018908498199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6326144954637358544664265 4744608715978018908498199)
              ·
                refine ⟨7116913073967028362747299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744608715978018908498199 7116913073967028362747299)
                ·
                  refine ⟨10675369610950542544120949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7116913073967028362747299 10675369610950542544120949)
                  ·
                    refine ⟨1000815901026613363511339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10675369610950542544120949 1000815901026613363511339)
                    ·
                      rfl

theorem cell22_2923623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2923623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923623 prefixEnd_2923623 := by exact prefixLift 2923623
  have htrace : WordTrace (prefixWord ++ tailWord_2923623) baseStart_2923623 baseEnd_2923623 := by
    simpa [prefixWord, tailWord_2923623, baseEnd_2923623] using wordTrace_append hprefix tailTrace_2923623
  have hstable : (prefixWord ++ tailWord_2923623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923623).length < 2 ^ (prefixWord ++ tailWord_2923623).sum := by decide
  have hdescent : baseEnd_2923623 < baseStart_2923623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923638 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2923638 : Nat := 118140960795 + 2923638 * 2 ^ 59
def prefixEnd_2923638 : Nat := 4983230072969 + 3 ^ 40 * 2923638 * 2
def baseEnd_2923638 : Nat := 1000821035833158324386293

theorem tailTrace_2923638 : CollatzResearch.WordTrace tailWord_2923638 prefixEnd_2923638 1000821035833158324386293 := by
  unfold tailWord_2923638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664614886385394903925223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71089225454777545641869045 6664614886385394903925223)
  ·
    refine ⟨9996922329578092355887835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6664614886385394903925223 9996922329578092355887835)
    ·
      refine ⟨14995383494367138533831753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9996922329578092355887835 14995383494367138533831753)
      ·
        refine ⟨11246537620775353900373815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14995383494367138533831753 11246537620775353900373815)
        ·
          refine ⟨16869806431163030850560723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11246537620775353900373815 16869806431163030850560723)
          ·
            refine ⟨25304709646744546275841085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16869806431163030850560723 25304709646744546275841085)
            ·
              refine ⟨9489266117529204853440407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25304709646744546275841085 9489266117529204853440407)
              ·
                refine ⟨14233899176293807280160611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9489266117529204853440407 14233899176293807280160611)
                ·
                  refine ⟨21350848764440710920240917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14233899176293807280160611 21350848764440710920240917)
                  ·
                    refine ⟨1000821035833158324386293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21350848764440710920240917 1000821035833158324386293)
                    ·
                      rfl

theorem cell22_2923638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2923638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923638 prefixEnd_2923638 := by exact prefixLift 2923638
  have htrace : WordTrace (prefixWord ++ tailWord_2923638) baseStart_2923638 baseEnd_2923638 := by
    simpa [prefixWord, tailWord_2923638, baseEnd_2923638] using wordTrace_append hprefix tailTrace_2923638
  have hstable : (prefixWord ++ tailWord_2923638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923638).length < 2 ^ (prefixWord ++ tailWord_2923638).sum := by decide
  have hdescent : baseEnd_2923638 < baseStart_2923638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923732 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2923732 : Nat := 118140960795 + 2923732 * 2 ^ 59
def prefixEnd_2923732 : Nat := 4983230072969 + 3 ^ 40 * 2923732 * 2
def baseEnd_2923732 : Nat := 333617737984724470845335

theorem tailTrace_2923732 : CollatzResearch.WordTrace tailWord_2923732 prefixEnd_2923732 333617737984724470845335 := by
  unfold tailWord_2923732
  simp only [CollatzResearch.WordTrace]
  refine ⟨53318633321912886258362725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71091511095883848344483633 53318633321912886258362725)
  ·
    refine ⟨9997243747858666173443011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53318633321912886258362725 9997243747858666173443011)
    ·
      refine ⟨14995865621787999260164517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9997243747858666173443011 14995865621787999260164517)
      ·
        refine ⟨2811724804085249861280847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14995865621787999260164517 2811724804085249861280847)
        ·
          refine ⟨4217587206127874791921271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811724804085249861280847 4217587206127874791921271)
          ·
            refine ⟨6326380809191812187881907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217587206127874791921271 6326380809191812187881907)
            ·
              refine ⟨9489571213787718281822861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326380809191812187881907 9489571213787718281822861)
              ·
                refine ⟨3558589205170394355683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9489571213787718281822861 3558589205170394355683573)
                ·
                  refine ⟨333617737984724470845335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558589205170394355683573 333617737984724470845335)
                  ·
                    rfl

theorem cell22_2923732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2923732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923732 prefixEnd_2923732 := by exact prefixLift 2923732
  have htrace : WordTrace (prefixWord ++ tailWord_2923732) baseStart_2923732 baseEnd_2923732 := by
    simpa [prefixWord, tailWord_2923732, baseEnd_2923732] using wordTrace_append hprefix tailTrace_2923732
  have hstable : (prefixWord ++ tailWord_2923732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923732).length < 2 ^ (prefixWord ++ tailWord_2923732).sum := by decide
  have hdescent : baseEnd_2923732 < baseStart_2923732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923745 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2923745 : Nat := 118140960795 + 2923745 * 2 ^ 59
def prefixEnd_2923745 : Nat := 4983230072969 + 3 ^ 40 * 2923745 * 2
def baseEnd_2923745 : Nat := 1000857664119845711960965

theorem tailTrace_2923745 : CollatzResearch.WordTrace tailWord_2923745 prefixEnd_2923745 1000857664119845711960965 := by
  unfold tailWord_2923745
  simp only [CollatzResearch.WordTrace]
  refine ⟨106637740792778675736948689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71091827195185783824632459 106637740792778675736948689)
  ·
    refine ⟨79978305594584006802711517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106637740792778675736948689 79978305594584006802711517)
    ·
      refine ⟨29991864597969002551016819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79978305594584006802711517 29991864597969002551016819)
      ·
        refine ⟨44987796896953503826525229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29991864597969002551016819 44987796896953503826525229)
        ·
          refine ⟨16870423836357563934946961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44987796896953503826525229 16870423836357563934946961)
          ·
            refine ⟨12652817877268172951210221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16870423836357563934946961 12652817877268172951210221)
            ·
              refine ⟨4744806703975564856703833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12652817877268172951210221 4744806703975564856703833)
              ·
                refine ⟨3558605027981673642527875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744806703975564856703833 3558605027981673642527875)
                ·
                  refine ⟨5337907541972510463791813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558605027981673642527875 5337907541972510463791813)
                  ·
                    refine ⟨1000857664119845711960965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5337907541972510463791813 1000857664119845711960965)
                    ·
                      rfl

theorem cell22_2923745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2923745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923745 prefixEnd_2923745 := by exact prefixLift 2923745
  have htrace : WordTrace (prefixWord ++ tailWord_2923745) baseStart_2923745 baseEnd_2923745 := by
    simpa [prefixWord, tailWord_2923745, baseEnd_2923745] using wordTrace_append hprefix tailTrace_2923745
  have hstable : (prefixWord ++ tailWord_2923745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923745).length < 2 ^ (prefixWord ++ tailWord_2923745).sum := by decide
  have hdescent : baseEnd_2923745 < baseStart_2923745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923758 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2923758 : Nat := 118140960795 + 2923758 * 2 ^ 59
def prefixEnd_2923758 : Nat := 4983230072969 + 3 ^ 40 * 2923758 * 2
def baseEnd_2923758 : Nat := 1000862114285518011385925

theorem tailTrace_2923758 : CollatzResearch.WordTrace tailWord_2923758 prefixEnd_2923758 1000862114285518011385925 := by
  unfold tailWord_2923758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329776867716447369646491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71092143294487719304781285 13329776867716447369646491)
  ·
    refine ⟨19994665301574671054469737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13329776867716447369646491 19994665301574671054469737)
    ·
      refine ⟨14995998976181003290852303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19994665301574671054469737 14995998976181003290852303)
      ·
        refine ⟨22493998464271504936278455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14995998976181003290852303 22493998464271504936278455)
        ·
          refine ⟨33740997696407257404417683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22493998464271504936278455 33740997696407257404417683)
          ·
            refine ⟨50611496544610886106626525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33740997696407257404417683 50611496544610886106626525)
            ·
              refine ⟨18979311204229082289984947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50611496544610886106626525 18979311204229082289984947)
              ·
                refine ⟨28468966806343623434977421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18979311204229082289984947 28468966806343623434977421)
                ·
                  refine ⟨10675862552378858788116533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28468966806343623434977421 10675862552378858788116533)
                  ·
                    refine ⟨1000862114285518011385925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10675862552378858788116533 1000862114285518011385925)
                    ·
                      rfl

theorem cell22_2923758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2923758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923758 prefixEnd_2923758 := by exact prefixLift 2923758
  have htrace : WordTrace (prefixWord ++ tailWord_2923758) baseStart_2923758 baseEnd_2923758 := by
    simpa [prefixWord, tailWord_2923758, baseEnd_2923758] using wordTrace_append hprefix tailTrace_2923758
  have hstable : (prefixWord ++ tailWord_2923758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923758).length < 2 ^ (prefixWord ++ tailWord_2923758).sum := by decide
  have hdescent : baseEnd_2923758 < baseStart_2923758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923775 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 2, 3]
def baseStart_2923775 : Nat := 118140960795 + 2923775 * 2 ^ 59
def prefixEnd_2923775 : Nat := 4983230072969 + 3 ^ 40 * 2923775 * 2
def baseEnd_2923775 : Nat := 1000867933732935633710873

theorem tailTrace_2923775 : CollatzResearch.WordTrace tailWord_2923775 prefixEnd_2923775 1000867933732935633710873 := by
  unfold tailWord_2923775
  simp only [CollatzResearch.WordTrace]
  refine ⟨106638834982669990860540779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71092556655113327240360519 106638834982669990860540779)
  ·
    refine ⟨159958252474004986290811169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106638834982669990860540779 159958252474004986290811169)
    ·
      refine ⟨119968689355503739718108377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159958252474004986290811169 119968689355503739718108377)
      ·
        refine ⟨89976517016627804788581283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119968689355503739718108377 89976517016627804788581283)
        ·
          refine ⟨134964775524941707182871925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89976517016627804788581283 134964775524941707182871925)
          ·
            refine ⟨12652947705463285048394243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134964775524941707182871925 12652947705463285048394243)
            ·
              refine ⟨18979421558194927572591365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12652947705463285048394243 18979421558194927572591365)
              ·
                refine ⟨3558641542161548919860881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18979421558194927572591365 3558641542161548919860881)
                ·
                  refine ⟨2668981156621161689895661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558641542161548919860881 2668981156621161689895661)
                  ·
                    refine ⟨1000867933732935633710873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668981156621161689895661 1000867933732935633710873)
                    ·
                      rfl

theorem cell22_2923775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_2923775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923775 prefixEnd_2923775 := by exact prefixLift 2923775
  have htrace : WordTrace (prefixWord ++ tailWord_2923775) baseStart_2923775 baseEnd_2923775 := by
    simpa [prefixWord, tailWord_2923775, baseEnd_2923775] using wordTrace_append hprefix tailTrace_2923775
  have hstable : (prefixWord ++ tailWord_2923775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923775).length < 2 ^ (prefixWord ++ tailWord_2923775).sum := by decide
  have hdescent : baseEnd_2923775 < baseStart_2923775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923777 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 4]
def baseStart_2923777 : Nat := 118140960795 + 2923777 * 2 ^ 59
def prefixEnd_2923777 : Nat := 4983230072969 + 3 ^ 40 * 2923777 * 2
def baseEnd_2923777 : Nat := 333622872791269431720289

theorem tailTrace_2923777 : CollatzResearch.WordTrace tailWord_2923777 prefixEnd_2923777 333622872791269431720289 := by
  unfold tailWord_2923777
  simp only [CollatzResearch.WordTrace]
  refine ⟨106638907928662745202113585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71092605285775163468075723 106638907928662745202113585)
  ·
    refine ⟨79979180946497058901585189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106638907928662745202113585 79979180946497058901585189)
    ·
      refine ⟨14996096427468198544047223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79979180946497058901585189 14996096427468198544047223)
      ·
        refine ⟨22494144641202297816070835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14996096427468198544047223 22494144641202297816070835)
        ·
          refine ⟨33741216961803446724106253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494144641202297816070835 33741216961803446724106253)
          ·
            refine ⟨12652956360676292521539845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33741216961803446724106253 12652956360676292521539845)
            ·
              refine ⟨2372429317626804847788721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12652956360676292521539845 2372429317626804847788721)
              ·
                refine ⟨1779321988220103635841541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372429317626804847788721 1779321988220103635841541)
                ·
                  refine ⟨333622872791269431720289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779321988220103635841541 333622872791269431720289)
                  ·
                    rfl

theorem cell22_2923777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_2923777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923777 prefixEnd_2923777 := by exact prefixLift 2923777
  have htrace : WordTrace (prefixWord ++ tailWord_2923777) baseStart_2923777 baseEnd_2923777 := by
    simpa [prefixWord, tailWord_2923777, baseEnd_2923777] using wordTrace_append hprefix tailTrace_2923777
  have hstable : (prefixWord ++ tailWord_2923777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923777).length < 2 ^ (prefixWord ++ tailWord_2923777).sum := by decide
  have hdescent : baseEnd_2923777 < baseStart_2923777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923788 : List Nat := [2, 2, 1, 2, 2, 3, 3, 7]
def baseStart_2923788 : Nat := 118140960795 + 2923788 * 2 ^ 59
def prefixEnd_2923788 : Nat := 4983230072969 + 3 ^ 40 * 2923788 * 2
def baseEnd_2923788 : Nat := 111208042655400881459537

theorem tailTrace_2923788 : CollatzResearch.WordTrace tailWord_2923788 prefixEnd_2923788 111208042655400881459537 := by
  unfold tailWord_2923788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53319654565811447040382009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71092872754415262720509345 53319654565811447040382009)
  ·
    refine ⟨39989740924358585280286507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53319654565811447040382009 39989740924358585280286507)
    ·
      refine ⟨59984611386537877920429761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39989740924358585280286507 59984611386537877920429761)
      ·
        refine ⟨44988458539903408440322321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59984611386537877920429761 44988458539903408440322321)
        ·
          refine ⟨33741343904927556330241741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44988458539903408440322321 33741343904927556330241741)
          ·
            refine ⟨12653003964347833623840653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33741343904927556330241741 12653003964347833623840653)
            ·
              refine ⟨4744876486630437608940245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12653003964347833623840653 4744876486630437608940245)
              ·
                refine ⟨111208042655400881459537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4744876486630437608940245 111208042655400881459537)
                ·
                  rfl

theorem cell22_2923788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_2923788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923788 prefixEnd_2923788 := by exact prefixLift 2923788
  have htrace : WordTrace (prefixWord ++ tailWord_2923788) baseStart_2923788 baseEnd_2923788 := by
    simpa [prefixWord, tailWord_2923788, baseEnd_2923788] using wordTrace_append hprefix tailTrace_2923788
  have hstable : (prefixWord ++ tailWord_2923788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923788).length < 2 ^ (prefixWord ++ tailWord_2923788).sum := by decide
  have hdescent : baseEnd_2923788 < baseStart_2923788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923807 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 2, 4]
def baseStart_2923807 : Nat := 118140960795 + 2923807 * 2 ^ 59
def prefixEnd_2923807 : Nat := 4983230072969 + 3 ^ 40 * 2923807 * 2
def baseEnd_2923807 : Nat := 1000878887986898216910775

theorem tailTrace_2923807 : CollatzResearch.WordTrace tailWord_2923807 prefixEnd_2923807 1000878887986898216910775 := by
  unfold tailWord_2923807
  simp only [CollatzResearch.WordTrace]
  refine ⟨106640002118554060325705675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71093334745702706883803783 106640002118554060325705675)
  ·
    refine ⟨159960003177831090488558513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106640002118554060325705675 159960003177831090488558513)
    ·
      refine ⟨119970002383373317866418885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159960003177831090488558513 119970002383373317866418885)
      ·
        refine ⟨22494375446882497099953541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119970002383373317866418885 22494375446882497099953541)
        ·
          refine ⟨4217695396290468206241289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22494375446882497099953541 4217695396290468206241289)
          ·
            refine ⟨3163271547217851154680967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217695396290468206241289 3163271547217851154680967)
            ·
              refine ⟨4744907320826776732021451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163271547217851154680967 4744907320826776732021451)
              ·
                refine ⟨7117360981240165098032177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744907320826776732021451 7117360981240165098032177)
                ·
                  refine ⟨5338020735930123823524133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117360981240165098032177 5338020735930123823524133)
                  ·
                    refine ⟨1000878887986898216910775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338020735930123823524133 1000878887986898216910775)
                    ·
                      rfl

theorem cell22_2923807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_2923807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923807 prefixEnd_2923807 := by exact prefixLift 2923807
  have htrace : WordTrace (prefixWord ++ tailWord_2923807) baseStart_2923807 baseEnd_2923807 := by
    simpa [prefixWord, tailWord_2923807, baseEnd_2923807] using wordTrace_append hprefix tailTrace_2923807
  have hstable : (prefixWord ++ tailWord_2923807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923807).length < 2 ^ (prefixWord ++ tailWord_2923807).sum := by decide
  have hdescent : baseEnd_2923807 < baseStart_2923807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923925 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2923925 : Nat := 118140960795 + 2923925 * 2 ^ 59
def prefixEnd_2923925 : Nat := 4983230072969 + 3 ^ 40 * 2923925 * 2
def baseEnd_2923925 : Nat := 1000919281798385242460413

theorem tailTrace_2923925 : CollatzResearch.WordTrace tailWord_2923925 prefixEnd_2923925 1000919281798385242460413 := by
  unfold tailWord_2923925
  simp only [CollatzResearch.WordTrace]
  refine ⟨106644305932126566478501229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71096203954751044319000819 106644305932126566478501229)
  ·
    refine ⟨39991614724547462429437961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106644305932126566478501229 39991614724547462429437961)
    ·
      refine ⟨29993711043410596822078471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39991614724547462429437961 29993711043410596822078471)
      ·
        refine ⟨44990566565115895233117707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29993711043410596822078471 44990566565115895233117707)
        ·
          refine ⟨67485849847673842849676561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44990566565115895233117707 67485849847673842849676561)
          ·
            refine ⟨50614387385755382137257421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67485849847673842849676561 50614387385755382137257421)
            ·
              refine ⟨18980395269658268301471533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50614387385755382137257421 18980395269658268301471533)
              ·
                refine ⟨7117648226121850613051825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18980395269658268301471533 7117648226121850613051825)
                ·
                  refine ⟨5338236169591387959788869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117648226121850613051825 5338236169591387959788869)
                  ·
                    refine ⟨1000919281798385242460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338236169591387959788869 1000919281798385242460413)
                    ·
                      rfl

theorem cell22_2923925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2923925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923925 prefixEnd_2923925 := by exact prefixLift 2923925
  have htrace : WordTrace (prefixWord ++ tailWord_2923925) baseStart_2923925 baseEnd_2923925 := by
    simpa [prefixWord, tailWord_2923925, baseEnd_2923925] using wordTrace_append hprefix tailTrace_2923925
  have hstable : (prefixWord ++ tailWord_2923925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923925).length < 2 ^ (prefixWord ++ tailWord_2923925).sum := by decide
  have hdescent : baseEnd_2923925 < baseStart_2923925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923955 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 7, 3]
def baseStart_2923955 : Nat := 118140960795 + 2923955 * 2 ^ 59
def prefixEnd_2923955 : Nat := 4983230072969 + 3 ^ 40 * 2923955 * 2
def baseEnd_2923955 : Nat := 1000929551411475164210321

theorem tailTrace_2923955 : CollatzResearch.WordTrace tailWord_2923955 prefixEnd_2923955 1000929551411475164210321 := by
  unfold tailWord_2923955
  simp only [CollatzResearch.WordTrace]
  refine ⟨106645400122017881602093319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71096933414678587734728879 106645400122017881602093319)
  ·
    refine ⟨159968100183026822403139979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106645400122017881602093319 159968100183026822403139979)
    ·
      refine ⟨239952150274540233604709969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159968100183026822403139979 239952150274540233604709969)
      ·
        refine ⟨179964112705905175203532477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239952150274540233604709969 179964112705905175203532477)
        ·
          refine ⟨67486542264714440701324679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179964112705905175203532477 67486542264714440701324679)
          ·
            refine ⟨101229813397071661051987019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67486542264714440701324679 101229813397071661051987019)
            ·
              refine ⟨151844720095607491577980529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101229813397071661051987019 151844720095607491577980529)
              ·
                refine ⟨113883540071705618683485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151844720095607491577980529 113883540071705618683485397)
                ·
                  refine ⟨2669145470430600437894189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113883540071705618683485397 2669145470430600437894189)
                  ·
                    refine ⟨1000929551411475164210321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2669145470430600437894189 1000929551411475164210321)
                    ·
                      rfl

theorem cell22_2923955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].length) (baseStart_2923955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923955 prefixEnd_2923955 := by exact prefixLift 2923955
  have htrace : WordTrace (prefixWord ++ tailWord_2923955) baseStart_2923955 baseEnd_2923955 := by
    simpa [prefixWord, tailWord_2923955, baseEnd_2923955] using wordTrace_append hprefix tailTrace_2923955
  have hstable : (prefixWord ++ tailWord_2923955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923955).length < 2 ^ (prefixWord ++ tailWord_2923955).sum := by decide
  have hdescent : baseEnd_2923955 < baseStart_2923955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923957 : List Nat := [1, 3, 3, 2, 2, 3, 1, 7]
def baseStart_2923957 : Nat := 118140960795 + 2923957 * 2 ^ 59
def prefixEnd_2923957 : Nat := 4983230072969 + 3 ^ 40 * 2923957 * 2
def baseEnd_2923957 : Nat := 111214470672483091740035

theorem tailTrace_2923957 : CollatzResearch.WordTrace tailWord_2923957 prefixEnd_2923957 111214470672483091740035 := by
  unfold tailWord_2923957
  simp only [CollatzResearch.WordTrace]
  refine ⟨106645473068010635943666125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71096982045340423962444083 106645473068010635943666125)
  ·
    refine ⟨39992052400503988478874797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106645473068010635943666125 39992052400503988478874797)
    ·
      refine ⟨14997019650188995679578049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39992052400503988478874797 14997019650188995679578049)
      ·
        refine ⟨11247764737641746759683537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14997019650188995679578049 11247764737641746759683537)
        ·
          refine ⟨8435823553231310069762653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247764737641746759683537 8435823553231310069762653)
          ·
            refine ⟨3163433832461741276160995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8435823553231310069762653 3163433832461741276160995)
            ·
              refine ⟨4745150748692611914241493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163433832461741276160995 4745150748692611914241493)
              ·
                refine ⟨111214470672483091740035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4745150748692611914241493 111214470672483091740035)
                ·
                  rfl

theorem cell22_2923957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 7].length) (baseStart_2923957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2923957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2923957 prefixEnd_2923957 := by exact prefixLift 2923957
  have htrace : WordTrace (prefixWord ++ tailWord_2923957) baseStart_2923957 baseEnd_2923957 := by
    simpa [prefixWord, tailWord_2923957, baseEnd_2923957] using wordTrace_append hprefix tailTrace_2923957
  have hstable : (prefixWord ++ tailWord_2923957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923957).length < 2 ^ (prefixWord ++ tailWord_2923957).sum := by decide
  have hdescent : baseEnd_2923957 < baseStart_2923957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924015 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_2924015 : Nat := 118140960795 + 2924015 * 2 ^ 59
def prefixEnd_2924015 : Nat := 4983230072969 + 3 ^ 40 * 2924015 * 2
def baseEnd_2924015 : Nat := 1000950090637655007710137

theorem tailTrace_2924015 : CollatzResearch.WordTrace tailWord_2924015 prefixEnd_2924015 1000950090637655007710137 := by
  unfold tailWord_2924015
  simp only [CollatzResearch.WordTrace]
  refine ⟨106647588501800511849277499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71098392334533674566184999 106647588501800511849277499)
  ·
    refine ⟨159971382752700767773916249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106647588501800511849277499 159971382752700767773916249)
    ·
      refine ⟨119978537064525575830437187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159971382752700767773916249 119978537064525575830437187)
      ·
        refine ⟨179967805596788363745655781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119978537064525575830437187 179967805596788363745655781)
        ·
          refine ⟨33743963549397818202310459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179967805596788363745655781 33743963549397818202310459)
          ·
            refine ⟨50615945324096727303465689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33743963549397818202310459 50615945324096727303465689)
            ·
              refine ⟨37961958993072545477599267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50615945324096727303465689 37961958993072545477599267)
              ·
                refine ⟨56942938489608818216398901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37961958993072545477599267 56942938489608818216398901)
                ·
                  refine ⟨5338400483400826707787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56942938489608818216398901 5338400483400826707787397)
                  ·
                    refine ⟨1000950090637655007710137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338400483400826707787397 1000950090637655007710137)
                    ·
                      rfl

theorem cell22_2924015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_2924015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924015 prefixEnd_2924015 := by exact prefixLift 2924015
  have htrace : WordTrace (prefixWord ++ tailWord_2924015) baseStart_2924015 baseEnd_2924015 := by
    simpa [prefixWord, tailWord_2924015, baseEnd_2924015] using wordTrace_append hprefix tailTrace_2924015
  have hstable : (prefixWord ++ tailWord_2924015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924015).length < 2 ^ (prefixWord ++ tailWord_2924015).sum := by decide
  have hdescent : baseEnd_2924015 < baseStart_2924015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924064 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_2924064 : Nat := 118140960795 + 2924064 * 2 ^ 59
def prefixEnd_2924064 : Nat := 4983230072969 + 3 ^ 40 * 2924064 * 2
def baseEnd_2924064 : Nat := 333655621446345071078329

theorem tailTrace_2924064 : CollatzResearch.WordTrace tailWord_2924064 prefixEnd_2924064 333655621446345071078329 := by
  unfold tailWord_2924064
  simp only [CollatzResearch.WordTrace]
  refine ⟨53324687839311496608905623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71099583785748662145207497 53324687839311496608905623)
  ·
    refine ⟨79987031758967244913358435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53324687839311496608905623 79987031758967244913358435)
    ·
      refine ⟨119980547638450867370037653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79987031758967244913358435 119980547638450867370037653)
      ·
        refine ⟨5624088170552384407970515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119980547638450867370037653 5624088170552384407970515)
        ·
          refine ⟨8436132255828576611955773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624088170552384407970515 8436132255828576611955773)
          ·
            refine ⟨3163549595935716229483415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8436132255828576611955773 3163549595935716229483415)
            ·
              refine ⟨4745324393903574344225123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163549595935716229483415 4745324393903574344225123)
              ·
                refine ⟨7117986590855361516337685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745324393903574344225123 7117986590855361516337685)
                ·
                  refine ⟨333655621446345071078329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7117986590855361516337685 333655621446345071078329)
                  ·
                    rfl

theorem cell22_2924064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_2924064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924064 prefixEnd_2924064 := by exact prefixLift 2924064
  have htrace : WordTrace (prefixWord ++ tailWord_2924064) baseStart_2924064 baseEnd_2924064 := by
    simpa [prefixWord, tailWord_2924064, baseEnd_2924064] using wordTrace_append hprefix tailTrace_2924064
  have hstable : (prefixWord ++ tailWord_2924064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924064).length < 2 ^ (prefixWord ++ tailWord_2924064).sum := by decide
  have hdescent : baseEnd_2924064 < baseStart_2924064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924105 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_2924105 : Nat := 118140960795 + 2924105 * 2 ^ 59
def prefixEnd_2924105 : Nat := 4983230072969 + 3 ^ 40 * 2924105 * 2
def baseEnd_2924105 : Nat := 1000980899476924772959861

theorem tailTrace_2924105 : CollatzResearch.WordTrace tailWord_2924105 prefixEnd_2924105 1000980899476924772959861 := by
  unfold tailWord_2924105
  simp only [CollatzResearch.WordTrace]
  refine ⟨106650871071474457220053769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71100580714316304813369179 106650871071474457220053769)
  ·
    refine ⟨79988153303605842915040327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106650871071474457220053769 79988153303605842915040327)
    ·
      refine ⟨119982229955408764372560491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79988153303605842915040327 119982229955408764372560491)
      ·
        refine ⟨179973344933113146558840737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119982229955408764372560491 179973344933113146558840737)
        ·
          refine ⟨134980008699834859919130553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179973344933113146558840737 134980008699834859919130553)
          ·
            refine ⟨101235006524876144939347915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134980008699834859919130553 101235006524876144939347915)
            ·
              refine ⟨151852509787314217409021873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101235006524876144939347915 151852509787314217409021873)
              ·
                refine ⟨113889382340485663056766405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151852509787314217409021873 113889382340485663056766405)
                ·
                  refine ⟨21354259188841061823143701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113889382340485663056766405 21354259188841061823143701)
                  ·
                    refine ⟨1000980899476924772959861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21354259188841061823143701 1000980899476924772959861)
                    ·
                      rfl

theorem cell22_2924105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_2924105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924105 prefixEnd_2924105 := by exact prefixLift 2924105
  have htrace : WordTrace (prefixWord ++ tailWord_2924105) baseStart_2924105 baseEnd_2924105 := by
    simpa [prefixWord, tailWord_2924105, baseEnd_2924105] using wordTrace_append hprefix tailTrace_2924105
  have hstable : (prefixWord ++ tailWord_2924105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924105).length < 2 ^ (prefixWord ++ tailWord_2924105).sum := by decide
  have hdescent : baseEnd_2924105 < baseStart_2924105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924109 : List Nat := [1, 6, 1, 1, 4, 9]
def baseStart_2924109 : Nat := 118140960795 + 2924109 * 2 ^ 59
def prefixEnd_2924109 : Nat := 4983230072969 + 3 ^ 40 * 2924109 * 2
def baseEnd_2924109 : Nat := 12357805787144075257529

theorem tailTrace_2924109 : CollatzResearch.WordTrace tailWord_2924109 prefixEnd_2924109 12357805787144075257529 := by
  unfold tailWord_2924109
  simp only [CollatzResearch.WordTrace]
  refine ⟨106651016963459965903199381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71100677975639977268799587 106651016963459965903199381)
  ·
    refine ⟨4999266420162185901712471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106651016963459965903199381 4999266420162185901712471)
    ·
      refine ⟨7498899630243278852568707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999266420162185901712471 7498899630243278852568707)
      ·
        refine ⟨11248349445364918278853061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498899630243278852568707 11248349445364918278853061)
        ·
          refine ⟨2109065521005922177284949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11248349445364918278853061 2109065521005922177284949)
          ·
            refine ⟨12357805787144075257529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2109065521005922177284949 12357805787144075257529)
            ·
              rfl

theorem cell22_2924109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 9].length) (baseStart_2924109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924109 prefixEnd_2924109 := by exact prefixLift 2924109
  have htrace : WordTrace (prefixWord ++ tailWord_2924109) baseStart_2924109 baseEnd_2924109 := by
    simpa [prefixWord, tailWord_2924109, baseEnd_2924109] using wordTrace_append hprefix tailTrace_2924109
  have hstable : (prefixWord ++ tailWord_2924109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924109).length < 2 ^ (prefixWord ++ tailWord_2924109).sum := by decide
  have hdescent : baseEnd_2924109 < baseStart_2924109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924137 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 5]
def baseStart_2924137 : Nat := 118140960795 + 2924137 * 2 ^ 59
def prefixEnd_2924137 : Nat := 4983230072969 + 3 ^ 40 * 2924137 * 2
def baseEnd_2924137 : Nat := 333663951243629118719921

theorem tailTrace_2924137 : CollatzResearch.WordTrace tailWord_2924137 prefixEnd_2924137 333663951243629118719921 := by
  unfold tailWord_2924137
  simp only [CollatzResearch.WordTrace]
  refine ⟨106652038207358526685218665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71101358804905684456812443 106652038207358526685218665)
  ·
    refine ⟨79989028655518895013913999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106652038207358526685218665 79989028655518895013913999)
    ·
      refine ⟨119983542983278342520870999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79989028655518895013913999 119983542983278342520870999)
      ·
        refine ⟨179975314474917513781306499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119983542983278342520870999 179975314474917513781306499)
        ·
          refine ⟨269962971712376270671959749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179975314474917513781306499 269962971712376270671959749)
          ·
            refine ⟨50618057196070550750992453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269962971712376270671959749 50618057196070550750992453)
            ·
              refine ⟨9490885724263228265811085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50618057196070550750992453 9490885724263228265811085)
              ·
                refine ⟨3559082146598710599679157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9490885724263228265811085 3559082146598710599679157)
                ·
                  refine ⟨333663951243629118719921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559082146598710599679157 333663951243629118719921)
                  ·
                    rfl

theorem cell22_2924137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_2924137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924137 prefixEnd_2924137 := by exact prefixLift 2924137
  have htrace : WordTrace (prefixWord ++ tailWord_2924137) baseStart_2924137 baseEnd_2924137 := by
    simpa [prefixWord, tailWord_2924137, baseEnd_2924137] using wordTrace_append hprefix tailTrace_2924137
  have hstable : (prefixWord ++ tailWord_2924137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924137).length < 2 ^ (prefixWord ++ tailWord_2924137).sum := by decide
  have hdescent : baseEnd_2924137 < baseStart_2924137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924141 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_2924141 : Nat := 118140960795 + 2924141 * 2 ^ 59
def prefixEnd_2924141 : Nat := 4983230072969 + 3 ^ 40 * 2924141 * 2
def baseEnd_2924141 : Nat := 1000993223012632679059751

theorem tailTrace_2924141 : CollatzResearch.WordTrace tailWord_2924141 prefixEnd_2924141 1000993223012632679059751 := by
  unfold tailWord_2924141
  simp only [CollatzResearch.WordTrace]
  refine ⟨106652184099344035368364277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71101456066229356912242851 106652184099344035368364277)
  ·
    refine ⟨9998642259313503315784151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106652184099344035368364277 9998642259313503315784151)
    ·
      refine ⟨14997963388970254973676227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998642259313503315784151 14997963388970254973676227)
      ·
        refine ⟨22496945083455382460514341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997963388970254973676227 22496945083455382460514341)
        ·
          refine ⟨4218177203147884211346439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22496945083455382460514341 4218177203147884211346439)
          ·
            refine ⟨6327265804721826317019659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218177203147884211346439 6327265804721826317019659)
            ·
              refine ⟨9490898707082739475529489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327265804721826317019659 9490898707082739475529489)
              ·
                refine ⟨7118174030312054606647117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9490898707082739475529489 7118174030312054606647117)
                ·
                  refine ⟨2669315261367020477492669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118174030312054606647117 2669315261367020477492669)
                  ·
                    refine ⟨1000993223012632679059751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2669315261367020477492669 1000993223012632679059751)
                    ·
                      rfl

theorem cell22_2924141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_2924141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924141 prefixEnd_2924141 := by exact prefixLift 2924141
  have htrace : WordTrace (prefixWord ++ tailWord_2924141) baseStart_2924141 baseEnd_2924141 := by
    simpa [prefixWord, tailWord_2924141, baseEnd_2924141] using wordTrace_append hprefix tailTrace_2924141
  have hstable : (prefixWord ++ tailWord_2924141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924141).length < 2 ^ (prefixWord ++ tailWord_2924141).sum := by decide
  have hdescent : baseEnd_2924141 < baseStart_2924141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924244 : List Nat := [2, 4, 1, 3, 1, 1, 1, 9]
def baseStart_2924244 : Nat := 118140960795 + 2924244 * 2 ^ 59
def prefixEnd_2924244 : Nat := 4983230072969 + 3 ^ 40 * 2924244 * 2
def baseEnd_2924244 : Nat := 111225386890841638192715

theorem tailTrace_2924244 : CollatzResearch.WordTrace tailWord_2924244 prefixEnd_2924244 111225386890841638192715 := by
  unfold tailWord_2924244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53327970408985441979681893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71103960545313922639575857 53327970408985441979681893)
  ·
    refine ⟨9998994451684770371190355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53327970408985441979681893 9998994451684770371190355)
    ·
      refine ⟨14998491677527155556785533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998994451684770371190355 14998491677527155556785533)
      ·
        refine ⟨5624434379072683333794575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14998491677527155556785533 5624434379072683333794575)
        ·
          refine ⟨8436651568609025000691863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624434379072683333794575 8436651568609025000691863)
          ·
            refine ⟨12654977352913537501037795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436651568609025000691863 12654977352913537501037795)
            ·
              refine ⟨18982466029370306251556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654977352913537501037795 18982466029370306251556693)
              ·
                refine ⟨111225386890841638192715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18982466029370306251556693 111225386890841638192715)
                ·
                  rfl

theorem cell22_2924244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_2924244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924244 prefixEnd_2924244 := by exact prefixLift 2924244
  have htrace : WordTrace (prefixWord ++ tailWord_2924244) baseStart_2924244 baseEnd_2924244 := by
    simpa [prefixWord, tailWord_2924244, baseEnd_2924244] using wordTrace_append hprefix tailTrace_2924244
  have hstable : (prefixWord ++ tailWord_2924244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924244).length < 2 ^ (prefixWord ++ tailWord_2924244).sum := by decide
  have hdescent : baseEnd_2924244 < baseStart_2924244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924263 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2924263 : Nat := 118140960795 + 2924263 * 2 ^ 59
def prefixEnd_2924263 : Nat := 4983230072969 + 3 ^ 40 * 2924263 * 2
def baseEnd_2924263 : Nat := 1001034986105865027509377

theorem tailTrace_2924263 : CollatzResearch.WordTrace tailWord_2924263 prefixEnd_2924263 1001034986105865027509377 := by
  unfold tailWord_2924263
  simp only [CollatzResearch.WordTrace]
  refine ⟨106656633804902050204305443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71104422536601366802870295 106656633804902050204305443)
  ·
    refine ⟨159984950707353075306458165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106656633804902050204305443 159984950707353075306458165)
    ·
      refine ⟨14998589128814350809980453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159984950707353075306458165 14998589128814350809980453)
      ·
        refine ⟨2812235461652690776871335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14998589128814350809980453 2812235461652690776871335)
        ·
          refine ⟨4218353192479036165307003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812235461652690776871335 4218353192479036165307003)
          ·
            refine ⟨6327529788718554247960505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218353192479036165307003 6327529788718554247960505)
            ·
              refine ⟨4745647341538915685970379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327529788718554247960505 4745647341538915685970379)
              ·
                refine ⟨7118471012308373528955569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745647341538915685970379 7118471012308373528955569)
                ·
                  refine ⟨5338853259231280146716677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7118471012308373528955569 5338853259231280146716677)
                  ·
                    refine ⟨1001034986105865027509377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338853259231280146716677 1001034986105865027509377)
                    ·
                      rfl

theorem cell22_2924263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2924263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924263 prefixEnd_2924263 := by exact prefixLift 2924263
  have htrace : WordTrace (prefixWord ++ tailWord_2924263) baseStart_2924263 baseEnd_2924263 := by
    simpa [prefixWord, tailWord_2924263, baseEnd_2924263] using wordTrace_append hprefix tailTrace_2924263
  have hstable : (prefixWord ++ tailWord_2924263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924263).length < 2 ^ (prefixWord ++ tailWord_2924263).sum := by decide
  have hdescent : baseEnd_2924263 < baseStart_2924263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924272 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_2924272 : Nat := 118140960795 + 2924272 * 2 ^ 59
def prefixEnd_2924272 : Nat := 4983230072969 + 3 ^ 40 * 2924272 * 2
def baseEnd_2924272 : Nat := 333679355663264001344783

theorem tailTrace_2924272 : CollatzResearch.WordTrace tailWord_2924272 prefixEnd_2924272 333679355663264001344783 := by
  unfold tailWord_2924272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53328481030934722370691535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71104641374579629827588713 53328481030934722370691535)
  ·
    refine ⟨79992721546402083556037303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53328481030934722370691535 79992721546402083556037303)
    ·
      refine ⟨119989082319603125334055955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79992721546402083556037303 119989082319603125334055955)
      ·
        refine ⟨179983623479404688001083933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119989082319603125334055955 179983623479404688001083933)
        ·
          refine ⟨67493858804776758000406475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179983623479404688001083933 67493858804776758000406475)
          ·
            refine ⟨101240788207165137000609713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67493858804776758000406475 101240788207165137000609713)
            ·
              refine ⟨75930591155373852750457285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101240788207165137000609713 75930591155373852750457285)
              ·
                refine ⟨14236985841632597390710741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75930591155373852750457285 14236985841632597390710741)
                ·
                  refine ⟨333679355663264001344783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14236985841632597390710741 333679355663264001344783)
                  ·
                    rfl

theorem cell22_2924272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_2924272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924272 prefixEnd_2924272 := by exact prefixLift 2924272
  have htrace : WordTrace (prefixWord ++ tailWord_2924272) baseStart_2924272 baseEnd_2924272 := by
    simpa [prefixWord, tailWord_2924272, baseEnd_2924272] using wordTrace_append hprefix tailTrace_2924272
  have hstable : (prefixWord ++ tailWord_2924272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924272).length < 2 ^ (prefixWord ++ tailWord_2924272).sum := by decide
  have hdescent : baseEnd_2924272 < baseStart_2924272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924289 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 5]
def baseStart_2924289 : Nat := 118140960795 + 2924289 * 2 ^ 59
def prefixEnd_2924289 : Nat := 4983230072969 + 3 ^ 40 * 2924289 * 2
def baseEnd_2924289 : Nat := 333681295479069875453099

theorem tailTrace_2924289 : CollatzResearch.WordTrace tailWord_2924289 prefixEnd_2924289 333681295479069875453099 := by
  unfold tailWord_2924289
  simp only [CollatzResearch.WordTrace]
  refine ⟨106657582102807856644751921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71105054735205237763167947 106657582102807856644751921)
  ·
    refine ⟨79993186577105892483563941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106657582102807856644751921 79993186577105892483563941)
    ·
      refine ⟨14998722483207354840668239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79993186577105892483563941 14998722483207354840668239)
      ·
        refine ⟨22498083724811032261002359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14998722483207354840668239 22498083724811032261002359)
        ·
          refine ⟨33747125587216548391503539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22498083724811032261002359 33747125587216548391503539)
          ·
            refine ⟨50620688380824822587255309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33747125587216548391503539 50620688380824822587255309)
            ·
              refine ⟨18982758142809308470220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50620688380824822587255309 18982758142809308470220741)
              ·
                refine ⟨3559267151776745338166389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18982758142809308470220741 3559267151776745338166389)
                ·
                  refine ⟨333681295479069875453099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559267151776745338166389 333681295479069875453099)
                  ·
                    rfl

theorem cell22_2924289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_2924289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924289 prefixEnd_2924289 := by exact prefixLift 2924289
  have htrace : WordTrace (prefixWord ++ tailWord_2924289) baseStart_2924289 baseEnd_2924289 := by
    simpa [prefixWord, tailWord_2924289, baseEnd_2924289] using wordTrace_append hprefix tailTrace_2924289
  have hstable : (prefixWord ++ tailWord_2924289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924289).length < 2 ^ (prefixWord ++ tailWord_2924289).sum := by decide
  have hdescent : baseEnd_2924289 < baseStart_2924289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924319 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_2924319 : Nat := 118140960795 + 2924319 * 2 ^ 59
def prefixEnd_2924319 : Nat := 4983230072969 + 3 ^ 40 * 2924319 * 2
def baseEnd_2924319 : Nat := 1001054156050299548109205

theorem tailTrace_2924319 : CollatzResearch.WordTrace tailWord_2924319 prefixEnd_2924319 1001054156050299548109205 := by
  unfold tailWord_2924319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106658676292699171768344011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71105784195132781178896007 106658676292699171768344011)
  ·
    refine ⟨159988014439048757652516017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106658676292699171768344011 159988014439048757652516017)
    ·
      refine ⟨119991010829286568239387013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159988014439048757652516017 119991010829286568239387013)
      ·
        refine ⟨22498314530491231544885065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119991010829286568239387013 22498314530491231544885065)
        ·
          refine ⟨16873735897868423658663799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22498314530491231544885065 16873735897868423658663799)
          ·
            refine ⟨25310603846802635487995699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873735897868423658663799 25310603846802635487995699)
            ·
              refine ⟨37965905770203953231993549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25310603846802635487995699 37965905770203953231993549)
              ·
                refine ⟨14237214663826482461997581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37965905770203953231993549 14237214663826482461997581)
                ·
                  refine ⟨5338955498934930923249093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14237214663826482461997581 5338955498934930923249093)
                  ·
                    refine ⟨1001054156050299548109205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338955498934930923249093 1001054156050299548109205)
                    ·
                      rfl

theorem cell22_2924319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_2924319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924319 prefixEnd_2924319 := by exact prefixLift 2924319
  have htrace : WordTrace (prefixWord ++ tailWord_2924319) baseStart_2924319 baseEnd_2924319 := by
    simpa [prefixWord, tailWord_2924319, baseEnd_2924319] using wordTrace_append hprefix tailTrace_2924319
  have hstable : (prefixWord ++ tailWord_2924319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924319).length < 2 ^ (prefixWord ++ tailWord_2924319).sum := by decide
  have hdescent : baseEnd_2924319 < baseStart_2924319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924351 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 6]
def baseStart_2924351 : Nat := 118140960795 + 2924351 * 2 ^ 59
def prefixEnd_2924351 : Nat := 4983230072969 + 3 ^ 40 * 2924351 * 2
def baseEnd_2924351 : Nat := 333688370101420710436369

theorem tailTrace_2924351 : CollatzResearch.WordTrace tailWord_2924351 prefixEnd_2924351 333688370101420710436369 := by
  unfold tailWord_2924351
  simp only [CollatzResearch.WordTrace]
  refine ⟨106659843428583241233508907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71106562285722160822339271 106659843428583241233508907)
  ·
    refine ⟨159989765142874861850263361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106659843428583241233508907 159989765142874861850263361)
    ·
      refine ⟨119992323857156146387697521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159989765142874861850263361 119992323857156146387697521)
      ·
        refine ⟨89994242892867109790773141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119992323857156146387697521 89994242892867109790773141)
        ·
          refine ⟨4218480135603145771442491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89994242892867109790773141 4218480135603145771442491)
          ·
            refine ⟨6327720203404718657163737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218480135603145771442491 6327720203404718657163737)
            ·
              refine ⟨4745790152553538992872803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327720203404718657163737 4745790152553538992872803)
              ·
                refine ⟨7118685228830308489309205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745790152553538992872803 7118685228830308489309205)
                ·
                  refine ⟨333688370101420710436369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7118685228830308489309205 333688370101420710436369)
                  ·
                    rfl

theorem cell22_2924351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_2924351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924351 prefixEnd_2924351 := by exact prefixLift 2924351
  have htrace : WordTrace (prefixWord ++ tailWord_2924351) baseStart_2924351 baseEnd_2924351 := by
    simpa [prefixWord, tailWord_2924351, baseEnd_2924351] using wordTrace_append hprefix tailTrace_2924351
  have hstable : (prefixWord ++ tailWord_2924351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924351).length < 2 ^ (prefixWord ++ tailWord_2924351).sum := by decide
  have hdescent : baseEnd_2924351 < baseStart_2924351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924398 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2924398 : Nat := 118140960795 + 2924398 * 2 ^ 59
def prefixEnd_2924398 : Nat := 4983230072969 + 3 ^ 40 * 2924398 * 2
def baseEnd_2924398 : Nat := 1001081199364769675383963

theorem tailTrace_2924398 : CollatzResearch.WordTrace tailWord_2924398 prefixEnd_2924398 1001081199364769675383963 := by
  unfold tailWord_2924398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332694707426621032558731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71107705106275312173646565 13332694707426621032558731)
  ·
    refine ⟨19999042061139931548838097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332694707426621032558731 19999042061139931548838097)
    ·
      refine ⟨14999281545854948661628573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19999042061139931548838097 14999281545854948661628573)
      ·
        refine ⟨5624730579695605748110715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14999281545854948661628573 5624730579695605748110715)
        ·
          refine ⟨8437095869543408622166073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624730579695605748110715 8437095869543408622166073)
          ·
            refine ⟨6327821902157556466624555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8437095869543408622166073 6327821902157556466624555)
            ·
              refine ⟨9491732853236334699936833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327821902157556466624555 9491732853236334699936833)
              ·
                refine ⟨7118799639927251024952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491732853236334699936833 7118799639927251024952625)
                ·
                  refine ⟨5339099729945438268714469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7118799639927251024952625 5339099729945438268714469)
                  ·
                    refine ⟨1001081199364769675383963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339099729945438268714469 1001081199364769675383963)
                    ·
                      rfl

theorem cell22_2924398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2924398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924398 prefixEnd_2924398 := by exact prefixLift 2924398
  have htrace : WordTrace (prefixWord ++ tailWord_2924398) baseStart_2924398 baseEnd_2924398 := by
    simpa [prefixWord, tailWord_2924398, baseEnd_2924398] using wordTrace_append hprefix tailTrace_2924398
  have hstable : (prefixWord ++ tailWord_2924398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924398).length < 2 ^ (prefixWord ++ tailWord_2924398).sum := by decide
  have hdescent : baseEnd_2924398 < baseStart_2924398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924409 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_2924409 : Nat := 118140960795 + 2924409 * 2 ^ 59
def prefixEnd_2924409 : Nat := 4983230072969 + 3 ^ 40 * 2924409 * 2
def baseEnd_2924409 : Nat := 1001084964889569313358929

theorem tailTrace_2924409 : CollatzResearch.WordTrace tailWord_2924409 prefixEnd_2924409 1001084964889569313358929 := by
  unfold tailWord_2924409
  simp only [CollatzResearch.WordTrace]
  refine ⟨106661958862373117139120281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71107972574915411426080187 106661958862373117139120281)
  ·
    refine ⟨79996469146779837854340211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106661958862373117139120281 79996469146779837854340211)
    ·
      refine ⟨119994703720169756781510317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79996469146779837854340211 119994703720169756781510317)
      ·
        refine ⟨44998013895063658793066369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119994703720169756781510317 44998013895063658793066369)
        ·
          refine ⟨33748510421297744094799777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44998013895063658793066369 33748510421297744094799777)
          ·
            refine ⟨25311382815973308071099833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33748510421297744094799777 25311382815973308071099833)
            ·
              refine ⟨18983537111979981053324875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25311382815973308071099833 18983537111979981053324875)
              ·
                refine ⟨28475305667969971579987313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18983537111979981053324875 28475305667969971579987313)
                ·
                  refine ⟨21356479250977478684990485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28475305667969971579987313 21356479250977478684990485)
                  ·
                    refine ⟨1001084964889569313358929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21356479250977478684990485 1001084964889569313358929)
                    ·
                      rfl

theorem cell22_2924409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_2924409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924409 prefixEnd_2924409 := by exact prefixLift 2924409
  have htrace : WordTrace (prefixWord ++ tailWord_2924409) baseStart_2924409 baseEnd_2924409 := by
    simpa [prefixWord, tailWord_2924409, baseEnd_2924409] using wordTrace_append hprefix tailTrace_2924409
  have hstable : (prefixWord ++ tailWord_2924409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924409).length < 2 ^ (prefixWord ++ tailWord_2924409).sum := by decide
  have hdescent : baseEnd_2924409 < baseStart_2924409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924503 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 4]
def baseStart_2924503 : Nat := 118140960795 + 2924503 * 2 ^ 59
def prefixEnd_2924503 : Nat := 4983230072969 + 3 ^ 40 * 2924503 * 2
def baseEnd_2924503 : Nat := 333705714336861467169547

theorem tailTrace_2924503 : CollatzResearch.WordTrace tailWord_2924503 prefixEnd_2924503 333705714336861467169547 := by
  unfold tailWord_2924503
  simp only [CollatzResearch.WordTrace]
  refine ⟨106665387324032571193042163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71110258216021714128694775 106665387324032571193042163)
  ·
    refine ⟨159998080986048856789563245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106665387324032571193042163 159998080986048856789563245)
    ·
      refine ⟨59999280369768321296086217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159998080986048856789563245 59999280369768321296086217)
      ·
        refine ⟨44999460277326240972064663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59999280369768321296086217 44999460277326240972064663)
        ·
          refine ⟨67499190415989361458096995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44999460277326240972064663 67499190415989361458096995)
          ·
            refine ⟨101248785623984042187145493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67499190415989361458096995 101248785623984042187145493)
            ·
              refine ⟨4746036826124251977522445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101248785623984042187145493 4746036826124251977522445)
              ·
                refine ⟨1779763809796594491570917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4746036826124251977522445 1779763809796594491570917)
                ·
                  refine ⟨333705714336861467169547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779763809796594491570917 333705714336861467169547)
                  ·
                    rfl

theorem cell22_2924503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 4].length) (baseStart_2924503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924503 prefixEnd_2924503 := by exact prefixLift 2924503
  have htrace : WordTrace (prefixWord ++ tailWord_2924503) baseStart_2924503 baseEnd_2924503 := by
    simpa [prefixWord, tailWord_2924503, baseEnd_2924503] using wordTrace_append hprefix tailTrace_2924503
  have hstable : (prefixWord ++ tailWord_2924503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924503).length < 2 ^ (prefixWord ++ tailWord_2924503).sum := by decide
  have hdescent : baseEnd_2924503 < baseStart_2924503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924516 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2924516 : Nat := 118140960795 + 2924516 * 2 ^ 59
def prefixEnd_2924516 : Nat := 4983230072969 + 3 ^ 40 * 2924516 * 2
def baseEnd_2924516 : Nat := 1001121593176256700933601

theorem tailTrace_2924516 : CollatzResearch.WordTrace tailWord_2924516 prefixEnd_2924516 1001121593176256700933601 := by
  unfold tailWord_2924516
  simp only [CollatzResearch.WordTrace]
  refine ⟨53332930736492737206632701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71110574315323649608843601 53332930736492737206632701)
  ·
    refine ⟨19999849026184776452487263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53332930736492737206632701 19999849026184776452487263)
    ·
      refine ⟨29999773539277164678730895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19999849026184776452487263 29999773539277164678730895)
      ·
        refine ⟨44999660308915747018096343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29999773539277164678730895 44999660308915747018096343)
        ·
          refine ⟨67499490463373620527144515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44999660308915747018096343 67499490463373620527144515)
          ·
            refine ⟨101249235695060430790716773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67499490463373620527144515 101249235695060430790716773)
            ·
              refine ⟨18984231692823830773259395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101249235695060430790716773 18984231692823830773259395)
              ·
                refine ⟨28476347539235746159889093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18984231692823830773259395 28476347539235746159889093)
                ·
                  refine ⟨5339315163606702404979205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28476347539235746159889093 5339315163606702404979205)
                  ·
                    refine ⟨1001121593176256700933601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5339315163606702404979205 1001121593176256700933601)
                    ·
                      rfl

theorem cell22_2924516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2924516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924516 prefixEnd_2924516 := by exact prefixLift 2924516
  have htrace : WordTrace (prefixWord ++ tailWord_2924516) baseStart_2924516 baseEnd_2924516 := by
    simpa [prefixWord, tailWord_2924516, baseEnd_2924516] using wordTrace_append hprefix tailTrace_2924516
  have hstable : (prefixWord ++ tailWord_2924516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924516).length < 2 ^ (prefixWord ++ tailWord_2924516).sum := by decide
  have hdescent : baseEnd_2924516 < baseStart_2924516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924593 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 5]
def baseStart_2924593 : Nat := 118140960795 + 2924593 * 2 ^ 59
def prefixEnd_2924593 : Nat := 4983230072969 + 3 ^ 40 * 2924593 * 2
def baseEnd_2924593 : Nat := 333715983949951388919455

theorem tailTrace_2924593 : CollatzResearch.WordTrace tailWord_2924593 prefixEnd_2924593 333715983949951388919455 := by
  unfold tailWord_2924593
  simp only [CollatzResearch.WordTrace]
  refine ⟨106668669893706516563818433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71112446595804344375878955 106668669893706516563818433)
  ·
    refine ⟨80001502420279887422863825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106668669893706516563818433 80001502420279887422863825)
    ·
      refine ⟨60001126815209915567147869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80001502420279887422863825 60001126815209915567147869)
      ·
        refine ⟨22500422555703718337680451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60001126815209915567147869 22500422555703718337680451)
        ·
          refine ⟨33750633833555577506520677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22500422555703718337680451 33750633833555577506520677)
          ·
            refine ⟨6328243843791670782472627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33750633833555577506520677 6328243843791670782472627)
            ·
              refine ⟨9492365765687506173708941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328243843791670782472627 9492365765687506173708941)
              ·
                refine ⟨3559637162132814815140853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9492365765687506173708941 3559637162132814815140853)
                ·
                  refine ⟨333715983949951388919455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559637162132814815140853 333715983949951388919455)
                  ·
                    rfl

theorem cell22_2924593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_2924593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924593 prefixEnd_2924593 := by exact prefixLift 2924593
  have htrace : WordTrace (prefixWord ++ tailWord_2924593) baseStart_2924593 baseEnd_2924593 := by
    simpa [prefixWord, tailWord_2924593, baseEnd_2924593] using wordTrace_append hprefix tailTrace_2924593
  have hstable : (prefixWord ++ tailWord_2924593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924593).length < 2 ^ (prefixWord ++ tailWord_2924593).sum := by decide
  have hdescent : baseEnd_2924593 < baseStart_2924593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924614 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2924614 : Nat := 118140960795 + 2924614 * 2 ^ 59
def prefixEnd_2924614 : Nat := 4983230072969 + 3 ^ 40 * 2924614 * 2
def baseEnd_2924614 : Nat := 1001155140579017111983301

theorem tailTrace_2924614 : CollatzResearch.WordTrace tailWord_2924614 prefixEnd_2924614 1001155140579017111983301 := by
  unfold tailWord_2924614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333419869582201160947903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71112957217753624766888597 3333419869582201160947903)
  ·
    refine ⟨5000129804373301741421855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333419869582201160947903 5000129804373301741421855)
    ·
      refine ⟨7500194706559952612132783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000129804373301741421855 7500194706559952612132783)
      ·
        refine ⟨11250292059839928918199175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500194706559952612132783 11250292059839928918199175)
        ·
          refine ⟨16875438089759893377298763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11250292059839928918199175 16875438089759893377298763)
          ·
            refine ⟨25313157134639840065948145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16875438089759893377298763 25313157134639840065948145)
            ·
              refine ⟨18984867850979880049461109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25313157134639840065948145 18984867850979880049461109)
              ·
                refine ⟨1779831361029363754636979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18984867850979880049461109 1779831361029363754636979)
                ·
                  refine ⟨2669747041544045631955469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779831361029363754636979 2669747041544045631955469)
                  ·
                    refine ⟨1001155140579017111983301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2669747041544045631955469 1001155140579017111983301)
                    ·
                      rfl

theorem cell22_2924614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2924614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924614 prefixEnd_2924614 := by exact prefixLift 2924614
  have htrace : WordTrace (prefixWord ++ tailWord_2924614) baseStart_2924614 baseEnd_2924614 := by
    simpa [prefixWord, tailWord_2924614, baseEnd_2924614] using wordTrace_append hprefix tailTrace_2924614
  have hstable : (prefixWord ++ tailWord_2924614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924614).length < 2 ^ (prefixWord ++ tailWord_2924614).sum := by decide
  have hdescent : baseEnd_2924614 < baseStart_2924614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924668 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2924668 : Nat := 118140960795 + 2924668 * 2 ^ 59
def prefixEnd_2924668 : Nat := 4983230072969 + 3 ^ 40 * 2924668 * 2
def baseEnd_2924668 : Nat := 1001173625882578971133135

theorem tailTrace_2924668 : CollatzResearch.WordTrace tailWord_2924668 prefixEnd_2924668 1001173625882578971133135 := by
  unfold tailWord_2924668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53335702684217402186399329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71114270245623202915199105 53335702684217402186399329)
  ·
    refine ⟨40001777013163051639799497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53335702684217402186399329 40001777013163051639799497)
    ·
      refine ⟨30001332759872288729849623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40001777013163051639799497 30001332759872288729849623)
      ·
        refine ⟨45001999139808433094774435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30001332759872288729849623 45001999139808433094774435)
        ·
          refine ⟨67502998709712649642161653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45001999139808433094774435 67502998709712649642161653)
          ·
            refine ⟨6328406129035560903952655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67502998709712649642161653 6328406129035560903952655)
            ·
              refine ⟨9492609193553341355928983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328406129035560903952655 9492609193553341355928983)
              ·
                refine ⟨14238913790330012033893475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492609193553341355928983 14238913790330012033893475)
                ·
                  refine ⟨21358370685495018050840213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14238913790330012033893475 21358370685495018050840213)
                  ·
                    refine ⟨1001173625882578971133135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21358370685495018050840213 1001173625882578971133135)
                    ·
                      rfl

theorem cell22_2924668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2924668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924668 prefixEnd_2924668 := by exact prefixLift 2924668
  have htrace : WordTrace (prefixWord ++ tailWord_2924668) baseStart_2924668 baseEnd_2924668 := by
    simpa [prefixWord, tailWord_2924668, baseEnd_2924668] using wordTrace_append hprefix tailTrace_2924668
  have hstable : (prefixWord ++ tailWord_2924668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924668).length < 2 ^ (prefixWord ++ tailWord_2924668).sum := by decide
  have hdescent : baseEnd_2924668 < baseStart_2924668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924717 : List Nat := [1, 5, 2, 1, 2, 3, 2, 6]
def baseStart_2924717 : Nat := 118140960795 + 2924717 * 2 ^ 59
def prefixEnd_2924717 : Nat := 4983230072969 + 3 ^ 40 * 2924717 * 2
def baseEnd_2924717 : Nat := 111243377731551019628665

theorem tailTrace_2924717 : CollatzResearch.WordTrace tailWord_2924717 prefixEnd_2924717 111243377731551019628665 := by
  unfold tailWord_2924717
  simp only [CollatzResearch.WordTrace]
  refine ⟨106673192545257285741332405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71115461696838190494221603 106673192545257285741332405)
  ·
    refine ⟨10000611801117870538249913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106673192545257285741332405 10000611801117870538249913)
    ·
      refine ⟨7500458850838402903687435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10000611801117870538249913 7500458850838402903687435)
      ·
        refine ⟨11250688276257604355531153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500458850838402903687435 11250688276257604355531153)
        ·
          refine ⟨8438016207193203266648365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11250688276257604355531153 8438016207193203266648365)
          ·
            refine ⟨3164256077697451224993137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8438016207193203266648365 3164256077697451224993137)
            ·
              refine ⟨2373192058273088418744853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164256077697451224993137 2373192058273088418744853)
              ·
                refine ⟨111243377731551019628665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373192058273088418744853 111243377731551019628665)
                ·
                  rfl

theorem cell22_2924717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 6].length) (baseStart_2924717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924717 prefixEnd_2924717 := by exact prefixLift 2924717
  have htrace : WordTrace (prefixWord ++ tailWord_2924717) baseStart_2924717 baseEnd_2924717 := by
    simpa [prefixWord, tailWord_2924717, baseEnd_2924717] using wordTrace_append hprefix tailTrace_2924717
  have hstable : (prefixWord ++ tailWord_2924717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924717).length < 2 ^ (prefixWord ++ tailWord_2924717).sum := by decide
  have hdescent : baseEnd_2924717 < baseStart_2924717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924835 : List Nat := [1, 1, 1, 4, 2, 2, 5, 6]
def baseStart_2924835 : Nat := 118140960795 + 2924835 * 2 ^ 59
def prefixEnd_2924835 : Nat := 4983230072969 + 3 ^ 40 * 2924835 * 2
def baseEnd_2924835 : Nat := 111247865932827355800847

theorem tailTrace_2924835 : CollatzResearch.WordTrace tailWord_2924835 prefixEnd_2924835 111247865932827355800847 := by
  unfold tailWord_2924835
  simp only [CollatzResearch.WordTrace]
  refine ⟨106677496358829791894127959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71118330905886527929418639 106677496358829791894127959)
  ·
    refine ⟨160016244538244687841191939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106677496358829791894127959 160016244538244687841191939)
    ·
      refine ⟨240024366807367031761787909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160016244538244687841191939 240024366807367031761787909)
      ·
        refine ⟨45004568776381318455335233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240024366807367031761787909 45004568776381318455335233)
        ·
          refine ⟨33753426582285988841501425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45004568776381318455335233 33753426582285988841501425)
          ·
            refine ⟨25315069936714491631126069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33753426582285988841501425 25315069936714491631126069)
            ·
              refine ⟨2373287806566983590418069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25315069936714491631126069 2373287806566983590418069)
              ·
                refine ⟨111247865932827355800847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373287806566983590418069 111247865932827355800847)
                ·
                  rfl

theorem cell22_2924835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 6].length) (baseStart_2924835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924835 prefixEnd_2924835 := by exact prefixLift 2924835
  have htrace : WordTrace (prefixWord ++ tailWord_2924835) baseStart_2924835 baseEnd_2924835 := by
    simpa [prefixWord, tailWord_2924835, baseEnd_2924835] using wordTrace_append hprefix tailTrace_2924835
  have hstable : (prefixWord ++ tailWord_2924835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924835).length < 2 ^ (prefixWord ++ tailWord_2924835).sum := by decide
  have hdescent : baseEnd_2924835 < baseStart_2924835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924848 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_2924848 : Nat := 118140960795 + 2924848 * 2 ^ 59
def prefixEnd_2924848 : Nat := 4983230072969 + 3 ^ 40 * 2924848 * 2
def baseEnd_2924848 : Nat := 1001235243561118501632583

theorem tailTrace_2924848 : CollatzResearch.WordTrace tailWord_2924848 prefixEnd_2924848 1001235243561118501632583 := by
  unfold tailWord_2924848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53338985253891347557175599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71118647005188463409567465 53338985253891347557175599)
  ·
    refine ⟨80008477880837021335763399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53338985253891347557175599 80008477880837021335763399)
    ·
      refine ⟨120012716821255532003645099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80008477880837021335763399 120012716821255532003645099)
      ·
        refine ⟨180019075231883298005467649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120012716821255532003645099 180019075231883298005467649)
        ·
          refine ⟨135014306423912473504100737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180019075231883298005467649 135014306423912473504100737)
          ·
            refine ⟨101260729817934355128075553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135014306423912473504100737 101260729817934355128075553)
            ·
              refine ⟨75945547363450766346056665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101260729817934355128075553 75945547363450766346056665)
              ·
                refine ⟨56959160522588074759542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75945547363450766346056665 56959160522588074759542499)
                ·
                  refine ⟨85438740783882112139313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56959160522588074759542499 85438740783882112139313749)
                  ·
                    refine ⟨1001235243561118501632583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85438740783882112139313749 1001235243561118501632583)
                    ·
                      rfl

theorem cell22_2924848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_2924848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924848 prefixEnd_2924848 := by exact prefixLift 2924848
  have htrace : WordTrace (prefixWord ++ tailWord_2924848) baseStart_2924848 baseEnd_2924848 := by
    simpa [prefixWord, tailWord_2924848, baseEnd_2924848] using wordTrace_append hprefix tailTrace_2924848
  have hstable : (prefixWord ++ tailWord_2924848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924848).length < 2 ^ (prefixWord ++ tailWord_2924848).sum := by decide
  have hdescent : baseEnd_2924848 < baseStart_2924848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924901 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_2924901 : Nat := 118140960795 + 2924901 * 2 ^ 59
def prefixEnd_2924901 : Nat := 4983230072969 + 3 ^ 40 * 2924901 * 2
def baseEnd_2924901 : Nat := 1001253386544244030057421

theorem tailTrace_2924901 : CollatzResearch.WordTrace tailWord_2924901 prefixEnd_2924901 1001253386544244030057421 := by
  unfold tailWord_2924901
  simp only [CollatzResearch.WordTrace]
  refine ⟨106679903576590685166030557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71119935717727123444020371 106679903576590685166030557)
  ·
    refine ⟨40004963841221506937261459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106679903576590685166030557 40004963841221506937261459)
    ·
      refine ⟨60007445761832260405892189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40004963841221506937261459 60007445761832260405892189)
      ·
        refine ⟨22502792160687097652209571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60007445761832260405892189 22502792160687097652209571)
        ·
          refine ⟨33754188241030646478314357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22502792160687097652209571 33754188241030646478314357)
          ·
            refine ⟨3164455147596623107341971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33754188241030646478314357 3164455147596623107341971)
            ·
              refine ⟨4746682721394934661012957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164455147596623107341971 4746682721394934661012957)
              ·
                refine ⟨1780006020523100497879859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4746682721394934661012957 1780006020523100497879859)
                ·
                  refine ⟨2670009030784650746819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780006020523100497879859 2670009030784650746819789)
                  ·
                    refine ⟨1001253386544244030057421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670009030784650746819789 1001253386544244030057421)
                    ·
                      rfl

theorem cell22_2924901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_2924901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924901 prefixEnd_2924901 := by exact prefixLift 2924901
  have htrace : WordTrace (prefixWord ++ tailWord_2924901) baseStart_2924901 baseEnd_2924901 := by
    simpa [prefixWord, tailWord_2924901, baseEnd_2924901] using wordTrace_append hprefix tailTrace_2924901
  have hstable : (prefixWord ++ tailWord_2924901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924901).length < 2 ^ (prefixWord ++ tailWord_2924901).sum := by decide
  have hdescent : baseEnd_2924901 < baseStart_2924901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924918 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2924918 : Nat := 118140960795 + 2924918 * 2 ^ 59
def prefixEnd_2924918 : Nat := 4983230072969 + 3 ^ 40 * 2924918 * 2
def baseEnd_2924918 : Nat := 1001259205991661652382369

theorem tailTrace_2924918 : CollatzResearch.WordTrace tailWord_2924918 prefixEnd_2924918 1001259205991661652382369 := by
  unfold tailWord_2924918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667532726095568566837463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71120349078352731379599605 6667532726095568566837463)
  ·
    refine ⟨10001299089143352850256195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667532726095568566837463 10001299089143352850256195)
    ·
      refine ⟨15001948633715029275384293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10001299089143352850256195 15001948633715029275384293)
      ·
        refine ⟨2812865368821567989134555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15001948633715029275384293 2812865368821567989134555)
        ·
          refine ⟨4219298053232351983701833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812865368821567989134555 4219298053232351983701833)
          ·
            refine ⟨3164473539924263987776375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219298053232351983701833 3164473539924263987776375)
            ·
              refine ⟨4746710309886395981664563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164473539924263987776375 4746710309886395981664563)
              ·
                refine ⟨7120065464829593972496845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746710309886395981664563 7120065464829593972496845)
                ·
                  refine ⟨2670024549311097739686317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7120065464829593972496845 2670024549311097739686317)
                  ·
                    refine ⟨1001259205991661652382369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670024549311097739686317 1001259205991661652382369)
                    ·
                      rfl

theorem cell22_2924918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2924918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924918 prefixEnd_2924918 := by exact prefixLift 2924918
  have htrace : WordTrace (prefixWord ++ tailWord_2924918) baseStart_2924918 baseEnd_2924918 := by
    simpa [prefixWord, tailWord_2924918, baseEnd_2924918] using wordTrace_append hprefix tailTrace_2924918
  have hstable : (prefixWord ++ tailWord_2924918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924918).length < 2 ^ (prefixWord ++ tailWord_2924918).sum := by decide
  have hdescent : baseEnd_2924918 < baseStart_2924918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924931 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 5]
def baseStart_2924931 : Nat := 118140960795 + 2924931 * 2 ^ 59
def prefixEnd_2924931 : Nat := 4983230072969 + 3 ^ 40 * 2924931 * 2
def baseEnd_2924931 : Nat := 333754552052444650602443

theorem tailTrace_2924931 : CollatzResearch.WordTrace tailWord_2924931 prefixEnd_2924931 333754552052444650602443 := by
  unfold tailWord_2924931
  simp only [CollatzResearch.WordTrace]
  refine ⟨106680997766482000289622647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71120665177654666859748431 106680997766482000289622647)
  ·
    refine ⟨160021496649723000434433971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106680997766482000289622647 160021496649723000434433971)
    ·
      refine ⟨240032244974584500651650957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160021496649723000434433971 240032244974584500651650957)
      ·
        refine ⟨90012091865469187744369109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240032244974584500651650957 90012091865469187744369109)
        ·
          refine ⟨2109658403096934087758651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90012091865469187744369109 2109658403096934087758651)
          ·
            refine ⟨3164487604645401131637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109658403096934087758651 3164487604645401131637977)
            ·
              refine ⟨2373365703484050848728483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164487604645401131637977 2373365703484050848728483)
              ·
                refine ⟨3560048555226076273092725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373365703484050848728483 3560048555226076273092725)
                ·
                  refine ⟨333754552052444650602443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3560048555226076273092725 333754552052444650602443)
                  ·
                    rfl

theorem cell22_2924931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 5].length) (baseStart_2924931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2924931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2924931 prefixEnd_2924931 := by exact prefixLift 2924931
  have htrace : WordTrace (prefixWord ++ tailWord_2924931) baseStart_2924931 baseEnd_2924931 := by
    simpa [prefixWord, tailWord_2924931, baseEnd_2924931] using wordTrace_append hprefix tailTrace_2924931
  have hstable : (prefixWord ++ tailWord_2924931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924931).length < 2 ^ (prefixWord ++ tailWord_2924931).sum := by decide
  have hdescent : baseEnd_2924931 < baseStart_2924931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925004 : List Nat := [2, 2, 1, 4, 3, 1, 3, 6]
def baseStart_2925004 : Nat := 118140960795 + 2925004 * 2 ^ 59
def prefixEnd_2925004 : Nat := 4983230072969 + 3 ^ 40 * 2925004 * 2
def baseEnd_2925004 : Nat := 111254293949909566081345

theorem tailTrace_2925004 : CollatzResearch.WordTrace tailWord_2925004 prefixEnd_2925004 111254293949909566081345 := by
  unfold tailWord_2925004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53341830147608766878515033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71122440196811689171353377 53341830147608766878515033)
  ·
    refine ⟨40006372610706575158886275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53341830147608766878515033 40006372610706575158886275)
    ·
      refine ⟨60009558916059862738329413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40006372610706575158886275 60009558916059862738329413)
      ·
        refine ⟨11251792296761224263436765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60009558916059862738329413 11251792296761224263436765)
        ·
          refine ⟨4219422111285459098788787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11251792296761224263436765 4219422111285459098788787)
          ·
            refine ⟨6329133166928188648183181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219422111285459098788787 6329133166928188648183181)
            ·
              refine ⟨2373424937598070743068693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6329133166928188648183181 2373424937598070743068693)
              ·
                refine ⟨111254293949909566081345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373424937598070743068693 111254293949909566081345)
                ·
                  rfl

theorem cell22_2925004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_2925004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925004 prefixEnd_2925004 := by exact prefixLift 2925004
  have htrace : WordTrace (prefixWord ++ tailWord_2925004) baseStart_2925004 baseEnd_2925004 := by
    simpa [prefixWord, tailWord_2925004, baseEnd_2925004] using wordTrace_append hprefix tailTrace_2925004
  have hstable : (prefixWord ++ tailWord_2925004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925004).length < 2 ^ (prefixWord ++ tailWord_2925004).sum := by decide
  have hdescent : baseEnd_2925004 < baseStart_2925004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925032 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_2925032 : Nat := 118140960795 + 2925032 * 2 ^ 59
def prefixEnd_2925032 : Nat := 4983230072969 + 3 ^ 40 * 2925032 * 2
def baseEnd_2925032 : Nat := 333766076840467785010673

theorem tailTrace_2925032 : CollatzResearch.WordTrace tailWord_2925032 prefixEnd_2925032 333766076840467785010673 := by
  unfold tailWord_2925032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53342340769558047269524675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71123121026077396359366233 53342340769558047269524675)
  ·
    refine ⟨80013511154337070904287013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53342340769558047269524675 80013511154337070904287013)
    ·
      refine ⟨15002533341438200794553815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80013511154337070904287013 15002533341438200794553815)
      ·
        refine ⟨22503800012157301191830723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15002533341438200794553815 22503800012157301191830723)
        ·
          refine ⟨33755700018235951787746085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22503800012157301191830723 33755700018235951787746085)
          ·
            refine ⟨6329193753419240960202391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33755700018235951787746085 6329193753419240960202391)
            ·
              refine ⟨9493790630128861440303587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329193753419240960202391 9493790630128861440303587)
              ·
                refine ⟨14240685945193292160455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9493790630128861440303587 14240685945193292160455381)
                ·
                  refine ⟨333766076840467785010673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14240685945193292160455381 333766076840467785010673)
                  ·
                    rfl

theorem cell22_2925032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_2925032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925032 prefixEnd_2925032 := by exact prefixLift 2925032
  have htrace : WordTrace (prefixWord ++ tailWord_2925032) baseStart_2925032 baseEnd_2925032 := by
    simpa [prefixWord, tailWord_2925032, baseEnd_2925032] using wordTrace_append hprefix tailTrace_2925032
  have hstable : (prefixWord ++ tailWord_2925032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925032).length < 2 ^ (prefixWord ++ tailWord_2925032).sum := by decide
  have hdescent : baseEnd_2925032 < baseStart_2925032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925107 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_2925107 : Nat := 118140960795 + 2925107 * 2 ^ 59
def prefixEnd_2925107 : Nat := 4983230072969 + 3 ^ 40 * 2925107 * 2
def baseEnd_2925107 : Nat := 1001323904554128159406789

theorem tailTrace_2925107 : CollatzResearch.WordTrace tailWord_2925107 prefixEnd_2925107 1001323904554128159406789 := by
  unfold tailWord_2925107
  simp only [CollatzResearch.WordTrace]
  refine ⟨106687417013844382348029575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71124944675896254898686383 106687417013844382348029575)
  ·
    refine ⟨160031125520766573522044363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106687417013844382348029575 160031125520766573522044363)
    ·
      refine ⟨240046688281149860283066545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160031125520766573522044363 240046688281149860283066545)
      ·
        refine ⟨180035016210862395212299909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240046688281149860283066545 180035016210862395212299909)
        ·
          refine ⟨33756565539536699102306233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180035016210862395212299909 33756565539536699102306233)
          ·
            refine ⟨25317424154652524326729675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33756565539536699102306233 25317424154652524326729675)
            ·
              refine ⟨37976136231978786490094513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25317424154652524326729675 37976136231978786490094513)
              ·
                refine ⟨28482102173984089867570885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37976136231978786490094513 28482102173984089867570885)
                ·
                  refine ⟨5340394157622016850169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28482102173984089867570885 5340394157622016850169541)
                  ·
                    refine ⟨1001323904554128159406789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5340394157622016850169541 1001323904554128159406789)
                    ·
                      rfl

theorem cell22_2925107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_2925107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925107 prefixEnd_2925107 := by exact prefixLift 2925107
  have htrace : WordTrace (prefixWord ++ tailWord_2925107) baseStart_2925107 baseEnd_2925107 := by
    simpa [prefixWord, tailWord_2925107, baseEnd_2925107] using wordTrace_append hprefix tailTrace_2925107
  have hstable : (prefixWord ++ tailWord_2925107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925107).length < 2 ^ (prefixWord ++ tailWord_2925107).sum := by decide
  have hdescent : baseEnd_2925107 < baseStart_2925107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925126 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2925126 : Nat := 118140960795 + 2925126 * 2 ^ 59
def prefixEnd_2925126 : Nat := 4983230072969 + 3 ^ 40 * 2925126 * 2
def baseEnd_2925126 : Nat := 1001330408642418443181731

theorem tailTrace_2925126 : CollatzResearch.WordTrace tailWord_2925126 prefixEnd_2925126 1001330408642418443181731 := by
  unfold tailWord_2925126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334003437524235893530351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71125406667183699061980821 3334003437524235893530351)
  ·
    refine ⟨5001005156286353840295527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3334003437524235893530351 5001005156286353840295527)
    ·
      refine ⟨7501507734429530760443291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001005156286353840295527 7501507734429530760443291)
      ·
        refine ⟨11252261601644296140664937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501507734429530760443291 11252261601644296140664937)
        ·
          refine ⟨8439196201233222105498703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11252261601644296140664937 8439196201233222105498703)
          ·
            refine ⟨12658794301849833158248055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439196201233222105498703 12658794301849833158248055)
            ·
              refine ⟨18988191452774749737372083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12658794301849833158248055 18988191452774749737372083)
              ·
                refine ⟨28482287179162124606058125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18988191452774749737372083 28482287179162124606058125)
                ·
                  refine ⟨10680857692185796727271797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28482287179162124606058125 10680857692185796727271797)
                  ·
                    refine ⟨1001330408642418443181731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10680857692185796727271797 1001330408642418443181731)
                    ·
                      rfl

theorem cell22_2925126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2925126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925126 prefixEnd_2925126 := by exact prefixLift 2925126
  have htrace : WordTrace (prefixWord ++ tailWord_2925126) baseStart_2925126 baseEnd_2925126 := by
    simpa [prefixWord, tailWord_2925126, baseEnd_2925126] using wordTrace_append hprefix tailTrace_2925126
  have hstable : (prefixWord ++ tailWord_2925126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925126).length < 2 ^ (prefixWord ++ tailWord_2925126).sum := by decide
  have hdescent : baseEnd_2925126 < baseStart_2925126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925152 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_2925152 : Nat := 118140960795 + 2925152 * 2 ^ 59
def prefixEnd_2925152 : Nat := 4983230072969 + 3 ^ 40 * 2925152 * 2
def baseEnd_2925152 : Nat := 1001339308973763042031651

theorem tailTrace_2925152 : CollatzResearch.WordTrace tailWord_2925152 prefixEnd_2925152 1001339308973763042031651 := by
  unfold tailWord_2925152
  simp only [CollatzResearch.WordTrace]
  refine ⟨53344529149340677516708855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71126038865787570022278473 53344529149340677516708855)
  ·
    refine ⟨80016793724011016275063283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53344529149340677516708855 80016793724011016275063283)
    ·
      refine ⟨120025190586016524412594925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80016793724011016275063283 120025190586016524412594925)
      ·
        refine ⟨45009446469756196654723097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120025190586016524412594925 45009446469756196654723097)
        ·
          refine ⟨33757084852317147491042323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45009446469756196654723097 33757084852317147491042323)
          ·
            refine ⟨50635627278475721236563485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33757084852317147491042323 50635627278475721236563485)
            ·
              refine ⟨18988360229428395463711307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50635627278475721236563485 18988360229428395463711307)
              ·
                refine ⟨28482540344142593195566961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18988360229428395463711307 28482540344142593195566961)
                ·
                  refine ⟨21361905258106944896675221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28482540344142593195566961 21361905258106944896675221)
                  ·
                    refine ⟨1001339308973763042031651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21361905258106944896675221 1001339308973763042031651)
                    ·
                      rfl

theorem cell22_2925152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_2925152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925152 prefixEnd_2925152 := by exact prefixLift 2925152
  have htrace : WordTrace (prefixWord ++ tailWord_2925152) baseStart_2925152 baseEnd_2925152 := by
    simpa [prefixWord, tailWord_2925152, baseEnd_2925152] using wordTrace_append hprefix tailTrace_2925152
  have hstable : (prefixWord ++ tailWord_2925152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925152).length < 2 ^ (prefixWord ++ tailWord_2925152).sum := by decide
  have hdescent : baseEnd_2925152 < baseStart_2925152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925188 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2925188 : Nat := 118140960795 + 2925188 * 2 ^ 59
def prefixEnd_2925188 : Nat := 4983230072969 + 3 ^ 40 * 2925188 * 2
def baseEnd_2925188 : Nat := 1001351632509470948131541

theorem tailTrace_2925188 : CollatzResearch.WordTrace tailWord_2925188 prefixEnd_2925188 1001351632509470948131541 := by
  unfold tailWord_2925188
  simp only [CollatzResearch.WordTrace]
  refine ⟨53345185663275466590864109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71126914217700622121152145 53345185663275466590864109)
  ·
    refine ⟨20004444623728299971574041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53345185663275466590864109 20004444623728299971574041)
    ·
      refine ⟨15003333467796224978680531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20004444623728299971574041 15003333467796224978680531)
      ·
        refine ⟨22505000201694337468020797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15003333467796224978680531 22505000201694337468020797)
        ·
          refine ⟨8439375075635376550507799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22505000201694337468020797 8439375075635376550507799)
          ·
            refine ⟨12659062613453064825761699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439375075635376550507799 12659062613453064825761699)
            ·
              refine ⟨18988593920179597238642549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12659062613453064825761699 18988593920179597238642549)
              ·
                refine ⟨1780180680016837241122739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18988593920179597238642549 1780180680016837241122739)
                ·
                  refine ⟨2670271020025255861684109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780180680016837241122739 2670271020025255861684109)
                  ·
                    refine ⟨1001351632509470948131541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670271020025255861684109 1001351632509470948131541)
                    ·
                      rfl

theorem cell22_2925188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2925188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925188 prefixEnd_2925188 := by exact prefixLift 2925188
  have htrace : WordTrace (prefixWord ++ tailWord_2925188) baseStart_2925188 baseEnd_2925188 := by
    simpa [prefixWord, tailWord_2925188, baseEnd_2925188] using wordTrace_append hprefix tailTrace_2925188
  have hstable : (prefixWord ++ tailWord_2925188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925188).length < 2 ^ (prefixWord ++ tailWord_2925188).sum := by decide
  have hdescent : baseEnd_2925188 < baseStart_2925188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925231 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 1, 4]
def baseStart_2925231 : Nat := 118140960795 + 2925231 * 2 ^ 59
def prefixEnd_2925231 : Nat := 4983230072969 + 3 ^ 40 * 2925231 * 2
def baseEnd_2925231 : Nat := 1001366352288233169306409

theorem tailTrace_2925231 : CollatzResearch.WordTrace tailWord_2925231 prefixEnd_2925231 1001366352288233169306409 := by
  unfold tailWord_2925231
  simp only [CollatzResearch.WordTrace]
  refine ⟨106691939665395151525543547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71127959776930101017029031 106691939665395151525543547)
  ·
    refine ⟨160037909498092727288315321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106691939665395151525543547 160037909498092727288315321)
    ·
      refine ⟨120028432123569545466236491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160037909498092727288315321 120028432123569545466236491)
      ·
        refine ⟨180042648185354318199354737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120028432123569545466236491 180042648185354318199354737)
        ·
          refine ⟨135031986139015738649516053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180042648185354318199354737 135031986139015738649516053)
          ·
            refine ⟨6329624350266362749196065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135031986139015738649516053 6329624350266362749196065)
            ·
              refine ⟨4747218262699772061897049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329624350266362749196065 4747218262699772061897049)
              ·
                refine ⟨3560413697024829046422787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747218262699772061897049 3560413697024829046422787)
                ·
                  refine ⟨5340620545537243569634181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560413697024829046422787 5340620545537243569634181)
                  ·
                    refine ⟨1001366352288233169306409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5340620545537243569634181 1001366352288233169306409)
                    ·
                      rfl

theorem cell22_2925231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_2925231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925231 prefixEnd_2925231 := by exact prefixLift 2925231
  have htrace : WordTrace (prefixWord ++ tailWord_2925231) baseStart_2925231 baseEnd_2925231 := by
    simpa [prefixWord, tailWord_2925231, baseEnd_2925231] using wordTrace_append hprefix tailTrace_2925231
  have hstable : (prefixWord ++ tailWord_2925231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925231).length < 2 ^ (prefixWord ++ tailWord_2925231).sum := by decide
  have hdescent : baseEnd_2925231 < baseStart_2925231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925244 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2925244 : Nat := 118140960795 + 2925244 * 2 ^ 59
def prefixEnd_2925244 : Nat := 4983230072969 + 3 ^ 40 * 2925244 * 2
def baseEnd_2925244 : Nat := 1001370802453905468731369

theorem tailTrace_2925244 : CollatzResearch.WordTrace tailWord_2925244 prefixEnd_2925244 1001370802453905468731369 := by
  unfold tailWord_2925244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53346206907174027372883393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71128275876232036497177857 53346206907174027372883393)
  ·
    refine ⟨40009655180380520529662545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53346206907174027372883393 40009655180380520529662545)
    ·
      refine ⟨30007241385285390397246909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40009655180380520529662545 30007241385285390397246909)
      ·
        refine ⟨11252715519482021398967591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30007241385285390397246909 11252715519482021398967591)
        ·
          refine ⟨16879073279223032098451387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252715519482021398967591 16879073279223032098451387)
          ·
            refine ⟨25318609918834548147677081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16879073279223032098451387 25318609918834548147677081)
            ·
              refine ⟨18988957439125911110757811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25318609918834548147677081 18988957439125911110757811)
              ·
                refine ⟨28483436158688866666136717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18988957439125911110757811 28483436158688866666136717)
                ·
                  refine ⟨10681288559508324999801269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28483436158688866666136717 10681288559508324999801269)
                  ·
                    refine ⟨1001370802453905468731369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10681288559508324999801269 1001370802453905468731369)
                    ·
                      rfl

theorem cell22_2925244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2925244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925244 prefixEnd_2925244 := by exact prefixLift 2925244
  have htrace : WordTrace (prefixWord ++ tailWord_2925244) baseStart_2925244 baseEnd_2925244 := by
    simpa [prefixWord, tailWord_2925244, baseEnd_2925244] using wordTrace_append hprefix tailTrace_2925244
  have hstable : (prefixWord ++ tailWord_2925244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925244).length < 2 ^ (prefixWord ++ tailWord_2925244).sum := by decide
  have hdescent : baseEnd_2925244 < baseStart_2925244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925274 : List Nat := [3, 1, 1, 2, 2, 2, 4, 7]
def baseStart_2925274 : Nat := 118140960795 + 2925274 * 2 ^ 59
def prefixEnd_2925274 : Nat := 4983230072969 + 3 ^ 40 * 2925274 * 2
def baseEnd_2925274 : Nat := 111264563562999487831253

theorem tailTrace_2925274 : CollatzResearch.WordTrace tailWord_2925274 prefixEnd_2925274 111264563562999487831253 := by
  unfold tailWord_2925274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26673377001059842467339719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71129005336159579912905917 26673377001059842467339719)
  ·
    refine ⟨40010065501589763701009579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26673377001059842467339719 40010065501589763701009579)
    ·
      refine ⟨60015098252384645551514369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40010065501589763701009579 60015098252384645551514369)
      ·
        refine ⟨45011323689288484163635777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60015098252384645551514369 45011323689288484163635777)
        ·
          refine ⟨33758492766966363122726833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45011323689288484163635777 33758492766966363122726833)
          ·
            refine ⟨25318869575224772342045125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33758492766966363122726833 25318869575224772342045125)
            ·
              refine ⟨4747288045354644814133461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25318869575224772342045125 4747288045354644814133461)
              ·
                refine ⟨111264563562999487831253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4747288045354644814133461 111264563562999487831253)
                ·
                  rfl

theorem cell22_2925274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_2925274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925274 prefixEnd_2925274 := by exact prefixLift 2925274
  have htrace : WordTrace (prefixWord ++ tailWord_2925274) baseStart_2925274 baseEnd_2925274 := by
    simpa [prefixWord, tailWord_2925274, baseEnd_2925274] using wordTrace_append hprefix tailTrace_2925274
  have hstable : (prefixWord ++ tailWord_2925274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925274).length < 2 ^ (prefixWord ++ tailWord_2925274).sum := by decide
  have hdescent : baseEnd_2925274 < baseStart_2925274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925370 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_2925370 : Nat := 118140960795 + 2925370 * 2 ^ 59
def prefixEnd_2925370 : Nat := 4983230072969 + 3 ^ 40 * 2925370 * 2
def baseEnd_2925370 : Nat := 333804644942961046693661

theorem tailTrace_2925370 : CollatzResearch.WordTrace tailWord_2925370 prefixEnd_2925370 333804644942961046693661 := by
  unfold tailWord_2925370
  simp only [CollatzResearch.WordTrace]
  refine ⟨26674252352972894566213391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71131339607927718843235709 26674252352972894566213391)
  ·
    refine ⟨40011378529459341849320087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26674252352972894566213391 40011378529459341849320087)
    ·
      refine ⟨60017067794189012773980131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40011378529459341849320087 60017067794189012773980131)
      ·
        refine ⟨90025601691283519160970197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60017067794189012773980131 90025601691283519160970197)
        ·
          refine ⟨2109975039639457480335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90025601691283519160970197 2109975039639457480335239)
          ·
            refine ⟨3164962559459186220502859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109975039639457480335239 3164962559459186220502859)
            ·
              refine ⟨4747443839188779330754289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164962559459186220502859 4747443839188779330754289)
              ·
                refine ⟨3560582879391584498065717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747443839188779330754289 3560582879391584498065717)
                ·
                  refine ⟨333804644942961046693661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3560582879391584498065717 333804644942961046693661)
                  ·
                    rfl

theorem cell22_2925370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_2925370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925370 prefixEnd_2925370 := by exact prefixLift 2925370
  have htrace : WordTrace (prefixWord ++ tailWord_2925370) baseStart_2925370 baseEnd_2925370 := by
    simpa [prefixWord, tailWord_2925370, baseEnd_2925370] using wordTrace_append hprefix tailTrace_2925370
  have hstable : (prefixWord ++ tailWord_2925370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925370).length < 2 ^ (prefixWord ++ tailWord_2925370).sum := by decide
  have hdescent : baseEnd_2925370 < baseStart_2925370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925411 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_2925411 : Nat := 118140960795 + 2925411 * 2 ^ 59
def prefixEnd_2925411 : Nat := 4983230072969 + 3 ^ 40 * 2925411 * 2
def baseEnd_2925411 : Nat := 1001427969966772699805857

theorem tailTrace_2925411 : CollatzResearch.WordTrace tailWord_2925411 prefixEnd_2925411 1001427969966772699805857 := by
  unfold tailWord_2925411
  simp only [CollatzResearch.WordTrace]
  refine ⟨106698504804743042267096087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71132336536495361511397391 106698504804743042267096087)
  ·
    refine ⟨160047757207114563400644131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106698504804743042267096087 160047757207114563400644131)
    ·
      refine ⟨240071635810671845100966197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160047757207114563400644131 240071635810671845100966197)
      ·
        refine ⟨22506715857250485478215581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240071635810671845100966197 22506715857250485478215581)
        ·
          refine ⟨8440018446468932054330843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22506715857250485478215581 8440018446468932054330843)
          ·
            refine ⟨12660027669703398081496265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440018446468932054330843 12660027669703398081496265)
            ·
              refine ⟨9495020752277548561122199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660027669703398081496265 9495020752277548561122199)
              ·
                refine ⟨14242531128416322841683299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495020752277548561122199 14242531128416322841683299)
                ·
                  refine ⟨21363796692624484262524949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14242531128416322841683299 21363796692624484262524949)
                  ·
                    refine ⟨1001427969966772699805857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21363796692624484262524949 1001427969966772699805857)
                    ·
                      rfl

theorem cell22_2925411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_2925411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925411 prefixEnd_2925411 := by exact prefixLift 2925411
  have htrace : WordTrace (prefixWord ++ tailWord_2925411) baseStart_2925411 baseEnd_2925411 := by
    simpa [prefixWord, tailWord_2925411, baseEnd_2925411] using wordTrace_append hprefix tailTrace_2925411
  have hstable : (prefixWord ++ tailWord_2925411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925411).length < 2 ^ (prefixWord ++ tailWord_2925411).sum := by decide
  have hdescent : baseEnd_2925411 < baseStart_2925411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925415 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 4]
def baseStart_2925415 : Nat := 118140960795 + 2925415 * 2 ^ 59
def prefixEnd_2925415 : Nat := 4983230072969 + 3 ^ 40 * 2925415 * 2
def baseEnd_2925415 : Nat := 333809779749506007568615

theorem tailTrace_2925415 : CollatzResearch.WordTrace tailWord_2925415 prefixEnd_2925415 333809779749506007568615 := by
  unfold tailWord_2925415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106698650696728550950241699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71132433797819033966827799 106698650696728550950241699)
  ·
    refine ⟨160047976045092826425362549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106698650696728550950241699 160047976045092826425362549)
    ·
      refine ⟨15004497754227452477377739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160047976045092826425362549 15004497754227452477377739)
      ·
        refine ⟨22506746631341178716066609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004497754227452477377739 22506746631341178716066609)
        ·
          refine ⟨16880059973505884037049957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22506746631341178716066609 16880059973505884037049957)
          ·
            refine ⟨3165011245032353256946867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16880059973505884037049957 3165011245032353256946867)
            ·
              refine ⟨4747516867548529885420301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165011245032353256946867 4747516867548529885420301)
              ·
                refine ⟨1780318825330698707032613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747516867548529885420301 1780318825330698707032613)
                ·
                  refine ⟨333809779749506007568615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780318825330698707032613 333809779749506007568615)
                  ·
                    rfl

theorem cell22_2925415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 4].length) (baseStart_2925415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925415 prefixEnd_2925415 := by exact prefixLift 2925415
  have htrace : WordTrace (prefixWord ++ tailWord_2925415) baseStart_2925415 baseEnd_2925415 := by
    simpa [prefixWord, tailWord_2925415, baseEnd_2925415] using wordTrace_append hprefix tailTrace_2925415
  have hstable : (prefixWord ++ tailWord_2925415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925415).length < 2 ^ (prefixWord ++ tailWord_2925415).sum := by decide
  have hdescent : baseEnd_2925415 < baseStart_2925415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925430 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2925430 : Nat := 118140960795 + 2925430 * 2 ^ 59
def prefixEnd_2925430 : Nat := 4983230072969 + 3 ^ 40 * 2925430 * 2
def baseEnd_2925430 : Nat := 1001434474055062983580799

theorem tailTrace_2925430 : CollatzResearch.WordTrace tailWord_2925430 prefixEnd_2925430 1001434474055062983580799 := by
  unfold tailWord_2925430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668699861979638032002359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71132798527782805674691829 6668699861979638032002359)
  ·
    refine ⟨10003049792969457048003539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668699861979638032002359 10003049792969457048003539)
    ·
      refine ⟨15004574689454185572005309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003049792969457048003539 15004574689454185572005309)
      ·
        refine ⟨5626715508545319589501991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15004574689454185572005309 5626715508545319589501991)
        ·
          refine ⟨8440073262817979384252987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626715508545319589501991 8440073262817979384252987)
          ·
            refine ⟨12660109894226969076379481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440073262817979384252987 12660109894226969076379481)
            ·
              refine ⟨9495082420670226807284611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660109894226969076379481 9495082420670226807284611)
              ·
                refine ⟨14242623631005340210926917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495082420670226807284611 14242623631005340210926917)
                ·
                  refine ⟨2670491930813501289548797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14242623631005340210926917 2670491930813501289548797)
                  ·
                    refine ⟨1001434474055062983580799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670491930813501289548797 1001434474055062983580799)
                    ·
                      rfl

theorem cell22_2925430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2925430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925430 prefixEnd_2925430 := by exact prefixLift 2925430
  have htrace : WordTrace (prefixWord ++ tailWord_2925430) baseStart_2925430 baseEnd_2925430 := by
    simpa [prefixWord, tailWord_2925430, baseEnd_2925430] using wordTrace_append hprefix tailTrace_2925430
  have hstable : (prefixWord ++ tailWord_2925430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925430).length < 2 ^ (prefixWord ++ tailWord_2925430).sum := by decide
  have hdescent : baseEnd_2925430 < baseStart_2925430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925447 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 2, 3]
def baseStart_2925447 : Nat := 118140960795 + 2925447 * 2 ^ 59
def prefixEnd_2925447 : Nat := 4983230072969 + 3 ^ 40 * 2925447 * 2
def baseEnd_2925447 : Nat := 1001440293502480605905747

theorem tailTrace_2925447 : CollatzResearch.WordTrace tailWord_2925447 prefixEnd_2925447 1001440293502480605905747 := by
  unfold tailWord_2925447
  simp only [CollatzResearch.WordTrace]
  refine ⟨106699817832612620415406595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71133211888408413610271063 106699817832612620415406595)
  ·
    refine ⟨160049726748918930623109893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106699817832612620415406595 160049726748918930623109893)
    ·
      refine ⟨30009323765422299491833105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160049726748918930623109893 30009323765422299491833105)
      ·
        refine ⟨22506992824066724618874829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30009323765422299491833105 22506992824066724618874829)
        ·
          refine ⟨8440122309025021732078061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22506992824066724618874829 8440122309025021732078061)
          ·
            refine ⟨3165045865884383149529273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8440122309025021732078061 3165045865884383149529273)
            ·
              refine ⟨2373784399413287362146955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165045865884383149529273 2373784399413287362146955)
              ·
                refine ⟨3560676599119931043220433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373784399413287362146955 3560676599119931043220433)
                ·
                  refine ⟨2670507449339948282415325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3560676599119931043220433 2670507449339948282415325)
                  ·
                    refine ⟨1001440293502480605905747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670507449339948282415325 1001440293502480605905747)
                    ·
                      rfl

theorem cell22_2925447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_2925447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925447 prefixEnd_2925447 := by exact prefixLift 2925447
  have htrace : WordTrace (prefixWord ++ tailWord_2925447) baseStart_2925447 baseEnd_2925447 := by
    simpa [prefixWord, tailWord_2925447, baseEnd_2925447] using wordTrace_append hprefix tailTrace_2925447
  have hstable : (prefixWord ++ tailWord_2925447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925447).length < 2 ^ (prefixWord ++ tailWord_2925447).sum := by decide
  have hdescent : baseEnd_2925447 < baseStart_2925447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925462 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2925462 : Nat := 118140960795 + 2925462 * 2 ^ 59
def prefixEnd_2925462 : Nat := 4983230072969 + 3 ^ 40 * 2925462 * 2
def baseEnd_2925462 : Nat := 1001445428309025566780701

theorem tailTrace_2925462 : CollatzResearch.WordTrace tailWord_2925462 prefixEnd_2925462 1001445428309025566780701 := by
  unfold tailWord_2925462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668772807972392373575165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71133576618372185318135093 6668772807972392373575165)
  ·
    refine ⟨2500789802989647140090687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6668772807972392373575165 2500789802989647140090687)
    ·
      refine ⟨3751184704484470710136031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500789802989647140090687 3751184704484470710136031)
      ·
        refine ⟨5626777056726706065204047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751184704484470710136031 5626777056726706065204047)
        ·
          refine ⟨8440165585090059097806071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626777056726706065204047 8440165585090059097806071)
          ·
            refine ⟨12660248377635088646709107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440165585090059097806071 12660248377635088646709107)
            ·
              refine ⟨18990372566452632970063661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12660248377635088646709107 18990372566452632970063661)
              ·
                refine ⟨7121389712419737363773873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18990372566452632970063661 7121389712419737363773873)
                ·
                  refine ⟨5341042284314803022830405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121389712419737363773873 5341042284314803022830405)
                  ·
                    refine ⟨1001445428309025566780701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341042284314803022830405 1001445428309025566780701)
                    ·
                      rfl

theorem cell22_2925462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2925462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925462 prefixEnd_2925462 := by exact prefixLift 2925462
  have htrace : WordTrace (prefixWord ++ tailWord_2925462) baseStart_2925462 baseEnd_2925462 := by
    simpa [prefixWord, tailWord_2925462, baseEnd_2925462] using wordTrace_append hprefix tailTrace_2925462
  have hstable : (prefixWord ++ tailWord_2925462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925462).length < 2 ^ (prefixWord ++ tailWord_2925462).sum := by decide
  have hdescent : baseEnd_2925462 < baseStart_2925462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925494 : List Nat := [5, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2925494 : Nat := 118140960795 + 2925494 * 2 ^ 59
def prefixEnd_2925494 : Nat := 4983230072969 + 3 ^ 40 * 2925494 * 2
def baseEnd_2925494 : Nat := 111272931395887572220067

theorem tailTrace_2925494 : CollatzResearch.WordTrace tailWord_2925494 prefixEnd_2925494 111272931395887572220067 := by
  unfold tailWord_2925494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668845753965146715147971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71134354708961564961578357 6668845753965146715147971)
  ·
    refine ⟨10003268630947720072721957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668845753965146715147971 10003268630947720072721957)
    ·
      refine ⟨1875612868302697513635367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10003268630947720072721957 1875612868302697513635367)
      ·
        refine ⟨2813419302454046270453051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875612868302697513635367 2813419302454046270453051)
        ·
          refine ⟨4220128953681069405679577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813419302454046270453051 4220128953681069405679577)
          ·
            refine ⟨3165096715260802054259683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4220128953681069405679577 3165096715260802054259683)
            ·
              refine ⟨4747645072891203081389525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165096715260802054259683 4747645072891203081389525)
              ·
                refine ⟨111272931395887572220067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4747645072891203081389525 111272931395887572220067)
                ·
                  rfl

theorem cell22_2925494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2925494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925494 prefixEnd_2925494 := by exact prefixLift 2925494
  have htrace : WordTrace (prefixWord ++ tailWord_2925494) baseStart_2925494 baseEnd_2925494 := by
    simpa [prefixWord, tailWord_2925494, baseEnd_2925494] using wordTrace_append hprefix tailTrace_2925494
  have hstable : (prefixWord ++ tailWord_2925494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925494).length < 2 ^ (prefixWord ++ tailWord_2925494).sum := by decide
  have hdescent : baseEnd_2925494 < baseStart_2925494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925518 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2925518 : Nat := 118140960795 + 2925518 * 2 ^ 59
def prefixEnd_2925518 : Nat := 4983230072969 + 3 ^ 40 * 2925518 * 2
def baseEnd_2925518 : Nat := 1001464598253460087380529

theorem tailTrace_2925518 : CollatzResearch.WordTrace tailWord_2925518 prefixEnd_2925518 1001464598253460087380529 := by
  unfold tailWord_2925518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337800926919424942655151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71134938276903599694160805 13337800926919424942655151)
  ·
    refine ⟨20006701390379137413982727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13337800926919424942655151 20006701390379137413982727)
    ·
      refine ⟨30010052085568706120974091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20006701390379137413982727 30010052085568706120974091)
      ·
        refine ⟨45015078128353059181461137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30010052085568706120974091 45015078128353059181461137)
        ·
          refine ⟨33761308596264794386095853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45015078128353059181461137 33761308596264794386095853)
          ·
            refine ⟨12660490723599297894785945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33761308596264794386095853 12660490723599297894785945)
            ·
              refine ⟨9495368042699473421089459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660490723599297894785945 9495368042699473421089459)
              ·
                refine ⟨14243052064049210131634189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495368042699473421089459 14243052064049210131634189)
                ·
                  refine ⟨5341144524018453799362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14243052064049210131634189 5341144524018453799362821)
                  ·
                    refine ⟨1001464598253460087380529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341144524018453799362821 1001464598253460087380529)
                    ·
                      rfl

theorem cell22_2925518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2925518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925518 prefixEnd_2925518 := by exact prefixLift 2925518
  have htrace : WordTrace (prefixWord ++ tailWord_2925518) baseStart_2925518 baseEnd_2925518 := by
    simpa [prefixWord, tailWord_2925518, baseEnd_2925518] using wordTrace_append hprefix tailTrace_2925518
  have hstable : (prefixWord ++ tailWord_2925518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925518).length < 2 ^ (prefixWord ++ tailWord_2925518).sum := by decide
  have hdescent : baseEnd_2925518 < baseStart_2925518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925535 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 1, 4]
def baseStart_2925535 : Nat := 118140960795 + 2925535 * 2 ^ 59
def prefixEnd_2925535 : Nat := 4983230072969 + 3 ^ 40 * 2925535 * 2
def baseEnd_2925535 : Nat := 1001470417700877709705477

theorem tailTrace_2925535 : CollatzResearch.WordTrace tailWord_2925535 prefixEnd_2925535 1001470417700877709705477 := by
  unfold tailWord_2925535
  simp only [CollatzResearch.WordTrace]
  refine ⟨106703027456293811444610059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71135351637529207629740039 106703027456293811444610059)
  ·
    refine ⟨160054541184440717166915089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106703027456293811444610059 160054541184440717166915089)
    ·
      refine ⟨120040905888330537875186317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160054541184440717166915089 120040905888330537875186317)
      ·
        refine ⟨45015339708123951703194869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120040905888330537875186317 45015339708123951703194869)
        ·
          refine ⟨4220188097636620472174519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45015339708123951703194869 4220188097636620472174519)
          ·
            refine ⟨6330282146454930708261779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220188097636620472174519 6330282146454930708261779)
            ·
              refine ⟨9495423219682396062392669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330282146454930708261779 9495423219682396062392669)
              ·
                refine ⟨3560783707380898523397251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9495423219682396062392669 3560783707380898523397251)
                ·
                  refine ⟨5341175561071347785095877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560783707380898523397251 5341175561071347785095877)
                  ·
                    refine ⟨1001470417700877709705477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5341175561071347785095877 1001470417700877709705477)
                    ·
                      rfl

theorem cell22_2925535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_2925535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925535 prefixEnd_2925535 := by exact prefixLift 2925535
  have htrace : WordTrace (prefixWord ++ tailWord_2925535) baseStart_2925535 baseEnd_2925535 := by
    simpa [prefixWord, tailWord_2925535, baseEnd_2925535] using wordTrace_append hprefix tailTrace_2925535
  have hstable : (prefixWord ++ tailWord_2925535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925535).length < 2 ^ (prefixWord ++ tailWord_2925535).sum := by decide
  have hdescent : baseEnd_2925535 < baseStart_2925535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925550 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_2925550 : Nat := 118140960795 + 2925550 * 2 ^ 59
def prefixEnd_2925550 : Nat := 4983230072969 + 3 ^ 40 * 2925550 * 2
def baseEnd_2925550 : Nat := 333825184169140890193477

theorem tailTrace_2925550 : CollatzResearch.WordTrace tailWord_2925550 prefixEnd_2925550 333825184169140890193477 := by
  unfold tailWord_2925550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337946818904933625800763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71135716367492979337604069 13337946818904933625800763)
  ·
    refine ⟨20006920228357400438701145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13337946818904933625800763 20006920228357400438701145)
    ·
      refine ⟨15005190171268050329025859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20006920228357400438701145 15005190171268050329025859)
      ·
        refine ⟨22507785256902075493538789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005190171268050329025859 22507785256902075493538789)
        ·
          refine ⟨4220209735669139155038523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22507785256902075493538789 4220209735669139155038523)
          ·
            refine ⟨6330314603503708732557785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220209735669139155038523 6330314603503708732557785)
            ·
              refine ⟨4747735952627781549418339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330314603503708732557785 4747735952627781549418339)
              ·
                refine ⟨7121603928941672324127509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747735952627781549418339 7121603928941672324127509)
                ·
                  refine ⟨333825184169140890193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7121603928941672324127509 333825184169140890193477)
                  ·
                    rfl

theorem cell22_2925550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_2925550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925550 prefixEnd_2925550 := by exact prefixLift 2925550
  have htrace : WordTrace (prefixWord ++ tailWord_2925550) baseStart_2925550 baseEnd_2925550 := by
    simpa [prefixWord, tailWord_2925550, baseEnd_2925550] using wordTrace_append hprefix tailTrace_2925550
  have hstable : (prefixWord ++ tailWord_2925550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925550).length < 2 ^ (prefixWord ++ tailWord_2925550).sum := by decide
  have hdescent : baseEnd_2925550 < baseStart_2925550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925561 : List Nat := [1, 2, 1, 3, 1, 3, 2, 9]
def baseStart_2925561 : Nat := 118140960795 + 2925561 * 2 ^ 59
def prefixEnd_2925561 : Nat := 4983230072969 + 3 ^ 40 * 2925561 * 2
def baseEnd_2925561 : Nat := 111275479781358034283933

theorem tailTrace_2925561 : CollatzResearch.WordTrace tailWord_2925561 prefixEnd_2925561 111275479781358034283933 := by
  unfold tailWord_2925561
  simp only [CollatzResearch.WordTrace]
  refine ⟨106703975754199617885056537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71135983836133078590037691 106703975754199617885056537)
  ·
    refine ⟨80027981815649713413792403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106703975754199617885056537 80027981815649713413792403)
    ·
      refine ⟨120041972723474570120688605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80027981815649713413792403 120041972723474570120688605)
      ·
        refine ⟨45015739771302963795258227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120041972723474570120688605 45015739771302963795258227)
        ·
          refine ⟨67523609656954445692887341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45015739771302963795258227 67523609656954445692887341)
          ·
            refine ⟨25321353621357917134832753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67523609656954445692887341 25321353621357917134832753)
            ·
              refine ⟨18991015216018437851124565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25321353621357917134832753 18991015216018437851124565)
              ·
                refine ⟨111275479781358034283933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18991015216018437851124565 111275479781358034283933)
                ·
                  rfl

theorem cell22_2925561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 9].length) (baseStart_2925561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925561 prefixEnd_2925561 := by exact prefixLift 2925561
  have htrace : WordTrace (prefixWord ++ tailWord_2925561) baseStart_2925561 baseEnd_2925561 := by
    simpa [prefixWord, tailWord_2925561, baseEnd_2925561] using wordTrace_append hprefix tailTrace_2925561
  have hstable : (prefixWord ++ tailWord_2925561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925561).length < 2 ^ (prefixWord ++ tailWord_2925561).sum := by decide
  have hdescent : baseEnd_2925561 < baseStart_2925561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925578 : List Nat := [3, 1, 2, 2, 3, 2, 1, 8]
def baseStart_2925578 : Nat := 118140960795 + 2925578 * 2 ^ 59
def prefixEnd_2925578 : Nat := 4983230072969 + 3 ^ 40 * 2925578 * 2
def baseEnd_2925578 : Nat := 111276126386626658986705

theorem tailTrace_2925578 : CollatzResearch.WordTrace tailWord_2925578 prefixEnd_2925578 111276126386626658986705 := by
  unfold tailWord_2925578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676148948784507447106347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71136397196758686525616925 26676148948784507447106347)
  ·
    refine ⟨40014223423176761170659521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26676148948784507447106347 40014223423176761170659521)
    ·
      refine ⟨30010667567382570877994641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40014223423176761170659521 30010667567382570877994641)
      ·
        refine ⟨22508000675536928158495981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30010667567382570877994641 22508000675536928158495981)
        ·
          refine ⟨8440500253326348059435993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22508000675536928158495981 8440500253326348059435993)
          ·
            refine ⟨6330375189994761044576995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440500253326348059435993 6330375189994761044576995)
            ·
              refine ⟨9495562784992141566865493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330375189994761044576995 9495562784992141566865493)
              ·
                refine ⟨111276126386626658986705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9495562784992141566865493 111276126386626658986705)
                ·
                  rfl

theorem cell22_2925578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_2925578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925578 prefixEnd_2925578 := by exact prefixLift 2925578
  have htrace : WordTrace (prefixWord ++ tailWord_2925578) baseStart_2925578 baseEnd_2925578 := by
    simpa [prefixWord, tailWord_2925578, baseEnd_2925578] using wordTrace_append hprefix tailTrace_2925578
  have hstable : (prefixWord ++ tailWord_2925578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925578).length < 2 ^ (prefixWord ++ tailWord_2925578).sum := by decide
  have hdescent : baseEnd_2925578 < baseStart_2925578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925593 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_2925593 : Nat := 118140960795 + 2925593 * 2 ^ 59
def prefixEnd_2925593 : Nat := 4983230072969 + 3 ^ 40 * 2925593 * 2
def baseEnd_2925593 : Nat := 1001490272286184891755299

theorem tailTrace_2925593 : CollatzResearch.WordTrace tailWord_2925593 prefixEnd_2925593 1001490272286184891755299 := by
  unfold tailWord_2925593
  simp only [CollatzResearch.WordTrace]
  refine ⟨106705142890083687350221433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71136761926722458233480955 106705142890083687350221433)
  ·
    refine ⟨80028857167562765512666075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106705142890083687350221433 80028857167562765512666075)
    ·
      refine ⟨120043285751344148268999113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80028857167562765512666075 120043285751344148268999113)
      ·
        refine ⟨90032464313508111201749335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120043285751344148268999113 90032464313508111201749335)
        ·
          refine ⟨135048696470262166802624003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90032464313508111201749335 135048696470262166802624003)
          ·
            refine ⟨202573044705393250203936005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135048696470262166802624003 202573044705393250203936005)
            ·
              refine ⟨37982445882261234413238001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202573044705393250203936005 37982445882261234413238001)
              ·
                refine ⟨28486834411695925809928501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37982445882261234413238001 28486834411695925809928501)
                ·
                  refine ⟨2670640726096493044680797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28486834411695925809928501 2670640726096493044680797)
                  ·
                    refine ⟨1001490272286184891755299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670640726096493044680797 1001490272286184891755299)
                    ·
                      rfl

theorem cell22_2925593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_2925593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925593 prefixEnd_2925593 := by exact prefixLift 2925593
  have htrace : WordTrace (prefixWord ++ tailWord_2925593) baseStart_2925593 baseEnd_2925593 := by
    simpa [prefixWord, tailWord_2925593, baseEnd_2925593] using wordTrace_append hprefix tailTrace_2925593
  have hstable : (prefixWord ++ tailWord_2925593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925593).length < 2 ^ (prefixWord ++ tailWord_2925593).sum := by decide
  have hdescent : baseEnd_2925593 < baseStart_2925593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925661 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2925661 : Nat := 118140960795 + 2925661 * 2 ^ 59
def prefixEnd_2925661 : Nat := 4983230072969 + 3 ^ 40 * 2925661 * 2
def baseEnd_2925661 : Nat := 1001513550075855381055091

theorem tailTrace_2925661 : CollatzResearch.WordTrace tailWord_2925661 prefixEnd_2925661 1001513550075855381055091 := by
  unfold tailWord_2925661
  simp only [CollatzResearch.WordTrace]
  refine ⟨106707623053837334963696837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71138415369224889975797891 106707623053837334963696837)
  ·
    refine ⟨20007679322594500305693157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106707623053837334963696837 20007679322594500305693157)
    ·
      refine ⟨3751439872986468807317467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20007679322594500305693157 3751439872986468807317467)
      ·
        refine ⟨5627159809479703210976201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751439872986468807317467 5627159809479703210976201)
        ·
          refine ⟨4220369857109777408232151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627159809479703210976201 4220369857109777408232151)
          ·
            refine ⟨6330554785664666112348227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220369857109777408232151 6330554785664666112348227)
            ·
              refine ⟨9495832178496999168522341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330554785664666112348227 9495832178496999168522341)
              ·
                refine ⟨1780468533468187344097939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9495832178496999168522341 1780468533468187344097939)
                ·
                  refine ⟨2670702800202281016146909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780468533468187344097939 2670702800202281016146909)
                  ·
                    refine ⟨1001513550075855381055091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670702800202281016146909 1001513550075855381055091)
                    ·
                      rfl

theorem cell22_2925661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2925661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925661 prefixEnd_2925661 := by exact prefixLift 2925661
  have htrace : WordTrace (prefixWord ++ tailWord_2925661) baseStart_2925661 baseEnd_2925661 := by
    simpa [prefixWord, tailWord_2925661, baseEnd_2925661] using wordTrace_append hprefix tailTrace_2925661
  have hstable : (prefixWord ++ tailWord_2925661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925661).length < 2 ^ (prefixWord ++ tailWord_2925661).sum := by decide
  have hdescent : baseEnd_2925661 < baseStart_2925661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925668 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2925668 : Nat := 118140960795 + 2925668 * 2 ^ 59
def prefixEnd_2925668 : Nat := 4983230072969 + 3 ^ 40 * 2925668 * 2
def baseEnd_2925668 : Nat := 333838648772969898710023

theorem tailTrace_2925668 : CollatzResearch.WordTrace tailWord_2925668 prefixEnd_2925668 333838648772969898710023 := by
  unfold tailWord_2925668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53353939182405987579600829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71138585576541316772801105 53353939182405987579600829)
  ·
    refine ⟨20007727193402245342350311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53353939182405987579600829 20007727193402245342350311)
    ·
      refine ⟨30011590790103368013525467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20007727193402245342350311 30011590790103368013525467)
      ·
        refine ⟨45017386185155052020288201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30011590790103368013525467 45017386185155052020288201)
        ·
          refine ⟨33763039638866289015216151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45017386185155052020288201 33763039638866289015216151)
          ·
            refine ⟨50644559458299433522824227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33763039638866289015216151 50644559458299433522824227)
            ·
              refine ⟨75966839187449150284236341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50644559458299433522824227 75966839187449150284236341)
              ·
                refine ⟨7121891173823357839147157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75966839187449150284236341 7121891173823357839147157)
                ·
                  refine ⟨333838648772969898710023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7121891173823357839147157 333838648772969898710023)
                  ·
                    rfl

theorem cell22_2925668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2925668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925668 prefixEnd_2925668 := by exact prefixLift 2925668
  have htrace : WordTrace (prefixWord ++ tailWord_2925668) baseStart_2925668 baseEnd_2925668 := by
    simpa [prefixWord, tailWord_2925668, baseEnd_2925668] using wordTrace_append hprefix tailTrace_2925668
  have hstable : (prefixWord ++ tailWord_2925668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925668).length < 2 ^ (prefixWord ++ tailWord_2925668).sum := by decide
  have hdescent : baseEnd_2925668 < baseStart_2925668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925672 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_2925672 : Nat := 118140960795 + 2925672 * 2 ^ 59
def prefixEnd_2925672 : Nat := 4983230072969 + 3 ^ 40 * 2925672 * 2
def baseEnd_2925672 : Nat := 1001517315600655019030057

theorem tailTrace_2925672 : CollatzResearch.WordTrace tailWord_2925672 prefixEnd_2925672 1001517315600655019030057 := by
  unfold tailWord_2925672
  simp only [CollatzResearch.WordTrace]
  refine ⟨53354012128398741921173635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71138682837864989228231513 53354012128398741921173635)
  ·
    refine ⟨80031018192598112881760453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53354012128398741921173635 80031018192598112881760453)
    ·
      refine ⟨15005815911112146165330085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80031018192598112881760453 15005815911112146165330085)
      ·
        refine ⟨2813590483333527405999391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15005815911112146165330085 2813590483333527405999391)
        ·
          refine ⟨4220385725000291108999087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813590483333527405999391 4220385725000291108999087)
          ·
            refine ⟨6330578587500436663498631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220385725000291108999087 6330578587500436663498631)
            ·
              refine ⟨9495867881250654995247947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330578587500436663498631 9495867881250654995247947)
              ·
                refine ⟨14243801821875982492871921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495867881250654995247947 14243801821875982492871921)
                ·
                  refine ⟨10682851366406986869653941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14243801821875982492871921 10682851366406986869653941)
                  ·
                    refine ⟨1001517315600655019030057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10682851366406986869653941 1001517315600655019030057)
                    ·
                      rfl

theorem cell22_2925672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_2925672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925672 prefixEnd_2925672 := by exact prefixLift 2925672
  have htrace : WordTrace (prefixWord ++ tailWord_2925672) baseStart_2925672 baseEnd_2925672 := by
    simpa [prefixWord, tailWord_2925672, baseEnd_2925672] using wordTrace_append hprefix tailTrace_2925672
  have hstable : (prefixWord ++ tailWord_2925672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925672).length < 2 ^ (prefixWord ++ tailWord_2925672).sum := by decide
  have hdescent : baseEnd_2925672 < baseStart_2925672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925700 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2925700 : Nat := 118140960795 + 2925700 * 2 ^ 59
def prefixEnd_2925700 : Nat := 4983230072969 + 3 ^ 40 * 2925700 * 2
def baseEnd_2925700 : Nat := 1001526900572872279329971

theorem tailTrace_2925700 : CollatzResearch.WordTrace tailWord_2925700 prefixEnd_2925700 1001526900572872279329971 := by
  unfold tailWord_2925700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53354522750348022312183277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71139363667130696416244369 53354522750348022312183277)
  ·
    refine ⟨20007946031380508367068729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53354522750348022312183277 20007946031380508367068729)
    ·
      refine ⟨15005959523535381275301547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20007946031380508367068729 15005959523535381275301547)
      ·
        refine ⟨22508939285303071912952321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005959523535381275301547 22508939285303071912952321)
        ·
          refine ⟨16881704463977303934714241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22508939285303071912952321 16881704463977303934714241)
          ·
            refine ⟨12661278347982977951035681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16881704463977303934714241 12661278347982977951035681)
            ·
              refine ⟨9495958760987233463276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12661278347982977951035681 9495958760987233463276761)
              ·
                refine ⟨7121969070740425097457571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9495958760987233463276761 7121969070740425097457571)
                ·
                  refine ⟨10682953606110637646186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121969070740425097457571 10682953606110637646186357)
                  ·
                    refine ⟨1001526900572872279329971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10682953606110637646186357 1001526900572872279329971)
                    ·
                      rfl

theorem cell22_2925700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2925700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925700 prefixEnd_2925700 := by exact prefixLift 2925700
  have htrace : WordTrace (prefixWord ++ tailWord_2925700) baseStart_2925700 baseEnd_2925700 := by
    simpa [prefixWord, tailWord_2925700, baseEnd_2925700] using wordTrace_append hprefix tailTrace_2925700
  have hstable : (prefixWord ++ tailWord_2925700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925700).length < 2 ^ (prefixWord ++ tailWord_2925700).sum := by decide
  have hdescent : baseEnd_2925700 < baseStart_2925700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925743 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_2925743 : Nat := 118140960795 + 2925743 * 2 ^ 59
def prefixEnd_2925743 : Nat := 4983230072969 + 3 ^ 40 * 2925743 * 2
def baseEnd_2925743 : Nat := 1001541620351634500504839

theorem tailTrace_2925743 : CollatzResearch.WordTrace tailWord_2925743 prefixEnd_2925743 1001541620351634500504839 := by
  unfold tailWord_2925743
  simp only [CollatzResearch.WordTrace]
  refine ⟨106710613839540262968181883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71140409226360175312121255 106710613839540262968181883)
  ·
    refine ⟨160065920759310394452272825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106710613839540262968181883 160065920759310394452272825)
    ·
      refine ⟨120049440569482795839204619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160065920759310394452272825 120049440569482795839204619)
      ·
        refine ⟨180074160854224193758806929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120049440569482795839204619 180074160854224193758806929)
        ·
          refine ⟨135055620640668145319105197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180074160854224193758806929 135055620640668145319105197)
          ·
            refine ⟨50645857740250554494664449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135055620640668145319105197 50645857740250554494664449)
            ·
              refine ⟨37984393305187915870998337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50645857740250554494664449 37984393305187915870998337)
              ·
                refine ⟨28488294978890936903248753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37984393305187915870998337 28488294978890936903248753)
                ·
                  refine ⟨21366221234168202677436565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28488294978890936903248753 21366221234168202677436565)
                  ·
                    refine ⟨1001541620351634500504839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21366221234168202677436565 1001541620351634500504839)
                    ·
                      rfl

theorem cell22_2925743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_2925743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925743 prefixEnd_2925743 := by exact prefixLift 2925743
  have htrace : WordTrace (prefixWord ++ tailWord_2925743) baseStart_2925743 baseEnd_2925743 := by
    simpa [prefixWord, tailWord_2925743, baseEnd_2925743] using wordTrace_append hprefix tailTrace_2925743
  have hstable : (prefixWord ++ tailWord_2925743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925743).length < 2 ^ (prefixWord ++ tailWord_2925743).sum := by decide
  have hdescent : baseEnd_2925743 < baseStart_2925743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925792 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_2925792 : Nat := 118140960795 + 2925792 * 2 ^ 59
def prefixEnd_2925792 : Nat := 4983230072969 + 3 ^ 40 * 2925792 * 2
def baseEnd_2925792 : Nat := 333852798017671568676563

theorem tailTrace_2925792 : CollatzResearch.WordTrace tailWord_2925792 prefixEnd_2925792 333852798017671568676563 := by
  unfold tailWord_2925792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53356200508181372168357815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71141600677575162891143753 53356200508181372168357815)
  ·
    refine ⟨80034300762272058252536723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53356200508181372168357815 80034300762272058252536723)
    ·
      refine ⟨120051451143408087378805085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80034300762272058252536723 120051451143408087378805085)
      ·
        refine ⟨45019294178778032767051907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120051451143408087378805085 45019294178778032767051907)
        ·
          refine ⟨67528941268167049150577861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45019294178778032767051907 67528941268167049150577861)
          ·
            refine ⟨12661676487781321715733349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67528941268167049150577861 12661676487781321715733349)
            ·
              refine ⟨2374064341458997821700003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12661676487781321715733349 2374064341458997821700003)
              ·
                refine ⟨3561096512188496732550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374064341458997821700003 3561096512188496732550005)
                ·
                  refine ⟨333852798017671568676563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561096512188496732550005 333852798017671568676563)
                  ·
                    rfl

theorem cell22_2925792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_2925792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925792 prefixEnd_2925792 := by exact prefixLift 2925792
  have htrace : WordTrace (prefixWord ++ tailWord_2925792) baseStart_2925792 baseEnd_2925792 := by
    simpa [prefixWord, tailWord_2925792, baseEnd_2925792] using wordTrace_append hprefix tailTrace_2925792
  have hstable : (prefixWord ++ tailWord_2925792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925792).length < 2 ^ (prefixWord ++ tailWord_2925792).sum := by decide
  have hdescent : baseEnd_2925792 < baseStart_2925792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925869 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2925869 : Nat := 118140960795 + 2925869 * 2 ^ 59
def prefixEnd_2925869 : Nat := 4983230072969 + 3 ^ 40 * 2925869 * 2
def baseEnd_2925869 : Nat := 1001584752726612171854453

theorem tailTrace_2925869 : CollatzResearch.WordTrace tailWord_2925869 prefixEnd_2925869 1001584752726612171854453 := by
  unfold tailWord_2925869
  simp only [CollatzResearch.WordTrace]
  refine ⟨106715209437083786487268661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71143472958055857658179107 106715209437083786487268661)
  ·
    refine ⟨10004550884726604983181437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106715209437083786487268661 10004550884726604983181437)
    ·
      refine ⟨3751706581772476868693039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10004550884726604983181437 3751706581772476868693039)
      ·
        refine ⟨5627559872658715303039559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751706581772476868693039 5627559872658715303039559)
        ·
          refine ⟨8441339808988072954559339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627559872658715303039559 8441339808988072954559339)
          ·
            refine ⟨12662009713482109431839009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441339808988072954559339 12662009713482109431839009)
            ·
              refine ⟨9496507285111582073879257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662009713482109431839009 9496507285111582073879257)
              ·
                refine ⟨7122380463833686555409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496507285111582073879257 7122380463833686555409443)
                ·
                  refine ⟨10683570695750529833114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122380463833686555409443 10683570695750529833114165)
                  ·
                    refine ⟨1001584752726612171854453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10683570695750529833114165 1001584752726612171854453)
                    ·
                      rfl

theorem cell22_2925869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2925869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925869 prefixEnd_2925869 := by exact prefixLift 2925869
  have htrace : WordTrace (prefixWord ++ tailWord_2925869) baseStart_2925869 baseEnd_2925869 := by
    simpa [prefixWord, tailWord_2925869, baseEnd_2925869] using wordTrace_append hprefix tailTrace_2925869
  have hstable : (prefixWord ++ tailWord_2925869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925869).length < 2 ^ (prefixWord ++ tailWord_2925869).sum := by decide
  have hdescent : baseEnd_2925869 < baseStart_2925869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925897 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_2925897 : Nat := 118140960795 + 2925897 * 2 ^ 59
def prefixEnd_2925897 : Nat := 4983230072969 + 3 ^ 40 * 2925897 * 2
def baseEnd_2925897 : Nat := 1001594337698829432154367

theorem tailTrace_2925897 : CollatzResearch.WordTrace tailWord_2925897 prefixEnd_2925897 1001594337698829432154367 := by
  unfold tailWord_2925897
  simp only [CollatzResearch.WordTrace]
  refine ⟨106716230680982347269287945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71144153787321564846191963 106716230680982347269287945)
  ·
    refine ⟨80037173010736760451965959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106716230680982347269287945 80037173010736760451965959)
    ·
      refine ⟨120055759516105140677948939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80037173010736760451965959 120055759516105140677948939)
      ·
        refine ⟨180083639274157711016923409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120055759516105140677948939 180083639274157711016923409)
        ·
          refine ⟨135062729455618283262692557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180083639274157711016923409 135062729455618283262692557)
          ·
            refine ⟨50648523545856856223509709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135062729455618283262692557 50648523545856856223509709)
            ·
              refine ⟨18993196329696321083816141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50648523545856856223509709 18993196329696321083816141)
              ·
                refine ⟨7122448623636120406431053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18993196329696321083816141 7122448623636120406431053)
                ·
                  refine ⟨2670918233863545152411645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7122448623636120406431053 2670918233863545152411645)
                  ·
                    refine ⟨1001594337698829432154367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670918233863545152411645 1001594337698829432154367)
                    ·
                      rfl

theorem cell22_2925897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_2925897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925897 prefixEnd_2925897 := by exact prefixLift 2925897
  have htrace : WordTrace (prefixWord ++ tailWord_2925897) baseStart_2925897 baseEnd_2925897 := by
    simpa [prefixWord, tailWord_2925897, baseEnd_2925897] using wordTrace_append hprefix tailTrace_2925897
  have hstable : (prefixWord ++ tailWord_2925897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925897).length < 2 ^ (prefixWord ++ tailWord_2925897).sum := by decide
  have hdescent : baseEnd_2925897 < baseStart_2925897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925961 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 5]
def baseStart_2925961 : Nat := 118140960795 + 2925961 * 2 ^ 59
def prefixEnd_2925961 : Nat := 4983230072969 + 3 ^ 40 * 2925961 * 2
def baseEnd_2925961 : Nat := 333872082068918199518057

theorem tailTrace_2925961 : CollatzResearch.WordTrace tailWord_2925961 prefixEnd_2925961 333872082068918199518057 := by
  unfold tailWord_2925961
  simp only [CollatzResearch.WordTrace]
  refine ⟨106718564952750486199617737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71145709968500324133078491 106718564952750486199617737)
  ·
    refine ⟨80038923714562864649713303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106718564952750486199617737 80038923714562864649713303)
    ·
      refine ⟨120058385571844296974569955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80038923714562864649713303 120058385571844296974569955)
      ·
        refine ⟨180087578357766445461854933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120058385571844296974569955 180087578357766445461854933)
        ·
          refine ⟨4220802617760151065512225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 180087578357766445461854933 4220802617760151065512225)
          ·
            refine ⟨3165601963320113299134169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4220802617760151065512225 3165601963320113299134169)
            ·
              refine ⟨2374201472490084974350627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165601963320113299134169 2374201472490084974350627)
              ·
                refine ⟨3561302208735127461525941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374201472490084974350627 3561302208735127461525941)
                ·
                  refine ⟨333872082068918199518057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561302208735127461525941 333872082068918199518057)
                  ·
                    rfl

theorem cell22_2925961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_2925961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925961 prefixEnd_2925961 := by exact prefixLift 2925961
  have htrace : WordTrace (prefixWord ++ tailWord_2925961) baseStart_2925961 baseEnd_2925961 := by
    simpa [prefixWord, tailWord_2925961, baseEnd_2925961] using wordTrace_append hprefix tailTrace_2925961
  have hstable : (prefixWord ++ tailWord_2925961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925961).length < 2 ^ (prefixWord ++ tailWord_2925961).sum := by decide
  have hdescent : baseEnd_2925961 < baseStart_2925961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925987 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_2925987 : Nat := 118140960795 + 2925987 * 2 ^ 59
def prefixEnd_2925987 : Nat := 4983230072969 + 3 ^ 40 * 2925987 * 2
def baseEnd_2925987 : Nat := 1001625146538099197404091

theorem tailTrace_2925987 : CollatzResearch.WordTrace tailWord_2925987 prefixEnd_2925987 1001625146538099197404091 := by
  unfold tailWord_2925987
  simp only [CollatzResearch.WordTrace]
  refine ⟨106719513250656292640064215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71146342167104195093376143 106719513250656292640064215)
  ·
    refine ⟨160079269875984438960096323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106719513250656292640064215 160079269875984438960096323)
    ·
      refine ⟨240118904813976658440144485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160079269875984438960096323 240118904813976658440144485)
      ·
        refine ⟨45022294652620623457527091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240118904813976658440144485 45022294652620623457527091)
        ·
          refine ⟨67533441978930935186290637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45022294652620623457527091 67533441978930935186290637)
          ·
            refine ⟨25325040742099100694858989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67533441978930935186290637 25325040742099100694858989)
            ·
              refine ⟨9496890278287162760572121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25325040742099100694858989 9496890278287162760572121)
              ·
                refine ⟨7122667708715372070429091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496890278287162760572121 7122667708715372070429091)
                ·
                  refine ⟨10684001563073058105643637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122667708715372070429091 10684001563073058105643637)
                  ·
                    refine ⟨1001625146538099197404091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10684001563073058105643637 1001625146538099197404091)
                    ·
                      rfl

theorem cell22_2925987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_2925987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925987 prefixEnd_2925987 := by exact prefixLift 2925987
  have htrace : WordTrace (prefixWord ++ tailWord_2925987) baseStart_2925987 baseEnd_2925987 := by
    simpa [prefixWord, tailWord_2925987, baseEnd_2925987] using wordTrace_append hprefix tailTrace_2925987
  have hstable : (prefixWord ++ tailWord_2925987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925987).length < 2 ^ (prefixWord ++ tailWord_2925987).sum := by decide
  have hdescent : baseEnd_2925987 < baseStart_2925987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925991 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2925991 : Nat := 118140960795 + 2925991 * 2 ^ 59
def prefixEnd_2925991 : Nat := 4983230072969 + 3 ^ 40 * 2925991 * 2
def baseEnd_2925991 : Nat := 1001626515819844520304079

theorem tailTrace_2925991 : CollatzResearch.WordTrace tailWord_2925991 prefixEnd_2925991 1001626515819844520304079 := by
  unfold tailWord_2925991
  simp only [CollatzResearch.WordTrace]
  refine ⟨106719659142641801323209827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71146439428427867548806551 106719659142641801323209827)
  ·
    refine ⟨160079488713962701984814741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106719659142641801323209827 160079488713962701984814741)
    ·
      refine ⟨7503726033467001655538191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160079488713962701984814741 7503726033467001655538191)
      ·
        refine ⟨11255589050200502483307287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7503726033467001655538191 11255589050200502483307287)
        ·
          refine ⟨16883383575300753724960931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11255589050200502483307287 16883383575300753724960931)
          ·
            refine ⟨25325075362951130587441397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16883383575300753724960931 25325075362951130587441397)
            ·
              refine ⟨2374225815276668492572631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25325075362951130587441397 2374225815276668492572631)
              ·
                refine ⟨3561338722915002738858947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374225815276668492572631 3561338722915002738858947)
                ·
                  refine ⟨5342008084372504108288421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561338722915002738858947 5342008084372504108288421)
                  ·
                    refine ⟨1001626515819844520304079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342008084372504108288421 1001626515819844520304079)
                    ·
                      rfl

theorem cell22_2925991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2925991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2925991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2925991 prefixEnd_2925991 := by exact prefixLift 2925991
  have htrace : WordTrace (prefixWord ++ tailWord_2925991) baseStart_2925991 baseEnd_2925991 := by
    simpa [prefixWord, tailWord_2925991, baseEnd_2925991] using wordTrace_append hprefix tailTrace_2925991
  have hstable : (prefixWord ++ tailWord_2925991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925991).length < 2 ^ (prefixWord ++ tailWord_2925991).sum := by decide
  have hdescent : baseEnd_2925991 < baseStart_2925991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926002 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2926002 : Nat := 118140960795 + 2926002 * 2 ^ 59
def prefixEnd_2926002 : Nat := 4983230072969 + 3 ^ 40 * 2926002 * 2
def baseEnd_2926002 : Nat := 1001630281344644158279045

theorem tailTrace_2926002 : CollatzResearch.WordTrace tailWord_2926002 prefixEnd_2926002 1001630281344644158279045 := by
  unfold tailWord_2926002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680015086400487550465065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71146706897067966801240173 26680015086400487550465065)
  ·
    refine ⟨20010011314800365662848799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26680015086400487550465065 20010011314800365662848799)
    ·
      refine ⟨30015016972200548494273199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010011314800365662848799 30015016972200548494273199)
      ·
        refine ⟨45022525458300822741409799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30015016972200548494273199 45022525458300822741409799)
        ·
          refine ⟨67533788187451234112114699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45022525458300822741409799 67533788187451234112114699)
          ·
            refine ⟨101300682281176851168172049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67533788187451234112114699 101300682281176851168172049)
            ·
              refine ⟨75975511710882638376129037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101300682281176851168172049 75975511710882638376129037)
              ·
                refine ⟨28490816891580989391048389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75975511710882638376129037 28490816891580989391048389)
                ·
                  refine ⟨5342028167171435510821573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28490816891580989391048389 5342028167171435510821573)
                  ·
                    refine ⟨1001630281344644158279045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342028167171435510821573 1001630281344644158279045)
                    ·
                      rfl

theorem cell22_2926002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2926002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926002 prefixEnd_2926002 := by exact prefixLift 2926002
  have htrace : WordTrace (prefixWord ++ tailWord_2926002) baseStart_2926002 baseEnd_2926002 := by
    simpa [prefixWord, tailWord_2926002, baseEnd_2926002] using wordTrace_append hprefix tailTrace_2926002
  have hstable : (prefixWord ++ tailWord_2926002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926002).length < 2 ^ (prefixWord ++ tailWord_2926002).sum := by decide
  have hdescent : baseEnd_2926002 < baseStart_2926002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926066 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2926066 : Nat := 118140960795 + 2926066 * 2 ^ 59
def prefixEnd_2926066 : Nat := 4983230072969 + 3 ^ 40 * 2926066 * 2
def baseEnd_2926066 : Nat := 1001652189852569324678849

theorem tailTrace_2926066 : CollatzResearch.WordTrace tailWord_2926066 prefixEnd_2926066 1001652189852569324678849 := by
  unfold tailWord_2926066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680598654342522283047513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71148263078246726088126701 26680598654342522283047513)
  ·
    refine ⟨20010448990756891712285635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26680598654342522283047513 20010448990756891712285635)
    ·
      refine ⟨30015673486135337568428453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010448990756891712285635 30015673486135337568428453)
      ·
        refine ⟨5627938778650375794080335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30015673486135337568428453 5627938778650375794080335)
        ·
          refine ⟨8441908167975563691120503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627938778650375794080335 8441908167975563691120503)
          ·
            refine ⟨12662862251963345536680755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441908167975563691120503 12662862251963345536680755)
            ·
              refine ⟨18994293377945018305021133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12662862251963345536680755 18994293377945018305021133)
              ·
                refine ⟨7122860016729381864382925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18994293377945018305021133 7122860016729381864382925)
                ·
                  refine ⟨2671072506273518199143597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7122860016729381864382925 2671072506273518199143597)
                  ·
                    refine ⟨1001652189852569324678849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671072506273518199143597 1001652189852569324678849)
                    ·
                      rfl

theorem cell22_2926066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2926066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926066 prefixEnd_2926066 := by exact prefixLift 2926066
  have htrace : WordTrace (prefixWord ++ tailWord_2926066) baseStart_2926066 baseEnd_2926066 := by
    simpa [prefixWord, tailWord_2926066, baseEnd_2926066] using wordTrace_append hprefix tailTrace_2926066
  have hstable : (prefixWord ++ tailWord_2926066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926066).length < 2 ^ (prefixWord ++ tailWord_2926066).sum := by decide
  have hdescent : baseEnd_2926066 < baseStart_2926066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926186 : List Nat := [3, 1, 3, 2, 1, 4, 1, 7]
def baseStart_2926186 : Nat := 118140960795 + 2926186 * 2 ^ 59
def prefixEnd_2926186 : Nat := 4983230072969 + 3 ^ 40 * 2926186 * 2
def baseEnd_2926186 : Nat := 111299252033881001297609

theorem tailTrace_2926186 : CollatzResearch.WordTrace tailWord_2926186 prefixEnd_2926186 111299252033881001297609 := by
  unfold tailWord_2926186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681692844233837406639603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71151180917956899751038941 26681692844233837406639603)
  ·
    refine ⟨40022539266350756109959405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26681692844233837406639603 40022539266350756109959405)
    ·
      refine ⟨15008452224881533541234777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40022539266350756109959405 15008452224881533541234777)
      ·
        refine ⟨11256339168661150155926083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15008452224881533541234777 11256339168661150155926083)
        ·
          refine ⟨16884508752991725233889125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11256339168661150155926083 16884508752991725233889125)
          ·
            refine ⟨3165845391185948481354211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16884508752991725233889125 3165845391185948481354211)
            ·
              refine ⟨4748768086778922722031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165845391185948481354211 4748768086778922722031317)
              ·
                refine ⟨111299252033881001297609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4748768086778922722031317 111299252033881001297609)
                ·
                  rfl

theorem cell22_2926186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_2926186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926186 prefixEnd_2926186 := by exact prefixLift 2926186
  have htrace : WordTrace (prefixWord ++ tailWord_2926186) baseStart_2926186 baseEnd_2926186 := by
    simpa [prefixWord, tailWord_2926186, baseEnd_2926186] using wordTrace_append hprefix tailTrace_2926186
  have hstable : (prefixWord ++ tailWord_2926186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926186).length < 2 ^ (prefixWord ++ tailWord_2926186).sum := by decide
  have hdescent : baseEnd_2926186 < baseStart_2926186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926201 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_2926201 : Nat := 118140960795 + 2926201 * 2 ^ 59
def prefixEnd_2926201 : Nat := 4983230072969 + 3 ^ 40 * 2926201 * 2
def baseEnd_2926201 : Nat := 1001698403111473972553435

theorem tailTrace_2926201 : CollatzResearch.WordTrace tailWord_2926201 prefixEnd_2926201 1001698403111473972553435 := by
  unfold tailWord_2926201
  simp only [CollatzResearch.WordTrace]
  refine ⟨106727318471881007188354457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71151545647920671458902971 106727318471881007188354457)
  ·
    refine ⟨80045488853910755391265843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106727318471881007188354457 80045488853910755391265843)
    ·
      refine ⟨120068233280866133086898765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80045488853910755391265843 120068233280866133086898765)
      ·
        refine ⟨45025587480324799907587037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120068233280866133086898765 45025587480324799907587037)
        ·
          refine ⟨16884595305121799965345139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45025587480324799907587037 16884595305121799965345139)
          ·
            refine ⟨25326892957682699948017709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16884595305121799965345139 25326892957682699948017709)
            ·
              refine ⟨9497584859131012480506641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25326892957682699948017709 9497584859131012480506641)
              ·
                refine ⟨7123188644348259360379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497584859131012480506641 7123188644348259360379981)
                ·
                  refine ⟨2671195741630597260142493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7123188644348259360379981 2671195741630597260142493)
                  ·
                    refine ⟨1001698403111473972553435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671195741630597260142493 1001698403111473972553435)
                    ·
                      rfl

theorem cell22_2926201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_2926201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926201 prefixEnd_2926201 := by exact prefixLift 2926201
  have htrace : WordTrace (prefixWord ++ tailWord_2926201) baseStart_2926201 baseEnd_2926201 := by
    simpa [prefixWord, tailWord_2926201, baseEnd_2926201] using wordTrace_append hprefix tailTrace_2926201
  have hstable : (prefixWord ++ tailWord_2926201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926201).length < 2 ^ (prefixWord ++ tailWord_2926201).sum := by decide
  have hdescent : baseEnd_2926201 < baseStart_2926201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926231 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 5]
def baseStart_2926231 : Nat := 118140960795 + 2926231 * 2 ^ 59
def prefixEnd_2926231 : Nat := 4983230072969 + 3 ^ 40 * 2926231 * 2
def baseEnd_2926231 : Nat := 333902890908187964767781

theorem tailTrace_2926231 : CollatzResearch.WordTrace tailWord_2926231 prefixEnd_2926231 333902890908187964767781 := by
  unfold tailWord_2926231
  simp only [CollatzResearch.WordTrace]
  refine ⟨106728412661772322311946547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71152275107848214874631031 106728412661772322311946547)
  ·
    refine ⟨160092618992658483467919821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106728412661772322311946547 160092618992658483467919821)
    ·
      refine ⟨60034732122246931300469933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160092618992658483467919821 60034732122246931300469933)
      ·
        refine ⟨22513024545842599237676225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60034732122246931300469933 22513024545842599237676225)
        ·
          refine ⟨16884768409381949428257169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22513024545842599237676225 16884768409381949428257169)
          ·
            refine ⟨12663576307036462071192877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16884768409381949428257169 12663576307036462071192877)
            ·
              refine ⟨4748841115138673276697329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12663576307036462071192877 4748841115138673276697329)
              ·
                refine ⟨3561630836354004957522997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748841115138673276697329 3561630836354004957522997)
                ·
                  refine ⟨333902890908187964767781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561630836354004957522997 333902890908187964767781)
                  ·
                    rfl

theorem cell22_2926231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].length) (baseStart_2926231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926231 prefixEnd_2926231 := by exact prefixLift 2926231
  have htrace : WordTrace (prefixWord ++ tailWord_2926231) baseStart_2926231 baseEnd_2926231 := by
    simpa [prefixWord, tailWord_2926231, baseEnd_2926231] using wordTrace_append hprefix tailTrace_2926231
  have hstable : (prefixWord ++ tailWord_2926231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926231).length < 2 ^ (prefixWord ++ tailWord_2926231).sum := by decide
  have hdescent : baseEnd_2926231 < baseStart_2926231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926259 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 6]
def baseStart_2926259 : Nat := 118140960795 + 2926259 * 2 ^ 59
def prefixEnd_2926259 : Nat := 4983230072969 + 3 ^ 40 * 2926259 * 2
def baseEnd_2926259 : Nat := 333906085898927051534419

theorem tailTrace_2926259 : CollatzResearch.WordTrace tailWord_2926259 prefixEnd_2926259 333906085898927051534419 := by
  unfold tailWord_2926259
  simp only [CollatzResearch.WordTrace]
  refine ⟨106729433905670883093965831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71152955937113922062643887 106729433905670883093965831)
  ·
    refine ⟨160094150858506324640948747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106729433905670883093965831 160094150858506324640948747)
    ·
      refine ⟨240141226287759486961423121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160094150858506324640948747 240141226287759486961423121)
      ·
        refine ⟨180105919715819615221067341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240141226287759486961423121 180105919715819615221067341)
        ·
          refine ⟨67539719893432355707900253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180105919715819615221067341 67539719893432355707900253)
          ·
            refine ⟨25327394960037133390462595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67539719893432355707900253 25327394960037133390462595)
            ·
              refine ⟨37991092440055700085693893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25327394960037133390462595 37991092440055700085693893)
              ·
                refine ⟨7123329832510443766067605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37991092440055700085693893 7123329832510443766067605)
                ·
                  refine ⟨333906085898927051534419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7123329832510443766067605 333906085898927051534419)
                  ·
                    rfl

theorem cell22_2926259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_2926259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926259 prefixEnd_2926259 := by exact prefixLift 2926259
  have htrace : WordTrace (prefixWord ++ tailWord_2926259) baseStart_2926259 baseEnd_2926259 := by
    simpa [prefixWord, tailWord_2926259, baseEnd_2926259] using wordTrace_append hprefix tailTrace_2926259
  have hstable : (prefixWord ++ tailWord_2926259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926259).length < 2 ^ (prefixWord ++ tailWord_2926259).sum := by decide
  have hdescent : baseEnd_2926259 < baseStart_2926259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926304 : List Nat := [2, 1, 1, 3, 1, 2, 3, 9]
def baseStart_2926304 : Nat := 118140960795 + 2926304 * 2 ^ 59
def prefixEnd_2926304 : Nat := 4983230072969 + 3 ^ 40 * 2926304 * 2
def baseEnd_2926304 : Nat := 111303740235157337469791

theorem tailTrace_2926304 : CollatzResearch.WordTrace tailWord_2926304 prefixEnd_2926304 111303740235157337469791 := by
  unfold tailWord_2926304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53365537595253927889676983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71154050127005237186235977 53365537595253927889676983)
  ·
    refine ⟨80048306392880891834515475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53365537595253927889676983 80048306392880891834515475)
    ·
      refine ⟨120072459589321337751773213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80048306392880891834515475 120072459589321337751773213)
      ·
        refine ⟨45027172345995501656914955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120072459589321337751773213 45027172345995501656914955)
        ·
          refine ⟨67540758518993252485372433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45027172345995501656914955 67540758518993252485372433)
          ·
            refine ⟨50655568889244939364029325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67540758518993252485372433 50655568889244939364029325)
            ·
              refine ⟨18995838333466852261510997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50655568889244939364029325 18995838333466852261510997)
              ·
                refine ⟨111303740235157337469791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18995838333466852261510997 111303740235157337469791)
                ·
                  rfl

theorem cell22_2926304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_2926304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926304 prefixEnd_2926304 := by exact prefixLift 2926304
  have htrace : WordTrace (prefixWord ++ tailWord_2926304) baseStart_2926304 baseEnd_2926304 := by
    simpa [prefixWord, tailWord_2926304, baseEnd_2926304] using wordTrace_append hprefix tailTrace_2926304
  have hstable : (prefixWord ++ tailWord_2926304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926304).length < 2 ^ (prefixWord ++ tailWord_2926304).sum := by decide
  have hdescent : baseEnd_2926304 < baseStart_2926304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926308 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2926308 : Nat := 118140960795 + 2926308 * 2 ^ 59
def prefixEnd_2926308 : Nat := 4983230072969 + 3 ^ 40 * 2926308 * 2
def baseEnd_2926308 : Nat := 1001735031398161360128107

theorem tailTrace_2926308 : CollatzResearch.WordTrace tailWord_2926308 prefixEnd_2926308 1001735031398161360128107 := by
  unfold tailWord_2926308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53365610541246682231249789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71154147388328909641666385 53365610541246682231249789)
  ·
    refine ⟨20012103952967505836718671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53365610541246682231249789 20012103952967505836718671)
    ·
      refine ⟨30018155929451258755078007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20012103952967505836718671 30018155929451258755078007)
      ·
        refine ⟨45027233894176888132617011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30018155929451258755078007 45027233894176888132617011)
        ·
          refine ⟨67540850841265332198925517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45027233894176888132617011 67540850841265332198925517)
          ·
            refine ⟨25327819065474499574597069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67540850841265332198925517 25327819065474499574597069)
            ·
              refine ⟨9497932149552937340473901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25327819065474499574597069 9497932149552937340473901)
              ·
                refine ⟨3561724556082351502677713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9497932149552937340473901 3561724556082351502677713)
                ·
                  refine ⟨2671293417061763627008285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561724556082351502677713 2671293417061763627008285)
                  ·
                    refine ⟨1001735031398161360128107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671293417061763627008285 1001735031398161360128107)
                    ·
                      rfl

theorem cell22_2926308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2926308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926308 prefixEnd_2926308 := by exact prefixLift 2926308
  have htrace : WordTrace (prefixWord ++ tailWord_2926308) baseStart_2926308 baseEnd_2926308 := by
    simpa [prefixWord, tailWord_2926308, baseEnd_2926308] using wordTrace_append hprefix tailTrace_2926308
  have hstable : (prefixWord ++ tailWord_2926308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926308).length < 2 ^ (prefixWord ++ tailWord_2926308).sum := by decide
  have hdescent : baseEnd_2926308 < baseStart_2926308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926336 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_2926336 : Nat := 118140960795 + 2926336 * 2 ^ 59
def prefixEnd_2926336 : Nat := 4983230072969 + 3 ^ 40 * 2926336 * 2
def baseEnd_2926336 : Nat := 1001744616370378620428021

theorem tailTrace_2926336 : CollatzResearch.WordTrace tailWord_2926336 prefixEnd_2926336 1001744616370378620428021 := by
  unfold tailWord_2926336
  simp only [CollatzResearch.WordTrace]
  refine ⟨53366121163195962622259431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71154828217594616829679241 53366121163195962622259431)
  ·
    refine ⟨80049181744793943933389147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53366121163195962622259431 80049181744793943933389147)
    ·
      refine ⟨120073772617190915900083721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80049181744793943933389147 120073772617190915900083721)
      ·
        refine ⟨90055329462893186925062791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120073772617190915900083721 90055329462893186925062791)
        ·
          refine ⟨135082994194339780387594187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90055329462893186925062791 135082994194339780387594187)
          ·
            refine ⟨202624491291509670581391281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135082994194339780387594187 202624491291509670581391281)
            ·
              refine ⟨151968368468632252936043461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202624491291509670581391281 151968368468632252936043461)
              ·
                refine ⟨28494069087868547425508149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151968368468632252936043461 28494069087868547425508149)
                ·
                  refine ⟨2671318976987676321141389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28494069087868547425508149 2671318976987676321141389)
                  ·
                    refine ⟨1001744616370378620428021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671318976987676321141389 1001744616370378620428021)
                    ·
                      rfl

theorem cell22_2926336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_2926336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926336 prefixEnd_2926336 := by exact prefixLift 2926336
  have htrace : WordTrace (prefixWord ++ tailWord_2926336) baseStart_2926336 baseEnd_2926336 := by
    simpa [prefixWord, tailWord_2926336, baseEnd_2926336] using wordTrace_append hprefix tailTrace_2926336
  have hstable : (prefixWord ++ tailWord_2926336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926336).length < 2 ^ (prefixWord ++ tailWord_2926336).sum := by decide
  have hdescent : baseEnd_2926336 < baseStart_2926336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926387 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 1, 3]
def baseStart_2926387 : Nat := 118140960795 + 2926387 * 2 ^ 59
def prefixEnd_2926387 : Nat := 4983230072969 + 3 ^ 40 * 2926387 * 2
def baseEnd_2926387 : Nat := 1001762074712631487402865

theorem tailTrace_2926387 : CollatzResearch.WordTrace tailWord_2926387 prefixEnd_2926387 1001762074712631487402865 := by
  unfold tailWord_2926387
  simp only [CollatzResearch.WordTrace]
  refine ⟨106734102449207160954625415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71156068299471440636416943 106734102449207160954625415)
  ·
    refine ⟨160101153673810741431938123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106734102449207160954625415 160101153673810741431938123)
    ·
      refine ⟨240151730510716112147907185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160101153673810741431938123 240151730510716112147907185)
      ·
        refine ⟨180113797883037084110930389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240151730510716112147907185 180113797883037084110930389)
        ·
          refine ⟨4221417137883681658849931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 180113797883037084110930389 4221417137883681658849931)
          ·
            refine ⟨6332125706825522488274897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221417137883681658849931 6332125706825522488274897)
            ·
              refine ⟨4749094280119141866206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332125706825522488274897 4749094280119141866206173)
              ·
                refine ⟨1780910355044678199827315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4749094280119141866206173 1780910355044678199827315)
                ·
                  refine ⟨2671365532567017299740973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780910355044678199827315 2671365532567017299740973)
                  ·
                    refine ⟨1001762074712631487402865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671365532567017299740973 1001762074712631487402865)
                    ·
                      rfl

theorem cell22_2926387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 3].length) (baseStart_2926387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926387 prefixEnd_2926387 := by exact prefixLift 2926387
  have htrace : WordTrace (prefixWord ++ tailWord_2926387) baseStart_2926387 baseEnd_2926387 := by
    simpa [prefixWord, tailWord_2926387, baseEnd_2926387] using wordTrace_append hprefix tailTrace_2926387
  have hstable : (prefixWord ++ tailWord_2926387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926387).length < 2 ^ (prefixWord ++ tailWord_2926387).sum := by decide
  have hdescent : baseEnd_2926387 < baseStart_2926387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926398 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2926398 : Nat := 118140960795 + 2926398 * 2 ^ 59
def prefixEnd_2926398 : Nat := 4983230072969 + 3 ^ 40 * 2926398 * 2
def baseEnd_2926398 : Nat := 1001765840237431125377831

theorem tailTrace_2926398 : CollatzResearch.WordTrace tailWord_2926398 prefixEnd_2926398 1001765840237431125377831 := by
  unfold tailWord_2926398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341812956520913729159481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71156335768111539888850565 13341812956520913729159481)
  ·
    refine ⟨10006359717390685296869611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13341812956520913729159481 10006359717390685296869611)
    ·
      refine ⟨15009539576086027945304417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006359717390685296869611 15009539576086027945304417)
      ·
        refine ⟨11257154682064520958978313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15009539576086027945304417 11257154682064520958978313)
        ·
          refine ⟨8442866011548390719233735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11257154682064520958978313 8442866011548390719233735)
          ·
            refine ⟨12664299017322586078850603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442866011548390719233735 12664299017322586078850603)
            ·
              refine ⟨18996448525983879118275905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664299017322586078850603 18996448525983879118275905)
              ·
                refine ⟨14247336394487909338706929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18996448525983879118275905 14247336394487909338706929)
                ·
                  refine ⟨10685502295865932004030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14247336394487909338706929 10685502295865932004030197)
                  ·
                    refine ⟨1001765840237431125377831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10685502295865932004030197 1001765840237431125377831)
                    ·
                      rfl

theorem cell22_2926398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2926398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926398 prefixEnd_2926398 := by exact prefixLift 2926398
  have htrace : WordTrace (prefixWord ++ tailWord_2926398) baseStart_2926398 baseEnd_2926398 := by
    simpa [prefixWord, tailWord_2926398, baseEnd_2926398] using wordTrace_append hprefix tailTrace_2926398
  have hstable : (prefixWord ++ tailWord_2926398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926398).length < 2 ^ (prefixWord ++ tailWord_2926398).sum := by decide
  have hdescent : baseEnd_2926398 < baseStart_2926398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_2926441 : Nat := 118140960795 + 2926441 * 2 ^ 59
def prefixEnd_2926441 : Nat := 4983230072969 + 3 ^ 40 * 2926441 * 2
def baseEnd_2926441 : Nat := 1001780560016193346552699

theorem tailTrace_2926441 : CollatzResearch.WordTrace tailWord_2926441 prefixEnd_2926441 1001780560016193346552699 := by
  unfold tailWord_2926441
  simp only [CollatzResearch.WordTrace]
  refine ⟨106736071991011528177091177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71157381327341018784727451 106736071991011528177091177)
  ·
    refine ⟨80052053993258646132818383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106736071991011528177091177 80052053993258646132818383)
    ·
      refine ⟨120078080989887969199227575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80052053993258646132818383 120078080989887969199227575)
      ·
        refine ⟨180117121484831953798841363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120078080989887969199227575 180117121484831953798841363)
        ·
          refine ⟨270175682227247930698262045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180117121484831953798841363 270175682227247930698262045)
          ·
            refine ⟨101315880835217974011848267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270175682227247930698262045 101315880835217974011848267)
            ·
              refine ⟨151973821252826961017772401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101315880835217974011848267 151973821252826961017772401)
              ·
                refine ⟨113980365939620220763329301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151973821252826961017772401 113980365939620220763329301)
                ·
                  refine ⟨5342829653419697848281061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113980365939620220763329301 5342829653419697848281061)
                  ·
                    refine ⟨1001780560016193346552699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342829653419697848281061 1001780560016193346552699)
                    ·
                      rfl

theorem cell22_2926441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_2926441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926441 prefixEnd_2926441 := by exact prefixLift 2926441
  have htrace : WordTrace (prefixWord ++ tailWord_2926441) baseStart_2926441 baseEnd_2926441 := by
    simpa [prefixWord, tailWord_2926441, baseEnd_2926441] using wordTrace_append hprefix tailTrace_2926441
  have hstable : (prefixWord ++ tailWord_2926441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926441).length < 2 ^ (prefixWord ++ tailWord_2926441).sum := by decide
  have hdescent : baseEnd_2926441 < baseStart_2926441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926445 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2926445 : Nat := 118140960795 + 2926445 * 2 ^ 59
def prefixEnd_2926445 : Nat := 4983230072969 + 3 ^ 40 * 2926445 * 2
def baseEnd_2926445 : Nat := 333927309765979556484229

theorem tailTrace_2926445 : CollatzResearch.WordTrace tailWord_2926445 prefixEnd_2926445 333927309765979556484229 := by
  unfold tailWord_2926445
  simp only [CollatzResearch.WordTrace]
  refine ⟨106736217882997036860236789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71157478588664691240157859 106736217882997036860236789)
  ·
    refine ⟨10006520426530972205647199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106736217882997036860236789 10006520426530972205647199)
    ·
      refine ⟨15009780639796458308470799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006520426530972205647199 15009780639796458308470799)
      ·
        refine ⟨22514670959694687462706199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15009780639796458308470799 22514670959694687462706199)
        ·
          refine ⟨33772006439542031194059299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22514670959694687462706199 33772006439542031194059299)
          ·
            refine ⟨50658009659313046791088949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33772006439542031194059299 50658009659313046791088949)
            ·
              refine ⟨4749188405560598136664589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50658009659313046791088949 4749188405560598136664589)
              ·
                refine ⟨1780945652085224301249221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4749188405560598136664589 1780945652085224301249221)
                ·
                  refine ⟨333927309765979556484229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780945652085224301249221 333927309765979556484229)
                  ·
                    rfl

theorem cell22_2926445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2926445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926445 prefixEnd_2926445 := by exact prefixLift 2926445
  have htrace : WordTrace (prefixWord ++ tailWord_2926445) baseStart_2926445 baseEnd_2926445 := by
    simpa [prefixWord, tailWord_2926445, baseEnd_2926445] using wordTrace_append hprefix tailTrace_2926445
  have hstable : (prefixWord ++ tailWord_2926445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926445).length < 2 ^ (prefixWord ++ tailWord_2926445).sum := by decide
  have hdescent : baseEnd_2926445 < baseStart_2926445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926462 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2926462 : Nat := 118140960795 + 2926462 * 2 ^ 59
def prefixEnd_2926462 : Nat := 4983230072969 + 3 ^ 40 * 2926462 * 2
def baseEnd_2926462 : Nat := 333929249581785430592545

theorem tailTrace_2926462 : CollatzResearch.WordTrace tailWord_2926462 prefixEnd_2926462 333929249581785430592545 := by
  unfold tailWord_2926462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342104740491931095450705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71157891949290299175737093 13342104740491931095450705)
  ·
    refine ⟨10006578555368948321588029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13342104740491931095450705 10006578555368948321588029)
    ·
      refine ⟨3752466958263355620595511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10006578555368948321588029 3752466958263355620595511)
      ·
        refine ⟨5628700437395033430893267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752466958263355620595511 5628700437395033430893267)
        ·
          refine ⟨8443050656092550146339901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628700437395033430893267 8443050656092550146339901)
          ·
            refine ⟨3166143996034706304877463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8443050656092550146339901 3166143996034706304877463)
            ·
              refine ⟨4749215994052059457316195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166143996034706304877463 4749215994052059457316195)
              ·
                refine ⟨7123823991078089185974293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749215994052059457316195 7123823991078089185974293)
                ·
                  refine ⟨333929249581785430592545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7123823991078089185974293 333929249581785430592545)
                  ·
                    rfl

theorem cell22_2926462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2926462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926462 prefixEnd_2926462 := by exact prefixLift 2926462
  have htrace : WordTrace (prefixWord ++ tailWord_2926462) baseStart_2926462 baseEnd_2926462 := by
    simpa [prefixWord, tailWord_2926462, baseEnd_2926462] using wordTrace_append hprefix tailTrace_2926462
  have hstable : (prefixWord ++ tailWord_2926462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926462).length < 2 ^ (prefixWord ++ tailWord_2926462).sum := by decide
  have hdescent : baseEnd_2926462 < baseStart_2926462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926501 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2926501 : Nat := 118140960795 + 2926501 * 2 ^ 59
def prefixEnd_2926501 : Nat := 4983230072969 + 3 ^ 40 * 2926501 * 2
def baseEnd_2926501 : Nat := 333933699747457730017505

theorem tailTrace_2926501 : CollatzResearch.WordTrace tailWord_2926501 prefixEnd_2926501 333933699747457730017505 := by
  unfold tailWord_2926501
  simp only [CollatzResearch.WordTrace]
  refine ⟨106738260370794158424275357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71158840247196105616183571 106738260370794158424275357)
  ·
    refine ⟨40026847639047809409103259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106738260370794158424275357 40026847639047809409103259)
    ·
      refine ⟨60040271458571714113654889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40026847639047809409103259 60040271458571714113654889)
      ·
        refine ⟨45030203593928785585241167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60040271458571714113654889 45030203593928785585241167)
        ·
          refine ⟨67545305390893178377861751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45030203593928785585241167 67545305390893178377861751)
          ·
            refine ⟨101317958086339767566792627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67545305390893178377861751 101317958086339767566792627)
            ·
              refine ⟨151976937129509651350188941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101317958086339767566792627 151976937129509651350188941)
              ·
                refine ⟨56991351423566119256320853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151976937129509651350188941 56991351423566119256320853)
                ·
                  refine ⟨333933699747457730017505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56991351423566119256320853 333933699747457730017505)
                  ·
                    rfl

theorem cell22_2926501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2926501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926501 prefixEnd_2926501 := by exact prefixLift 2926501
  have htrace : WordTrace (prefixWord ++ tailWord_2926501) baseStart_2926501 baseEnd_2926501 := by
    simpa [prefixWord, tailWord_2926501, baseEnd_2926501] using wordTrace_append hprefix tailTrace_2926501
  have hstable : (prefixWord ++ tailWord_2926501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926501).length < 2 ^ (prefixWord ++ tailWord_2926501).sum := by decide
  have hdescent : baseEnd_2926501 < baseStart_2926501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926531 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_2926531 : Nat := 118140960795 + 2926531 * 2 ^ 59
def prefixEnd_2926531 : Nat := 4983230072969 + 3 ^ 40 * 2926531 * 2
def baseEnd_2926531 : Nat := 1001811368855463111802423

theorem tailTrace_2926531 : CollatzResearch.WordTrace tailWord_2926531 prefixEnd_2926531 1001811368855463111802423 := by
  unfold tailWord_2926531
  simp only [CollatzResearch.WordTrace]
  refine ⟨106739354560685473547867447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71159569707123649031911631 106739354560685473547867447)
  ·
    refine ⟨160109031841028210321801171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106739354560685473547867447 160109031841028210321801171)
    ·
      refine ⟨240163547761542315482701757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160109031841028210321801171 240163547761542315482701757)
      ·
        refine ⟨90061330410578368306013159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240163547761542315482701757 90061330410578368306013159)
        ·
          refine ⟨135091995615867552459019739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90061330410578368306013159 135091995615867552459019739)
          ·
            refine ⟨202637993423801328688529609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135091995615867552459019739 202637993423801328688529609)
            ·
              refine ⟨151978495067850996516397207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202637993423801328688529609 151978495067850996516397207)
              ·
                refine ⟨227967742601776494774595811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151978495067850996516397207 227967742601776494774595811)
                ·
                  refine ⟨341951613902664742161893717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227967742601776494774595811 341951613902664742161893717)
                  ·
                    refine ⟨1001811368855463111802423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 341951613902664742161893717 1001811368855463111802423)
                    ·
                      rfl

theorem cell22_2926531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_2926531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926531 prefixEnd_2926531 := by exact prefixLift 2926531
  have htrace : WordTrace (prefixWord ++ tailWord_2926531) baseStart_2926531 baseEnd_2926531 := by
    simpa [prefixWord, tailWord_2926531, baseEnd_2926531] using wordTrace_append hprefix tailTrace_2926531
  have hstable : (prefixWord ++ tailWord_2926531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926531).length < 2 ^ (prefixWord ++ tailWord_2926531).sum := by decide
  have hdescent : baseEnd_2926531 < baseStart_2926531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926593 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2926593 : Nat := 118140960795 + 2926593 * 2 ^ 59
def prefixEnd_2926593 : Nat := 4983230072969 + 3 ^ 40 * 2926593 * 2
def baseEnd_2926593 : Nat := 1001832592722515616752233

theorem tailTrace_2926593 : CollatzResearch.WordTrace tailWord_2926593 prefixEnd_2926593 1001832592722515616752233 := by
  unfold tailWord_2926593
  simp only [CollatzResearch.WordTrace]
  refine ⟨106741615886460858136624433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71161077257640572091082955 106741615886460858136624433)
  ·
    refine ⟨80056211914845643602468325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106741615886460858136624433 80056211914845643602468325)
    ·
      refine ⟨15010539734033558175462811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80056211914845643602468325 15010539734033558175462811)
      ·
        refine ⟨22515809601050337263194217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010539734033558175462811 22515809601050337263194217)
        ·
          refine ⟨16886857200787752947395663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22515809601050337263194217 16886857200787752947395663)
          ·
            refine ⟨25330285801181629421093495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16886857200787752947395663 25330285801181629421093495)
            ·
              refine ⟨37995428701772444131640243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25330285801181629421093495 37995428701772444131640243)
              ·
                refine ⟨56993143052658666197460365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37995428701772444131640243 56993143052658666197460365)
                ·
                  refine ⟨21372428644746999824047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56993143052658666197460365 21372428644746999824047637)
                  ·
                    refine ⟨1001832592722515616752233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21372428644746999824047637 1001832592722515616752233)
                    ·
                      rfl

theorem cell22_2926593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2926593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926593 prefixEnd_2926593 := by exact prefixLift 2926593
  have htrace : WordTrace (prefixWord ++ tailWord_2926593) baseStart_2926593 baseEnd_2926593 := by
    simpa [prefixWord, tailWord_2926593, baseEnd_2926593] using wordTrace_append hprefix tailTrace_2926593
  have hstable : (prefixWord ++ tailWord_2926593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926593).length < 2 ^ (prefixWord ++ tailWord_2926593).sum := by decide
  have hdescent : baseEnd_2926593 < baseStart_2926593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926595 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 2, 3]
def baseStart_2926595 : Nat := 118140960795 + 2926595 * 2 ^ 59
def prefixEnd_2926595 : Nat := 4983230072969 + 3 ^ 40 * 2926595 * 2
def baseEnd_2926595 : Nat := 1001833277363388278202227

theorem tailTrace_2926595 : CollatzResearch.WordTrace tailWord_2926595 prefixEnd_2926595 1001833277363388278202227 := by
  unfold tailWord_2926595
  simp only [CollatzResearch.WordTrace]
  refine ⟨106741688832453612478197239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71161125888302408318798159 106741688832453612478197239)
  ·
    refine ⟨160112533248680418717295859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106741688832453612478197239 160112533248680418717295859)
    ·
      refine ⟨240168799873020628075943789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160112533248680418717295859 240168799873020628075943789)
      ·
        refine ⟨90063299952382735528478921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240168799873020628075943789 90063299952382735528478921)
        ·
          refine ⟨67547474964287051646359191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90063299952382735528478921 67547474964287051646359191)
          ·
            refine ⟨101321212446430577469538787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67547474964287051646359191 101321212446430577469538787)
            ·
              refine ⟨151981818669645866204308181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101321212446430577469538787 151981818669645866204308181)
              ·
                refine ⟨3562073875069824989163473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151981818669645866204308181 3562073875069824989163473)
                ·
                  refine ⟨2671555406302368741872605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562073875069824989163473 2671555406302368741872605)
                  ·
                    refine ⟨1001833277363388278202227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671555406302368741872605 1001833277363388278202227)
                    ·
                      rfl

theorem cell22_2926595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].length) (baseStart_2926595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926595 prefixEnd_2926595 := by exact prefixLift 2926595
  have htrace : WordTrace (prefixWord ++ tailWord_2926595) baseStart_2926595 baseEnd_2926595 := by
    simpa [prefixWord, tailWord_2926595, baseEnd_2926595] using wordTrace_append hprefix tailTrace_2926595
  have hstable : (prefixWord ++ tailWord_2926595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926595).length < 2 ^ (prefixWord ++ tailWord_2926595).sum := by decide
  have hdescent : baseEnd_2926595 < baseStart_2926595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926625 : List Nat := [1, 2, 3, 2, 4, 2, 8]
def baseStart_2926625 : Nat := 118140960795 + 2926625 * 2 ^ 59
def prefixEnd_2926625 : Nat := 4983230072969 + 3 ^ 40 * 2926625 * 2
def baseEnd_2926625 : Nat := 37105316554684377776005

theorem tailTrace_2926625 : CollatzResearch.WordTrace tailWord_2926625 prefixEnd_2926625 37105316554684377776005 := by
  unfold tailWord_2926625
  simp only [CollatzResearch.WordTrace]
  refine ⟨106742783022344927601789329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71161855348229951734526219 106742783022344927601789329)
  ·
    refine ⟨80057087266758695701341997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106742783022344927601789329 80057087266758695701341997)
    ·
      refine ⟨30021407725034510888003249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80057087266758695701341997 30021407725034510888003249)
      ·
        refine ⟨22516055793775883166002437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30021407725034510888003249 22516055793775883166002437)
        ·
          refine ⟨4221760461332978093625457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22516055793775883166002437 4221760461332978093625457)
          ·
            refine ⟨3166320345999733570219093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4221760461332978093625457 3166320345999733570219093)
            ·
              refine ⟨37105316554684377776005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3166320345999733570219093 37105316554684377776005)
              ·
                rfl

theorem cell22_2926625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 8].length) (baseStart_2926625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926625 prefixEnd_2926625 := by exact prefixLift 2926625
  have htrace : WordTrace (prefixWord ++ tailWord_2926625) baseStart_2926625 baseEnd_2926625 := by
    simpa [prefixWord, tailWord_2926625, baseEnd_2926625] using wordTrace_append hprefix tailTrace_2926625
  have hstable : (prefixWord ++ tailWord_2926625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926625).length < 2 ^ (prefixWord ++ tailWord_2926625).sum := by decide
  have hdescent : baseEnd_2926625 < baseStart_2926625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926631 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 4]
def baseStart_2926631 : Nat := 118140960795 + 2926631 * 2 ^ 59
def prefixEnd_2926631 : Nat := 4983230072969 + 3 ^ 40 * 2926631 * 2
def baseEnd_2926631 : Nat := 333948533633032061434039

theorem tailTrace_2926631 : CollatzResearch.WordTrace tailWord_2926631 prefixEnd_2926631 333948533633032061434039 := by
  unfold tailWord_2926631
  simp only [CollatzResearch.WordTrace]
  refine ⟨106743001860323190626507747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71162001240215460417671831 106743001860323190626507747)
  ·
    refine ⟨160114502790484785939761621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106743001860323190626507747 160114502790484785939761621)
    ·
      refine ⟨3752683659151987170463163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160114502790484785939761621 3752683659151987170463163)
      ·
        refine ⟨5629025488727980755694745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752683659151987170463163 5629025488727980755694745)
        ·
          refine ⟨4221769116545985566771059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629025488727980755694745 4221769116545985566771059)
          ·
            refine ⟨6332653674818978350156589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221769116545985566771059 6332653674818978350156589)
            ·
              refine ⟨2374745128057116881308721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6332653674818978350156589 2374745128057116881308721)
              ·
                refine ⟨1781058846042837660981541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374745128057116881308721 1781058846042837660981541)
                ·
                  refine ⟨333948533633032061434039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781058846042837660981541 333948533633032061434039)
                  ·
                    rfl

theorem cell22_2926631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 4].length) (baseStart_2926631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926631 prefixEnd_2926631 := by exact prefixLift 2926631
  have htrace : WordTrace (prefixWord ++ tailWord_2926631) baseStart_2926631 baseEnd_2926631 := by
    simpa [prefixWord, tailWord_2926631, baseEnd_2926631] using wordTrace_append hprefix tailTrace_2926631
  have hstable : (prefixWord ++ tailWord_2926631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926631).length < 2 ^ (prefixWord ++ tailWord_2926631).sum := by decide
  have hdescent : baseEnd_2926631 < baseStart_2926631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926700 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_2926700 : Nat := 118140960795 + 2926700 * 2 ^ 59
def prefixEnd_2926700 : Nat := 4983230072969 + 3 ^ 40 * 2926700 * 2
def baseEnd_2926700 : Nat := 1001869221009203004326905

theorem tailTrace_2926700 : CollatzResearch.WordTrace tailWord_2926700 prefixEnd_2926700 1001869221009203004326905 := by
  unfold tailWord_2926700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372759248536607705384777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71163678998048810273846369 53372759248536607705384777)
  ·
    refine ⟨40029569436402455779038583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53372759248536607705384777 40029569436402455779038583)
    ·
      refine ⟨60044354154603683668557875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40029569436402455779038583 60044354154603683668557875)
      ·
        refine ⟨90066531231905525502836813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60044354154603683668557875 90066531231905525502836813)
        ·
          refine ⟨33774949211964572063563805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90066531231905525502836813 33774949211964572063563805)
          ·
            refine ⟨12665605954486714523836427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33774949211964572063563805 12665605954486714523836427)
            ·
              refine ⟨18998408931730071785754641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12665605954486714523836427 18998408931730071785754641)
              ·
                refine ⟨14248806698797553839315981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18998408931730071785754641 14248806698797553839315981)
                ·
                  refine ⟨5343302512049082689743493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14248806698797553839315981 5343302512049082689743493)
                  ·
                    refine ⟨1001869221009203004326905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5343302512049082689743493 1001869221009203004326905)
                    ·
                      rfl

theorem cell22_2926700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_2926700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926700 prefixEnd_2926700 := by exact prefixLift 2926700
  have htrace : WordTrace (prefixWord ++ tailWord_2926700) baseStart_2926700 baseEnd_2926700 := by
    simpa [prefixWord, tailWord_2926700, baseEnd_2926700] using wordTrace_append hprefix tailTrace_2926700
  have hstable : (prefixWord ++ tailWord_2926700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926700).length < 2 ^ (prefixWord ++ tailWord_2926700).sum := by decide
  have hdescent : baseEnd_2926700 < baseStart_2926700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926734 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2926734 : Nat := 118140960795 + 2926734 * 2 ^ 59
def prefixEnd_2926734 : Nat := 4983230072969 + 3 ^ 40 * 2926734 * 2
def baseEnd_2926734 : Nat := 1001880859904038248976801

theorem tailTrace_2926734 : CollatzResearch.WordTrace tailWord_2926734 prefixEnd_2926734 1001880859904038248976801 := by
  unfold tailWord_2926734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343344822368754902188407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71164505719300026145004837 13343344822368754902188407)
  ·
    refine ⟨20015017233553132353282611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13343344822368754902188407 20015017233553132353282611)
    ·
      refine ⟨30022525850329698529923917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20015017233553132353282611 30022525850329698529923917)
      ·
        refine ⟨11258447193873636948721469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30022525850329698529923917 11258447193873636948721469)
        ·
          refine ⟨4221917697702613855770551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11258447193873636948721469 4221917697702613855770551)
          ·
            refine ⟨6332876546553920783655827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221917697702613855770551 6332876546553920783655827)
            ·
              refine ⟨9499314819830881175483741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332876546553920783655827 9499314819830881175483741)
              ·
                refine ⟨3562243057436580440806403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9499314819830881175483741 3562243057436580440806403)
                ·
                  refine ⟨5343364586154870661209605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562243057436580440806403 5343364586154870661209605)
                  ·
                    refine ⟨1001880859904038248976801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5343364586154870661209605 1001880859904038248976801)
                    ·
                      rfl

theorem cell22_2926734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2926734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926734 prefixEnd_2926734 := by exact prefixLift 2926734
  have htrace : WordTrace (prefixWord ++ tailWord_2926734) baseStart_2926734 baseEnd_2926734 := by
    simpa [prefixWord, tailWord_2926734, baseEnd_2926734] using wordTrace_append hprefix tailTrace_2926734
  have hstable : (prefixWord ++ tailWord_2926734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926734).length < 2 ^ (prefixWord ++ tailWord_2926734).sum := by decide
  have hdescent : baseEnd_2926734 < baseStart_2926734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926745 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_2926745 : Nat := 118140960795 + 2926745 * 2 ^ 59
def prefixEnd_2926745 : Nat := 4983230072969 + 3 ^ 40 * 2926745 * 2
def baseEnd_2926745 : Nat := 1001884625428837886951767

theorem tailTrace_2926745 : CollatzResearch.WordTrace tailWord_2926745 prefixEnd_2926745 1001884625428837886951767 := by
  unfold tailWord_2926745
  simp only [CollatzResearch.WordTrace]
  refine ⟨106747159781910188096157689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71164773187940125397438459 106747159781910188096157689)
  ·
    refine ⟨80060369836432641072118267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106747159781910188096157689 80060369836432641072118267)
    ·
      refine ⟨120090554754648961608177401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80060369836432641072118267 120090554754648961608177401)
      ·
        refine ⟨90067916065986721206133051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120090554754648961608177401 90067916065986721206133051)
        ·
          refine ⟨135101874098980081809199577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90067916065986721206133051 135101874098980081809199577)
          ·
            refine ⟨101326405574235061356899683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135101874098980081809199577 101326405574235061356899683)
            ·
              refine ⟨151989608361352592035349525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101326405574235061356899683 151989608361352592035349525)
              ·
                refine ⟨7124512891938402751657009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151989608361352592035349525 7124512891938402751657009)
                ·
                  refine ⟨5343384668953802063742757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7124512891938402751657009 5343384668953802063742757)
                  ·
                    refine ⟨1001884625428837886951767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5343384668953802063742757 1001884625428837886951767)
                    ·
                      rfl

theorem cell22_2926745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_2926745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926745 prefixEnd_2926745 := by exact prefixLift 2926745
  have htrace : WordTrace (prefixWord ++ tailWord_2926745) baseStart_2926745 baseEnd_2926745 := by
    simpa [prefixWord, tailWord_2926745, baseEnd_2926745] using wordTrace_append hprefix tailTrace_2926745
  have hstable : (prefixWord ++ tailWord_2926745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926745).length < 2 ^ (prefixWord ++ tailWord_2926745).sum := by decide
  have hdescent : baseEnd_2926745 < baseStart_2926745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
