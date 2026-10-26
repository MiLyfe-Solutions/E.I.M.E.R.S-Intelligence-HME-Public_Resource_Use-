import V185TrunkScan23Chunk0842

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4989036 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 6]
def baseStart_4989036 : Nat := 118140960795 + 4989036 * 2 ^ 59
def prefixEnd_4989036 : Nat := 4983230072969 + 3 ^ 40 * 4989036 * 2
def baseEnd_4989036 : Nat := 284641496731627511933983

theorem tailTrace_4989036 : CollatzResearch.WordTrace tailWord_4989036 prefixEnd_4989036 284641496731627511933983 := by
  unfold tailWord_4989036
  simp only [CollatzResearch.WordTrace]
  refine ⟨90982545976791053178993481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121310061302388070905324641 90982545976791053178993481)
  ·
    refine ⟨68236909482593289884245111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90982545976791053178993481 68236909482593289884245111)
    ·
      refine ⟨102355364223889934826367667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68236909482593289884245111 102355364223889934826367667)
      ·
        refine ⟨153533046335834902239551501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102355364223889934826367667 153533046335834902239551501)
        ·
          refine ⟨57574892375938088339831813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153533046335834902239551501 57574892375938088339831813)
          ·
            refine ⟨10795292320488391563718465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57574892375938088339831813 10795292320488391563718465)
            ·
              refine ⟨8096469240366293672788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10795292320488391563718465 8096469240366293672788849)
              ·
                refine ⟨6072351930274720254591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096469240366293672788849 6072351930274720254591637)
                ·
                  refine ⟨284641496731627511933983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6072351930274720254591637 284641496731627511933983)
                  ·
                    rfl

theorem cell23_4989036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_4989036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989036 prefixEnd_4989036 := by exact prefixLift 4989036
  have htrace : WordTrace (prefixWord ++ tailWord_4989036) baseStart_4989036 baseEnd_4989036 := by
    simpa [prefixWord, tailWord_4989036, baseEnd_4989036] using wordTrace_append hprefix tailTrace_4989036
  have hstable : (prefixWord ++ tailWord_4989036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989036).length < 2 ^ (prefixWord ++ tailWord_4989036).sum := by decide
  have hdescent : baseEnd_4989036 < baseStart_4989036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989040 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 1, 4]
def baseStart_4989040 : Nat := 118140960795 + 4989040 * 2 ^ 59
def prefixEnd_4989040 : Nat := 4983230072969 + 3 ^ 40 * 4989040 * 2
def baseEnd_4989040 : Nat := 853925174835755197251943

theorem tailTrace_4989040 : CollatzResearch.WordTrace tailWord_4989040 prefixEnd_4989040 853925174835755197251943 := by
  unfold tailWord_4989040
  simp only [CollatzResearch.WordTrace]
  refine ⟨90982618922783807520566287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121310158563711743360755049 90982618922783807520566287)
  ·
    refine ⟨136473928384175711280849431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90982618922783807520566287 136473928384175711280849431)
    ·
      refine ⟨204710892576263566921274147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136473928384175711280849431 204710892576263566921274147)
      ·
        refine ⟨307066338864395350381911221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204710892576263566921274147 307066338864395350381911221)
        ·
          refine ⟨28787469268537064098304177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307066338864395350381911221 28787469268537064098304177)
          ·
            refine ⟨21590601951402798073728133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28787469268537064098304177 21590601951402798073728133)
            ·
              refine ⟨4048237865888024638824025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21590601951402798073728133 4048237865888024638824025)
              ·
                refine ⟨3036178399416018479118019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048237865888024638824025 3036178399416018479118019)
                ·
                  refine ⟨4554267599124027718677029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036178399416018479118019 4554267599124027718677029)
                  ·
                    refine ⟨853925174835755197251943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4554267599124027718677029 853925174835755197251943)
                    ·
                      rfl

theorem cell23_4989040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_4989040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989040 prefixEnd_4989040 := by exact prefixLift 4989040
  have htrace : WordTrace (prefixWord ++ tailWord_4989040) baseStart_4989040 baseEnd_4989040 := by
    simpa [prefixWord, tailWord_4989040, baseEnd_4989040] using wordTrace_append hprefix tailTrace_4989040
  have hstable : (prefixWord ++ tailWord_4989040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989040).length < 2 ^ (prefixWord ++ tailWord_4989040).sum := by decide
  have hdescent : baseEnd_4989040 < baseStart_4989040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989056 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2]
def baseStart_4989056 : Nat := 118140960795 + 4989056 * 2 ^ 59
def prefixEnd_4989056 : Nat := 4983230072969 + 3 ^ 40 * 4989056 * 2
def baseEnd_4989056 : Nat := 2561783740197737529155755

theorem tailTrace_4989056 : CollatzResearch.WordTrace tailWord_4989056 prefixEnd_4989056 2561783740197737529155755 := by
  unfold tailWord_4989056
  simp only [CollatzResearch.WordTrace]
  refine ⟨90982910706754824886857511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121310547609006433182476681 90982910706754824886857511)
  ·
    refine ⟨136474366060132237330286267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90982910706754824886857511 136474366060132237330286267)
    ·
      refine ⟨204711549090198355995429401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136474366060132237330286267 204711549090198355995429401)
      ·
        refine ⟨153533661817648766996572051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204711549090198355995429401 153533661817648766996572051)
        ·
          refine ⟨230300492726473150494858077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153533661817648766996572051 230300492726473150494858077)
          ·
            refine ⟨86362684772427431435571779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230300492726473150494858077 86362684772427431435571779)
            ·
              refine ⟨129544027158641147153357669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86362684772427431435571779 129544027158641147153357669)
              ·
                refine ⟨24289505092245215091254563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129544027158641147153357669 24289505092245215091254563)
                ·
                  refine ⟨36434257638367822636881845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24289505092245215091254563 36434257638367822636881845)
                  ·
                    refine ⟨3415711653596983372207673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36434257638367822636881845 3415711653596983372207673)
                    ·
                      refine ⟨2561783740197737529155755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415711653596983372207673 2561783740197737529155755)
                      ·
                        rfl

theorem cell23_4989056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_4989056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989056 prefixEnd_4989056 := by exact prefixLift 4989056
  have htrace : WordTrace (prefixWord ++ tailWord_4989056) baseStart_4989056 baseEnd_4989056 := by
    simpa [prefixWord, tailWord_4989056, baseEnd_4989056] using wordTrace_append hprefix tailTrace_4989056
  have hstable : (prefixWord ++ tailWord_4989056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989056).length < 2 ^ (prefixWord ++ tailWord_4989056).sum := by decide
  have hdescent : baseEnd_4989056 < baseStart_4989056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989066 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_4989066 : Nat := 118140960795 + 4989066 * 2 ^ 59
def prefixEnd_4989066 : Nat := 4983230072969 + 3 ^ 40 * 4989066 * 2
def baseEnd_4989066 : Nat := 853929625001427496676903

theorem tailTrace_4989066 : CollatzResearch.WordTrace tailWord_4989066 prefixEnd_4989066 853929625001427496676903 := by
  unfold tailWord_4989066
  simp only [CollatzResearch.WordTrace]
  refine ⟨45491546535868355370394763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121310790762315614321052701 45491546535868355370394763)
  ·
    refine ⟨68237319803802533055592145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45491546535868355370394763 68237319803802533055592145)
    ·
      refine ⟨51177989852851899791694109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68237319803802533055592145 51177989852851899791694109)
      ·
        refine ⟨19191746194819462421885291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51177989852851899791694109 19191746194819462421885291)
        ·
          refine ⟨28787619292229193632827937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19191746194819462421885291 28787619292229193632827937)
          ·
            refine ⟨21590714469171895224620953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28787619292229193632827937 21590714469171895224620953)
            ·
              refine ⟨16193035851878921418465715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21590714469171895224620953 16193035851878921418465715)
              ·
                refine ⟨24289553777818382127698573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16193035851878921418465715 24289553777818382127698573)
                ·
                  refine ⟨9108582666681893297886965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24289553777818382127698573 9108582666681893297886965)
                  ·
                    refine ⟨853929625001427496676903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9108582666681893297886965 853929625001427496676903)
                    ·
                      rfl

theorem cell23_4989066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_4989066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989066 prefixEnd_4989066 := by exact prefixLift 4989066
  have htrace : WordTrace (prefixWord ++ tailWord_4989066) baseStart_4989066 baseEnd_4989066 := by
    simpa [prefixWord, tailWord_4989066, baseEnd_4989066] using wordTrace_append hprefix tailTrace_4989066
  have hstable : (prefixWord ++ tailWord_4989066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989066).length < 2 ^ (prefixWord ++ tailWord_4989066).sum := by decide
  have hdescent : baseEnd_4989066 < baseStart_4989066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989106 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_4989106 : Nat := 118140960795 + 4989106 * 2 ^ 59
def prefixEnd_4989106 : Nat := 4983230072969 + 3 ^ 40 * 4989106 * 2
def baseEnd_4989106 : Nat := 2561809414230462333530525

theorem tailTrace_4989106 : CollatzResearch.WordTrace tailWord_4989106 prefixEnd_4989106 2561809414230462333530525 := by
  unfold tailWord_4989106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45491911265832127078258793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121311763375552338875356781 45491911265832127078258793)
  ·
    refine ⟨34118933449374095308694095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45491911265832127078258793 34118933449374095308694095)
    ·
      refine ⟨51178400174061142963041143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34118933449374095308694095 51178400174061142963041143)
      ·
        refine ⟨76767600261091714444561715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51178400174061142963041143 76767600261091714444561715)
        ·
          refine ⟨115151400391637571666842573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76767600261091714444561715 115151400391637571666842573)
          ·
            refine ⟨43181775146864089375065965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115151400391637571666842573 43181775146864089375065965)
            ·
              refine ⟨16193165680074033515649737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43181775146864089375065965 16193165680074033515649737)
              ·
                refine ⟨12144874260055525136737303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16193165680074033515649737 12144874260055525136737303)
                ·
                  refine ⟨18217311390083287705105955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12144874260055525136737303 18217311390083287705105955)
                  ·
                    refine ⟨27325967085124931557658933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18217311390083287705105955 27325967085124931557658933)
                    ·
                      refine ⟨2561809414230462333530525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27325967085124931557658933 2561809414230462333530525)
                      ·
                        rfl

theorem cell23_4989106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_4989106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989106 prefixEnd_4989106 := by exact prefixLift 4989106
  have htrace : WordTrace (prefixWord ++ tailWord_4989106) baseStart_4989106 baseEnd_4989106 := by
    simpa [prefixWord, tailWord_4989106, baseEnd_4989106] using wordTrace_append hprefix tailTrace_4989106
  have hstable : (prefixWord ++ tailWord_4989106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989106).length < 2 ^ (prefixWord ++ tailWord_4989106).sum := by decide
  have hdescent : baseEnd_4989106 < baseStart_4989106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989120 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2]
def baseStart_4989120 : Nat := 118140960795 + 4989120 * 2 ^ 59
def prefixEnd_4989120 : Nat := 4983230072969 + 3 ^ 40 * 4989120 * 2
def baseEnd_4989120 : Nat := 2561816602959625278755461

theorem tailTrace_4989120 : CollatzResearch.WordTrace tailWord_4989120 prefixEnd_4989120 2561816602959625278755461 := by
  unfold tailWord_4989120
  simp only [CollatzResearch.WordTrace]
  refine ⟨90984077842638894352022407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121312103790185192469363209 90984077842638894352022407)
  ·
    refine ⟨136476116763958341528033611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90984077842638894352022407 136476116763958341528033611)
    ·
      refine ⟨204714175145937512292050417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136476116763958341528033611 204714175145937512292050417)
      ·
        refine ⟨153535631359453134219037813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204714175145937512292050417 153535631359453134219037813)
        ·
          refine ⟨14393965439948731333034795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153535631359453134219037813 14393965439948731333034795)
          ·
            refine ⟨21590948159923096999552193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14393965439948731333034795 21590948159923096999552193)
            ·
              refine ⟨16193211119942322749664145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21590948159923096999552193 16193211119942322749664145)
              ·
                refine ⟨12144908339956742062248109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16193211119942322749664145 12144908339956742062248109)
                ·
                  refine ⟨4554340627483778273343041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12144908339956742062248109 4554340627483778273343041)
                  ·
                    refine ⟨3415755470612833705007281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554340627483778273343041 3415755470612833705007281)
                    ·
                      refine ⟨2561816602959625278755461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415755470612833705007281 2561816602959625278755461)
                      ·
                        rfl

theorem cell23_4989120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_4989120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989120 prefixEnd_4989120 := by exact prefixLift 4989120
  have htrace : WordTrace (prefixWord ++ tailWord_4989120) baseStart_4989120 baseEnd_4989120 := by
    simpa [prefixWord, tailWord_4989120, baseEnd_4989120] using wordTrace_append hprefix tailTrace_4989120
  have hstable : (prefixWord ++ tailWord_4989120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989120).length < 2 ^ (prefixWord ++ tailWord_4989120).sum := by decide
  have hdescent : baseEnd_4989120 < baseStart_4989120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989137 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_4989137 : Nat := 118140960795 + 4989137 * 2 ^ 59
def prefixEnd_4989137 : Nat := 4983230072969 + 3 ^ 40 * 4989137 * 2
def baseEnd_4989137 : Nat := 2561825332130751712242883

theorem tailTrace_4989137 : CollatzResearch.WordTrace tailWord_4989137 prefixEnd_4989137 2561825332130751712242883 := by
  unfold tailWord_4989137
  simp only [CollatzResearch.WordTrace]
  refine ⟨181968775726216200607413665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121312517150810800404942443 181968775726216200607413665)
  ·
    refine ⟨136476581794662150455560249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181968775726216200607413665 136476581794662150455560249)
    ·
      refine ⟨102357436345996612841670187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136476581794662150455560249 102357436345996612841670187)
      ·
        refine ⟨153536154518994919262505281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102357436345996612841670187 153536154518994919262505281)
        ·
          refine ⟨115152115889246189446878961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153536154518994919262505281 115152115889246189446878961)
          ·
            refine ⟨86364086916934642085159221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115152115889246189446878961 86364086916934642085159221)
            ·
              refine ⟨8096633148462622695483677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86364086916934642085159221 8096633148462622695483677)
              ·
                refine ⟨3036237430673483510806379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8096633148462622695483677 3036237430673483510806379)
                ·
                  refine ⟨4554356146010225266209569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036237430673483510806379 4554356146010225266209569)
                  ·
                    refine ⟨3415767109507668949657177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554356146010225266209569 3415767109507668949657177)
                    ·
                      refine ⟨2561825332130751712242883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415767109507668949657177 2561825332130751712242883)
                      ·
                        rfl

theorem cell23_4989137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_4989137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989137 prefixEnd_4989137 := by exact prefixLift 4989137
  have htrace : WordTrace (prefixWord ++ tailWord_4989137) baseStart_4989137 baseEnd_4989137 := by
    simpa [prefixWord, tailWord_4989137, baseEnd_4989137] using wordTrace_append hprefix tailTrace_4989137
  have hstable : (prefixWord ++ tailWord_4989137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989137).length < 2 ^ (prefixWord ++ tailWord_4989137).sum := by decide
  have hdescent : baseEnd_4989137 < baseStart_4989137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989153 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4989153 : Nat := 118140960795 + 4989153 * 2 ^ 59
def prefixEnd_4989153 : Nat := 4983230072969 + 3 ^ 40 * 4989153 * 2
def baseEnd_4989153 : Nat := 2561833547821223649642809

theorem tailTrace_4989153 : CollatzResearch.WordTrace tailWord_4989153 prefixEnd_4989153 2561833547821223649642809 := by
  unfold tailWord_4989153
  simp only [CollatzResearch.WordTrace]
  refine ⟨181969359294158235339996113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121312906196105490226664075 181969359294158235339996113)
  ·
    refine ⟨136477019470618676504997085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181969359294158235339996113 136477019470618676504997085)
    ·
      refine ⟨51178882301482003689373907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136477019470618676504997085 51178882301482003689373907)
      ·
        refine ⟨76768323452223005534060861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51178882301482003689373907 76768323452223005534060861)
        ·
          refine ⟨28788121294583627075272823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76768323452223005534060861 28788121294583627075272823)
          ·
            refine ⟨43182181941875440612909235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28788121294583627075272823 43182181941875440612909235)
            ·
              refine ⟨64773272912813160919363853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43182181941875440612909235 64773272912813160919363853)
              ·
                refine ⟨24289977342304935344761445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64773272912813160919363853 24289977342304935344761445)
                ·
                  refine ⟨4554370751682175377142771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24289977342304935344761445 4554370751682175377142771)
                  ·
                    refine ⟨6831556127523263065714157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554370751682175377142771 6831556127523263065714157)
                    ·
                      refine ⟨2561833547821223649642809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831556127523263065714157 2561833547821223649642809)
                      ·
                        rfl

theorem cell23_4989153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4989153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989153 prefixEnd_4989153 := by exact prefixLift 4989153
  have htrace : WordTrace (prefixWord ++ tailWord_4989153) baseStart_4989153 baseEnd_4989153 := by
    simpa [prefixWord, tailWord_4989153, baseEnd_4989153] using wordTrace_append hprefix tailTrace_4989153
  have hstable : (prefixWord ++ tailWord_4989153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989153).length < 2 ^ (prefixWord ++ tailWord_4989153).sum := by decide
  have hdescent : baseEnd_4989153 < baseStart_4989153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989163 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 3, 3, 2]
def baseStart_4989163 : Nat := 118140960795 + 4989163 * 2 ^ 59
def prefixEnd_4989163 : Nat := 4983230072969 + 3 ^ 40 * 4989163 * 2
def baseEnd_4989163 : Nat := 2561838682627768610517763

theorem tailTrace_4989163 : CollatzResearch.WordTrace tailWord_4989163 prefixEnd_4989163 2561838682627768610517763 := by
  unfold tailWord_4989163
  simp only [CollatzResearch.WordTrace]
  refine ⟨181969724024122007047860143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121313149349414671365240095 181969724024122007047860143)
  ·
    refine ⟨272954586036183010571790215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181969724024122007047860143 272954586036183010571790215)
    ·
      refine ⟨409431879054274515857685323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272954586036183010571790215 409431879054274515857685323)
      ·
        refine ⟨614147818581411773786527985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409431879054274515857685323 614147818581411773786527985)
        ·
          refine ⟨460610863936058830339895989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614147818581411773786527985 460610863936058830339895989)
          ·
            refine ⟨43182268494005515344365249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 460610863936058830339895989 43182268494005515344365249)
            ·
              refine ⟨32386701370504136508273937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43182268494005515344365249 32386701370504136508273937)
              ·
                refine ⟨24290026027878102381205453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32386701370504136508273937 24290026027878102381205453)
                ·
                  refine ⟨9108759760454288392952045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24290026027878102381205453 9108759760454288392952045)
                  ·
                    refine ⟨3415784910170358147357017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9108759760454288392952045 3415784910170358147357017)
                    ·
                      refine ⟨2561838682627768610517763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415784910170358147357017 2561838682627768610517763)
                      ·
                        rfl

theorem cell23_4989163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3, 2].length) (baseStart_4989163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989163 prefixEnd_4989163 := by exact prefixLift 4989163
  have htrace : WordTrace (prefixWord ++ tailWord_4989163) baseStart_4989163 baseEnd_4989163 := by
    simpa [prefixWord, tailWord_4989163, baseEnd_4989163] using wordTrace_append hprefix tailTrace_4989163
  have hstable : (prefixWord ++ tailWord_4989163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989163).length < 2 ^ (prefixWord ++ tailWord_4989163).sum := by decide
  have hdescent : baseEnd_4989163 < baseStart_4989163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989179 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_4989179 : Nat := 118140960795 + 4989179 * 2 ^ 59
def prefixEnd_4989179 : Nat := 4983230072969 + 3 ^ 40 * 4989179 * 2
def baseEnd_4989179 : Nat := 2561846898318240547917689

theorem tailTrace_4989179 : CollatzResearch.WordTrace tailWord_4989179 prefixEnd_4989179 2561846898318240547917689 := by
  unfold tailWord_4989179
  simp only [CollatzResearch.WordTrace]
  refine ⟨181970307592064041780442591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121313538394709361186961727 181970307592064041780442591)
  ·
    refine ⟨272955461388096062670663887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181970307592064041780442591 272955461388096062670663887)
    ·
      refine ⟨409433192082144094005995831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272955461388096062670663887 409433192082144094005995831)
      ·
        refine ⟨614149788123216141008993747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409433192082144094005995831 614149788123216141008993747)
        ·
          refine ⟨921224682184824211513490621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614149788123216141008993747 921224682184824211513490621)
          ·
            refine ⟨345459255819309079317558983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921224682184824211513490621 345459255819309079317558983)
            ·
              refine ⟨518188883728963618976338475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345459255819309079317558983 518188883728963618976338475)
              ·
                refine ⟨777283325593445428464507713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518188883728963618976338475 777283325593445428464507713)
                ·
                  refine ⟨582962494195084071348380785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777283325593445428464507713 582962494195084071348380785)
                  ·
                    refine ⟨437221870646313053511285589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 582962494195084071348380785 437221870646313053511285589)
                    ·
                      refine ⟨2561846898318240547917689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 437221870646313053511285589 2561846898318240547917689)
                      ·
                        rfl

theorem cell23_4989179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_4989179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989179 prefixEnd_4989179 := by exact prefixLift 4989179
  have htrace : WordTrace (prefixWord ++ tailWord_4989179) baseStart_4989179 baseEnd_4989179 := by
    simpa [prefixWord, tailWord_4989179, baseEnd_4989179] using wordTrace_append hprefix tailTrace_4989179
  have hstable : (prefixWord ++ tailWord_4989179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989179).length < 2 ^ (prefixWord ++ tailWord_4989179).sum := by decide
  have hdescent : baseEnd_4989179 < baseStart_4989179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989180 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_4989180 : Nat := 118140960795 + 4989180 * 2 ^ 59
def prefixEnd_4989180 : Nat := 4983230072969 + 3 ^ 40 * 4989180 * 2
def baseEnd_4989180 : Nat := 2561847411798895044005185

theorem tailTrace_4989180 : CollatzResearch.WordTrace tailWord_4989180 prefixEnd_4989180 2561847411798895044005185 := by
  unfold tailWord_4989180
  simp only [CollatzResearch.WordTrace]
  refine ⟨90985172032530209475614497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121313562710040279300819329 90985172032530209475614497)
  ·
    refine ⟨68238879024397657106710873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90985172032530209475614497 68238879024397657106710873)
    ·
      refine ⟨51179159268298242830033155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68238879024397657106710873 51179159268298242830033155)
      ·
        refine ⟨76768738902447364245049733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51179159268298242830033155 76768738902447364245049733)
        ·
          refine ⟨14394138544208880795946825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76768738902447364245049733 14394138544208880795946825)
          ·
            refine ⟨10795603908156660596960119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14394138544208880795946825 10795603908156660596960119)
            ·
              refine ⟨16193405862234990895440179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10795603908156660596960119 16193405862234990895440179)
              ·
                refine ⟨24290108793352486343160269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16193405862234990895440179 24290108793352486343160269)
                ·
                  refine ⟨9108790797507182378685101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24290108793352486343160269 9108790797507182378685101)
                  ·
                    refine ⟨3415796549065193392006913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9108790797507182378685101 3415796549065193392006913)
                    ·
                      refine ⟨2561847411798895044005185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415796549065193392006913 2561847411798895044005185)
                      ·
                        rfl

theorem cell23_4989180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_4989180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989180 prefixEnd_4989180 := by exact prefixLift 4989180
  have htrace : WordTrace (prefixWord ++ tailWord_4989180) baseStart_4989180 baseEnd_4989180 := by
    simpa [prefixWord, tailWord_4989180, baseEnd_4989180] using wordTrace_append hprefix tailTrace_4989180
  have hstable : (prefixWord ++ tailWord_4989180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989180).length < 2 ^ (prefixWord ++ tailWord_4989180).sum := by decide
  have hdescent : baseEnd_4989180 < baseStart_4989180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989193 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 4, 2]
def baseStart_4989193 : Nat := 118140960795 + 4989193 * 2 ^ 59
def prefixEnd_4989193 : Nat := 4983230072969 + 3 ^ 40 * 4989193 * 2
def baseEnd_4989193 : Nat := 2561854087047403493142625

theorem tailTrace_4989193 : CollatzResearch.WordTrace tailWord_4989193 prefixEnd_4989193 2561854087047403493142625 := by
  unfold tailWord_4989193
  simp only [CollatzResearch.WordTrace]
  refine ⟨181970818214013322171452233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121313878809342214780968155 181970818214013322171452233)
  ·
    refine ⟨136478113660509991628589175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181970818214013322171452233 136478113660509991628589175)
    ·
      refine ⟨204717170490764987442883763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136478113660509991628589175 204717170490764987442883763)
      ·
        refine ⟨307075755736147481164325645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204717170490764987442883763 307075755736147481164325645)
        ·
          refine ⟨115153408401055305436622117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307075755736147481164325645 115153408401055305436622117)
          ·
            refine ⟨21591264075197869769366647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115153408401055305436622117 21591264075197869769366647)
            ·
              refine ⟨32386896112796804654049971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21591264075197869769366647 32386896112796804654049971)
              ·
                refine ⟨48580344169195206981074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32386896112796804654049971 48580344169195206981074957)
                ·
                  refine ⟨18217629063448202617903109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48580344169195206981074957 18217629063448202617903109)
                  ·
                    refine ⟨3415805449396537990856833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18217629063448202617903109 3415805449396537990856833)
                    ·
                      refine ⟨2561854087047403493142625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415805449396537990856833 2561854087047403493142625)
                      ·
                        rfl

theorem cell23_4989193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4, 2].length) (baseStart_4989193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989193 prefixEnd_4989193 := by exact prefixLift 4989193
  have htrace : WordTrace (prefixWord ++ tailWord_4989193) baseStart_4989193 baseEnd_4989193 := by
    simpa [prefixWord, tailWord_4989193, baseEnd_4989193] using wordTrace_append hprefix tailTrace_4989193
  have hstable : (prefixWord ++ tailWord_4989193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989193).length < 2 ^ (prefixWord ++ tailWord_4989193).sum := by decide
  have hdescent : baseEnd_4989193 < baseStart_4989193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989196 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4989196 : Nat := 118140960795 + 4989196 * 2 ^ 59
def prefixEnd_4989196 : Nat := 4983230072969 + 3 ^ 40 * 4989196 * 2
def baseEnd_4989196 : Nat := 2561855627489366981405111

theorem tailTrace_4989196 : CollatzResearch.WordTrace tailWord_4989196 prefixEnd_4989196 2561855627489366981405111 := by
  unfold tailWord_4989196
  simp only [CollatzResearch.WordTrace]
  refine ⟨90985463816501226841905721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121313951755334969122540961 90985463816501226841905721)
  ·
    refine ⟨68239097862375920131429291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90985463816501226841905721 68239097862375920131429291)
    ·
      refine ⟨102358646793563880197143937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68239097862375920131429291 102358646793563880197143937)
      ·
        refine ⟨76768985095172910147857953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102358646793563880197143937 76768985095172910147857953)
        ·
          refine ⟨57576738821379682610893465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76768985095172910147857953 57576738821379682610893465)
          ·
            refine ⟨43182554116034761958170099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57576738821379682610893465 43182554116034761958170099)
            ·
              refine ⟨64773831174052142937255149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43182554116034761958170099 64773831174052142937255149)
              ·
                refine ⟨24290186690269553601470681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64773831174052142937255149 24290186690269553601470681)
                ·
                  refine ⟨18217640017702165201103011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24290186690269553601470681 18217640017702165201103011)
                  ·
                    refine ⟨27326460026553247801654517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18217640017702165201103011 27326460026553247801654517)
                    ·
                      refine ⟨2561855627489366981405111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27326460026553247801654517 2561855627489366981405111)
                      ·
                        rfl

theorem cell23_4989196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4989196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989196 prefixEnd_4989196 := by exact prefixLift 4989196
  have htrace : WordTrace (prefixWord ++ tailWord_4989196) baseStart_4989196 baseEnd_4989196 := by
    simpa [prefixWord, tailWord_4989196, baseEnd_4989196] using wordTrace_append hprefix tailTrace_4989196
  have hstable : (prefixWord ++ tailWord_4989196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989196).length < 2 ^ (prefixWord ++ tailWord_4989196).sum := by decide
  have hdescent : baseEnd_4989196 < baseStart_4989196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989233 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 7]
def baseStart_4989233 : Nat := 118140960795 + 4989233 * 2 ^ 59
def prefixEnd_4989233 : Nat := 4983230072969 + 3 ^ 40 * 4989233 * 2
def baseEnd_4989233 : Nat := 284652736252620370738049

theorem tailTrace_4989233 : CollatzResearch.WordTrace tailWord_4989233 prefixEnd_4989233 284652736252620370738049 := by
  unfold tailWord_4989233
  simp only [CollatzResearch.WordTrace]
  refine ⟨181972277133868409002908353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121314851422578939335272235 181972277133868409002908353)
  ·
    refine ⟨136479207850401306752181265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181972277133868409002908353 136479207850401306752181265)
    ·
      refine ⟨102359405887800980064135949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136479207850401306752181265 102359405887800980064135949)
      ·
        refine ⟨38384777207925367524050981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102359405887800980064135949 38384777207925367524050981)
        ·
          refine ⟨7197145726486006410759559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38384777207925367524050981 7197145726486006410759559)
          ·
            refine ⟨10795718589729009616139339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197145726486006410759559 10795718589729009616139339)
            ·
              refine ⟨16193577884593514424209009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10795718589729009616139339 16193577884593514424209009)
              ·
                refine ⟨12145183413445135818156757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16193577884593514424209009 12145183413445135818156757)
                ·
                  refine ⟨284652736252620370738049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12145183413445135818156757 284652736252620370738049)
                  ·
                    rfl

theorem cell23_4989233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_4989233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989233 prefixEnd_4989233 := by exact prefixLift 4989233
  have htrace : WordTrace (prefixWord ++ tailWord_4989233) baseStart_4989233 baseEnd_4989233 := by
    simpa [prefixWord, tailWord_4989233, baseEnd_4989233] using wordTrace_append hprefix tailTrace_4989233
  have hstable : (prefixWord ++ tailWord_4989233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989233).length < 2 ^ (prefixWord ++ tailWord_4989233).sum := by decide
  have hdescent : baseEnd_4989233 < baseStart_4989233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989256 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4989256 : Nat := 118140960795 + 4989256 * 2 ^ 59
def prefixEnd_4989256 : Nat := 4983230072969 + 3 ^ 40 * 4989256 * 2
def baseEnd_4989256 : Nat := 2561886436328636746654835

theorem tailTrace_4989256 : CollatzResearch.WordTrace tailWord_4989256 prefixEnd_4989256 2561886436328636746654835 := by
  unfold tailWord_4989256
  simp only [CollatzResearch.WordTrace]
  refine ⟨90986558006392541965497811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121315410675190055953997081 90986558006392541965497811)
  ·
    refine ⟨136479837009588812948246717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90986558006392541965497811 136479837009588812948246717)
    ·
      refine ⟨51179938878595804855592519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136479837009588812948246717 51179938878595804855592519)
      ·
        refine ⟨76769908317893707283388779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51179938878595804855592519 76769908317893707283388779)
        ·
          refine ⟨115154862476840560925083169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76769908317893707283388779 115154862476840560925083169)
          ·
            refine ⟨86366146857630420693812377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115154862476840560925083169 86366146857630420693812377)
            ·
              refine ⟨64774610143222815520359283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86366146857630420693812377 64774610143222815520359283)
              ·
                refine ⟨97161915214834223280538925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64774610143222815520359283 97161915214834223280538925)
                ·
                  refine ⟨36435718205562833730202097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97161915214834223280538925 36435718205562833730202097)
                  ·
                    refine ⟨27326788654172125297651573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36435718205562833730202097 27326788654172125297651573)
                    ·
                      refine ⟨2561886436328636746654835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27326788654172125297651573 2561886436328636746654835)
                      ·
                        rfl

theorem cell23_4989256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4989256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989256 prefixEnd_4989256 := by exact prefixLift 4989256
  have htrace : WordTrace (prefixWord ++ tailWord_4989256) baseStart_4989256 baseEnd_4989256 := by
    simpa [prefixWord, tailWord_4989256, baseEnd_4989256] using wordTrace_append hprefix tailTrace_4989256
  have hstable : (prefixWord ++ tailWord_4989256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989256).length < 2 ^ (prefixWord ++ tailWord_4989256).sum := by decide
  have hdescent : baseEnd_4989256 < baseStart_4989256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989320 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4989320 : Nat := 118140960795 + 4989320 * 2 ^ 59
def prefixEnd_4989320 : Nat := 4983230072969 + 3 ^ 40 * 4989320 * 2
def baseEnd_4989320 : Nat := 2561919299090524496254541

theorem tailTrace_4989320 : CollatzResearch.WordTrace tailWord_4989320 prefixEnd_4989320 2561919299090524496254541 := by
  unfold tailWord_4989320
  simp only [CollatzResearch.WordTrace]
  refine ⟨90987725142276611430662707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121316966856368815240883609 90987725142276611430662707)
  ·
    refine ⟨136481587713414917145994061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90987725142276611430662707 136481587713414917145994061)
    ·
      refine ⟨51180595392530593929747773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136481587713414917145994061 51180595392530593929747773)
      ·
        refine ⟨19192723272198972723655415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51180595392530593929747773 19192723272198972723655415)
        ·
          refine ⟨28789084908298459085483123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19192723272198972723655415 28789084908298459085483123)
          ·
            refine ⟨43183627362447688628224685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28789084908298459085483123 43183627362447688628224685)
            ·
              refine ⟨16193860260917883235584257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43183627362447688628224685 16193860260917883235584257)
              ·
                refine ⟨12145395195688412426688193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16193860260917883235584257 12145395195688412426688193)
                ·
                  refine ⟨9109046396766309320016145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12145395195688412426688193 9109046396766309320016145)
                  ·
                    refine ⟨6831784797574731990012109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9109046396766309320016145 6831784797574731990012109)
                    ·
                      refine ⟨2561919299090524496254541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831784797574731990012109 2561919299090524496254541)
                      ·
                        rfl

theorem cell23_4989320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4989320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989320 prefixEnd_4989320 := by exact prefixLift 4989320
  have htrace : WordTrace (prefixWord ++ tailWord_4989320) baseStart_4989320 baseEnd_4989320 := by
    simpa [prefixWord, tailWord_4989320, baseEnd_4989320] using wordTrace_append hprefix tailTrace_4989320
  have hstable : (prefixWord ++ tailWord_4989320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989320).length < 2 ^ (prefixWord ++ tailWord_4989320).sum := by decide
  have hdescent : baseEnd_4989320 < baseStart_4989320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989384 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_4989384 : Nat := 118140960795 + 4989384 * 2 ^ 59
def prefixEnd_4989384 : Nat := 4983230072969 + 3 ^ 40 * 4989384 * 2
def baseEnd_4989384 : Nat := 2561952161852412245854247

theorem tailTrace_4989384 : CollatzResearch.WordTrace tailWord_4989384 prefixEnd_4989384 2561952161852412245854247 := by
  unfold tailWord_4989384
  simp only [CollatzResearch.WordTrace]
  refine ⟨90988892278160680895827603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121318523037547574527770137 90988892278160680895827603)
  ·
    refine ⟨136483338417241021343741405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90988892278160680895827603 136483338417241021343741405)
    ·
      refine ⟨51181251906465383003903027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136483338417241021343741405 51181251906465383003903027)
      ·
        refine ⟨76771877859698074505854541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51181251906465383003903027 76771877859698074505854541)
        ·
          refine ⟨28789454197386777939695453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76771877859698074505854541 28789454197386777939695453)
          ·
            refine ⟨10796045324020041727385795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28789454197386777939695453 10796045324020041727385795)
            ·
              refine ⟨16194067986030062591078693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796045324020041727385795 16194067986030062591078693)
              ·
                refine ⟨3036387747380636735827255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16194067986030062591078693 3036387747380636735827255)
                ·
                  refine ⟨4554581621070955103740883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036387747380636735827255 4554581621070955103740883)
                  ·
                    refine ⟨6831872431606432655611325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554581621070955103740883 6831872431606432655611325)
                    ·
                      refine ⟨2561952161852412245854247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831872431606432655611325 2561952161852412245854247)
                      ·
                        rfl

theorem cell23_4989384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_4989384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989384 prefixEnd_4989384 := by exact prefixLift 4989384
  have htrace : WordTrace (prefixWord ++ tailWord_4989384) baseStart_4989384 baseEnd_4989384 := by
    simpa [prefixWord, tailWord_4989384, baseEnd_4989384] using wordTrace_append hprefix tailTrace_4989384
  have hstable : (prefixWord ++ tailWord_4989384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989384).length < 2 ^ (prefixWord ++ tailWord_4989384).sum := by decide
  have hdescent : baseEnd_4989384 < baseStart_4989384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989390 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_4989390 : Nat := 118140960795 + 4989390 * 2 ^ 59
def prefixEnd_4989390 : Nat := 4983230072969 + 3 ^ 40 * 4989390 * 2
def baseEnd_4989390 : Nat := 2561955242736339222379219

theorem tailTrace_4989390 : CollatzResearch.WordTrace tailWord_4989390 prefixEnd_4989390 2561955242736339222379219 := by
  unfold tailWord_4989390
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747250424287453102046703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121318668929533083210915749 22747250424287453102046703)
  ·
    refine ⟨34120875636431179653070055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22747250424287453102046703 34120875636431179653070055)
    ·
      refine ⟨51181313454646769479605083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34120875636431179653070055 51181313454646769479605083)
      ·
        refine ⟨76771970181970154219407625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51181313454646769479605083 76771970181970154219407625)
        ·
          refine ⟨57578977636477615664555719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76771970181970154219407625 57578977636477615664555719)
          ·
            refine ⟨86368466454716423496833579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57578977636477615664555719 86368466454716423496833579)
            ·
              refine ⟨129552699682074635245250369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86368466454716423496833579 129552699682074635245250369)
              ·
                refine ⟨97164524761555976433937777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129552699682074635245250369 97164524761555976433937777)
                ·
                  refine ⟨72873393571166982325453333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97164524761555976433937777 72873393571166982325453333)
                  ·
                    refine ⟨3415940323648452296505625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72873393571166982325453333 3415940323648452296505625)
                    ·
                      refine ⟨2561955242736339222379219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415940323648452296505625 2561955242736339222379219)
                      ·
                        rfl

theorem cell23_4989390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_4989390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989390 prefixEnd_4989390 := by exact prefixLift 4989390
  have htrace : WordTrace (prefixWord ++ tailWord_4989390) baseStart_4989390 baseEnd_4989390 := by
    simpa [prefixWord, tailWord_4989390, baseEnd_4989390] using wordTrace_append hprefix tailTrace_4989390
  have hstable : (prefixWord ++ tailWord_4989390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989390).length < 2 ^ (prefixWord ++ tailWord_4989390).sum := by decide
  have hdescent : baseEnd_4989390 < baseStart_4989390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_4989393 : Nat := 118140960795 + 4989393 * 2 ^ 59
def prefixEnd_4989393 : Nat := 4983230072969 + 3 ^ 40 * 4989393 * 2
def baseEnd_4989393 : Nat := 2561956783178302710641705

theorem tailTrace_4989393 : CollatzResearch.WordTrace tailWord_4989393 prefixEnd_4989393 2561956783178302710641705 := by
  unfold tailWord_4989393
  simp only [CollatzResearch.WordTrace]
  refine ⟨181978112813288756328732833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121318741875525837552488555 181978112813288756328732833)
  ·
    refine ⟨136483584609966567246549625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181978112813288756328732833 136483584609966567246549625)
    ·
      refine ⟨102362688457474925434912219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136483584609966567246549625 102362688457474925434912219)
      ·
        refine ⟨153544032686212388152368329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102362688457474925434912219 153544032686212388152368329)
        ·
          refine ⟨115158024514659291114276247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153544032686212388152368329 115158024514659291114276247)
          ·
            refine ⟨172737036771988936671414371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115158024514659291114276247 172737036771988936671414371)
            ·
              refine ⟨259105555157983405007121557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172737036771988936671414371 259105555157983405007121557)
              ·
                refine ⟨12145572898030472109708823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259105555157983405007121557 12145572898030472109708823)
                ·
                  refine ⟨18218359347045708164563235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12145572898030472109708823 18218359347045708164563235)
                  ·
                    refine ⟨27327539020568562246844853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18218359347045708164563235 27327539020568562246844853)
                    ·
                      refine ⟨2561956783178302710641705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27327539020568562246844853 2561956783178302710641705)
                      ·
                        rfl

theorem cell23_4989393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_4989393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989393 prefixEnd_4989393 := by exact prefixLift 4989393
  have htrace : WordTrace (prefixWord ++ tailWord_4989393) baseStart_4989393 baseEnd_4989393 := by
    simpa [prefixWord, tailWord_4989393, baseEnd_4989393] using wordTrace_append hprefix tailTrace_4989393
  have hstable : (prefixWord ++ tailWord_4989393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989393).length < 2 ^ (prefixWord ++ tailWord_4989393).sum := by decide
  have hdescent : baseEnd_4989393 < baseStart_4989393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989407 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 5, 2, 2]
def baseStart_4989407 : Nat := 118140960795 + 4989407 * 2 ^ 59
def prefixEnd_4989407 : Nat := 4983230072969 + 3 ^ 40 * 4989407 * 2
def baseEnd_4989407 : Nat := 2561963971907465655866641

theorem tailTrace_4989407 : CollatzResearch.WordTrace tailWord_4989407 prefixEnd_4989407 2561963971907465655866641 := by
  unfold tailWord_4989407
  simp only [CollatzResearch.WordTrace]
  refine ⟨181978623435238036719742475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121319082290158691146494983 181978623435238036719742475)
  ·
    refine ⟨272967935152857055079613713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181978623435238036719742475 272967935152857055079613713)
    ·
      refine ⟨204725951364642791309710285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272967935152857055079613713 204725951364642791309710285)
      ·
        refine ⟨76772231761741046741141357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204725951364642791309710285 76772231761741046741141357)
        ·
          refine ⟨28789586910652892527928009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76772231761741046741141357 28789586910652892527928009)
          ·
            refine ⟨21592190182989669395946007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28789586910652892527928009 21592190182989669395946007)
            ·
              refine ⟨32388285274484504093919011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21592190182989669395946007 32388285274484504093919011)
              ·
                refine ⟨48582427911726756140878517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32388285274484504093919011 48582427911726756140878517)
                ·
                  refine ⟨4554602616724383388207361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48582427911726756140878517 4554602616724383388207361)
                  ·
                    refine ⟨3415951962543287541155521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554602616724383388207361 3415951962543287541155521)
                    ·
                      refine ⟨2561963971907465655866641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415951962543287541155521 2561963971907465655866641)
                      ·
                        rfl

theorem cell23_4989407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_4989407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989407 prefixEnd_4989407 := by exact prefixLift 4989407
  have htrace : WordTrace (prefixWord ++ tailWord_4989407) baseStart_4989407 baseEnd_4989407 := by
    simpa [prefixWord, tailWord_4989407, baseEnd_4989407] using wordTrace_append hprefix tailTrace_4989407
  have hstable : (prefixWord ++ tailWord_4989407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989407).length < 2 ^ (prefixWord ++ tailWord_4989407).sum := by decide
  have hdescent : baseEnd_4989407 < baseStart_4989407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989411 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4989411 : Nat := 118140960795 + 4989411 * 2 ^ 59
def prefixEnd_4989411 : Nat := 4983230072969 + 3 ^ 40 * 4989411 * 2
def baseEnd_4989411 : Nat := 2561966025830083640216623

theorem tailTrace_4989411 : CollatzResearch.WordTrace tailWord_4989411 prefixEnd_4989411 2561966025830083640216623 := by
  unfold tailWord_4989411
  simp only [CollatzResearch.WordTrace]
  refine ⟨181978769327223545402888087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121319179551482363601925391 181978769327223545402888087)
  ·
    refine ⟨272968153990835318104332131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181978769327223545402888087 272968153990835318104332131)
    ·
      refine ⟨409452230986252977156498197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272968153990835318104332131 409452230986252977156498197)
      ·
        refine ⟨19193073327480608304210853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 409452230986252977156498197 19193073327480608304210853)
        ·
          refine ⟨3598701248902614057039535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19193073327480608304210853 3598701248902614057039535)
          ·
            refine ⟨5398051873353921085559303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598701248902614057039535 5398051873353921085559303)
            ·
              refine ⟨8097077810030881628338955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398051873353921085559303 8097077810030881628338955)
              ·
                refine ⟨12145616715046322442508433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8097077810030881628338955 12145616715046322442508433)
                ·
                  refine ⟨9109212536284741831881325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12145616715046322442508433 9109212536284741831881325)
                  ·
                    refine ⟨3415954701106778186955497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9109212536284741831881325 3415954701106778186955497)
                    ·
                      refine ⟨2561966025830083640216623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415954701106778186955497 2561966025830083640216623)
                      ·
                        rfl

theorem cell23_4989411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4989411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989411 prefixEnd_4989411 := by exact prefixLift 4989411
  have htrace : WordTrace (prefixWord ++ tailWord_4989411) baseStart_4989411 baseEnd_4989411 := by
    simpa [prefixWord, tailWord_4989411, baseEnd_4989411] using wordTrace_append hprefix tailTrace_4989411
  have hstable : (prefixWord ++ tailWord_4989411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989411).length < 2 ^ (prefixWord ++ tailWord_4989411).sum := by decide
  have hdescent : baseEnd_4989411 < baseStart_4989411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989441 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4989441 : Nat := 118140960795 + 4989441 * 2 ^ 59
def prefixEnd_4989441 : Nat := 4983230072969 + 3 ^ 40 * 4989441 * 2
def baseEnd_4989441 : Nat := 2561981430249718522841485

theorem tailTrace_4989441 : CollatzResearch.WordTrace tailWord_4989441 prefixEnd_4989441 2561981430249718522841485 := by
  unfold tailWord_4989441
  simp only [CollatzResearch.WordTrace]
  refine ⟨181979863517114860526480177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121319909011409907017653451 181979863517114860526480177)
  ·
    refine ⟨136484897637836145394860133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181979863517114860526480177 136484897637836145394860133)
    ·
      refine ⟨25590918307094277261536275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136484897637836145394860133 25590918307094277261536275)
      ·
        refine ⟨38386377460641415892304413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25590918307094277261536275 38386377460641415892304413)
        ·
          refine ⟨14394891547740530959614155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38386377460641415892304413 14394891547740530959614155)
          ·
            refine ⟨21592337321610796439421233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14394891547740530959614155 21592337321610796439421233)
            ·
              refine ⟨16194252991208097329565925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21592337321610796439421233 16194252991208097329565925)
              ·
                refine ⟨3036422435851518249293611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16194252991208097329565925 3036422435851518249293611)
                ·
                  refine ⟨4554633653777277373940417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036422435851518249293611 4554633653777277373940417)
                  ·
                    refine ⟨3415975240332958030455313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554633653777277373940417 3415975240332958030455313)
                    ·
                      refine ⟨2561981430249718522841485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415975240332958030455313 2561981430249718522841485)
                      ·
                        rfl

theorem cell23_4989441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4989441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989441 prefixEnd_4989441 := by exact prefixLift 4989441
  have htrace : WordTrace (prefixWord ++ tailWord_4989441) baseStart_4989441 baseEnd_4989441 := by
    simpa [prefixWord, tailWord_4989441, baseEnd_4989441] using wordTrace_append hprefix tailTrace_4989441
  have hstable : (prefixWord ++ tailWord_4989441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989441).length < 2 ^ (prefixWord ++ tailWord_4989441).sum := by decide
  have hdescent : baseEnd_4989441 < baseStart_4989441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989492 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4989492 : Nat := 118140960795 + 4989492 * 2 ^ 59
def prefixEnd_4989492 : Nat := 4983230072969 + 3 ^ 40 * 4989492 * 2
def baseEnd_4989492 : Nat := 2562007617763097823303751

theorem tailTrace_4989492 : CollatzResearch.WordTrace tailWord_4989492 prefixEnd_4989492 2562007617763097823303751 := by
  unfold tailWord_4989492
  simp only [CollatzResearch.WordTrace]
  refine ⟨90990861819965048118293365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121321149093286730824391153 90990861819965048118293365)
  ·
    refine ⟨8530393295621723261090003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90990861819965048118293365 8530393295621723261090003)
    ·
      refine ⟨12795589943432584891635005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530393295621723261090003 12795589943432584891635005)
      ·
        refine ⟨4798346228787219334363127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12795589943432584891635005 4798346228787219334363127)
        ·
          refine ⟨7197519343180829001544691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798346228787219334363127 7197519343180829001544691)
          ·
            refine ⟨10796279014771243502317037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197519343180829001544691 10796279014771243502317037)
            ·
              refine ⟨4048604630539216313368889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10796279014771243502317037 4048604630539216313368889)
              ·
                refine ⟨3036453472904412235026667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048604630539216313368889 3036453472904412235026667)
                ·
                  refine ⟨4554680209356618352540001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036453472904412235026667 4554680209356618352540001)
                  ·
                    refine ⟨3416010157017463764405001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554680209356618352540001 3416010157017463764405001)
                    ·
                      refine ⟨2562007617763097823303751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416010157017463764405001 2562007617763097823303751)
                      ·
                        rfl

theorem cell23_4989492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4989492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989492 prefixEnd_4989492 := by exact prefixLift 4989492
  have htrace : WordTrace (prefixWord ++ tailWord_4989492) baseStart_4989492 baseEnd_4989492 := by
    simpa [prefixWord, tailWord_4989492, baseEnd_4989492] using wordTrace_append hprefix tailTrace_4989492
  have hstable : (prefixWord ++ tailWord_4989492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989492).length < 2 ^ (prefixWord ++ tailWord_4989492).sum := by decide
  have hdescent : baseEnd_4989492 < baseStart_4989492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989517 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4989517 : Nat := 118140960795 + 4989517 * 2 ^ 59
def prefixEnd_4989517 : Nat := 4983230072969 + 3 ^ 40 * 4989517 * 2
def baseEnd_4989517 : Nat := 2562020454779460225491135

theorem tailTrace_4989517 : CollatzResearch.WordTrace tailWord_4989517 prefixEnd_4989517 2562020454779460225491135 := by
  unfold tailWord_4989517
  simp only [CollatzResearch.WordTrace]
  refine ⟨181982635464839525506246805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121321756976559683670831203 181982635464839525506246805)
  ·
    refine ⟨8530436037414352758105319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181982635464839525506246805 8530436037414352758105319)
    ·
      refine ⟨12795654056121529137157979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530436037414352758105319 12795654056121529137157979)
      ·
        refine ⟨19193481084182293705736969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795654056121529137157979 19193481084182293705736969)
        ·
          refine ⟨14395110813136720279302727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19193481084182293705736969 14395110813136720279302727)
          ·
            refine ⟨21592666219705080418954091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14395110813136720279302727 21592666219705080418954091)
            ·
              refine ⟨32388999329557620628431137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21592666219705080418954091 32388999329557620628431137)
              ·
                refine ⟨24291749497168215471323353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32388999329557620628431137 24291749497168215471323353)
                ·
                  refine ⟨18218812122876161603492515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24291749497168215471323353 18218812122876161603492515)
                  ·
                    refine ⟨27328218184314242405238773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18218812122876161603492515 27328218184314242405238773)
                    ·
                      refine ⟨2562020454779460225491135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27328218184314242405238773 2562020454779460225491135)
                      ·
                        rfl

theorem cell23_4989517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4989517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989517 prefixEnd_4989517 := by exact prefixLift 4989517
  have htrace : WordTrace (prefixWord ++ tailWord_4989517) baseStart_4989517 baseEnd_4989517 := by
    simpa [prefixWord, tailWord_4989517, baseEnd_4989517] using wordTrace_append hprefix tailTrace_4989517
  have hstable : (prefixWord ++ tailWord_4989517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989517).length < 2 ^ (prefixWord ++ tailWord_4989517).sum := by decide
  have hdescent : baseEnd_4989517 < baseStart_4989517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989530 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_4989530 : Nat := 118140960795 + 4989530 * 2 ^ 59
def prefixEnd_4989530 : Nat := 4983230072969 + 3 ^ 40 * 4989530 * 2
def baseEnd_4989530 : Nat := 2562027130027968674628575

theorem tailTrace_4989530 : CollatzResearch.WordTrace tailWord_4989530 prefixEnd_4989530 2562027130027968674628575 := by
  unfold tailWord_4989530
  simp only [CollatzResearch.WordTrace]
  refine ⟨45495777403448107181617511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121322073075861619150980029 45495777403448107181617511)
  ·
    refine ⟨68243666105172160772426267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45495777403448107181617511 68243666105172160772426267)
    ·
      refine ⟨102365499157758241158639401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68243666105172160772426267 102365499157758241158639401)
      ·
        refine ⟨76774124368318680868979551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102365499157758241158639401 76774124368318680868979551)
        ·
          refine ⟨115161186552478021303469327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76774124368318680868979551 115161186552478021303469327)
          ·
            refine ⟨172741779828717031955203991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115161186552478021303469327 172741779828717031955203991)
            ·
              refine ⟨259112669743075547932805987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172741779828717031955203991 259112669743075547932805987)
              ·
                refine ⟨388669004614613321899208981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259112669743075547932805987 388669004614613321899208981)
                ·
                  refine ⟨18218859591309999464025421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 388669004614613321899208981 18218859591309999464025421)
                  ·
                    refine ⟨6832072346741249799009533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18218859591309999464025421 6832072346741249799009533)
                    ·
                      refine ⟨2562027130027968674628575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6832072346741249799009533 2562027130027968674628575)
                      ·
                        rfl

theorem cell23_4989530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_4989530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989530 prefixEnd_4989530 := by exact prefixLift 4989530
  have htrace : WordTrace (prefixWord ++ tailWord_4989530) baseStart_4989530 baseEnd_4989530 := by
    simpa [prefixWord, tailWord_4989530, baseEnd_4989530] using wordTrace_append hprefix tailTrace_4989530
  have hstable : (prefixWord ++ tailWord_4989530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989530).length < 2 ^ (prefixWord ++ tailWord_4989530).sum := by decide
  have hdescent : baseEnd_4989530 < baseStart_4989530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989554 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_4989554 : Nat := 118140960795 + 4989554 * 2 ^ 59
def prefixEnd_4989554 : Nat := 4983230072969 + 3 ^ 40 * 4989554 * 2
def baseEnd_4989554 : Nat := 284671050395964064525385

theorem tailTrace_4989554 : CollatzResearch.WordTrace tailWord_4989554 prefixEnd_4989554 284671050395964064525385 := by
  unfold tailWord_4989554
  simp only [CollatzResearch.WordTrace]
  refine ⟨45495996241426370206335929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121322656643803653883562477 45495996241426370206335929)
  ·
    refine ⟨34121997181069777654751947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45495996241426370206335929 34121997181069777654751947)
    ·
      refine ⟨51182995771604666482127921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34121997181069777654751947 51182995771604666482127921)
      ·
        refine ⟨38387246828703499861595941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51182995771604666482127921 38387246828703499861595941)
        ·
          refine ⟨7197608780381906224049239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38387246828703499861595941 7197608780381906224049239)
          ·
            refine ⟨10796413170572859336073859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197608780381906224049239 10796413170572859336073859)
            ·
              refine ⟨16194619755859289004110789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796413170572859336073859 16194619755859289004110789)
              ·
                refine ⟨3036491204223616688270773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16194619755859289004110789 3036491204223616688270773)
                ·
                  refine ⟨284671050395964064525385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036491204223616688270773 284671050395964064525385)
                  ·
                    rfl

theorem cell23_4989554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_4989554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989554 prefixEnd_4989554 := by exact prefixLift 4989554
  have htrace : WordTrace (prefixWord ++ tailWord_4989554) baseStart_4989554 baseEnd_4989554 := by
    simpa [prefixWord, tailWord_4989554, baseEnd_4989554] using wordTrace_append hprefix tailTrace_4989554
  have hstable : (prefixWord ++ tailWord_4989554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989554).length < 2 ^ (prefixWord ++ tailWord_4989554).sum := by decide
  have hdescent : baseEnd_4989554 < baseStart_4989554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989657 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_4989657 : Nat := 118140960795 + 4989657 * 2 ^ 59
def prefixEnd_4989657 : Nat := 4983230072969 + 3 ^ 40 * 4989657 * 2
def baseEnd_4989657 : Nat := 854030780690363225913497

theorem tailTrace_4989657 : CollatzResearch.WordTrace tailWord_4989657 prefixEnd_4989657 854030780690363225913497 := by
  unfold tailWord_4989657
  simp only [CollatzResearch.WordTrace]
  refine ⟨181987741684332329416343225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121325161122888219610895483 181987741684332329416343225)
  ·
    refine ⟨136490806263249247062257419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181987741684332329416343225 136490806263249247062257419)
    ·
      refine ⟨204736209394873870593386129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136490806263249247062257419 204736209394873870593386129)
      ·
        refine ⟨153552157046155402945039597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204736209394873870593386129 153552157046155402945039597)
        ·
          refine ⟨57582058892308276104389849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153552157046155402945039597 57582058892308276104389849)
          ·
            refine ⟨43186544169231207078292387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57582058892308276104389849 43186544169231207078292387)
            ·
              refine ⟨64779816253846810617438581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43186544169231207078292387 64779816253846810617438581)
              ·
                refine ⟨6073107773798138495384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64779816253846810617438581 6073107773798138495384867)
                ·
                  refine ⟨9109661660697207743077301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6073107773798138495384867 9109661660697207743077301)
                  ·
                    refine ⟨854030780690363225913497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9109661660697207743077301 854030780690363225913497)
                    ·
                      rfl

theorem cell23_4989657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_4989657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989657 prefixEnd_4989657 := by exact prefixLift 4989657
  have htrace : WordTrace (prefixWord ++ tailWord_4989657) baseStart_4989657 baseEnd_4989657 := by
    simpa [prefixWord, tailWord_4989657, baseEnd_4989657] using wordTrace_append hprefix tailTrace_4989657
  have hstable : (prefixWord ++ tailWord_4989657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989657).length < 2 ^ (prefixWord ++ tailWord_4989657).sum := by decide
  have hdescent : baseEnd_4989657 < baseStart_4989657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989698 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_4989698 : Nat := 118140960795 + 4989698 * 2 ^ 59
def prefixEnd_4989698 : Nat := 4983230072969 + 3 ^ 40 * 4989698 * 2
def baseEnd_4989698 : Nat := 2562113394777924017327803

theorem tailTrace_4989698 : CollatzResearch.WordTrace tailWord_4989698 prefixEnd_4989698 2562113394777924017327803 := by
  unfold tailWord_4989698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45497309269295948354646437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121326158051455862279057165 45497309269295948354646437)
  ·
    refine ⟨8530745487992990316496207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45497309269295948354646437 8530745487992990316496207)
    ·
      refine ⟨12796118231989485474744311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530745487992990316496207 12796118231989485474744311)
      ·
        refine ⟨19194177347984228212116467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12796118231989485474744311 19194177347984228212116467)
        ·
          refine ⟨28791266021976342318174701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19194177347984228212116467 28791266021976342318174701)
          ·
            refine ⟨10796724758241128369315513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28791266021976342318174701 10796724758241128369315513)
            ·
              refine ⟨8097543568680846276986635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10796724758241128369315513 8097543568680846276986635)
              ·
                refine ⟨12146315353021269415479953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8097543568680846276986635 12146315353021269415479953)
                ·
                  refine ⟨9109736514765952061609965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12146315353021269415479953 9109736514765952061609965)
                  ·
                    refine ⟨3416151193037232023103737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9109736514765952061609965 3416151193037232023103737)
                    ·
                      refine ⟨2562113394777924017327803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416151193037232023103737 2562113394777924017327803)
                      ·
                        rfl

theorem cell23_4989698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_4989698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989698 prefixEnd_4989698 := by exact prefixLift 4989698
  have htrace : WordTrace (prefixWord ++ tailWord_4989698) baseStart_4989698 baseEnd_4989698 := by
    simpa [prefixWord, tailWord_4989698, baseEnd_4989698] using wordTrace_append hprefix tailTrace_4989698
  have hstable : (prefixWord ++ tailWord_4989698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989698).length < 2 ^ (prefixWord ++ tailWord_4989698).sum := by decide
  have hdescent : baseEnd_4989698 < baseStart_4989698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989784 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_4989784 : Nat := 118140960795 + 4989784 * 2 ^ 59
def prefixEnd_4989784 : Nat := 4983230072969 + 3 ^ 40 * 4989784 * 2
def baseEnd_4989784 : Nat := 2562157554114210680852407

theorem tailTrace_4989784 : CollatzResearch.WordTrace tailWord_4989784 prefixEnd_4989784 2562157554114210680852407 := by
  unfold tailWord_4989784
  simp only [CollatzResearch.WordTrace]
  refine ⟨90996186877436115053108203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121328249169914820070810937 90996186877436115053108203)
  ·
    refine ⟨136494280316154172579662305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90996186877436115053108203 136494280316154172579662305)
    ·
      refine ⟨102370710237115629434746729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136494280316154172579662305 102370710237115629434746729)
      ·
        refine ⟨76778032677836722076060047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102370710237115629434746729 76778032677836722076060047)
        ·
          refine ⟨115167049016755083114090071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76778032677836722076060047 115167049016755083114090071)
          ·
            refine ⟨172750573525132624671135107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115167049016755083114090071 172750573525132624671135107)
            ·
              refine ⟨259125860287698937006702661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172750573525132624671135107 259125860287698937006702661)
              ·
                refine ⟨48586098803943550688756749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259125860287698937006702661 48586098803943550688756749)
                ·
                  refine ⟨18219787051478831508283781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48586098803943550688756749 18219787051478831508283781)
                  ·
                    refine ⟨3416210072152280907803209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18219787051478831508283781 3416210072152280907803209)
                    ·
                      refine ⟨2562157554114210680852407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416210072152280907803209 2562157554114210680852407)
                      ·
                        rfl

theorem cell23_4989784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_4989784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989784 prefixEnd_4989784 := by exact prefixLift 4989784
  have htrace : WordTrace (prefixWord ++ tailWord_4989784) baseStart_4989784 baseEnd_4989784 := by
    simpa [prefixWord, tailWord_4989784, baseEnd_4989784] using wordTrace_append hprefix tailTrace_4989784
  have hstable : (prefixWord ++ tailWord_4989784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989784).length < 2 ^ (prefixWord ++ tailWord_4989784).sum := by decide
  have hdescent : baseEnd_4989784 < baseStart_4989784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3]
def baseStart_4989787 : Nat := 118140960795 + 4989787 * 2 ^ 59
def prefixEnd_4989787 : Nat := 4983230072969 + 3 ^ 40 * 4989787 * 2
def baseEnd_4989787 : Nat := 2562159094556174169114893

theorem tailTrace_4989787 : CollatzResearch.WordTrace tailWord_4989787 prefixEnd_4989787 2562159094556174169114893 := by
  unfold tailWord_4989787
  simp only [CollatzResearch.WordTrace]
  refine ⟨181992483173861361618575615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121328322115907574412383743 181992483173861361618575615)
  ·
    refine ⟨272988724760792042427863423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181992483173861361618575615 272988724760792042427863423)
    ·
      refine ⟨409483087141188063641795135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272988724760792042427863423 409483087141188063641795135)
      ·
        refine ⟨614224630711782095462692703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409483087141188063641795135 614224630711782095462692703)
        ·
          refine ⟨921336946067673143194039055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614224630711782095462692703 921336946067673143194039055)
          ·
            refine ⟨1382005419101509714791058583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921336946067673143194039055 1382005419101509714791058583)
            ·
              refine ⟨2073008128652264572186587875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382005419101509714791058583 2073008128652264572186587875)
              ·
                refine ⟨3109512192978396858279881813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073008128652264572186587875 3109512192978396858279881813)
                ·
                  refine ⟨36439596011465588182967365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3109512192978396858279881813 36439596011465588182967365)
                  ·
                    refine ⟨6832424252149797784306381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36439596011465588182967365 6832424252149797784306381)
                    ·
                      refine ⟨2562159094556174169114893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6832424252149797784306381 2562159094556174169114893)
                      ·
                        rfl

theorem cell23_4989787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].length) (baseStart_4989787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989787 prefixEnd_4989787 := by exact prefixLift 4989787
  have htrace : WordTrace (prefixWord ++ tailWord_4989787) baseStart_4989787 baseEnd_4989787 := by
    simpa [prefixWord, tailWord_4989787, baseEnd_4989787] using wordTrace_append hprefix tailTrace_4989787
  have hstable : (prefixWord ++ tailWord_4989787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989787).length < 2 ^ (prefixWord ++ tailWord_4989787).sum := by decide
  have hdescent : baseEnd_4989787 < baseStart_4989787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989824 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 5]
def baseStart_4989824 : Nat := 118140960795 + 4989824 * 2 ^ 59
def prefixEnd_4989824 : Nat := 4983230072969 + 3 ^ 40 * 4989824 * 2
def baseEnd_4989824 : Nat := 284686454815598947150247

theorem tailTrace_4989824 : CollatzResearch.WordTrace tailWord_4989824 prefixEnd_4989824 284686454815598947150247 := by
  unfold tailWord_4989824
  simp only [CollatzResearch.WordTrace]
  refine ⟨90996916337363658468836263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121329221783151544625115017 90996916337363658468836263)
  ·
    refine ⟨136495374506045487703254395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90996916337363658468836263 136495374506045487703254395)
    ·
      refine ⟨204743061759068231554881593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136495374506045487703254395 204743061759068231554881593)
      ·
        refine ⟨153557296319301173666161195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204743061759068231554881593 153557296319301173666161195)
        ·
          refine ⟨230335944478951760499241793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153557296319301173666161195 230335944478951760499241793)
          ·
            refine ⟨172751958359213820374431345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230335944478951760499241793 172751958359213820374431345)
            ·
              refine ⟨129563968769410365280823509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172751958359213820374431345 129563968769410365280823509)
              ·
                refine ⟨3036655518033055436269301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129563968769410365280823509 3036655518033055436269301)
                ·
                  refine ⟨284686454815598947150247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036655518033055436269301 284686454815598947150247)
                  ·
                    rfl

theorem cell23_4989824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 5].length) (baseStart_4989824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989824 prefixEnd_4989824 := by exact prefixLift 4989824
  have htrace : WordTrace (prefixWord ++ tailWord_4989824) baseStart_4989824 baseEnd_4989824 := by
    simpa [prefixWord, tailWord_4989824, baseEnd_4989824] using wordTrace_append hprefix tailTrace_4989824
  have hstable : (prefixWord ++ tailWord_4989824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989824).length < 2 ^ (prefixWord ++ tailWord_4989824).sum := by decide
  have hdescent : baseEnd_4989824 < baseStart_4989824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989892 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 5]
def baseStart_4989892 : Nat := 118140960795 + 4989892 * 2 ^ 59
def prefixEnd_4989892 : Nat := 4983230072969 + 3 ^ 40 * 4989892 * 2
def baseEnd_4989892 : Nat := 284690334447210695366879

theorem tailTrace_4989892 : CollatzResearch.WordTrace tailWord_4989892 prefixEnd_4989892 284690334447210695366879 := by
  unfold tailWord_4989892
  simp only [CollatzResearch.WordTrace]
  refine ⟨90998156419240482275573965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121330875225653976367431953 90998156419240482275573965)
  ·
    refine ⟨34124308657215180853340237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90998156419240482275573965 34124308657215180853340237)
    ·
      refine ⟨12796615746455692820002589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34124308657215180853340237 12796615746455692820002589)
      ·
        refine ⟨4798730904920884807500971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12796615746455692820002589 4798730904920884807500971)
        ·
          refine ⟨7198096357381327211251457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798730904920884807500971 7198096357381327211251457)
          ·
            refine ⟨5398572268035995408438593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198096357381327211251457 5398572268035995408438593)
            ·
              refine ⟨4048929201026996556328945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398572268035995408438593 4048929201026996556328945)
              ·
                refine ⟨3036696900770247417246709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048929201026996556328945 3036696900770247417246709)
                ·
                  refine ⟨284690334447210695366879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036696900770247417246709 284690334447210695366879)
                  ·
                    rfl

theorem cell23_4989892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_4989892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989892 prefixEnd_4989892 := by exact prefixLift 4989892
  have htrace : WordTrace (prefixWord ++ tailWord_4989892) baseStart_4989892 baseEnd_4989892 := by
    simpa [prefixWord, tailWord_4989892, baseEnd_4989892] using wordTrace_append hprefix tailTrace_4989892
  have hstable : (prefixWord ++ tailWord_4989892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989892).length < 2 ^ (prefixWord ++ tailWord_4989892).sum := by decide
  have hdescent : baseEnd_4989892 < baseStart_4989892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989908 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4989908 : Nat := 118140960795 + 4989908 * 2 ^ 59
def prefixEnd_4989908 : Nat := 4983230072969 + 3 ^ 40 * 4989908 * 2
def baseEnd_4989908 : Nat := 2562221225715368195701837

theorem tailTrace_4989908 : CollatzResearch.WordTrace tailWord_4989908 prefixEnd_4989908 2562221225715368195701837 := by
  unfold tailWord_4989908
  simp only [CollatzResearch.WordTrace]
  refine ⟨90998448203211499641865189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121331264270948666189153585 90998448203211499641865189)
  ·
    refine ⟨17062209038102156182849723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90998448203211499641865189 17062209038102156182849723)
    ·
      refine ⟨25593313557153234274274585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17062209038102156182849723 25593313557153234274274585)
      ·
        refine ⟨19194985167864925705705939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25593313557153234274274585 19194985167864925705705939)
        ·
          refine ⟨28792477751797388558558909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19194985167864925705705939 28792477751797388558558909)
          ·
            refine ⟨10797179156924020709459591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28792477751797388558558909 10797179156924020709459591)
            ·
              refine ⟨16195768735386031064189387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10797179156924020709459591 16195768735386031064189387)
              ·
                refine ⟨24293653103079046596284081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16195768735386031064189387 24293653103079046596284081)
                ·
                  refine ⟨18220239827309284947213061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24293653103079046596284081 18220239827309284947213061)
                  ·
                    refine ⟨3416294967620490927602449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18220239827309284947213061 3416294967620490927602449)
                    ·
                      refine ⟨2562221225715368195701837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416294967620490927602449 2562221225715368195701837)
                      ·
                        rfl

theorem cell23_4989908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4989908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989908 prefixEnd_4989908 := by exact prefixLift 4989908
  have htrace : WordTrace (prefixWord ++ tailWord_4989908) baseStart_4989908 baseEnd_4989908 := by
    simpa [prefixWord, tailWord_4989908, baseEnd_4989908] using wordTrace_append hprefix tailTrace_4989908
  have hstable : (prefixWord ++ tailWord_4989908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989908).length < 2 ^ (prefixWord ++ tailWord_4989908).sum := by decide
  have hdescent : baseEnd_4989908 < baseStart_4989908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989924 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_4989924 : Nat := 118140960795 + 4989924 * 2 ^ 59
def prefixEnd_4989924 : Nat := 4983230072969 + 3 ^ 40 * 4989924 * 2
def baseEnd_4989924 : Nat := 2562229441405840133101763

theorem tailTrace_4989924 : CollatzResearch.WordTrace tailWord_4989924 prefixEnd_4989924 2562229441405840133101763 := by
  unfold tailWord_4989924
  simp only [CollatzResearch.WordTrace]
  refine ⟨90998739987182517008156413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121331653316243356010875217 90998739987182517008156413)
  ·
    refine ⟨34124527495193443878058655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90998739987182517008156413 34124527495193443878058655)
    ·
      refine ⟨51186791242790165817087983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34124527495193443878058655 51186791242790165817087983)
      ·
        refine ⟨76780186864185248725631975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51186791242790165817087983 76780186864185248725631975)
        ·
          refine ⟨115170280296277873088447963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76780186864185248725631975 115170280296277873088447963)
          ·
            refine ⟨172755420444416809632671945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115170280296277873088447963 172755420444416809632671945)
            ·
              refine ⟨129566565333312607224503959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172755420444416809632671945 129566565333312607224503959)
              ·
                refine ⟨194349847999968910836755939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129566565333312607224503959 194349847999968910836755939)
                ·
                  refine ⟨291524771999953366255133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194349847999968910836755939 291524771999953366255133909)
                  ·
                    refine ⟨6832611843748907021604701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 291524771999953366255133909 6832611843748907021604701)
                    ·
                      refine ⟨2562229441405840133101763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6832611843748907021604701 2562229441405840133101763)
                      ·
                        rfl

theorem cell23_4989924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_4989924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989924 prefixEnd_4989924 := by exact prefixLift 4989924
  have htrace : WordTrace (prefixWord ++ tailWord_4989924) baseStart_4989924 baseEnd_4989924 := by
    simpa [prefixWord, tailWord_4989924, baseEnd_4989924] using wordTrace_append hprefix tailTrace_4989924
  have hstable : (prefixWord ++ tailWord_4989924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989924).length < 2 ^ (prefixWord ++ tailWord_4989924).sum := by decide
  have hdescent : baseEnd_4989924 < baseStart_4989924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989925 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4989925 : Nat := 118140960795 + 4989925 * 2 ^ 59
def prefixEnd_4989925 : Nat := 4983230072969 + 3 ^ 40 * 4989925 * 2
def baseEnd_4989925 : Nat := 2562229954886494629189259

theorem tailTrace_4989925 : CollatzResearch.WordTrace tailWord_4989925 prefixEnd_4989925 2562229954886494629189259 := by
  unfold tailWord_4989925
  simp only [CollatzResearch.WordTrace]
  refine ⟨181997516447361411187099229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121331677631574274124732819 181997516447361411187099229)
  ·
    refine ⟨68249068667760529195162211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181997516447361411187099229 68249068667760529195162211)
    ·
      refine ⟨102373603001640793792743317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68249068667760529195162211 102373603001640793792743317)
      ·
        refine ⟨4798762640701912209034843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102373603001640793792743317 4798762640701912209034843)
        ·
          refine ⟨7198143961052868313552265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798762640701912209034843 7198143961052868313552265)
          ·
            refine ⟨5398607970789651235164199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198143961052868313552265 5398607970789651235164199)
            ·
              refine ⟨8097911956184476852746299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398607970789651235164199 8097911956184476852746299)
              ·
                refine ⟨12146867934276715279119449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8097911956184476852746299 12146867934276715279119449)
                ·
                  refine ⟨9110150950707536459339587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12146867934276715279119449 9110150950707536459339587)
                  ·
                    refine ⟨13665226426061304689009381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9110150950707536459339587 13665226426061304689009381)
                    ·
                      refine ⟨2562229954886494629189259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13665226426061304689009381 2562229954886494629189259)
                      ·
                        rfl

theorem cell23_4989925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4989925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989925 prefixEnd_4989925 := by exact prefixLift 4989925
  have htrace : WordTrace (prefixWord ++ tailWord_4989925) baseStart_4989925 baseEnd_4989925 := by
    simpa [prefixWord, tailWord_4989925, baseEnd_4989925] using wordTrace_append hprefix tailTrace_4989925
  have hstable : (prefixWord ++ tailWord_4989925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989925).length < 2 ^ (prefixWord ++ tailWord_4989925).sum := by decide
  have hdescent : baseEnd_4989925 < baseStart_4989925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989998 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4989998 : Nat := 118140960795 + 4989998 * 2 ^ 59
def prefixEnd_4989998 : Nat := 4983230072969 + 3 ^ 40 * 4989998 * 2
def baseEnd_4989998 : Nat := 2562267438974272843576423

theorem tailTrace_4989998 : CollatzResearch.WordTrace tailWord_4989998 prefixEnd_4989998 2562267438974272843576423 := by
  unfold tailWord_4989998
  simp only [CollatzResearch.WordTrace]
  refine ⟨22750022372012118081813331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121333452650731296436337765 22750022372012118081813331)
  ·
    refine ⟨34125033558018177122719997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22750022372012118081813331 34125033558018177122719997)
    ·
      refine ⟨12796887584256816421019999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34125033558018177122719997 12796887584256816421019999)
      ·
        refine ⟨19195331376385224631529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12796887584256816421019999 19195331376385224631529999)
        ·
          refine ⟨28792997064577836947294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19195331376385224631529999 28792997064577836947294999)
          ·
            refine ⟨43189495596866755420942499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28792997064577836947294999 43189495596866755420942499)
            ·
              refine ⟨64784243395300133131413749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43189495596866755420942499 64784243395300133131413749)
              ·
                refine ⟨6073522818309387481070039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64784243395300133131413749 6073522818309387481070039)
                ·
                  refine ⟨9110284227464081221605059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6073522818309387481070039 9110284227464081221605059)
                  ·
                    refine ⟨13665426341196121832407589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9110284227464081221605059 13665426341196121832407589)
                    ·
                      refine ⟨2562267438974272843576423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13665426341196121832407589 2562267438974272843576423)
                      ·
                        rfl

theorem cell23_4989998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4989998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989998 prefixEnd_4989998 := by exact prefixLift 4989998
  have htrace : WordTrace (prefixWord ++ tailWord_4989998) baseStart_4989998 baseEnd_4989998 := by
    simpa [prefixWord, tailWord_4989998, baseEnd_4989998] using wordTrace_append hprefix tailTrace_4989998
  have hstable : (prefixWord ++ tailWord_4989998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989998).length < 2 ^ (prefixWord ++ tailWord_4989998).sum := by decide
  have hdescent : baseEnd_4989998 < baseStart_4989998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990001 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_4990001 : Nat := 118140960795 + 4990001 * 2 ^ 59
def prefixEnd_4990001 : Nat := 4983230072969 + 3 ^ 40 * 4990001 * 2
def baseEnd_4990001 : Nat := 2562268979416236331838909

theorem tailTrace_4990001 : CollatzResearch.WordTrace tailWord_4990001 prefixEnd_4990001 2562268979416236331838909 := by
  unfold tailWord_4990001
  simp only [CollatzResearch.WordTrace]
  refine ⟨182000288395086076166865857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121333525596724050777910571 182000288395086076166865857)
  ·
    refine ⟨136500216296314557125149393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182000288395086076166865857 136500216296314557125149393)
    ·
      refine ⟨102375162222235917843862045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136500216296314557125149393 102375162222235917843862045)
      ·
        refine ⟨38390685833338469191448267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102375162222235917843862045 38390685833338469191448267)
        ·
          refine ⟨57586028750007703787172401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38390685833338469191448267 57586028750007703787172401)
          ·
            refine ⟨43189521562505777840379301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57586028750007703787172401 43189521562505777840379301)
            ·
              refine ⟨8098035292969833345071119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43189521562505777840379301 8098035292969833345071119)
              ·
                refine ⟨12147052939454750017606679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8098035292969833345071119 12147052939454750017606679)
                ·
                  refine ⟨18220579409182125026410019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12147052939454750017606679 18220579409182125026410019)
                  ·
                    refine ⟨27330869113773187539615029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18220579409182125026410019 27330869113773187539615029)
                    ·
                      refine ⟨2562268979416236331838909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27330869113773187539615029 2562268979416236331838909)
                      ·
                        rfl

theorem cell23_4990001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_4990001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990001 prefixEnd_4990001 := by exact prefixLift 4990001
  have htrace : WordTrace (prefixWord ++ tailWord_4990001) baseStart_4990001 baseEnd_4990001 := by
    simpa [prefixWord, tailWord_4990001, baseEnd_4990001] using wordTrace_append hprefix tailTrace_4990001
  have hstable : (prefixWord ++ tailWord_4990001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990001).length < 2 ^ (prefixWord ++ tailWord_4990001).sum := by decide
  have hdescent : baseEnd_4990001 < baseStart_4990001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990024 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4990024 : Nat := 118140960795 + 4990024 * 2 ^ 59
def prefixEnd_4990024 : Nat := 4983230072969 + 3 ^ 40 * 4990024 * 2
def baseEnd_4990024 : Nat := 2562280789471289741851303

theorem tailTrace_4990024 : CollatzResearch.WordTrace tailWord_4990024 prefixEnd_4990024 2562280789471289741851303 := by
  unfold tailWord_4990024
  simp only [CollatzResearch.WordTrace]
  refine ⟨91000563637001375547476563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121334084849335167396635417 91000563637001375547476563)
  ·
    refine ⟨136500845455502063321214845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91000563637001375547476563 136500845455502063321214845)
    ·
      refine ⟨51187817045813273745455567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136500845455502063321214845 51187817045813273745455567)
      ·
        refine ⟨76781725568719910618183351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51187817045813273745455567 76781725568719910618183351)
        ·
          refine ⟨115172588353079865927275027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76781725568719910618183351 115172588353079865927275027)
          ·
            refine ⟨172758882529619798890912541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115172588353079865927275027 172758882529619798890912541)
            ·
              refine ⟨64784580948607424584092203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172758882529619798890912541 64784580948607424584092203)
              ·
                refine ⟨97176871422911136876138305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64784580948607424584092203 97176871422911136876138305)
                ·
                  refine ⟨72882653567183352657103729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97176871422911136876138305 72882653567183352657103729)
                  ·
                    refine ⟨54661990175387514492827797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72882653567183352657103729 54661990175387514492827797)
                    ·
                      refine ⟨2562280789471289741851303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54661990175387514492827797 2562280789471289741851303)
                      ·
                        rfl

theorem cell23_4990024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4990024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990024 prefixEnd_4990024 := by exact prefixLift 4990024
  have htrace : WordTrace (prefixWord ++ tailWord_4990024) baseStart_4990024 baseEnd_4990024 := by
    simpa [prefixWord, tailWord_4990024, baseEnd_4990024] using wordTrace_append hprefix tailTrace_4990024
  have hstable : (prefixWord ++ tailWord_4990024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990024).length < 2 ^ (prefixWord ++ tailWord_4990024).sum := by decide
  have hdescent : baseEnd_4990024 < baseStart_4990024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990045 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4990045 : Nat := 118140960795 + 4990045 * 2 ^ 59
def prefixEnd_4990045 : Nat := 4983230072969 + 3 ^ 40 * 4990045 * 2
def baseEnd_4990045 : Nat := 2562291572565034159688707

theorem tailTrace_4990045 : CollatzResearch.WordTrace tailWord_4990045 prefixEnd_4990045 2562291572565034159688707 := by
  unfold tailWord_4990045
  simp only [CollatzResearch.WordTrace]
  refine ⟨182001893206926671681467589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121334595471284447787645059 182001893206926671681467589)
  ·
    refine ⟨34125354976298750940275173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182001893206926671681467589 34125354976298750940275173)
    ·
      refine ⟨6398504058056015801301595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34125354976298750940275173 6398504058056015801301595)
      ·
        refine ⟨9597756087084023701952393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398504058056015801301595 9597756087084023701952393)
        ·
          refine ⟨7198317065313017776464295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9597756087084023701952393 7198317065313017776464295)
          ·
            refine ⟨10797475597969526664696443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198317065313017776464295 10797475597969526664696443)
            ·
              refine ⟨16196213396954289997044665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10797475597969526664696443 16196213396954289997044665)
              ·
                refine ⟨12147160047715717497783499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16196213396954289997044665 12147160047715717497783499)
                ·
                  refine ⟨18220740071573576246675249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12147160047715717497783499 18220740071573576246675249)
                  ·
                    refine ⟨13665555053680182185006437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18220740071573576246675249 13665555053680182185006437)
                    ·
                      refine ⟨2562291572565034159688707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13665555053680182185006437 2562291572565034159688707)
                      ·
                        rfl

theorem cell23_4990045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4990045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990045 prefixEnd_4990045 := by exact prefixLift 4990045
  have htrace : WordTrace (prefixWord ++ tailWord_4990045) baseStart_4990045 baseEnd_4990045 := by
    simpa [prefixWord, tailWord_4990045, baseEnd_4990045] using wordTrace_append hprefix tailTrace_4990045
  have hstable : (prefixWord ++ tailWord_4990045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990045).length < 2 ^ (prefixWord ++ tailWord_4990045).sum := by decide
  have hdescent : baseEnd_4990045 < baseStart_4990045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990081 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4990081 : Nat := 118140960795 + 4990081 * 2 ^ 59
def prefixEnd_4990081 : Nat := 4983230072969 + 3 ^ 40 * 4990081 * 2
def baseEnd_4990081 : Nat := 854103352622865339612847

theorem tailTrace_4990081 : CollatzResearch.WordTrace tailWord_4990081 prefixEnd_4990081 854103352622865339612847 := by
  unfold tailWord_4990081
  simp only [CollatzResearch.WordTrace]
  refine ⟨182003206234796249829778097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121335470823197499886518731 182003206234796249829778097)
  ·
    refine ⟨136502404676097187372333573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182003206234796249829778097 136502404676097187372333573)
    ·
      refine ⟨25594200876768222632312545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136502404676097187372333573 25594200876768222632312545)
      ·
        refine ⟨19195650657576166974234409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25594200876768222632312545 19195650657576166974234409)
        ·
          refine ⟨14396737993182125230675807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19195650657576166974234409 14396737993182125230675807)
          ·
            refine ⟨21595106989773187846013711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14396737993182125230675807 21595106989773187846013711)
            ·
              refine ⟨32392660484659781769020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21595106989773187846013711 32392660484659781769020567)
              ·
                refine ⟨48588990726989672653530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32392660484659781769020567 48588990726989672653530851)
                ·
                  refine ⟨72883486090484508980296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48588990726989672653530851 72883486090484508980296277)
                  ·
                    refine ⟨854103352622865339612847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72883486090484508980296277 854103352622865339612847)
                    ·
                      rfl

theorem cell23_4990081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4990081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990081 prefixEnd_4990081 := by exact prefixLift 4990081
  have htrace : WordTrace (prefixWord ++ tailWord_4990081) baseStart_4990081 baseEnd_4990081 := by
    simpa [prefixWord, tailWord_4990081, baseEnd_4990081] using wordTrace_append hprefix tailTrace_4990081
  have hstable : (prefixWord ++ tailWord_4990081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990081).length < 2 ^ (prefixWord ++ tailWord_4990081).sum := by decide
  have hdescent : baseEnd_4990081 < baseStart_4990081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990141 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_4990141 : Nat := 118140960795 + 4990141 * 2 ^ 59
def prefixEnd_4990141 : Nat := 4983230072969 + 3 ^ 40 * 4990141 * 2
def baseEnd_4990141 : Nat := 854113622235955261362755

theorem tailTrace_4990141 : CollatzResearch.WordTrace tailWord_4990141 prefixEnd_4990141 854113622235955261362755 := by
  unfold tailWord_4990141
  simp only [CollatzResearch.WordTrace]
  refine ⟨182005394614578880076962277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121336929743052586717974851 182005394614578880076962277)
  ·
    refine ⟨34126011490233540014430427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182005394614578880076962277 34126011490233540014430427)
    ·
      refine ⟨51189017235350310021645641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34126011490233540014430427 51189017235350310021645641)
      ·
        refine ⟨38391762926512732516234231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51189017235350310021645641 38391762926512732516234231)
        ·
          refine ⟨57587644389769098774351347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38391762926512732516234231 57587644389769098774351347)
          ·
            refine ⟨86381466584653648161527021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57587644389769098774351347 86381466584653648161527021)
            ·
              refine ⟨32393049969245118060572633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86381466584653648161527021 32393049969245118060572633)
              ·
                refine ⟨24294787476933838545429475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32393049969245118060572633 24294787476933838545429475)
                ·
                  refine ⟨36442181215400757818144213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24294787476933838545429475 36442181215400757818144213)
                  ·
                    refine ⟨854113622235955261362755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36442181215400757818144213 854113622235955261362755)
                    ·
                      rfl

theorem cell23_4990141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_4990141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990141 prefixEnd_4990141 := by exact prefixLift 4990141
  have htrace : WordTrace (prefixWord ++ tailWord_4990141) baseStart_4990141 baseEnd_4990141 := by
    simpa [prefixWord, tailWord_4990141, baseEnd_4990141] using wordTrace_append hprefix tailTrace_4990141
  have hstable : (prefixWord ++ tailWord_4990141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990141).length < 2 ^ (prefixWord ++ tailWord_4990141).sum := by decide
  have hdescent : baseEnd_4990141 < baseStart_4990141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990279 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_4990279 : Nat := 118140960795 + 4990279 * 2 ^ 59
def prefixEnd_4990279 : Nat := 4983230072969 + 3 ^ 40 * 4990279 * 2
def baseEnd_4990279 : Nat := 2562411727038186244162631

theorem tailTrace_4990279 : CollatzResearch.WordTrace tailWord_4990279 prefixEnd_4990279 2562411727038186244162631 := by
  unfold tailWord_4990279
  simp only [CollatzResearch.WordTrace]
  refine ⟨182010427888078929645485891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121340285258719286430323927 182010427888078929645485891)
  ·
    refine ⟨273015641832118394468228837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182010427888078929645485891 273015641832118394468228837)
    ·
      refine ⟨51190432843522198962792907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273015641832118394468228837 51190432843522198962792907)
      ·
        refine ⟨76785649265283298444189361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51190432843522198962792907 76785649265283298444189361)
        ·
          refine ⟨57589236948962473833142021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76785649265283298444189361 57589236948962473833142021)
          ·
            refine ⟨10797981927930463843714129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57589236948962473833142021 10797981927930463843714129)
            ·
              refine ⟨8098486445947847882785597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10797981927930463843714129 8098486445947847882785597)
              ·
                refine ⟨3036932417230442956044599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8098486445947847882785597 3036932417230442956044599)
                ·
                  refine ⟨4555398625845664434066899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036932417230442956044599 4555398625845664434066899)
                  ·
                    refine ⟨6833097938768496651100349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4555398625845664434066899 6833097938768496651100349)
                    ·
                      refine ⟨2562411727038186244162631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833097938768496651100349 2562411727038186244162631)
                      ·
                        rfl

theorem cell23_4990279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_4990279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990279 prefixEnd_4990279 := by exact prefixLift 4990279
  have htrace : WordTrace (prefixWord ++ tailWord_4990279) baseStart_4990279 baseEnd_4990279 := by
    simpa [prefixWord, tailWord_4990279, baseEnd_4990279] using wordTrace_append hprefix tailTrace_4990279
  have hstable : (prefixWord ++ tailWord_4990279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990279).length < 2 ^ (prefixWord ++ tailWord_4990279).sum := by decide
  have hdescent : baseEnd_4990279 < baseStart_4990279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990288 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_4990288 : Nat := 118140960795 + 4990288 * 2 ^ 59
def prefixEnd_4990288 : Nat := 4983230072969 + 3 ^ 40 * 4990288 * 2
def baseEnd_4990288 : Nat := 2562416348364076708950089

theorem tailTrace_4990288 : CollatzResearch.WordTrace tailWord_4990288 prefixEnd_4990288 2562416348364076708950089 := by
  unfold tailWord_4990288
  simp only [CollatzResearch.WordTrace]
  refine ⟨91005378072523162091281759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121340504096697549455042345 91005378072523162091281759)
  ·
    refine ⟨136508067108784743136922639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91005378072523162091281759 136508067108784743136922639)
    ·
      refine ⟨204762100663177114705383959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136508067108784743136922639 204762100663177114705383959)
      ·
        refine ⟨307143150994765672058075939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204762100663177114705383959 307143150994765672058075939)
        ·
          refine ⟨460714726492148508087113909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307143150994765672058075939 460714726492148508087113909)
          ·
            refine ⟨43192005608638922633166929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 460714726492148508087113909 43192005608638922633166929)
            ·
              refine ⟨32394004206479191974875197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43192005608638922633166929 32394004206479191974875197)
              ·
                refine ⟨12147751577429696990578199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32394004206479191974875197 12147751577429696990578199)
                ·
                  refine ⟨18221627366144545485867299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12147751577429696990578199 18221627366144545485867299)
                  ·
                    refine ⟨27332441049216818228800949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18221627366144545485867299 27332441049216818228800949)
                    ·
                      refine ⟨2562416348364076708950089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27332441049216818228800949 2562416348364076708950089)
                      ·
                        rfl

theorem cell23_4990288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_4990288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990288 prefixEnd_4990288 := by exact prefixLift 4990288
  have htrace : WordTrace (prefixWord ++ tailWord_4990288) baseStart_4990288 baseEnd_4990288 := by
    simpa [prefixWord, tailWord_4990288, baseEnd_4990288] using wordTrace_append hprefix tailTrace_4990288
  have hstable : (prefixWord ++ tailWord_4990288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990288).length < 2 ^ (prefixWord ++ tailWord_4990288).sum := by decide
  have hdescent : baseEnd_4990288 < baseStart_4990288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990291 : List Nat := [1, 1, 1, 2, 1, 1, 16]
def baseStart_4990291 : Nat := 118140960795 + 4990291 * 2 ^ 59
def prefixEnd_4990291 : Nat := 4983230072969 + 3 ^ 40 * 4990291 * 2
def baseEnd_4990291 : Nat := 31634788750691854286575

theorem tailTrace_4990291 : CollatzResearch.WordTrace tailWord_4990291 prefixEnd_4990291 31634788750691854286575 := by
  unfold tailWord_4990291
  simp only [CollatzResearch.WordTrace]
  refine ⟨182010865564035455694922727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121340577042690303796615151 182010865564035455694922727)
  ·
    refine ⟨273016298346053183542384091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182010865564035455694922727 273016298346053183542384091)
    ·
      refine ⟨409524447519079775313576137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273016298346053183542384091 409524447519079775313576137)
      ·
        refine ⟨307143335639309831485182103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409524447519079775313576137 307143335639309831485182103)
        ·
          refine ⟨460715003458964747227773155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307143335639309831485182103 460715003458964747227773155)
          ·
            refine ⟨691072505188447120841659733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460715003458964747227773155 691072505188447120841659733)
            ·
              refine ⟨31634788750691854286575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 691072505188447120841659733 31634788750691854286575)
              ·
                rfl

theorem cell23_4990291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 16].length) (baseStart_4990291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990291 prefixEnd_4990291 := by exact prefixLift 4990291
  have htrace : WordTrace (prefixWord ++ tailWord_4990291) baseStart_4990291 baseEnd_4990291 := by
    simpa [prefixWord, tailWord_4990291, baseEnd_4990291] using wordTrace_append hprefix tailTrace_4990291
  have hstable : (prefixWord ++ tailWord_4990291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990291).length < 2 ^ (prefixWord ++ tailWord_4990291).sum := by decide
  have hdescent : baseEnd_4990291 < baseStart_4990291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990295 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 4, 4]
def baseStart_4990295 : Nat := 118140960795 + 4990295 * 2 ^ 59
def prefixEnd_4990295 : Nat := 4983230072969 + 3 ^ 40 * 4990295 * 2
def baseEnd_4990295 : Nat := 854139980909552727187519

theorem tailTrace_4990295 : CollatzResearch.WordTrace tailWord_4990295 prefixEnd_4990295 854139980909552727187519 := by
  unfold tailWord_4990295
  simp only [CollatzResearch.WordTrace]
  refine ⟨182011011456020964378068339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121340674304013976252045559 182011011456020964378068339)
  ·
    refine ⟨273016517184031446567102509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182011011456020964378068339 273016517184031446567102509)
    ·
      refine ⟨102381193944011792462663441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273016517184031446567102509 102381193944011792462663441)
      ·
        refine ⟨76785895458008844346997581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102381193944011792462663441 76785895458008844346997581)
        ·
          refine ⟨28794710796753316630124093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76785895458008844346997581 28794710796753316630124093)
          ·
            refine ⟨10798016548782493736296535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28794710796753316630124093 10798016548782493736296535)
            ·
              refine ⟨16197024823173740604444803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798016548782493736296535 16197024823173740604444803)
              ·
                refine ⟨24295537234760610906667205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16197024823173740604444803 24295537234760610906667205)
                ·
                  refine ⟨4555413231517614545000101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24295537234760610906667205 4555413231517614545000101)
                  ·
                    refine ⟨854139980909552727187519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555413231517614545000101 854139980909552727187519)
                    ·
                      rfl

theorem cell23_4990295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_4990295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990295 prefixEnd_4990295 := by exact prefixLift 4990295
  have htrace : WordTrace (prefixWord ++ tailWord_4990295) baseStart_4990295 baseEnd_4990295 := by
    simpa [prefixWord, tailWord_4990295, baseEnd_4990295] using wordTrace_append hprefix tailTrace_4990295
  have hstable : (prefixWord ++ tailWord_4990295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990295).length < 2 ^ (prefixWord ++ tailWord_4990295).sum := by decide
  have hdescent : baseEnd_4990295 < baseStart_4990295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990298 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4990298 : Nat := 118140960795 + 4990298 * 2 ^ 59
def prefixEnd_4990298 : Nat := 4983230072969 + 3 ^ 40 * 4990298 * 2
def baseEnd_4990298 : Nat := 2562421483170621669825043

theorem tailTrace_4990298 : CollatzResearch.WordTrace tailWord_4990298 prefixEnd_4990298 2562421483170621669825043 := by
  unfold tailWord_4990298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502780218752523972606887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121340747250006730593618365 45502780218752523972606887)
  ·
    refine ⟨68254170328128785958910331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45502780218752523972606887 68254170328128785958910331)
    ·
      refine ⟨102381255492193178938365497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68254170328128785958910331 102381255492193178938365497)
      ·
        refine ⟨76785941619144884203774123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102381255492193178938365497 76785941619144884203774123)
        ·
          refine ⟨115178912428717326305661185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76785941619144884203774123 115178912428717326305661185)
          ·
            refine ⟨86384184321537994729245889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115178912428717326305661185 86384184321537994729245889)
            ·
              refine ⟨64788138241153496046934417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86384184321537994729245889 64788138241153496046934417)
              ·
                refine ⟨48591103680865122035200813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64788138241153496046934417 48591103680865122035200813)
                ·
                  refine ⟨18221663880324420763200305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48591103680865122035200813 18221663880324420763200305)
                  ·
                    refine ⟨13666247910243315572400229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18221663880324420763200305 13666247910243315572400229)
                    ·
                      refine ⟨2562421483170621669825043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13666247910243315572400229 2562421483170621669825043)
                      ·
                        rfl

theorem cell23_4990298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4990298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990298 prefixEnd_4990298 := by exact prefixLift 4990298
  have htrace : WordTrace (prefixWord ++ tailWord_4990298) baseStart_4990298 baseEnd_4990298 := by
    simpa [prefixWord, tailWord_4990298, baseEnd_4990298] using wordTrace_append hprefix tailTrace_4990298
  have hstable : (prefixWord ++ tailWord_4990298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990298).length < 2 ^ (prefixWord ++ tailWord_4990298).sum := by decide
  have hdescent : baseEnd_4990298 < baseStart_4990298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990312 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4990312 : Nat := 118140960795 + 4990312 * 2 ^ 59
def prefixEnd_4990312 : Nat := 4983230072969 + 3 ^ 40 * 4990312 * 2
def baseEnd_4990312 : Nat := 854142890633261538349993

theorem tailTrace_4990312 : CollatzResearch.WordTrace tailWord_4990312 prefixEnd_4990312 854142890633261538349993 := by
  unfold tailWord_4990312
  simp only [CollatzResearch.WordTrace]
  refine ⟨91005815748479688140718595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121341087664639584187624793 91005815748479688140718595)
  ·
    refine ⟨136508723622719532211077893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91005815748479688140718595 136508723622719532211077893)
    ·
      refine ⟨25595385679259912289577105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136508723622719532211077893 25595385679259912289577105)
      ·
        refine ⟨19196539259444934217182829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25595385679259912289577105 19196539259444934217182829)
        ·
          refine ⟨7198702222291850331443561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19196539259444934217182829 7198702222291850331443561)
          ·
            refine ⟨5399026666718887748582671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198702222291850331443561 5399026666718887748582671)
            ·
              refine ⟨8098540000078331622874007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399026666718887748582671 8098540000078331622874007)
              ·
                refine ⟨12147810000117497434311011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8098540000078331622874007 12147810000117497434311011)
                ·
                  refine ⟨18221715000176246151466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12147810000117497434311011 18221715000176246151466517)
                  ·
                    refine ⟨854142890633261538349993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18221715000176246151466517 854142890633261538349993)
                    ·
                      rfl

theorem cell23_4990312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4990312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990312 prefixEnd_4990312 := by exact prefixLift 4990312
  have htrace : WordTrace (prefixWord ++ tailWord_4990312) baseStart_4990312 baseEnd_4990312 := by
    simpa [prefixWord, tailWord_4990312, baseEnd_4990312] using wordTrace_append hprefix tailTrace_4990312
  have hstable : (prefixWord ++ tailWord_4990312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990312).length < 2 ^ (prefixWord ++ tailWord_4990312).sum := by decide
  have hdescent : baseEnd_4990312 < baseStart_4990312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990322 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_4990322 : Nat := 118140960795 + 4990322 * 2 ^ 59
def prefixEnd_4990322 : Nat := 4983230072969 + 3 ^ 40 * 4990322 * 2
def baseEnd_4990322 : Nat := 2562433806706329575924933

theorem tailTrace_4990322 : CollatzResearch.WordTrace tailWord_4990322 prefixEnd_4990322 2562433806706329575924933 := by
  unfold tailWord_4990322
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502999056730786997325305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121341330817948765326200813 45502999056730786997325305)
  ·
    refine ⟨34127249292548090247993979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45502999056730786997325305 34127249292548090247993979)
    ·
      refine ⟨51190873938822135371990969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34127249292548090247993979 51190873938822135371990969)
      ·
        refine ⟨38393155454116601528993227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51190873938822135371990969 38393155454116601528993227)
        ·
          refine ⟨57589733181174902293489841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38393155454116601528993227 57589733181174902293489841)
          ·
            refine ⟨43192299885881176720117381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57589733181174902293489841 43192299885881176720117381)
            ·
              refine ⟨8098556228602720635022009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43192299885881176720117381 8098556228602720635022009)
              ·
                refine ⟨6073917171452040476266507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8098556228602720635022009 6073917171452040476266507)
                ·
                  refine ⟨9110875757178060714399761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6073917171452040476266507 9110875757178060714399761)
                  ·
                    refine ⟨6833156817883545535799821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9110875757178060714399761 6833156817883545535799821)
                    ·
                      refine ⟨2562433806706329575924933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833156817883545535799821 2562433806706329575924933)
                      ·
                        rfl

theorem cell23_4990322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_4990322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990322 prefixEnd_4990322 := by exact prefixLift 4990322
  have htrace : WordTrace (prefixWord ++ tailWord_4990322) baseStart_4990322 baseEnd_4990322 := by
    simpa [prefixWord, tailWord_4990322, baseEnd_4990322] using wordTrace_append hprefix tailTrace_4990322
  have hstable : (prefixWord ++ tailWord_4990322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990322).length < 2 ^ (prefixWord ++ tailWord_4990322).sum := by decide
  have hdescent : baseEnd_4990322 < baseStart_4990322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990325 : List Nat := [1, 3, 4, 1, 3, 1, 1, 9]
def baseStart_4990325 : Nat := 118140960795 + 4990325 * 2 ^ 59
def prefixEnd_4990325 : Nat := 4983230072969 + 3 ^ 40 * 4990325 * 2
def baseEnd_4990325 : Nat := 94905012857344187562497

theorem tailTrace_4990325 : CollatzResearch.WordTrace tailWord_4990325 prefixEnd_4990325 94905012857344187562497 := by
  unfold tailWord_4990325
  simp only [CollatzResearch.WordTrace]
  refine ⟨182012105645912279501660429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121341403763941519667773619 182012105645912279501660429)
  ·
    refine ⟨68254539617217104813122661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182012105645912279501660429 68254539617217104813122661)
    ·
      refine ⟨12797726178228207152460499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68254539617217104813122661 12797726178228207152460499)
      ·
        refine ⟨19196589267342310728690749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12797726178228207152460499 19196589267342310728690749)
        ·
          refine ⟨7198720975253366523259031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19196589267342310728690749 7198720975253366523259031)
          ·
            refine ⟨10798081462880049784888547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198720975253366523259031 10798081462880049784888547)
            ·
              refine ⟨16197122194320074677332821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798081462880049784888547 16197122194320074677332821)
              ·
                refine ⟨94905012857344187562497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16197122194320074677332821 94905012857344187562497)
                ·
                  rfl

theorem cell23_4990325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 9].length) (baseStart_4990325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990325 prefixEnd_4990325 := by exact prefixLift 4990325
  have htrace : WordTrace (prefixWord ++ tailWord_4990325) baseStart_4990325 baseEnd_4990325 := by
    simpa [prefixWord, tailWord_4990325, baseEnd_4990325] using wordTrace_append hprefix tailTrace_4990325
  have hstable : (prefixWord ++ tailWord_4990325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990325).length < 2 ^ (prefixWord ++ tailWord_4990325).sum := by decide
  have hdescent : baseEnd_4990325 < baseStart_4990325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990348 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4990348 : Nat := 118140960795 + 4990348 * 2 ^ 59
def prefixEnd_4990348 : Nat := 4983230072969 + 3 ^ 40 * 4990348 * 2
def baseEnd_4990348 : Nat := 2562447157203346474199813

theorem tailTrace_4990348 : CollatzResearch.WordTrace tailWord_4990348 prefixEnd_4990348 2562447157203346474199813 := by
  unfold tailWord_4990348
  simp only [CollatzResearch.WordTrace]
  refine ⟨91006472262414477214873849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121341963016552636286498465 91006472262414477214873849)
  ·
    refine ⟨68254854196810857911155387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91006472262414477214873849 68254854196810857911155387)
    ·
      refine ⟨102382281295216286866733081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68254854196810857911155387 102382281295216286866733081)
      ·
        refine ⟨76786710971412215150049811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102382281295216286866733081 76786710971412215150049811)
        ·
          refine ⟨115180066457118322725074717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76786710971412215150049811 115180066457118322725074717)
          ·
            refine ⟨43192524921419371021903019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115180066457118322725074717 43192524921419371021903019)
            ·
              refine ⟨64788787382129056532854529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43192524921419371021903019 64788787382129056532854529)
              ·
                refine ⟨48591590536596792399640897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64788787382129056532854529 48591590536596792399640897)
                ·
                  refine ⟨36443692902447594299730673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48591590536596792399640897 36443692902447594299730673)
                  ·
                    refine ⟨27332769676835695724798005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36443692902447594299730673 27332769676835695724798005)
                    ·
                      refine ⟨2562447157203346474199813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27332769676835695724798005 2562447157203346474199813)
                      ·
                        rfl

theorem cell23_4990348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4990348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990348 prefixEnd_4990348 := by exact prefixLift 4990348
  have htrace : WordTrace (prefixWord ++ tailWord_4990348) baseStart_4990348 baseEnd_4990348 := by
    simpa [prefixWord, tailWord_4990348, baseEnd_4990348] using wordTrace_append hprefix tailTrace_4990348
  have hstable : (prefixWord ++ tailWord_4990348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990348).length < 2 ^ (prefixWord ++ tailWord_4990348).sum := by decide
  have hdescent : baseEnd_4990348 < baseStart_4990348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990362 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_4990362 : Nat := 118140960795 + 4990362 * 2 ^ 59
def prefixEnd_4990362 : Nat := 4983230072969 + 3 ^ 40 * 4990362 * 2
def baseEnd_4990362 : Nat := 2562454345932509419424749

theorem tailTrace_4990362 : CollatzResearch.WordTrace tailWord_4990362 prefixEnd_4990362 2562454345932509419424749 := by
  unfold tailWord_4990362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503363786694558705189335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121342303431185489880504893 45503363786694558705189335)
  ·
    refine ⟨68255045680041838057784003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45503363786694558705189335 68255045680041838057784003)
    ·
      refine ⟨102382568520062757086676005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68255045680041838057784003 102382568520062757086676005)
      ·
        refine ⟨19196731597511766953751751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102382568520062757086676005 19196731597511766953751751)
        ·
          refine ⟨28795097396267650430627627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19196731597511766953751751 28795097396267650430627627)
          ·
            refine ⟨43192646094401475645941441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28795097396267650430627627 43192646094401475645941441)
            ·
              refine ⟨32394484570801106734456081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43192646094401475645941441 32394484570801106734456081)
              ·
                refine ⟨24295863428100830050842061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32394484570801106734456081 24295863428100830050842061)
                ·
                  refine ⟨9110948785537811269065773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24295863428100830050842061 9110948785537811269065773)
                  ·
                    refine ⟨3416605794576679225899665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9110948785537811269065773 3416605794576679225899665)
                    ·
                      refine ⟨2562454345932509419424749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416605794576679225899665 2562454345932509419424749)
                      ·
                        rfl

theorem cell23_4990362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_4990362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990362 prefixEnd_4990362 := by exact prefixLift 4990362
  have htrace : WordTrace (prefixWord ++ tailWord_4990362) baseStart_4990362 baseEnd_4990362 := by
    simpa [prefixWord, tailWord_4990362, baseEnd_4990362] using wordTrace_append hprefix tailTrace_4990362
  have hstable : (prefixWord ++ tailWord_4990362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990362).length < 2 ^ (prefixWord ++ tailWord_4990362).sum := by decide
  have hdescent : baseEnd_4990362 < baseStart_4990362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990368 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_4990368 : Nat := 118140960795 + 4990368 * 2 ^ 59
def prefixEnd_4990368 : Nat := 4983230072969 + 3 ^ 40 * 4990368 * 2
def baseEnd_4990368 : Nat := 854152475605478798649907

theorem tailTrace_4990368 : CollatzResearch.WordTrace tailWord_4990368 prefixEnd_4990368 854152475605478798649907 := by
  unfold tailWord_4990368
  simp only [CollatzResearch.WordTrace]
  refine ⟨91006836992378248922737879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121342449323170998563650505 91006836992378248922737879)
  ·
    refine ⟨136510255488567373384106819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91006836992378248922737879 136510255488567373384106819)
    ·
      refine ⟨204765383232851060076160229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136510255488567373384106819 204765383232851060076160229)
      ·
        refine ⟨38393509356159573764280043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204765383232851060076160229 38393509356159573764280043)
        ·
          refine ⟨57590264034239360646420065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38393509356159573764280043 57590264034239360646420065)
          ·
            refine ⟨43192698025679520484815049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57590264034239360646420065 43192698025679520484815049)
            ·
              refine ⟨32394523519259640363611287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43192698025679520484815049 32394523519259640363611287)
              ·
                refine ⟨48591785278889460545416931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32394523519259640363611287 48591785278889460545416931)
                ·
                  refine ⟨72887677918334190818125397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48591785278889460545416931 72887677918334190818125397)
                  ·
                    refine ⟨854152475605478798649907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72887677918334190818125397 854152475605478798649907)
                    ·
                      rfl

theorem cell23_4990368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_4990368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990368 prefixEnd_4990368 := by exact prefixLift 4990368
  have htrace : WordTrace (prefixWord ++ tailWord_4990368) baseStart_4990368 baseEnd_4990368 := by
    simpa [prefixWord, tailWord_4990368, baseEnd_4990368] using wordTrace_append hprefix tailTrace_4990368
  have hstable : (prefixWord ++ tailWord_4990368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990368).length < 2 ^ (prefixWord ++ tailWord_4990368).sum := by decide
  have hdescent : baseEnd_4990368 < baseStart_4990368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990392 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_4990392 : Nat := 118140960795 + 4990392 * 2 ^ 59
def prefixEnd_4990392 : Nat := 4983230072969 + 3 ^ 40 * 4990392 * 2
def baseEnd_4990392 : Nat := 2562469750352144302049611

theorem tailTrace_4990392 : CollatzResearch.WordTrace tailWord_4990392 prefixEnd_4990392 2562469750352144302049611 := by
  unfold tailWord_4990392
  simp only [CollatzResearch.WordTrace]
  refine ⟨91007274668334774972174715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121343032891113033296232953 91007274668334774972174715)
  ·
    refine ⟨136510912002502162458262073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91007274668334774972174715 136510912002502162458262073)
    ·
      refine ⟨102383184001876621843696555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136510912002502162458262073 102383184001876621843696555)
      ·
        refine ⟨153574776002814932765544833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102383184001876621843696555 153574776002814932765544833)
        ·
          refine ⟨115181082002111199574158625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153574776002814932765544833 115181082002111199574158625)
          ·
            refine ⟨86385811501583399680618969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115181082002111199574158625 86385811501583399680618969)
            ·
              refine ⟨64789358626187549760464227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86385811501583399680618969 64789358626187549760464227)
              ·
                refine ⟨97184037939281324640696341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64789358626187549760464227 97184037939281324640696341)
                ·
                  refine ⟨4555501778403812092532641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97184037939281324640696341 4555501778403812092532641)
                  ·
                    refine ⟨3416626333802859069399481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555501778403812092532641 3416626333802859069399481)
                    ·
                      refine ⟨2562469750352144302049611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416626333802859069399481 2562469750352144302049611)
                      ·
                        rfl

theorem cell23_4990392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_4990392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990392 prefixEnd_4990392 := by exact prefixLift 4990392
  have htrace : WordTrace (prefixWord ++ tailWord_4990392) baseStart_4990392 baseEnd_4990392 := by
    simpa [prefixWord, tailWord_4990392, baseEnd_4990392] using wordTrace_append hprefix tailTrace_4990392
  have hstable : (prefixWord ++ tailWord_4990392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990392).length < 2 ^ (prefixWord ++ tailWord_4990392).sum := by decide
  have hdescent : baseEnd_4990392 < baseStart_4990392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990422 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4990422 : Nat := 118140960795 + 4990422 * 2 ^ 59
def prefixEnd_4990422 : Nat := 4983230072969 + 3 ^ 40 * 4990422 * 2
def baseEnd_4990422 : Nat := 2562485154771779184674473

theorem tailTrace_4990422 : CollatzResearch.WordTrace tailWord_4990422 prefixEnd_4990422 2562485154771779184674473 := by
  unfold tailWord_4990422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375977720410054066746345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121343762351040576711961013 11375977720410054066746345)
  ·
    refine ⟨8531983290307540550059759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11375977720410054066746345 8531983290307540550059759)
    ·
      refine ⟨12797974935461310825089639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8531983290307540550059759 12797974935461310825089639)
      ·
        refine ⟨19196962403191966237634459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12797974935461310825089639 19196962403191966237634459)
        ·
          refine ⟨28795443604787949356451689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19196962403191966237634459 28795443604787949356451689)
          ·
            refine ⟨21596582703590962017338767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28795443604787949356451689 21596582703590962017338767)
            ·
              refine ⟨32394874055386443026008151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21596582703590962017338767 32394874055386443026008151)
              ·
                refine ⟨48592311083079664539012227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32394874055386443026008151 48592311083079664539012227)
                ·
                  refine ⟨72888466624619496808518341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48592311083079664539012227 72888466624619496808518341)
                  ·
                    refine ⟨13666587492116155651597189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72888466624619496808518341 13666587492116155651597189)
                    ·
                      refine ⟨2562485154771779184674473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13666587492116155651597189 2562485154771779184674473)
                      ·
                        rfl

theorem cell23_4990422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4990422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990422 prefixEnd_4990422 := by exact prefixLift 4990422
  have htrace : WordTrace (prefixWord ++ tailWord_4990422) baseStart_4990422 baseEnd_4990422 := by
    simpa [prefixWord, tailWord_4990422, baseEnd_4990422] using wordTrace_append hprefix tailTrace_4990422
  have hstable : (prefixWord ++ tailWord_4990422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990422).length < 2 ^ (prefixWord ++ tailWord_4990422).sum := by decide
  have hdescent : baseEnd_4990422 < baseStart_4990422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990425 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_4990425 : Nat := 118140960795 + 4990425 * 2 ^ 59
def prefixEnd_4990425 : Nat := 4983230072969 + 3 ^ 40 * 4990425 * 2
def baseEnd_4990425 : Nat := 2562486695213742672936959

theorem tailTrace_4990425 : CollatzResearch.WordTrace tailWord_4990425 prefixEnd_4990425 2562486695213742672936959 := by
  unfold tailWord_4990425
  simp only [CollatzResearch.WordTrace]
  refine ⟨182015752945549996580300729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121343835297033331053533819 182015752945549996580300729)
  ·
    refine ⟨136511814709162497435225547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182015752945549996580300729 136511814709162497435225547)
    ·
      refine ⟨204767722063743746152838321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136511814709162497435225547 204767722063743746152838321)
      ·
        refine ⟨153575791547807809614628741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204767722063743746152838321 153575791547807809614628741)
        ·
          refine ⟨28795460915213964302742889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153575791547807809614628741 28795460915213964302742889)
          ·
            refine ⟨21596595686410473227057167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28795460915213964302742889 21596595686410473227057167)
            ·
              refine ⟨32394893529615709840585751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21596595686410473227057167 32394893529615709840585751)
              ·
                refine ⟨48592340294423564760878627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32394893529615709840585751 48592340294423564760878627)
                ·
                  refine ⟨72888510441635347141317941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48592340294423564760878627 72888510441635347141317941)
                  ·
                    refine ⟨6833297853903313794498557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72888510441635347141317941 6833297853903313794498557)
                    ·
                      refine ⟨2562486695213742672936959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833297853903313794498557 2562486695213742672936959)
                      ·
                        rfl

theorem cell23_4990425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_4990425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990425 prefixEnd_4990425 := by exact prefixLift 4990425
  have htrace : WordTrace (prefixWord ++ tailWord_4990425) baseStart_4990425 baseEnd_4990425 := by
    simpa [prefixWord, tailWord_4990425, baseEnd_4990425] using wordTrace_append hprefix tailTrace_4990425
  have hstable : (prefixWord ++ tailWord_4990425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990425).length < 2 ^ (prefixWord ++ tailWord_4990425).sum := by decide
  have hdescent : baseEnd_4990425 < baseStart_4990425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990477 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4990477 : Nat := 118140960795 + 4990477 * 2 ^ 59
def prefixEnd_4990477 : Nat := 4983230072969 + 3 ^ 40 * 4990477 * 2
def baseEnd_4990477 : Nat := 2562513396207776469486721

theorem tailTrace_4990477 : CollatzResearch.WordTrace tailWord_4990477 prefixEnd_4990477 2562513396207776469486721 := by
  unfold tailWord_4990477
  simp only [CollatzResearch.WordTrace]
  refine ⟨182017649541361609461193685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121345099694241072974129123 182017649541361609461193685)
  ·
    refine ⟨4266038661125662721746727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 182017649541361609461193685 4266038661125662721746727)
    ·
      refine ⟨6399057991688494082620091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4266038661125662721746727 6399057991688494082620091)
      ·
        refine ⟨9598586987532741123930137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6399057991688494082620091 9598586987532741123930137)
        ·
          refine ⟨7198940240649555842947603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9598586987532741123930137 7198940240649555842947603)
          ·
            refine ⟨10798410360974333764421405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198940240649555842947603 10798410360974333764421405)
            ·
              refine ⟨4049403885365375161658027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10798410360974333764421405 4049403885365375161658027)
              ·
                refine ⟨6074105828048062742487041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049403885365375161658027 6074105828048062742487041)
                ·
                  refine ⟨4555579371036047056865281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6074105828048062742487041 4555579371036047056865281)
                  ·
                    refine ⟨3416684528277035292648961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555579371036047056865281 3416684528277035292648961)
                    ·
                      refine ⟨2562513396207776469486721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416684528277035292648961 2562513396207776469486721)
                      ·
                        rfl

theorem cell23_4990477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4990477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990477 prefixEnd_4990477 := by exact prefixLift 4990477
  have htrace : WordTrace (prefixWord ++ tailWord_4990477) baseStart_4990477 baseEnd_4990477 := by
    simpa [prefixWord, tailWord_4990477, baseEnd_4990477] using wordTrace_append hprefix tailTrace_4990477
  have hstable : (prefixWord ++ tailWord_4990477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990477).length < 2 ^ (prefixWord ++ tailWord_4990477).sum := by decide
  have hdescent : baseEnd_4990477 < baseStart_4990477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990492 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4990492 : Nat := 118140960795 + 4990492 * 2 ^ 59
def prefixEnd_4990492 : Nat := 4983230072969 + 3 ^ 40 * 4990492 * 2
def baseEnd_4990492 : Nat := 854173699472531303599717

theorem tailTrace_4990492 : CollatzResearch.WordTrace tailWord_4990492 prefixEnd_4990492 854173699472531303599717 := by
  unfold tailWord_4990492
  simp only [CollatzResearch.WordTrace]
  refine ⟨91009098318153633511494865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121345464424204844681993153 91009098318153633511494865)
  ·
    refine ⟨68256823738615225133621149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91009098318153633511494865 68256823738615225133621149)
    ·
      refine ⟨25596308901980709425107931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68256823738615225133621149 25596308901980709425107931)
      ·
        refine ⟨38394463352971064137661897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25596308901980709425107931 38394463352971064137661897)
        ·
          refine ⟨28795847514728298103246423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38394463352971064137661897 28795847514728298103246423)
          ·
            refine ⟨43193771272092447154869635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28795847514728298103246423 43193771272092447154869635)
            ·
              refine ⟨64790656908138670732304453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43193771272092447154869635 64790656908138670732304453)
              ·
                refine ⟨12148248170276000762307085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64790656908138670732304453 12148248170276000762307085)
                ·
                  refine ⟨4555593063853500285865157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12148248170276000762307085 4555593063853500285865157)
                  ·
                    refine ⟨854173699472531303599717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555593063853500285865157 854173699472531303599717)
                    ·
                      rfl

theorem cell23_4990492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4990492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990492 prefixEnd_4990492 := by exact prefixLift 4990492
  have htrace : WordTrace (prefixWord ++ tailWord_4990492) baseStart_4990492 baseEnd_4990492 := by
    simpa [prefixWord, tailWord_4990492, baseEnd_4990492] using wordTrace_append hprefix tailTrace_4990492
  have hstable : (prefixWord ++ tailWord_4990492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990492).length < 2 ^ (prefixWord ++ tailWord_4990492).sum := by decide
  have hdescent : baseEnd_4990492 < baseStart_4990492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990592 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_4990592 : Nat := 118140960795 + 4990592 * 2 ^ 59
def prefixEnd_4990592 : Nat := 4983230072969 + 3 ^ 40 * 4990592 * 2
def baseEnd_4990592 : Nat := 2562572446483043519548691

theorem tailTrace_4990592 : CollatzResearch.WordTrace tailWord_4990592 prefixEnd_4990592 2562572446483043519548691 := by
  unfold tailWord_4990592
  simp only [CollatzResearch.WordTrace]
  refine ⟨91010921967972492050815015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121347895957296656067753353 91010921967972492050815015)
  ·
    refine ⟨136516382951958738076222523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91010921967972492050815015 136516382951958738076222523)
    ·
      refine ⟨204774574427938107114333785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136516382951958738076222523 204774574427938107114333785)
      ·
        refine ⟨153580930820953580335750339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204774574427938107114333785 153580930820953580335750339)
        ·
          refine ⟨230371396231430370503625509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153580930820953580335750339 230371396231430370503625509)
          ·
            refine ⟨43194636793393194469429783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230371396231430370503625509 43194636793393194469429783)
            ·
              refine ⟨64791955190089791704144675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43194636793393194469429783 64791955190089791704144675)
              ·
                refine ⟨97187932785134687556217013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64791955190089791704144675 97187932785134687556217013)
                ·
                  refine ⟨9111368698606376958395345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97187932785134687556217013 9111368698606376958395345)
                  ·
                    refine ⟨6833526523954782718796509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9111368698606376958395345 6833526523954782718796509)
                    ·
                      refine ⟨2562572446483043519548691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833526523954782718796509 2562572446483043519548691)
                      ·
                        rfl

theorem cell23_4990592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_4990592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990592 prefixEnd_4990592 := by exact prefixLift 4990592
  have htrace : WordTrace (prefixWord ++ tailWord_4990592) baseStart_4990592 baseEnd_4990592 := by
    simpa [prefixWord, tailWord_4990592, baseEnd_4990592] using wordTrace_append hprefix tailTrace_4990592
  have hstable : (prefixWord ++ tailWord_4990592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990592).length < 2 ^ (prefixWord ++ tailWord_4990592).sum := by decide
  have hdescent : baseEnd_4990592 < baseStart_4990592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990599 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 2, 4]
def baseStart_4990599 : Nat := 118140960795 + 4990599 * 2 ^ 59
def prefixEnd_4990599 : Nat := 4983230072969 + 3 ^ 40 * 4990599 * 2
def baseEnd_4990599 : Nat := 854192013615874997387053

theorem tailTrace_4990599 : CollatzResearch.WordTrace tailWord_4990599 prefixEnd_4990599 854192013615874997387053 := by
  unfold tailWord_4990599
  simp only [CollatzResearch.WordTrace]
  refine ⟨182022099246919624297134851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121348066164613082864756567 182022099246919624297134851)
  ·
    refine ⟨273033148870379436445702277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182022099246919624297134851 273033148870379436445702277)
    ·
      refine ⟨51193715413196144333569177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273033148870379436445702277 51193715413196144333569177)
      ·
        refine ⟨38395286559897108250176883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51193715413196144333569177 38395286559897108250176883)
        ·
          refine ⟨57592929839845662375265325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38395286559897108250176883 57592929839845662375265325)
          ·
            refine ⟨21597348689942123390724497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57592929839845662375265325 21597348689942123390724497)
            ·
              refine ⟨16198011517456592543043373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21597348689942123390724497 16198011517456592543043373)
              ·
                refine ⟨6074254319046222203641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16198011517456592543043373 6074254319046222203641265)
                ·
                  refine ⟨4555690739284666652730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6074254319046222203641265 4555690739284666652730949)
                  ·
                    refine ⟨854192013615874997387053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4555690739284666652730949 854192013615874997387053)
                    ·
                      rfl

theorem cell23_4990599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_4990599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990599 prefixEnd_4990599 := by exact prefixLift 4990599
  have htrace : WordTrace (prefixWord ++ tailWord_4990599) baseStart_4990599 baseEnd_4990599 := by
    simpa [prefixWord, tailWord_4990599, baseEnd_4990599] using wordTrace_append hprefix tailTrace_4990599
  have hstable : (prefixWord ++ tailWord_4990599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990599).length < 2 ^ (prefixWord ++ tailWord_4990599).sum := by decide
  have hdescent : baseEnd_4990599 < baseStart_4990599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990606 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4990606 : Nat := 118140960795 + 4990606 * 2 ^ 59
def prefixEnd_4990606 : Nat := 4983230072969 + 3 ^ 40 * 4990606 * 2
def baseEnd_4990606 : Nat := 2562579635212206464773627

theorem tailTrace_4990606 : CollatzResearch.WordTrace tailWord_4990606 prefixEnd_4990606 2562579635212206464773627 := by
  unfold tailWord_4990606
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752794319736783061579959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121348236371929509661759781 22752794319736783061579959)
  ·
    refine ⟨34129191479605174592369939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22752794319736783061579959 34129191479605174592369939)
    ·
      refine ⟨51193787219407761888554909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34129191479605174592369939 51193787219407761888554909)
      ·
        refine ⟨19197670207277910708208091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51193787219407761888554909 19197670207277910708208091)
        ·
          refine ⟨28796505310916866062312137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19197670207277910708208091 28796505310916866062312137)
          ·
            refine ⟨21597378983187649546734103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28796505310916866062312137 21597378983187649546734103)
            ·
              refine ⟨32396068474781474320101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21597378983187649546734103 32396068474781474320101155)
              ·
                refine ⟨48594102712172211480151733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32396068474781474320101155 48594102712172211480151733)
                ·
                  refine ⟨4555697129266144826264225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48594102712172211480151733 4555697129266144826264225)
                  ·
                    refine ⟨3416772846949608619698169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555697129266144826264225 3416772846949608619698169)
                    ·
                      refine ⟨2562579635212206464773627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416772846949608619698169 2562579635212206464773627)
                      ·
                        rfl

theorem cell23_4990606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4990606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990606 prefixEnd_4990606 := by exact prefixLift 4990606
  have htrace : WordTrace (prefixWord ++ tailWord_4990606) baseStart_4990606 baseEnd_4990606 := by
    simpa [prefixWord, tailWord_4990606, baseEnd_4990606] using wordTrace_append hprefix tailTrace_4990606
  have hstable : (prefixWord ++ tailWord_4990606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990606).length < 2 ^ (prefixWord ++ tailWord_4990606).sum := by decide
  have hdescent : baseEnd_4990606 < baseStart_4990606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990610 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4990610 : Nat := 118140960795 + 4990610 * 2 ^ 59
def prefixEnd_4990610 : Nat := 4983230072969 + 3 ^ 40 * 4990610 * 2
def baseEnd_4990610 : Nat := 2562581689134824449123609

theorem tailTrace_4990610 : CollatzResearch.WordTrace tailWord_4990610 prefixEnd_4990610 2562581689134824449123609 := by
  unfold tailWord_4990610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45505625112469943293946321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121348333633253182117190189 45505625112469943293946321)
  ·
    refine ⟨34129218834352457470459741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45505625112469943293946321 34129218834352457470459741)
    ·
      refine ⟨12798457062882171551422403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34129218834352457470459741 12798457062882171551422403)
      ·
        refine ⟨19197685594323257327133605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12798457062882171551422403 19197685594323257327133605)
        ·
          refine ⟨3599566048935610748837551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19197685594323257327133605 3599566048935610748837551)
          ·
            refine ⟨5399349073403416123256327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599566048935610748837551 5399349073403416123256327)
            ·
              refine ⟨8099023610105124184884491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399349073403416123256327 8099023610105124184884491)
              ·
                refine ⟨12148535415157686277326737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099023610105124184884491 12148535415157686277326737)
                ·
                  refine ⟨9111401561368264707995053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12148535415157686277326737 9111401561368264707995053)
                  ·
                    refine ⟨3416775585513099265498145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9111401561368264707995053 3416775585513099265498145)
                    ·
                      refine ⟨2562581689134824449123609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416775585513099265498145 2562581689134824449123609)
                      ·
                        rfl

theorem cell23_4990610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4990610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990610 prefixEnd_4990610 := by exact prefixLift 4990610
  have htrace : WordTrace (prefixWord ++ tailWord_4990610) baseStart_4990610 baseEnd_4990610 := by
    simpa [prefixWord, tailWord_4990610, baseEnd_4990610] using wordTrace_append hprefix tailTrace_4990610
  have hstable : (prefixWord ++ tailWord_4990610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990610).length < 2 ^ (prefixWord ++ tailWord_4990610).sum := by decide
  have hdescent : baseEnd_4990610 < baseStart_4990610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990639 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_4990639 : Nat := 118140960795 + 4990639 * 2 ^ 59
def prefixEnd_4990639 : Nat := 4983230072969 + 3 ^ 40 * 4990639 * 2
def baseEnd_4990639 : Nat := 2562596580073804835660975

theorem tailTrace_4990639 : CollatzResearch.WordTrace tailWord_4990639 prefixEnd_4990639 2562596580073804835660975 := by
  unfold tailWord_4990639
  simp only [CollatzResearch.WordTrace]
  refine ⟨182023558166774711128590971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121349038777849807419060647 182023558166774711128590971)
  ·
    refine ⟨273035337250162066692886457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182023558166774711128590971 273035337250162066692886457)
    ·
      refine ⟨204776502937621550019664843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273035337250162066692886457 204776502937621550019664843)
      ·
        refine ⟨307164754406432325029497265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204776502937621550019664843 307164754406432325029497265)
        ·
          refine ⟨230373565804824243772122949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307164754406432325029497265 230373565804824243772122949)
          ·
            refine ⟨43195043588404545707273053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230373565804824243772122949 43195043588404545707273053)
            ·
              refine ⟨16198141345651704640227395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43195043588404545707273053 16198141345651704640227395)
              ·
                refine ⟨24297212018477556960341093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16198141345651704640227395 24297212018477556960341093)
                ·
                  refine ⟨4555727253464541930063955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24297212018477556960341093 4555727253464541930063955)
                  ·
                    refine ⟨6833590880196812895095933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4555727253464541930063955 6833590880196812895095933)
                    ·
                      refine ⟨2562596580073804835660975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833590880196812895095933 2562596580073804835660975)
                      ·
                        rfl

theorem cell23_4990639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_4990639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990639 prefixEnd_4990639 := by exact prefixLift 4990639
  have htrace : WordTrace (prefixWord ++ tailWord_4990639) baseStart_4990639 baseEnd_4990639 := by
    simpa [prefixWord, tailWord_4990639, baseEnd_4990639] using wordTrace_append hprefix tailTrace_4990639
  have hstable : (prefixWord ++ tailWord_4990639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990639).length < 2 ^ (prefixWord ++ tailWord_4990639).sum := by decide
  have hdescent : baseEnd_4990639 < baseStart_4990639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990649 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4990649 : Nat := 118140960795 + 4990649 * 2 ^ 59
def prefixEnd_4990649 : Nat := 4983230072969 + 3 ^ 40 * 4990649 * 2
def baseEnd_4990649 : Nat := 2562601714880349796535929

theorem tailTrace_4990649 : CollatzResearch.WordTrace tailWord_4990649 prefixEnd_4990649 2562601714880349796535929 := by
  unfold tailWord_4990649
  simp only [CollatzResearch.WordTrace]
  refine ⟨182023922896738482836455001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121349281931158988557636667 182023922896738482836455001)
  ·
    refine ⟨136517942172553862127341251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182023922896738482836455001 136517942172553862127341251)
    ·
      refine ⟨204776913258830793191011877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136517942172553862127341251 204776913258830793191011877)
      ·
        refine ⟨38395671236030773723314727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204776913258830793191011877 38395671236030773723314727)
        ·
          refine ⟨57593506854046160584972091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38395671236030773723314727 57593506854046160584972091)
          ·
            refine ⟨86390260281069240877458137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57593506854046160584972091 86390260281069240877458137)
            ·
              refine ⟨64792695210801930658093603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86390260281069240877458137 64792695210801930658093603)
              ·
                refine ⟨97189042816202895987140405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64792695210801930658093603 97189042816202895987140405)
                ·
                  refine ⟨9111472764019021498794413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97189042816202895987140405 9111472764019021498794413)
                  ·
                    refine ⟨3416802286507133062047905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9111472764019021498794413 3416802286507133062047905)
                    ·
                      refine ⟨2562601714880349796535929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416802286507133062047905 2562601714880349796535929)
                      ·
                        rfl

theorem cell23_4990649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4990649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990649 prefixEnd_4990649 := by exact prefixLift 4990649
  have htrace : WordTrace (prefixWord ++ tailWord_4990649) baseStart_4990649 baseEnd_4990649 := by
    simpa [prefixWord, tailWord_4990649, baseEnd_4990649] using wordTrace_append hprefix tailTrace_4990649
  have hstable : (prefixWord ++ tailWord_4990649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990649).length < 2 ^ (prefixWord ++ tailWord_4990649).sum := by decide
  have hdescent : baseEnd_4990649 < baseStart_4990649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990679 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_4990679 : Nat := 118140960795 + 4990679 * 2 ^ 59
def prefixEnd_4990679 : Nat := 4983230072969 + 3 ^ 40 * 4990679 * 2
def baseEnd_4990679 : Nat := 2562617119299984679160791

theorem tailTrace_4990679 : CollatzResearch.WordTrace tailWord_4990679 prefixEnd_4990679 2562617119299984679160791 := by
  unfold tailWord_4990679
  simp only [CollatzResearch.WordTrace]
  refine ⟨182025017086629797960047091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121350011391086531973364727 182025017086629797960047091)
  ·
    refine ⟨273037525629944696940070637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182025017086629797960047091 273037525629944696940070637)
    ·
      refine ⟨102389072111229261352526489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273037525629944696940070637 102389072111229261352526489)
      ·
        refine ⟨76791804083421946014394867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102389072111229261352526489 76791804083421946014394867)
        ·
          refine ⟨115187706125132919021592301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76791804083421946014394867 115187706125132919021592301)
          ·
            refine ⟨43195389796924844633097113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115187706125132919021592301 43195389796924844633097113)
            ·
              refine ⟨32396542347693633474822835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43195389796924844633097113 32396542347693633474822835)
              ·
                refine ⟨48594813521540450212234253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32396542347693633474822835 48594813521540450212234253)
                ·
                  refine ⟨18223055070577668829587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48594813521540450212234253 18223055070577668829587845)
                  ·
                    refine ⟨3416822825733312905547721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18223055070577668829587845 3416822825733312905547721)
                    ·
                      refine ⟨2562617119299984679160791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416822825733312905547721 2562617119299984679160791)
                      ·
                        rfl

theorem cell23_4990679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_4990679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990679 prefixEnd_4990679 := by exact prefixLift 4990679
  have htrace : WordTrace (prefixWord ++ tailWord_4990679) baseStart_4990679 baseEnd_4990679 := by
    simpa [prefixWord, tailWord_4990679, baseEnd_4990679] using wordTrace_append hprefix tailTrace_4990679
  have hstable : (prefixWord ++ tailWord_4990679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990679).length < 2 ^ (prefixWord ++ tailWord_4990679).sum := by decide
  have hdescent : baseEnd_4990679 < baseStart_4990679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990682 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4990682 : Nat := 118140960795 + 4990682 * 2 ^ 59
def prefixEnd_4990682 : Nat := 4983230072969 + 3 ^ 40 * 4990682 * 2
def baseEnd_4990682 : Nat := 2562618659741948167423277

theorem tailTrace_4990682 : CollatzResearch.WordTrace tailWord_4990682 prefixEnd_4990682 2562618659741948167423277 := by
  unfold tailWord_4990682
  simp only [CollatzResearch.WordTrace]
  refine ⟨45506281626404732368101575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121350084337079286314937533 45506281626404732368101575)
  ·
    refine ⟨68259422439607098552152363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45506281626404732368101575 68259422439607098552152363)
    ·
      refine ⟨102389133659410647828228545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68259422439607098552152363 102389133659410647828228545)
      ·
        refine ⟨76791850244557985871171409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102389133659410647828228545 76791850244557985871171409)
        ·
          refine ⟨57593887683418489403378557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76791850244557985871171409 57593887683418489403378557)
          ·
            refine ⟨21597707881281933526266959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57593887683418489403378557 21597707881281933526266959)
            ·
              refine ⟨32396561821922900289400439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21597707881281933526266959 32396561821922900289400439)
              ·
                refine ⟨48594842732884350434100659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32396561821922900289400439 48594842732884350434100659)
                ·
                  refine ⟨72892264099326525651150989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48594842732884350434100659 72892264099326525651150989)
                  ·
                    refine ⟨27334599037247447119181621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72892264099326525651150989 27334599037247447119181621)
                    ·
                      refine ⟨2562618659741948167423277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27334599037247447119181621 2562618659741948167423277)
                      ·
                        rfl

theorem cell23_4990682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4990682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990682 prefixEnd_4990682 := by exact prefixLift 4990682
  have htrace : WordTrace (prefixWord ++ tailWord_4990682) baseStart_4990682 baseEnd_4990682 := by
    simpa [prefixWord, tailWord_4990682, baseEnd_4990682] using wordTrace_append hprefix tailTrace_4990682
  have hstable : (prefixWord ++ tailWord_4990682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990682).length < 2 ^ (prefixWord ++ tailWord_4990682).sum := by decide
  have hdescent : baseEnd_4990682 < baseStart_4990682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990732 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_4990732 : Nat := 118140960795 + 4990732 * 2 ^ 59
def prefixEnd_4990732 : Nat := 4983230072969 + 3 ^ 40 * 4990732 * 2
def baseEnd_4990732 : Nat := 854214777924890990599349

theorem tailTrace_4990732 : CollatzResearch.WordTrace tailWord_4990732 prefixEnd_4990732 854214777924890990599349 := by
  unfold tailWord_4990732
  simp only [CollatzResearch.WordTrace]
  refine ⟨91013475077718894005863225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121351300103625192007817633 91013475077718894005863225)
  ·
    refine ⟨68260106308289170504397419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91013475077718894005863225 68260106308289170504397419)
    ·
      refine ⟨102390159462433755756596129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68260106308289170504397419 102390159462433755756596129)
      ·
        refine ⟨76792619596825316817447097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102390159462433755756596129 76792619596825316817447097)
        ·
          refine ⟨57594464697618987613085323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76792619596825316817447097 57594464697618987613085323)
          ·
            refine ⟨86391697046428481419627985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57594464697618987613085323 86391697046428481419627985)
            ·
              refine ⟨64793772784821361064720989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86391697046428481419627985 64793772784821361064720989)
              ·
                refine ⟨24297664794308010399270371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64793772784821361064720989 24297664794308010399270371)
                ·
                  refine ⟨36446497191462015598905557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24297664794308010399270371 36446497191462015598905557)
                  ·
                    refine ⟨854214777924890990599349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36446497191462015598905557 854214777924890990599349)
                    ·
                      rfl

theorem cell23_4990732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_4990732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990732 prefixEnd_4990732 := by exact prefixLift 4990732
  have htrace : WordTrace (prefixWord ++ tailWord_4990732) baseStart_4990732 baseEnd_4990732 := by
    simpa [prefixWord, tailWord_4990732, baseEnd_4990732] using wordTrace_append hprefix tailTrace_4990732
  have hstable : (prefixWord ++ tailWord_4990732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990732).length < 2 ^ (prefixWord ++ tailWord_4990732).sum := by decide
  have hdescent : baseEnd_4990732 < baseStart_4990732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990753 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 5]
def baseStart_4990753 : Nat := 118140960795 + 4990753 * 2 ^ 59
def prefixEnd_4990753 : Nat := 4983230072969 + 3 ^ 40 * 4990753 * 2
def baseEnd_4990753 : Nat := 284739457429824154403939

theorem tailTrace_4990753 : CollatzResearch.WordTrace tailWord_4990753 prefixEnd_4990753 284739457429824154403939 := by
  unfold tailWord_4990753
  simp only [CollatzResearch.WordTrace]
  refine ⟨182027716088361708598240913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121351810725574472398827275 182027716088361708598240913)
  ·
    refine ⟨136520787066271281448680685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182027716088361708598240913 136520787066271281448680685)
    ·
      refine ⟨51195295149851730543255257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136520787066271281448680685 51195295149851730543255257)
      ·
        refine ⟨38396471362388797907441443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51195295149851730543255257 38396471362388797907441443)
        ·
          refine ⟨57594707043583196861162165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38396471362388797907441443 57594707043583196861162165)
          ·
            refine ⟨5399503785335924705733953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57594707043583196861162165 5399503785335924705733953)
            ·
              refine ⟨4049627839001943529300465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5399503785335924705733953 4049627839001943529300465)
              ·
                refine ⟨3037220879251457646975349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049627839001943529300465 3037220879251457646975349)
                ·
                  refine ⟨284739457429824154403939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3037220879251457646975349 284739457429824154403939)
                  ·
                    rfl

theorem cell23_4990753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 5].length) (baseStart_4990753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990753 prefixEnd_4990753 := by exact prefixLift 4990753
  have htrace : WordTrace (prefixWord ++ tailWord_4990753) baseStart_4990753 baseEnd_4990753 := by
    simpa [prefixWord, tailWord_4990753, baseEnd_4990753] using wordTrace_append hprefix tailTrace_4990753
  have hstable : (prefixWord ++ tailWord_4990753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990753).length < 2 ^ (prefixWord ++ tailWord_4990753).sum := by decide
  have hdescent : baseEnd_4990753 < baseStart_4990753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990756 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4990756 : Nat := 118140960795 + 4990756 * 2 ^ 59
def prefixEnd_4990756 : Nat := 4983230072969 + 3 ^ 40 * 4990756 * 2
def baseEnd_4990756 : Nat := 2562656657310380877897937

theorem tailTrace_4990756 : CollatzResearch.WordTrace tailWord_4990756 prefixEnd_4990756 2562656657310380877897937 := by
  unfold tailWord_4990756
  simp only [CollatzResearch.WordTrace]
  refine ⟨91013912753675420055300061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121351883671567226740400081 91013912753675420055300061)
  ·
    refine ⟨34130217282628282520737523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91013912753675420055300061 34130217282628282520737523)
    ·
      refine ⟨51195325923942423781106285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34130217282628282520737523 51195325923942423781106285)
      ·
        refine ⟨19198247221478408917914857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51195325923942423781106285 19198247221478408917914857)
        ·
          refine ⟨14398685416108806688436143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19198247221478408917914857 14398685416108806688436143)
          ·
            refine ⟨21598028124163210032654215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14398685416108806688436143 21598028124163210032654215)
            ·
              refine ⟨32397042186244815048981323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21598028124163210032654215 32397042186244815048981323)
              ·
                refine ⟨48595563279367222573471985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32397042186244815048981323 48595563279367222573471985)
                ·
                  refine ⟨36446672459525416930103989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48595563279367222573471985 36446672459525416930103989)
                  ·
                    refine ⟨3416875543080507837197249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36446672459525416930103989 3416875543080507837197249)
                    ·
                      refine ⟨2562656657310380877897937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3416875543080507837197249 2562656657310380877897937)
                      ·
                        rfl

theorem cell23_4990756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4990756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990756 prefixEnd_4990756 := by exact prefixLift 4990756
  have htrace : WordTrace (prefixWord ++ tailWord_4990756) baseStart_4990756 baseEnd_4990756 := by
    simpa [prefixWord, tailWord_4990756, baseEnd_4990756] using wordTrace_append hprefix tailTrace_4990756
  have hstable : (prefixWord ++ tailWord_4990756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990756).length < 2 ^ (prefixWord ++ tailWord_4990756).sum := by decide
  have hdescent : baseEnd_4990756 < baseStart_4990756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990783 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 2, 5]
def baseStart_4990783 : Nat := 118140960795 + 4990783 * 2 ^ 59
def prefixEnd_4990783 : Nat := 4983230072969 + 3 ^ 40 * 4990783 * 2
def baseEnd_4990783 : Nat := 854223507096017424086771

theorem tailTrace_4990783 : CollatzResearch.WordTrace tailWord_4990783 prefixEnd_4990783 854223507096017424086771 := by
  unfold tailWord_4990783
  simp only [CollatzResearch.WordTrace]
  refine ⟨182028810278253023721833003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121352540185502015814555335 182028810278253023721833003)
  ·
    refine ⟨273043215417379535582749505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182028810278253023721833003 273043215417379535582749505)
    ·
      refine ⟨204782411563034651687062129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273043215417379535582749505 204782411563034651687062129)
      ·
        refine ⟨153586808672275988765296597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204782411563034651687062129 153586808672275988765296597)
        ·
          refine ⟨3599690828256468486686639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 153586808672275988765296597 3599690828256468486686639)
          ·
            refine ⟨5399536242384702730029959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599690828256468486686639 5399536242384702730029959)
            ·
              refine ⟨8099304363577054095044939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399536242384702730029959 8099304363577054095044939)
              ·
                refine ⟨12148956545365581142567409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099304363577054095044939 12148956545365581142567409)
                ·
                  refine ⟨9111717409024185856925557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12148956545365581142567409 9111717409024185856925557)
                  ·
                    refine ⟨854223507096017424086771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9111717409024185856925557 854223507096017424086771)
                    ·
                      rfl

theorem cell23_4990783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_4990783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990783 prefixEnd_4990783 := by exact prefixLift 4990783
  have htrace : WordTrace (prefixWord ++ tailWord_4990783) baseStart_4990783 baseEnd_4990783 := by
    simpa [prefixWord, tailWord_4990783, baseEnd_4990783] using wordTrace_append hprefix tailTrace_4990783
  have hstable : (prefixWord ++ tailWord_4990783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990783).length < 2 ^ (prefixWord ++ tailWord_4990783).sum := by decide
  have hdescent : baseEnd_4990783 < baseStart_4990783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990789 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_4990789 : Nat := 118140960795 + 4990789 * 2 ^ 59
def prefixEnd_4990789 : Nat := 4983230072969 + 3 ^ 40 * 4990789 * 2
def baseEnd_4990789 : Nat := 2562673602171979248785285

theorem tailTrace_4990789 : CollatzResearch.WordTrace tailWord_4990789 prefixEnd_4990789 2562673602171979248785285 := by
  unfold tailWord_4990789
  simp only [CollatzResearch.WordTrace]
  refine ⟨182029029116231286746551421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121352686077487524497700947 182029029116231286746551421)
  ·
    refine ⟨68260885918586732529956783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182029029116231286746551421 68260885918586732529956783)
    ·
      refine ⟨102391328877880098794935175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68260885918586732529956783 102391328877880098794935175)
      ·
        refine ⟨153586993316820148192402763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102391328877880098794935175 153586993316820148192402763)
        ·
          refine ⟨230380489975230222288604145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153586993316820148192402763 230380489975230222288604145)
          ·
            refine ⟨172785367481422666716453109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230380489975230222288604145 172785367481422666716453109)
            ·
              refine ⟨16198628201383375004667479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172785367481422666716453109 16198628201383375004667479)
              ·
                refine ⟨24297942302075062507001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16198628201383375004667479 24297942302075062507001219)
                ·
                  refine ⟨36446913453112593760501829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24297942302075062507001219 36446913453112593760501829)
                  ·
                    refine ⟨6833796272458611330094093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36446913453112593760501829 6833796272458611330094093)
                    ·
                      refine ⟨2562673602171979248785285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833796272458611330094093 2562673602171979248785285)
                      ·
                        rfl

theorem cell23_4990789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_4990789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990789 prefixEnd_4990789 := by exact prefixLift 4990789
  have htrace : WordTrace (prefixWord ++ tailWord_4990789) baseStart_4990789 baseEnd_4990789 := by
    simpa [prefixWord, tailWord_4990789, baseEnd_4990789] using wordTrace_append hprefix tailTrace_4990789
  have hstable : (prefixWord ++ tailWord_4990789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990789).length < 2 ^ (prefixWord ++ tailWord_4990789).sum := by decide
  have hdescent : baseEnd_4990789 < baseStart_4990789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990859 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4]
def baseStart_4990859 : Nat := 118140960795 + 4990859 * 2 ^ 59
def prefixEnd_4990859 : Nat := 4983230072969 + 3 ^ 40 * 4990859 * 2
def baseEnd_4990859 : Nat := 2562709545817793974909963

theorem tailTrace_4990859 : CollatzResearch.WordTrace tailWord_4990859 prefixEnd_4990859 2562709545817793974909963 := by
  unfold tailWord_4990859
  simp only [CollatzResearch.WordTrace]
  refine ⟨182031582225977688701599631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121354388150651792467733087 182031582225977688701599631)
  ·
    refine ⟨273047373338966533052399447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182031582225977688701599631 273047373338966533052399447)
    ·
      refine ⟨409571060008449799578599171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273047373338966533052399447 409571060008449799578599171)
      ·
        refine ⟨614356590012674699367898757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409571060008449799578599171 614356590012674699367898757)
        ·
          refine ⟨115191860627376506131481017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614356590012674699367898757 115191860627376506131481017)
          ·
            refine ⟨86393895470532379598610763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115191860627376506131481017 86393895470532379598610763)
            ·
              refine ⟨129590843205798569397916145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86393895470532379598610763 129590843205798569397916145)
              ·
                refine ⟨97193132404348927048437109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129590843205798569397916145 97193132404348927048437109)
                ·
                  refine ⟨9111856162907711910790979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97193132404348927048437109 9111856162907711910790979)
                  ·
                    refine ⟨13667784244361567866186469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9111856162907711910790979 13667784244361567866186469)
                    ·
                      refine ⟨2562709545817793974909963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13667784244361567866186469 2562709545817793974909963)
                      ·
                        rfl

theorem cell23_4990859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_4990859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990859 prefixEnd_4990859 := by exact prefixLift 4990859
  have htrace : WordTrace (prefixWord ++ tailWord_4990859) baseStart_4990859 baseEnd_4990859 := by
    simpa [prefixWord, tailWord_4990859, baseEnd_4990859] using wordTrace_append hprefix tailTrace_4990859
  have hstable : (prefixWord ++ tailWord_4990859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990859).length < 2 ^ (prefixWord ++ tailWord_4990859).sum := by decide
  have hdescent : baseEnd_4990859 < baseStart_4990859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990910 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_4990910 : Nat := 118140960795 + 4990910 * 2 ^ 59
def prefixEnd_4990910 : Nat := 4983230072969 + 3 ^ 40 * 4990910 * 2
def baseEnd_4990910 : Nat := 2562735733331173275372229

theorem tailTrace_4990910 : CollatzResearch.WordTrace tailWord_4990910 prefixEnd_4990910 2562735733331173275372229 := by
  unfold tailWord_4990910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22754180293599115551463273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121355628232528616274470789 22754180293599115551463273)
  ·
    refine ⟨17065635220199336663597455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22754180293599115551463273 17065635220199336663597455)
    ·
      refine ⟨25598452830299004995396183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17065635220199336663597455 25598452830299004995396183)
      ·
        refine ⟨38397679245448507493094275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25598452830299004995396183 38397679245448507493094275)
        ·
          refine ⟨57596518868172761239641413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38397679245448507493094275 57596518868172761239641413)
          ·
            refine ⟨10799347287782392732432765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57596518868172761239641413 10799347287782392732432765)
            ·
              refine ⟨4049755232918397274662287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10799347287782392732432765 4049755232918397274662287)
              ·
                refine ⟨6074632849377595911993431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049755232918397274662287 6074632849377595911993431)
                ·
                  refine ⟨9111949274066393867990147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6074632849377595911993431 9111949274066393867990147)
                  ·
                    refine ⟨13667923911099590801985221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9111949274066393867990147 13667923911099590801985221)
                    ·
                      refine ⟨2562735733331173275372229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13667923911099590801985221 2562735733331173275372229)
                      ·
                        rfl

theorem cell23_4990910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_4990910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990910 prefixEnd_4990910 := by exact prefixLift 4990910
  have htrace : WordTrace (prefixWord ++ tailWord_4990910) baseStart_4990910 baseEnd_4990910 := by
    simpa [prefixWord, tailWord_4990910, baseEnd_4990910] using wordTrace_append hprefix tailTrace_4990910
  have hstable : (prefixWord ++ tailWord_4990910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990910).length < 2 ^ (prefixWord ++ tailWord_4990910).sum := by decide
  have hdescent : baseEnd_4990910 < baseStart_4990910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990926 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_4990926 : Nat := 118140960795 + 4990926 * 2 ^ 59
def prefixEnd_4990926 : Nat := 4983230072969 + 3 ^ 40 * 4990926 * 2
def baseEnd_4990926 : Nat := 2562743949021645212772155

theorem tailTrace_4990926 : CollatzResearch.WordTrace tailWord_4990926 prefixEnd_4990926 2562743949021645212772155 := by
  unfold tailWord_4990926
  simp only [CollatzResearch.WordTrace]
  refine ⟨22754253239591869893036079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121356017277823306096192421 22754253239591869893036079)
  ·
    refine ⟨34131379859387804839554119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22754253239591869893036079 34131379859387804839554119)
    ·
      refine ⟨51197069789081707259331179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34131379859387804839554119 51197069789081707259331179)
      ·
        refine ⟨76795604683622560888996769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51197069789081707259331179 76795604683622560888996769)
        ·
          refine ⟨57596703512716920666747577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76795604683622560888996769 57596703512716920666747577)
          ·
            refine ⟨43197527634537690500060683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57596703512716920666747577 43197527634537690500060683)
            ·
              refine ⟨64796291451806535750091025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43197527634537690500060683 64796291451806535750091025)
              ·
                refine ⟨48597218588854901812568269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64796291451806535750091025 48597218588854901812568269)
                ·
                  refine ⟨18223956970820588179713101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48597218588854901812568269 18223956970820588179713101)
                  ·
                    refine ⟨6833983864057720567392413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18223956970820588179713101 6833983864057720567392413)
                    ·
                      refine ⟨2562743949021645212772155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6833983864057720567392413 2562743949021645212772155)
                      ·
                        rfl

theorem cell23_4990926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_4990926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990926 prefixEnd_4990926 := by exact prefixLift 4990926
  have htrace : WordTrace (prefixWord ++ tailWord_4990926) baseStart_4990926 baseEnd_4990926 := by
    simpa [prefixWord, tailWord_4990926, baseEnd_4990926] using wordTrace_append hprefix tailTrace_4990926
  have hstable : (prefixWord ++ tailWord_4990926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990926).length < 2 ^ (prefixWord ++ tailWord_4990926).sum := by decide
  have hdescent : baseEnd_4990926 < baseStart_4990926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990943 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_4990943 : Nat := 118140960795 + 4990943 * 2 ^ 59
def prefixEnd_4990943 : Nat := 4983230072969 + 3 ^ 40 * 4990943 * 2
def baseEnd_4990943 : Nat := 2562752678192771646259577

theorem tailTrace_4990943 : CollatzResearch.WordTrace tailWord_4990943 prefixEnd_4990943 2562752678192771646259577 := by
  unfold tailWord_4990943
  simp only [CollatzResearch.WordTrace]
  refine ⟨182034645957673371047657483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121356430638448914031771655 182034645957673371047657483)
  ·
    refine ⟨273051968936510056571486225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182034645957673371047657483 273051968936510056571486225)
    ·
      refine ⟨204788976702382542428614669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273051968936510056571486225 204788976702382542428614669)
      ·
        refine ⟨76795866263393453410730501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204788976702382542428614669 76795866263393453410730501)
        ·
          refine ⟨14399224924386272514511969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76795866263393453410730501 14399224924386272514511969)
          ·
            refine ⟨10799418693289704385883977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14399224924386272514511969 10799418693289704385883977)
            ·
              refine ⟨8099564019967278289412983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10799418693289704385883977 8099564019967278289412983)
              ·
                refine ⟨12149346029950917434119475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099564019967278289412983 12149346029950917434119475)
                ·
                  refine ⟨18224019044926376151179213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12149346029950917434119475 18224019044926376151179213)
                  ·
                    refine ⟨6834007141847391056692205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18224019044926376151179213 6834007141847391056692205)
                    ·
                      refine ⟨2562752678192771646259577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834007141847391056692205 2562752678192771646259577)
                      ·
                        rfl

theorem cell23_4990943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_4990943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990943 prefixEnd_4990943 := by exact prefixLift 4990943
  have htrace : WordTrace (prefixWord ++ tailWord_4990943) baseStart_4990943 baseEnd_4990943 := by
    simpa [prefixWord, tailWord_4990943, baseEnd_4990943] using wordTrace_append hprefix tailTrace_4990943
  have hstable : (prefixWord ++ tailWord_4990943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990943).length < 2 ^ (prefixWord ++ tailWord_4990943).sum := by decide
  have hdescent : baseEnd_4990943 < baseStart_4990943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4990959 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 8]
def baseStart_4990959 : Nat := 118140960795 + 4990959 * 2 ^ 59
def prefixEnd_4990959 : Nat := 4983230072969 + 3 ^ 40 * 4990959 * 2
def baseEnd_4990959 : Nat := 854253631294414527886501

theorem tailTrace_4990959 : CollatzResearch.WordTrace tailWord_4990959 prefixEnd_4990959 854253631294414527886501 := by
  unfold tailWord_4990959
  simp only [CollatzResearch.WordTrace]
  refine ⟨182035229525615405780239931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121356819683743603853493287 182035229525615405780239931)
  ·
    refine ⟨273052844288423108670359897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182035229525615405780239931 273052844288423108670359897)
    ·
      refine ⟨204789633216317331502769923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273052844288423108670359897 204789633216317331502769923)
      ·
        refine ⟨307184449824475997254154885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204789633216317331502769923 307184449824475997254154885)
        ·
          refine ⟨57597084342089249485154041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307184449824475997254154885 57597084342089249485154041)
          ·
            refine ⟨43197813256566937113865531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57597084342089249485154041 43197813256566937113865531)
            ·
              refine ⟨64796719884850405670798297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43197813256566937113865531 64796719884850405670798297)
              ·
                refine ⟨48597539913637804253098723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64796719884850405670798297 48597539913637804253098723)
                ·
                  refine ⟨72896309870456706379648085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48597539913637804253098723 72896309870456706379648085)
                  ·
                    refine ⟨854253631294414527886501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72896309870456706379648085 854253631294414527886501)
                    ·
                      rfl

theorem cell23_4990959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_4990959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4990959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4990959 prefixEnd_4990959 := by exact prefixLift 4990959
  have htrace : WordTrace (prefixWord ++ tailWord_4990959) baseStart_4990959 baseEnd_4990959 := by
    simpa [prefixWord, tailWord_4990959, baseEnd_4990959] using wordTrace_append hprefix tailTrace_4990959
  have hstable : (prefixWord ++ tailWord_4990959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4990959).length < 2 ^ (prefixWord ++ tailWord_4990959).sum := by decide
  have hdescent : baseEnd_4990959 < baseStart_4990959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4990959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991040 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 5]
def baseStart_4991040 : Nat := 118140960795 + 4991040 * 2 ^ 59
def prefixEnd_4991040 : Nat := 4983230072969 + 3 ^ 40 * 4991040 * 2
def baseEnd_4991040 : Nat := 284755831757361974082959

theorem tailTrace_4991040 : CollatzResearch.WordTrace tailWord_4991040 prefixEnd_4991040 284755831757361974082959 := by
  unfold tailWord_4991040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91019091919160978306969287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121358789225547971075959049 91019091919160978306969287)
  ·
    refine ⟨136528637878741467460453931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91019091919160978306969287 136528637878741467460453931)
    ·
      refine ⟨204792956818112201190680897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136528637878741467460453931 204792956818112201190680897)
      ·
        refine ⟨153594717613584150893010673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204792956818112201190680897 153594717613584150893010673)
        ·
          refine ⟨115196038210188113169758005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153594717613584150893010673 115196038210188113169758005)
          ·
            refine ⟨10799628582205135609664813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115196038210188113169758005 10799628582205135609664813)
            ·
              refine ⟨4049860718326925853624305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10799628582205135609664813 4049860718326925853624305)
              ·
                refine ⟨3037395538745194390218229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049860718326925853624305 3037395538745194390218229)
                ·
                  refine ⟨284755831757361974082959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3037395538745194390218229 284755831757361974082959)
                  ·
                    rfl

theorem cell23_4991040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 5].length) (baseStart_4991040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991040 prefixEnd_4991040 := by exact prefixLift 4991040
  have htrace : WordTrace (prefixWord ++ tailWord_4991040) baseStart_4991040 baseEnd_4991040 := by
    simpa [prefixWord, tailWord_4991040, baseEnd_4991040] using wordTrace_append hprefix tailTrace_4991040
  have hstable : (prefixWord ++ tailWord_4991040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991040).length < 2 ^ (prefixWord ++ tailWord_4991040).sum := by decide
  have hdescent : baseEnd_4991040 < baseStart_4991040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991053 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4991053 : Nat := 118140960795 + 4991053 * 2 ^ 59
def prefixEnd_4991053 : Nat := 4983230072969 + 3 ^ 40 * 4991053 * 2
def baseEnd_4991053 : Nat := 854269720354922071961357

theorem tailTrace_4991053 : CollatzResearch.WordTrace tailWord_4991053 prefixEnd_4991053 854269720354922071961357 := by
  unfold tailWord_4991053
  simp only [CollatzResearch.WordTrace]
  refine ⟨182038657987274859834161813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121359105324849906556107875 182038657987274859834161813)
  ·
    refine ⟨8533062093153509054726335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182038657987274859834161813 8533062093153509054726335)
    ·
      refine ⟨12799593139730263582089503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8533062093153509054726335 12799593139730263582089503)
      ·
        refine ⟨19199389709595395373134255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12799593139730263582089503 19199389709595395373134255)
        ·
          refine ⟨28799084564393093059701383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19199389709595395373134255 28799084564393093059701383)
          ·
            refine ⟨43198626846589639589552075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28799084564393093059701383 43198626846589639589552075)
            ·
              refine ⟨64797940269884459384328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43198626846589639589552075 64797940269884459384328113)
              ·
                refine ⟨48598455202413344538246085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64797940269884459384328113 48598455202413344538246085)
                ·
                  refine ⟨9112210350452502100921141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48598455202413344538246085 9112210350452502100921141)
                  ·
                    refine ⟨854269720354922071961357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9112210350452502100921141 854269720354922071961357)
                    ·
                      rfl

theorem cell23_4991053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4991053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991053 prefixEnd_4991053 := by exact prefixLift 4991053
  have htrace : WordTrace (prefixWord ++ tailWord_4991053) baseStart_4991053 baseEnd_4991053 := by
    simpa [prefixWord, tailWord_4991053, baseEnd_4991053] using wordTrace_append hprefix tailTrace_4991053
  have hstable : (prefixWord ++ tailWord_4991053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991053).length < 2 ^ (prefixWord ++ tailWord_4991053).sum := by decide
  have hdescent : baseEnd_4991053 < baseStart_4991053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4991073 : Nat := 118140960795 + 4991073 * 2 ^ 59
def prefixEnd_4991073 : Nat := 4983230072969 + 3 ^ 40 * 4991073 * 2
def baseEnd_4991073 : Nat := 2562819430677856137633979

theorem tailTrace_4991073 : CollatzResearch.WordTrace tailWord_4991073 prefixEnd_4991073 2562819430677856137633979 := by
  unfold tailWord_4991073
  simp only [CollatzResearch.WordTrace]
  refine ⟨182039387447202403249889873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121359591631468268833259915 182039387447202403249889873)
  ·
    refine ⟨136529540585401802437417405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182039387447202403249889873 136529540585401802437417405)
    ·
      refine ⟨51198577719525675914031527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136529540585401802437417405 51198577719525675914031527)
      ·
        refine ⟨76797866579288513871047291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51198577719525675914031527 76797866579288513871047291)
        ·
          refine ⟨115196799868932770806570937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76797866579288513871047291 115196799868932770806570937)
          ·
            refine ⟨86397599901699578104928203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115196799868932770806570937 86397599901699578104928203)
            ·
              refine ⟨129596399852549367157392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86397599901699578104928203 129596399852549367157392305)
              ·
                refine ⟨97197299889412025368044229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129596399852549367157392305 97197299889412025368044229)
                ·
                  refine ⟨18224493729264754756508293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97197299889412025368044229 18224493729264754756508293)
                  ·
                    refine ⟨3417092574237141516845305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18224493729264754756508293 3417092574237141516845305)
                    ·
                      refine ⟨2562819430677856137633979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417092574237141516845305 2562819430677856137633979)
                      ·
                        rfl

theorem cell23_4991073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4991073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991073 prefixEnd_4991073 := by exact prefixLift 4991073
  have htrace : WordTrace (prefixWord ++ tailWord_4991073) baseStart_4991073 baseEnd_4991073 := by
    simpa [prefixWord, tailWord_4991073, baseEnd_4991073] using wordTrace_append hprefix tailTrace_4991073
  have hstable : (prefixWord ++ tailWord_4991073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991073).length < 2 ^ (prefixWord ++ tailWord_4991073).sum := by decide
  have hdescent : baseEnd_4991073 < baseStart_4991073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991124 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4991124 : Nat := 118140960795 + 4991124 * 2 ^ 59
def prefixEnd_4991124 : Nat := 4983230072969 + 3 ^ 40 * 4991124 * 2
def baseEnd_4991124 : Nat := 2562845618191235438096245

theorem tailTrace_4991124 : CollatzResearch.WordTrace tailWord_4991124 prefixEnd_4991124 2562845618191235438096245 := by
  unfold tailWord_4991124
  simp only [CollatzResearch.WordTrace]
  refine ⟨91020623785008819479998213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121360831713345092639997617 91020623785008819479998213)
  ·
    refine ⟨17066366959689153652499665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91020623785008819479998213 17066366959689153652499665)
    ·
      refine ⟨12799775219766865239374749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17066366959689153652499665 12799775219766865239374749)
      ·
        refine ⟨4799915707412574464765531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12799775219766865239374749 4799915707412574464765531)
        ·
          refine ⟨7199873561118861697148297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799915707412574464765531 7199873561118861697148297)
          ·
            refine ⟨5399905170839146272861223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199873561118861697148297 5399905170839146272861223)
            ·
              refine ⟨8099857756258719409291835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399905170839146272861223 8099857756258719409291835)
              ·
                refine ⟨12149786634388079113937753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099857756258719409291835 12149786634388079113937753)
                ·
                  refine ⟨9112339975791059335453315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12149786634388079113937753 9112339975791059335453315)
                  ·
                    refine ⟨13668509963686589003179973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9112339975791059335453315 13668509963686589003179973)
                    ·
                      refine ⟨2562845618191235438096245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13668509963686589003179973 2562845618191235438096245)
                      ·
                        rfl

theorem cell23_4991124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4991124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991124 prefixEnd_4991124 := by exact prefixLift 4991124
  have htrace : WordTrace (prefixWord ++ tailWord_4991124) baseStart_4991124 baseEnd_4991124 := by
    simpa [prefixWord, tailWord_4991124, baseEnd_4991124] using wordTrace_append hprefix tailTrace_4991124
  have hstable : (prefixWord ++ tailWord_4991124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991124).length < 2 ^ (prefixWord ++ tailWord_4991124).sum := by decide
  have hdescent : baseEnd_4991124 < baseStart_4991124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991127 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4991127 : Nat := 118140960795 + 4991127 * 2 ^ 59
def prefixEnd_4991127 : Nat := 4983230072969 + 3 ^ 40 * 4991127 * 2
def baseEnd_4991127 : Nat := 2562847158633198926358731

theorem tailTrace_4991127 : CollatzResearch.WordTrace tailWord_4991127 prefixEnd_4991127 2562847158633198926358731 := by
  unfold tailWord_4991127
  simp only [CollatzResearch.WordTrace]
  refine ⟨182041356989006770472355635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121360904659337846981570423 182041356989006770472355635)
  ·
    refine ⟨273062035483510155708533453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182041356989006770472355635 273062035483510155708533453)
    ·
      refine ⟨102398263306316308390700045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273062035483510155708533453 102398263306316308390700045)
      ·
        refine ⟨38399348739868615646512517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102398263306316308390700045 38399348739868615646512517)
        ·
          refine ⟨7199877888725365433721097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38399348739868615646512517 7199877888725365433721097)
          ·
            refine ⟨5399908416544024075290823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199877888725365433721097 5399908416544024075290823)
            ·
              refine ⟨8099862624816036112936235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399908416544024075290823 8099862624816036112936235)
              ·
                refine ⟨12149793937224054169404353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099862624816036112936235 12149793937224054169404353)
                ·
                  refine ⟨9112345452918040627053265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12149793937224054169404353 9112345452918040627053265)
                  ·
                    refine ⟨6834259089688530470289949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9112345452918040627053265 6834259089688530470289949)
                    ·
                      refine ⟨2562847158633198926358731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834259089688530470289949 2562847158633198926358731)
                      ·
                        rfl

theorem cell23_4991127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4991127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991127 prefixEnd_4991127 := by exact prefixLift 4991127
  have htrace : WordTrace (prefixWord ++ tailWord_4991127) baseStart_4991127 baseEnd_4991127 := by
    simpa [prefixWord, tailWord_4991127, baseEnd_4991127] using wordTrace_append hprefix tailTrace_4991127
  have hstable : (prefixWord ++ tailWord_4991127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991127).length < 2 ^ (prefixWord ++ tailWord_4991127).sum := by decide
  have hdescent : baseEnd_4991127 < baseStart_4991127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991173 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_4991173 : Nat := 118140960795 + 4991173 * 2 ^ 59
def prefixEnd_4991173 : Nat := 4983230072969 + 3 ^ 40 * 4991173 * 2
def baseEnd_4991173 : Nat := 854290259581101915461173

theorem tailTrace_4991173 : CollatzResearch.WordTrace tailWord_4991173 prefixEnd_4991173 854290259581101915461173 := by
  unfold tailWord_4991173
  simp only [CollatzResearch.WordTrace]
  refine ⟨182043034746840120328530173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121362023164560080219020115 182043034746840120328530173)
  ·
    refine ⟨68266138030065045123198815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182043034746840120328530173 68266138030065045123198815)
    ·
      refine ⟨102399207045097567684798223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68266138030065045123198815 102399207045097567684798223)
      ·
        refine ⟨153598810567646351527197335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102399207045097567684798223 153598810567646351527197335)
        ·
          refine ⟨230398215851469527290796003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153598810567646351527197335 230398215851469527290796003)
          ·
            refine ⟨345597323777204290936194005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230398215851469527290796003 345597323777204290936194005)
            ·
              refine ⟨8099937276028225568817047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 345597323777204290936194005 8099937276028225568817047)
              ·
                refine ⟨12149905914042338353225571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099937276028225568817047 12149905914042338353225571)
                ·
                  refine ⟨18224858871063507529838357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12149905914042338353225571 18224858871063507529838357)
                  ·
                    refine ⟨854290259581101915461173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18224858871063507529838357 854290259581101915461173)
                    ·
                      rfl

theorem cell23_4991173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_4991173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991173 prefixEnd_4991173 := by exact prefixLift 4991173
  have htrace : WordTrace (prefixWord ++ tailWord_4991173) baseStart_4991173 baseEnd_4991173 := by
    simpa [prefixWord, tailWord_4991173, baseEnd_4991173] using wordTrace_append hprefix tailTrace_4991173
  have hstable : (prefixWord ++ tailWord_4991173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991173).length < 2 ^ (prefixWord ++ tailWord_4991173).sum := by decide
  have hdescent : baseEnd_4991173 < baseStart_4991173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991193 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_4991193 : Nat := 118140960795 + 4991193 * 2 ^ 59
def prefixEnd_4991193 : Nat := 4983230072969 + 3 ^ 40 * 4991193 * 2
def baseEnd_4991193 : Nat := 2562881048356395668133427

theorem tailTrace_4991193 : CollatzResearch.WordTrace tailWord_4991193 prefixEnd_4991193 2562881048356395668133427 := by
  unfold tailWord_4991193
  simp only [CollatzResearch.WordTrace]
  refine ⟨182043764206767663744258233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121362509471178442496172155 182043764206767663744258233)
  ·
    refine ⟨136532823155075747808193675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182043764206767663744258233 136532823155075747808193675)
    ·
      refine ⟨204799234732613621712290513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136532823155075747808193675 204799234732613621712290513)
      ·
        refine ⟨153599426049460216284217885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204799234732613621712290513 153599426049460216284217885)
        ·
          refine ⟨57599784768547581106581707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153599426049460216284217885 57599784768547581106581707)
          ·
            refine ⟨86399677152821371659872561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57599784768547581106581707 86399677152821371659872561)
            ·
              refine ⟨64799757864616028744904421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86399677152821371659872561 64799757864616028744904421)
              ·
                refine ⟨12149954599615505389669579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64799757864616028744904421 12149954599615505389669579)
                ·
                  refine ⟨18224931899423258084504369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12149954599615505389669579 18224931899423258084504369)
                  ·
                    refine ⟨13668698924567443563378277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18224931899423258084504369 13668698924567443563378277)
                    ·
                      refine ⟨2562881048356395668133427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13668698924567443563378277 2562881048356395668133427)
                      ·
                        rfl

theorem cell23_4991193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_4991193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991193 prefixEnd_4991193 := by exact prefixLift 4991193
  have htrace : WordTrace (prefixWord ++ tailWord_4991193) baseStart_4991193 baseEnd_4991193 := by
    simpa [prefixWord, tailWord_4991193, baseEnd_4991193] using wordTrace_append hprefix tailTrace_4991193
  have hstable : (prefixWord ++ tailWord_4991193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991193).length < 2 ^ (prefixWord ++ tailWord_4991193).sum := by decide
  have hdescent : baseEnd_4991193 < baseStart_4991193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991197 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4991197 : Nat := 118140960795 + 4991197 * 2 ^ 59
def prefixEnd_4991197 : Nat := 4983230072969 + 3 ^ 40 * 4991197 * 2
def baseEnd_4991197 : Nat := 2562883102279013652483409

theorem tailTrace_4991197 : CollatzResearch.WordTrace tailWord_4991197 prefixEnd_4991197 2562883102279013652483409 := by
  unfold tailWord_4991197
  simp only [CollatzResearch.WordTrace]
  refine ⟨182043910098753172427403845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121362606732502114951602563 182043910098753172427403845)
  ·
    refine ⟨34133233143516219830138221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182043910098753172427403845 34133233143516219830138221)
    ·
      refine ⟨12799962428818582436301833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34133233143516219830138221 12799962428818582436301833)
      ·
        refine ⟨9599971821613936827226375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12799962428818582436301833 9599971821613936827226375)
        ·
          refine ⟨14399957732420905240839563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9599971821613936827226375 14399957732420905240839563)
          ·
            refine ⟨21599936598631357861259345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14399957732420905240839563 21599936598631357861259345)
            ·
              refine ⟨16199952448973518395944509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21599936598631357861259345 16199952448973518395944509)
              ·
                refine ⟨6074982168365069398479191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16199952448973518395944509 6074982168365069398479191)
                ·
                  refine ⟨9112473252547604097718787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6074982168365069398479191 9112473252547604097718787)
                  ·
                    refine ⟨13668709878821406146578181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9112473252547604097718787 13668709878821406146578181)
                    ·
                      refine ⟨2562883102279013652483409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13668709878821406146578181 2562883102279013652483409)
                      ·
                        rfl

theorem cell23_4991197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4991197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991197 prefixEnd_4991197 := by exact prefixLift 4991197
  have htrace : WordTrace (prefixWord ++ tailWord_4991197) baseStart_4991197 baseEnd_4991197 := by
    simpa [prefixWord, tailWord_4991197, baseEnd_4991197] using wordTrace_append hprefix tailTrace_4991197
  have hstable : (prefixWord ++ tailWord_4991197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991197).length < 2 ^ (prefixWord ++ tailWord_4991197).sum := by decide
  have hdescent : baseEnd_4991197 < baseStart_4991197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991200 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_4991200 : Nat := 118140960795 + 4991200 * 2 ^ 59
def prefixEnd_4991200 : Nat := 4983230072969 + 3 ^ 40 * 4991200 * 2
def baseEnd_4991200 : Nat := 2562884642720977140745895

theorem tailTrace_4991200 : CollatzResearch.WordTrace tailWord_4991200 prefixEnd_4991200 2562884642720977140745895 := by
  unfold tailWord_4991200
  simp only [CollatzResearch.WordTrace]
  refine ⟨91022009758871151969881527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121362679678494869293175369 91022009758871151969881527)
  ·
    refine ⟨136533014638306727954822291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91022009758871151969881527 136533014638306727954822291)
    ·
      refine ⟨204799521957460091932233437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136533014638306727954822291 204799521957460091932233437)
      ·
        refine ⟨76799820734047534474587539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204799521957460091932233437 76799820734047534474587539)
        ·
          refine ⟨115199731101071301711881309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76799820734047534474587539 115199731101071301711881309)
          ·
            refine ⟨43199899162901738141955491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115199731101071301711881309 43199899162901738141955491)
            ·
              refine ⟨64799848744352607212933237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43199899162901738141955491 64799848744352607212933237)
              ·
                refine ⟨6074985819783056926212491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64799848744352607212933237 6074985819783056926212491)
                ·
                  refine ⟨9112478729674585389318737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6074985819783056926212491 9112478729674585389318737)
                  ·
                    refine ⟨6834359047255939041989053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9112478729674585389318737 6834359047255939041989053)
                    ·
                      refine ⟨2562884642720977140745895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834359047255939041989053 2562884642720977140745895)
                      ·
                        rfl

theorem cell23_4991200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_4991200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991200 prefixEnd_4991200 := by exact prefixLift 4991200
  have htrace : WordTrace (prefixWord ++ tailWord_4991200) baseStart_4991200 baseEnd_4991200 := by
    simpa [prefixWord, tailWord_4991200, baseEnd_4991200] using wordTrace_append hprefix tailTrace_4991200
  have hstable : (prefixWord ++ tailWord_4991200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991200).length < 2 ^ (prefixWord ++ tailWord_4991200).sum := by decide
  have hdescent : baseEnd_4991200 < baseStart_4991200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991234 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_4991234 : Nat := 118140960795 + 4991234 * 2 ^ 59
def prefixEnd_4991234 : Nat := 4983230072969 + 3 ^ 40 * 4991234 * 2
def baseEnd_4991234 : Nat := 2562902101063230007720739

theorem tailTrace_4991234 : CollatzResearch.WordTrace tailWord_4991234 prefixEnd_4991234 2562902101063230007720739 := by
  unfold tailWord_4991234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511314899904781936625189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121363506399746085164333837 45511314899904781936625189)
  ·
    refine ⟨8533371543732146613117223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45511314899904781936625189 8533371543732146613117223)
    ·
      refine ⟨12800057315598219919675835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8533371543732146613117223 12800057315598219919675835)
      ·
        refine ⟨19200085973397329879513753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12800057315598219919675835 19200085973397329879513753)
        ·
          refine ⟨14400064480047997409635315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19200085973397329879513753 14400064480047997409635315)
          ·
            refine ⟨21600096720071996114452973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14400064480047997409635315 21600096720071996114452973)
            ·
              refine ⟨8100036270026998542919865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21600096720071996114452973 8100036270026998542919865)
              ·
                refine ⟨6075027202520248907189899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8100036270026998542919865 6075027202520248907189899)
                ·
                  refine ⟨9112540803780373360784849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6075027202520248907189899 9112540803780373360784849)
                  ·
                    refine ⟨6834405602835280020588637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9112540803780373360784849 6834405602835280020588637)
                    ·
                      refine ⟨2562902101063230007720739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834405602835280020588637 2562902101063230007720739)
                      ·
                        rfl

theorem cell23_4991234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_4991234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991234 prefixEnd_4991234 := by exact prefixLift 4991234
  have htrace : WordTrace (prefixWord ++ tailWord_4991234) baseStart_4991234 baseEnd_4991234 := by
    simpa [prefixWord, tailWord_4991234, baseEnd_4991234] using wordTrace_append hprefix tailTrace_4991234
  have hstable : (prefixWord ++ tailWord_4991234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991234).length < 2 ^ (prefixWord ++ tailWord_4991234).sum := by decide
  have hdescent : baseEnd_4991234 < baseStart_4991234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991264 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4991264 : Nat := 118140960795 + 4991264 * 2 ^ 59
def prefixEnd_4991264 : Nat := 4983230072969 + 3 ^ 40 * 4991264 * 2
def baseEnd_4991264 : Nat := 2562917505482864890345601

theorem tailTrace_4991264 : CollatzResearch.WordTrace tailWord_4991264 prefixEnd_4991264 2562917505482864890345601 := by
  unfold tailWord_4991264
  simp only [CollatzResearch.WordTrace]
  refine ⟨91023176894755221435046423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121364235859673628580061897 91023176894755221435046423)
  ·
    refine ⟨136534765342132832152569635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91023176894755221435046423 136534765342132832152569635)
    ·
      refine ⟨204802148013199248228854453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136534765342132832152569635 204802148013199248228854453)
      ·
        refine ⟨19200201376237429521455105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204802148013199248228854453 19200201376237429521455105)
        ·
          refine ⟨14400151032178072141091329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19200201376237429521455105 14400151032178072141091329)
          ·
            refine ⟨10800113274133554105818497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14400151032178072141091329 10800113274133554105818497)
            ·
              refine ⟨8100084955600165579363873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10800113274133554105818497 8100084955600165579363873)
              ·
                refine ⟨6075063716700124184522905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8100084955600165579363873 6075063716700124184522905)
                ·
                  refine ⟨4556297787525093138392179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6075063716700124184522905 4556297787525093138392179)
                  ·
                    refine ⟨6834446681287639707588269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4556297787525093138392179 6834446681287639707588269)
                    ·
                      refine ⟨2562917505482864890345601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834446681287639707588269 2562917505482864890345601)
                      ·
                        rfl

theorem cell23_4991264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4991264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991264 prefixEnd_4991264 := by exact prefixLift 4991264
  have htrace : WordTrace (prefixWord ++ tailWord_4991264) baseStart_4991264 baseEnd_4991264 := by
    simpa [prefixWord, tailWord_4991264, baseEnd_4991264] using wordTrace_append hprefix tailTrace_4991264
  have hstable : (prefixWord ++ tailWord_4991264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991264).length < 2 ^ (prefixWord ++ tailWord_4991264).sum := by decide
  have hdescent : baseEnd_4991264 < baseStart_4991264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991271 : List Nat := [1, 1, 8, 1, 2, 1, 1, 8]
def baseStart_4991271 : Nat := 118140960795 + 4991271 * 2 ^ 59
def prefixEnd_4991271 : Nat := 4983230072969 + 3 ^ 40 * 4991271 * 2
def baseEnd_4991271 : Nat := 94923003698053568998447

theorem tailTrace_4991271 : CollatzResearch.WordTrace tailWord_4991271 prefixEnd_4991271 94923003698053568998447 := by
  unfold tailWord_4991271
  simp only [CollatzResearch.WordTrace]
  refine ⟨182046609100485083065597667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121364406066990055377065111 182046609100485083065597667)
  ·
    refine ⟨273069913650727624598396501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182046609100485083065597667 273069913650727624598396501)
    ·
      refine ⟨3200038050594464350762459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 273069913650727624598396501 3200038050594464350762459)
      ·
        refine ⟨4800057075891696526143689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200038050594464350762459 4800057075891696526143689)
        ·
          refine ⟨3600042806918772394607767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4800057075891696526143689 3600042806918772394607767)
          ·
            refine ⟨5400064210378158591911651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600042806918772394607767 5400064210378158591911651)
            ·
              refine ⟨8100096315567237887867477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400064210378158591911651 8100096315567237887867477)
              ·
                refine ⟨94923003698053568998447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8100096315567237887867477 94923003698053568998447)
                ·
                  rfl

theorem cell23_4991271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 8].length) (baseStart_4991271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991271 prefixEnd_4991271 := by exact prefixLift 4991271
  have htrace : WordTrace (prefixWord ++ tailWord_4991271) baseStart_4991271 baseEnd_4991271 := by
    simpa [prefixWord, tailWord_4991271, baseEnd_4991271] using wordTrace_append hprefix tailTrace_4991271
  have hstable : (prefixWord ++ tailWord_4991271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991271).length < 2 ^ (prefixWord ++ tailWord_4991271).sum := by decide
  have hdescent : baseEnd_4991271 < baseStart_4991271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991338 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4991338 : Nat := 118140960795 + 4991338 * 2 ^ 59
def prefixEnd_4991338 : Nat := 4983230072969 + 3 ^ 40 * 4991338 * 2
def baseEnd_4991338 : Nat := 2562955503051297600820261

theorem tailTrace_4991338 : CollatzResearch.WordTrace tailWord_4991338 prefixEnd_4991338 2562955503051297600820261 := by
  unfold tailWord_4991338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45512263197810588377071667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121366035194161569005524445 45512263197810588377071667)
  ·
    refine ⟨68268394796715882565607501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45512263197810588377071667 68268394796715882565607501)
    ·
      refine ⟨25600648048768455962102813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68268394796715882565607501 25600648048768455962102813)
      ·
        refine ⟨9600243018288170985788555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25600648048768455962102813 9600243018288170985788555)
        ·
          refine ⟨14400364527432256478682833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9600243018288170985788555 14400364527432256478682833)
          ·
            refine ⟨10800273395574192359012125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14400364527432256478682833 10800273395574192359012125)
            ·
              refine ⟨4050102523340322134629547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10800273395574192359012125 4050102523340322134629547)
              ·
                refine ⟨6075153785010483201944321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050102523340322134629547 6075153785010483201944321)
                ·
                  refine ⟨4556365338757862401458241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6075153785010483201944321 4556365338757862401458241)
                  ·
                    refine ⟨3417274004068396801093681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4556365338757862401458241 3417274004068396801093681)
                    ·
                      refine ⟨2562955503051297600820261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417274004068396801093681 2562955503051297600820261)
                      ·
                        rfl

theorem cell23_4991338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4991338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991338 prefixEnd_4991338 := by exact prefixLift 4991338
  have htrace : WordTrace (prefixWord ++ tailWord_4991338) baseStart_4991338 baseEnd_4991338 := by
    simpa [prefixWord, tailWord_4991338, baseEnd_4991338] using wordTrace_append hprefix tailTrace_4991338
  have hstable : (prefixWord ++ tailWord_4991338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991338).length < 2 ^ (prefixWord ++ tailWord_4991338).sum := by decide
  have hdescent : baseEnd_4991338 < baseStart_4991338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991353 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_4991353 : Nat := 118140960795 + 4991353 * 2 ^ 59
def prefixEnd_4991353 : Nat := 4983230072969 + 3 ^ 40 * 4991353 * 2
def baseEnd_4991353 : Nat := 854321068420371680710897

theorem tailTrace_4991353 : CollatzResearch.WordTrace tailWord_4991353 prefixEnd_4991353 854321068420371680710897 := by
  unfold tailWord_4991353
  simp only [CollatzResearch.WordTrace]
  refine ⟨182049599886188011070082713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121366399924125340713388475 182049599886188011070082713)
  ·
    refine ⟨136537199914641008302562035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182049599886188011070082713 136537199914641008302562035)
    ·
      refine ⟨204805799871961512453843053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136537199914641008302562035 204805799871961512453843053)
      ·
        refine ⟨76802174951985567170191145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204805799871961512453843053 76802174951985567170191145)
        ·
          refine ⟨57601631213989175377643359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76802174951985567170191145 57601631213989175377643359)
          ·
            refine ⟨86402446820983763066465039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57601631213989175377643359 86402446820983763066465039)
            ·
              refine ⟨129603670231475644599697559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86402446820983763066465039 129603670231475644599697559)
              ·
                refine ⟨194405505347213466899546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129603670231475644599697559 194405505347213466899546339)
                ·
                  refine ⟨291608258020820200349319509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194405505347213466899546339 291608258020820200349319509)
                  ·
                    refine ⟨854321068420371680710897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 291608258020820200349319509 854321068420371680710897)
                    ·
                      rfl

theorem cell23_4991353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_4991353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991353 prefixEnd_4991353 := by exact prefixLift 4991353
  have htrace : WordTrace (prefixWord ++ tailWord_4991353) baseStart_4991353 baseEnd_4991353 := by
    simpa [prefixWord, tailWord_4991353, baseEnd_4991353] using wordTrace_append hprefix tailTrace_4991353
  have hstable : (prefixWord ++ tailWord_4991353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991353).length < 2 ^ (prefixWord ++ tailWord_4991353).sum := by decide
  have hdescent : baseEnd_4991353 < baseStart_4991353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991461 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4991461 : Nat := 118140960795 + 4991461 * 2 ^ 59
def prefixEnd_4991461 : Nat := 4983230072969 + 3 ^ 40 * 4991461 * 2
def baseEnd_4991461 : Nat := 2563018661171800619582195

theorem tailTrace_4991461 : CollatzResearch.WordTrace tailWord_4991461 prefixEnd_4991461 2563018661171800619582195 := by
  unfold tailWord_4991461
  simp only [CollatzResearch.WordTrace]
  refine ⟨182053538969796745515014237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121369025979864497010009491 182053538969796745515014237)
  ·
    refine ⟨68270077113673779568130339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182053538969796745515014237 68270077113673779568130339)
    ·
      refine ⟨102405115670510669352195509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68270077113673779568130339 102405115670510669352195509)
      ·
        refine ⟨9600479594110375251768329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102405115670510669352195509 9600479594110375251768329)
        ·
          refine ⟨7200359695582781438826247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9600479594110375251768329 7200359695582781438826247)
          ·
            refine ⟨10800539543374172158239371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200359695582781438826247 10800539543374172158239371)
            ·
              refine ⟨16200809315061258237359057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10800539543374172158239371 16200809315061258237359057)
              ·
                refine ⟨12150606986295943678019293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16200809315061258237359057 12150606986295943678019293)
                ·
                  refine ⟨4556477619860978879257235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12150606986295943678019293 4556477619860978879257235)
                  ·
                    refine ⟨6834716429791468318885853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4556477619860978879257235 6834716429791468318885853)
                    ·
                      refine ⟨2563018661171800619582195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834716429791468318885853 2563018661171800619582195)
                      ·
                        rfl

theorem cell23_4991461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4991461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991461 prefixEnd_4991461 := by exact prefixLift 4991461
  have htrace : WordTrace (prefixWord ++ tailWord_4991461) baseStart_4991461 baseEnd_4991461 := by
    simpa [prefixWord, tailWord_4991461, baseEnd_4991461] using wordTrace_append hprefix tailTrace_4991461
  have hstable : (prefixWord ++ tailWord_4991461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991461).length < 2 ^ (prefixWord ++ tailWord_4991461).sum := by decide
  have hdescent : baseEnd_4991461 < baseStart_4991461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991467 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 4]
def baseStart_4991467 : Nat := 118140960795 + 4991467 * 2 ^ 59
def prefixEnd_4991467 : Nat := 4983230072969 + 3 ^ 40 * 4991467 * 2
def baseEnd_4991467 : Nat := 2563021742055727596107167

theorem tailTrace_4991467 : CollatzResearch.WordTrace tailWord_4991467 prefixEnd_4991467 2563021742055727596107167 := by
  unfold tailWord_4991467
  simp only [CollatzResearch.WordTrace]
  refine ⟨182053757807775008539732655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121369171871850005693155103 182053757807775008539732655)
  ·
    refine ⟨273080636711662512809598983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182053757807775008539732655 273080636711662512809598983)
    ·
      refine ⟨409620955067493769214398475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273080636711662512809598983 409620955067493769214398475)
      ·
        refine ⟨614431432601240653821597713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409620955067493769214398475 614431432601240653821597713)
        ·
          refine ⟨460823574450930490366198285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614431432601240653821597713 460823574450930490366198285)
          ·
            refine ⟨172808840419098933887324357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460823574450930490366198285 172808840419098933887324357)
            ·
              refine ⟨32401657578581050103873317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172808840419098933887324357 32401657578581050103873317)
              ·
                refine ⟨6075310795983946894476247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32401657578581050103873317 6075310795983946894476247)
                ·
                  refine ⟨9112966193975920341714371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6075310795983946894476247 9112966193975920341714371)
                  ·
                    refine ⟨13669449290963880512571557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9112966193975920341714371 13669449290963880512571557)
                    ·
                      refine ⟨2563021742055727596107167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13669449290963880512571557 2563021742055727596107167)
                      ·
                        rfl

theorem cell23_4991467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 4].length) (baseStart_4991467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991467 prefixEnd_4991467 := by exact prefixLift 4991467
  have htrace : WordTrace (prefixWord ++ tailWord_4991467) baseStart_4991467 baseEnd_4991467 := by
    simpa [prefixWord, tailWord_4991467, baseEnd_4991467] using wordTrace_append hprefix tailTrace_4991467
  have hstable : (prefixWord ++ tailWord_4991467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991467).length < 2 ^ (prefixWord ++ tailWord_4991467).sum := by decide
  have hdescent : baseEnd_4991467 < baseStart_4991467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991478 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4991478 : Nat := 118140960795 + 4991478 * 2 ^ 59
def prefixEnd_4991478 : Nat := 4983230072969 + 3 ^ 40 * 4991478 * 2
def baseEnd_4991478 : Nat := 2563027390342927053069617

theorem tailTrace_4991478 : CollatzResearch.WordTrace tailWord_4991478 prefixEnd_4991478 2563027390342927053069617 := by
  unfold tailWord_4991478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378384938170947338648943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121369439340490104945588725 11378384938170947338648943)
  ·
    refine ⟨17067577407256421007973415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11378384938170947338648943 17067577407256421007973415)
    ·
      refine ⟨25601366110884631511960123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17067577407256421007973415 25601366110884631511960123)
      ·
        refine ⟨38402049166326947267940185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25601366110884631511960123 38402049166326947267940185)
        ·
          refine ⟨28801536874745210450955139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38402049166326947267940185 28801536874745210450955139)
          ·
            refine ⟨43202305312117815676432709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28801536874745210450955139 43202305312117815676432709)
            ·
              refine ⟨8100432246022090439331133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43202305312117815676432709 8100432246022090439331133)
              ·
                refine ⟨3037662092258283914749175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8100432246022090439331133 3037662092258283914749175)
                ·
                  refine ⟨4556493138387425872123763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037662092258283914749175 4556493138387425872123763)
                  ·
                    refine ⟨6834739707581138808185645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4556493138387425872123763 6834739707581138808185645)
                    ·
                      refine ⟨2563027390342927053069617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6834739707581138808185645 2563027390342927053069617)
                      ·
                        rfl

theorem cell23_4991478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4991478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991478 prefixEnd_4991478 := by exact prefixLift 4991478
  have htrace : WordTrace (prefixWord ++ tailWord_4991478) baseStart_4991478 baseEnd_4991478 := by
    simpa [prefixWord, tailWord_4991478, baseEnd_4991478] using wordTrace_append hprefix tailTrace_4991478
  have hstable : (prefixWord ++ tailWord_4991478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991478).length < 2 ^ (prefixWord ++ tailWord_4991478).sum := by decide
  have hdescent : baseEnd_4991478 < baseStart_4991478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991484 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_4991484 : Nat := 118140960795 + 4991484 * 2 ^ 59
def prefixEnd_4991484 : Nat := 4983230072969 + 3 ^ 40 * 4991484 * 2
def baseEnd_4991484 : Nat := 2563030471226854029594589

theorem tailTrace_4991484 : CollatzResearch.WordTrace tailWord_4991484 prefixEnd_4991484 2563030471226854029594589 := by
  unfold tailWord_4991484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91027188924356710221550753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121369585232475613628734337 91027188924356710221550753)
  ·
    refine ⟨68270391693267532666163065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91027188924356710221550753 68270391693267532666163065)
    ·
      refine ⟨51202793769950649499622299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68270391693267532666163065 51202793769950649499622299)
      ·
        refine ⟨76804190654925974249433449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51202793769950649499622299 76804190654925974249433449)
        ·
          refine ⟨57603142991194480687075087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76804190654925974249433449 57603142991194480687075087)
          ·
            refine ⟨86404714486791721030612631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57603142991194480687075087 86404714486791721030612631)
            ·
              refine ⟨129607071730187581545918947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86404714486791721030612631 129607071730187581545918947)
              ·
                refine ⟨194410607595281372318878421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129607071730187581545918947 194410607595281372318878421)
                ·
                  refine ⟨4556498615514407163723713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 194410607595281372318878421 4556498615514407163723713)
                  ·
                    refine ⟨3417373961635805372792785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4556498615514407163723713 3417373961635805372792785)
                    ·
                      refine ⟨2563030471226854029594589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417373961635805372792785 2563030471226854029594589)
                      ·
                        rfl

theorem cell23_4991484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_4991484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991484 prefixEnd_4991484 := by exact prefixLift 4991484
  have htrace : WordTrace (prefixWord ++ tailWord_4991484) baseStart_4991484 baseEnd_4991484 := by
    simpa [prefixWord, tailWord_4991484, baseEnd_4991484] using wordTrace_append hprefix tailTrace_4991484
  have hstable : (prefixWord ++ tailWord_4991484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991484).length < 2 ^ (prefixWord ++ tailWord_4991484).sum := by decide
  have hdescent : baseEnd_4991484 < baseStart_4991484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991511 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 6]
def baseStart_4991511 : Nat := 118140960795 + 4991511 * 2 ^ 59
def prefixEnd_4991511 : Nat := 4983230072969 + 3 ^ 40 * 4991511 * 2
def baseEnd_4991511 : Nat := 854348111734841807985655

theorem tailTrace_4991511 : CollatzResearch.WordTrace tailWord_4991511 prefixEnd_4991511 854348111734841807985655 := by
  unfold tailWord_4991511
  simp only [CollatzResearch.WordTrace]
  refine ⟨182055362619615604054334387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121370241746410402702889591 182055362619615604054334387)
  ·
    refine ⟨273083043929423406081501581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182055362619615604054334387 273083043929423406081501581)
    ·
      refine ⟨102406141473533777280563093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273083043929423406081501581 102406141473533777280563093)
      ·
        refine ⟨4800287881571895810026395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102406141473533777280563093 4800287881571895810026395)
        ·
          refine ⟨7200431822357843715039593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800287881571895810026395 7200431822357843715039593)
          ·
            refine ⟨5400323866768382786279695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7200431822357843715039593 5400323866768382786279695)
            ·
              refine ⟨8100485800152574179419543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400323866768382786279695 8100485800152574179419543)
              ·
                refine ⟨12150728700228861269129315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100485800152574179419543 12150728700228861269129315)
                ·
                  refine ⟨18226093050343291903693973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12150728700228861269129315 18226093050343291903693973)
                  ·
                    refine ⟨854348111734841807985655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18226093050343291903693973 854348111734841807985655)
                    ·
                      rfl

theorem cell23_4991511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_4991511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991511 prefixEnd_4991511 := by exact prefixLift 4991511
  have htrace : WordTrace (prefixWord ++ tailWord_4991511) baseStart_4991511 baseEnd_4991511 := by
    simpa [prefixWord, tailWord_4991511, baseEnd_4991511] using wordTrace_append hprefix tailTrace_4991511
  have hstable : (prefixWord ++ tailWord_4991511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991511).length < 2 ^ (prefixWord ++ tailWord_4991511).sum := by decide
  have hdescent : baseEnd_4991511 < baseStart_4991511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991524 : List Nat := [2, 3, 1, 5, 1, 1, 1, 9]
def baseStart_4991524 : Nat := 118140960795 + 4991524 * 2 ^ 59
def prefixEnd_4991524 : Nat := 4983230072969 + 3 ^ 40 * 4991524 * 2
def baseEnd_4991524 : Nat := 94927815201964217522015

theorem tailTrace_4991524 : CollatzResearch.WordTrace tailWord_4991524 prefixEnd_4991524 94927815201964217522015 := by
  unfold tailWord_4991524
  simp only [CollatzResearch.WordTrace]
  refine ⟨91027918384284253637278813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121370557845712338183038417 91027918384284253637278813)
  ·
    refine ⟨34135469394106595113979555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91027918384284253637278813 34135469394106595113979555)
    ·
      refine ⟨51203204091159892670969333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34135469394106595113979555 51203204091159892670969333)
      ·
        refine ⟨4800300383546239937903375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51203204091159892670969333 4800300383546239937903375)
        ·
          refine ⟨7200450575319359906855063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800300383546239937903375 7200450575319359906855063)
          ·
            refine ⟨10800675862979039860282595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200450575319359906855063 10800675862979039860282595)
            ·
              refine ⟨16201013794468559790423893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10800675862979039860282595 16201013794468559790423893)
              ·
                refine ⟨94927815201964217522015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16201013794468559790423893 94927815201964217522015)
                ·
                  rfl

theorem cell23_4991524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 9].length) (baseStart_4991524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991524 prefixEnd_4991524 := by exact prefixLift 4991524
  have htrace : WordTrace (prefixWord ++ tailWord_4991524) baseStart_4991524 baseEnd_4991524 := by
    simpa [prefixWord, tailWord_4991524, baseEnd_4991524] using wordTrace_append hprefix tailTrace_4991524
  have hstable : (prefixWord ++ tailWord_4991524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991524).length < 2 ^ (prefixWord ++ tailWord_4991524).sum := by decide
  have hdescent : baseEnd_4991524 < baseStart_4991524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991644 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4991644 : Nat := 118140960795 + 4991644 * 2 ^ 59
def prefixEnd_4991644 : Nat := 4983230072969 + 3 ^ 40 * 4991644 * 2
def baseEnd_4991644 : Nat := 854370876043857801197951

theorem tailTrace_4991644 : CollatzResearch.WordTrace tailWord_4991644 prefixEnd_4991644 854370876043857801197951 := by
  unfold tailWord_4991644
  simp only [CollatzResearch.WordTrace]
  refine ⟨91030106764066883884462993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121373475685422511845950657 91030106764066883884462993)
  ·
    refine ⟨68272580073050162913347245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91030106764066883884462993 68272580073050162913347245)
    ·
      refine ⟨25602217527393811092505217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68272580073050162913347245 25602217527393811092505217)
      ·
        refine ⟨19201663145545358319378913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25602217527393811092505217 19201663145545358319378913)
        ·
          refine ⟨14401247359159018739534185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19201663145545358319378913 14401247359159018739534185)
          ·
            refine ⟨10800935519369264054650639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14401247359159018739534185 10800935519369264054650639)
            ·
              refine ⟨16201403279053896081975959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10800935519369264054650639 16201403279053896081975959)
              ·
                refine ⟨24302104918580844122963939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16201403279053896081975959 24302104918580844122963939)
                ·
                  refine ⟨36453157377871266184445909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24302104918580844122963939 36453157377871266184445909)
                  ·
                    refine ⟨854370876043857801197951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36453157377871266184445909 854370876043857801197951)
                    ·
                      rfl

theorem cell23_4991644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4991644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991644 prefixEnd_4991644 := by exact prefixLift 4991644
  have htrace : WordTrace (prefixWord ++ tailWord_4991644) baseStart_4991644 baseEnd_4991644 := by
    simpa [prefixWord, tailWord_4991644, baseEnd_4991644] using wordTrace_append hprefix tailTrace_4991644
  have hstable : (prefixWord ++ tailWord_4991644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991644).length < 2 ^ (prefixWord ++ tailWord_4991644).sum := by decide
  have hdescent : baseEnd_4991644 < baseStart_4991644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991725 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_4991725 : Nat := 118140960795 + 4991725 * 2 ^ 59
def prefixEnd_4991725 : Nat := 4983230072969 + 3 ^ 40 * 4991725 * 2
def baseEnd_4991725 : Nat := 854384740021529195560327

theorem tailTrace_4991725 : CollatzResearch.WordTrace tailWord_4991725 prefixEnd_4991725 854384740021529195560327 := by
  unfold tailWord_4991725
  simp only [CollatzResearch.WordTrace]
  refine ⟨182063167840840318602624629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121375445227226879068416419 182063167840840318602624629)
  ·
    refine ⟨17068421985078779868996059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182063167840840318602624629 17068421985078779868996059)
    ·
      refine ⟨25602632977618169803494089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17068421985078779868996059 25602632977618169803494089)
      ·
        refine ⟨19201974733213627352620567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25602632977618169803494089 19201974733213627352620567)
        ·
          refine ⟨28802962099820441028930851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19201974733213627352620567 28802962099820441028930851)
          ·
            refine ⟨43204443149730661543396277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28802962099820441028930851 43204443149730661543396277)
            ·
              refine ⟨4050416545287249519693401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43204443149730661543396277 4050416545287249519693401)
              ·
                refine ⟨3037812408965437139770051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050416545287249519693401 3037812408965437139770051)
                ·
                  refine ⟨4556718613448155709655077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037812408965437139770051 4556718613448155709655077)
                  ·
                    refine ⟨854384740021529195560327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556718613448155709655077 854384740021529195560327)
                    ·
                      rfl

theorem cell23_4991725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_4991725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991725 prefixEnd_4991725 := by exact prefixLift 4991725
  have htrace : WordTrace (prefixWord ++ tailWord_4991725) baseStart_4991725 baseEnd_4991725 := by
    simpa [prefixWord, tailWord_4991725, baseEnd_4991725] using wordTrace_append hprefix tailTrace_4991725
  have hstable : (prefixWord ++ tailWord_4991725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991725).length < 2 ^ (prefixWord ++ tailWord_4991725).sum := by decide
  have hdescent : baseEnd_4991725 < baseStart_4991725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991741 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_4991741 : Nat := 118140960795 + 4991741 * 2 ^ 59
def prefixEnd_4991741 : Nat := 4983230072969 + 3 ^ 40 * 4991741 * 2
def baseEnd_4991741 : Nat := 2563162435755059524080907

theorem tailTrace_4991741 : CollatzResearch.WordTrace tailWord_4991741 prefixEnd_4991741 2563162435755059524080907 := by
  unfold tailWord_4991741
  simp only [CollatzResearch.WordTrace]
  refine ⟨182063751408782353335207077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121375834272521568890138051 182063751408782353335207077)
  ·
    refine ⟨34136953389146691250351327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182063751408782353335207077 34136953389146691250351327)
    ·
      refine ⟨51205430083720036875526991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34136953389146691250351327 51205430083720036875526991)
      ·
        refine ⟨76808145125580055313290487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51205430083720036875526991 76808145125580055313290487)
        ·
          refine ⟨115212217688370082969935731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76808145125580055313290487 115212217688370082969935731)
          ·
            refine ⟨172818326532555124454903597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115212217688370082969935731 172818326532555124454903597)
            ·
              refine ⟨64806872449708171670588849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172818326532555124454903597 64806872449708171670588849)
              ·
                refine ⟨48605154337281128752941637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64806872449708171670588849 48605154337281128752941637)
                ·
                  refine ⟨9113466438240211641176557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48605154337281128752941637 9113466438240211641176557)
                  ·
                    refine ⟨3417549914340079365441209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9113466438240211641176557 3417549914340079365441209)
                    ·
                      refine ⟨2563162435755059524080907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417549914340079365441209 2563162435755059524080907)
                      ·
                        rfl

theorem cell23_4991741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_4991741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991741 prefixEnd_4991741 := by exact prefixLift 4991741
  have htrace : WordTrace (prefixWord ++ tailWord_4991741) baseStart_4991741 baseEnd_4991741 := by
    simpa [prefixWord, tailWord_4991741, baseEnd_4991741] using wordTrace_append hprefix tailTrace_4991741
  have hstable : (prefixWord ++ tailWord_4991741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991741).length < 2 ^ (prefixWord ++ tailWord_4991741).sum := by decide
  have hdescent : baseEnd_4991741 < baseStart_4991741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991751 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 3, 5]
def baseStart_4991751 : Nat := 118140960795 + 4991751 * 2 ^ 59
def prefixEnd_4991751 : Nat := 4983230072969 + 3 ^ 40 * 4991751 * 2
def baseEnd_4991751 : Nat := 854389190187201494985287

theorem tailTrace_4991751 : CollatzResearch.WordTrace tailWord_4991751 prefixEnd_4991751 854389190187201494985287 := by
  unfold tailWord_4991751
  simp only [CollatzResearch.WordTrace]
  refine ⟨182064116138746125043071107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121376077425830750028714071 182064116138746125043071107)
  ·
    refine ⟨273096174208119187564606661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182064116138746125043071107 273096174208119187564606661)
    ·
      refine ⟨51205532664022347668363749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273096174208119187564606661 51205532664022347668363749)
      ·
        refine ⟨9601037374504190187818203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51205532664022347668363749 9601037374504190187818203)
        ·
          refine ⟨14401556061756285281727305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9601037374504190187818203 14401556061756285281727305)
          ·
            refine ⟨10801167046317213961295479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14401556061756285281727305 10801167046317213961295479)
            ·
              refine ⟨16201750569475820941943219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10801167046317213961295479 16201750569475820941943219)
              ·
                refine ⟨24302625854213731412914829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16201750569475820941943219 24302625854213731412914829)
                ·
                  refine ⟨9113484695330149279843061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24302625854213731412914829 9113484695330149279843061)
                  ·
                    refine ⟨854389190187201494985287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9113484695330149279843061 854389190187201494985287)
                    ·
                      rfl

theorem cell23_4991751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_4991751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991751 prefixEnd_4991751 := by exact prefixLift 4991751
  have htrace : WordTrace (prefixWord ++ tailWord_4991751) baseStart_4991751 baseEnd_4991751 := by
    simpa [prefixWord, tailWord_4991751, baseEnd_4991751] using wordTrace_append hprefix tailTrace_4991751
  have hstable : (prefixWord ++ tailWord_4991751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991751).length < 2 ^ (prefixWord ++ tailWord_4991751).sum := by decide
  have hdescent : baseEnd_4991751 < baseStart_4991751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991788 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_4991788 : Nat := 118140960795 + 4991788 * 2 ^ 59
def prefixEnd_4991788 : Nat := 4983230072969 + 3 ^ 40 * 4991788 * 2
def baseEnd_4991788 : Nat := 2563186569345820840193191

theorem tailTrace_4991788 : CollatzResearch.WordTrace tailWord_4991788 prefixEnd_4991788 2563186569345820840193191 := by
  unfold tailWord_4991788
  simp only [CollatzResearch.WordTrace]
  refine ⟨91032732819806040181084009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121376977093074720241445345 91032732819806040181084009)
  ·
    refine ⟨68274549614854530135813007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91032732819806040181084009 68274549614854530135813007)
    ·
      refine ⟨102411824422281795203719511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68274549614854530135813007 102411824422281795203719511)
      ·
        refine ⟨153617736633422692805579267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102411824422281795203719511 153617736633422692805579267)
        ·
          refine ⟨230426604950134039208368901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153617736633422692805579267 230426604950134039208368901)
          ·
            refine ⟨43204988428150132351569169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230426604950134039208368901 43204988428150132351569169)
            ·
              refine ⟨32403741321112599263676877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43204988428150132351569169 32403741321112599263676877)
              ·
                refine ⟨12151402995417224723878829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32403741321112599263676877 12151402995417224723878829)
                ·
                  refine ⟨4556776123281459271454561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12151402995417224723878829 4556776123281459271454561)
                  ·
                    refine ⟨3417582092461094453590921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4556776123281459271454561 3417582092461094453590921)
                    ·
                      refine ⟨2563186569345820840193191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417582092461094453590921 2563186569345820840193191)
                      ·
                        rfl

theorem cell23_4991788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_4991788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991788 prefixEnd_4991788 := by exact prefixLift 4991788
  have htrace : WordTrace (prefixWord ++ tailWord_4991788) baseStart_4991788 baseEnd_4991788 := by
    simpa [prefixWord, tailWord_4991788, baseEnd_4991788] using wordTrace_append hprefix tailTrace_4991788
  have hstable : (prefixWord ++ tailWord_4991788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991788).length < 2 ^ (prefixWord ++ tailWord_4991788).sum := by decide
  have hdescent : baseEnd_4991788 < baseStart_4991788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991809 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4991809 : Nat := 118140960795 + 4991809 * 2 ^ 59
def prefixEnd_4991809 : Nat := 4983230072969 + 3 ^ 40 * 4991809 * 2
def baseEnd_4991809 : Nat := 2563197352439565258030595

theorem tailTrace_4991809 : CollatzResearch.WordTrace tailWord_4991809 prefixEnd_4991809 2563197352439565258030595 := by
  unfold tailWord_4991809
  simp only [CollatzResearch.WordTrace]
  refine ⟨182066231572536000948682481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121377487715024000632454987 182066231572536000948682481)
  ·
    refine ⟨136549673679402000711511861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182066231572536000948682481 136549673679402000711511861)
    ·
      refine ⟨12801531907443937566704237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136549673679402000711511861 12801531907443937566704237)
      ·
        refine ⟨4800574465291476587514089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12801531907443937566704237 4800574465291476587514089)
        ·
          refine ⟨3600430848968607440635567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4800574465291476587514089 3600430848968607440635567)
          ·
            refine ⟨5400646273452911160953351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600430848968607440635567 5400646273452911160953351)
            ·
              refine ⟨8100969410179366741430027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400646273452911160953351 8100969410179366741430027)
              ·
                refine ⟨12151454115269050112145041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100969410179366741430027 12151454115269050112145041)
                ·
                  refine ⟨9113590586451787584108781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12151454115269050112145041 9113590586451787584108781)
                  ·
                    refine ⟨3417596469919420344040793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9113590586451787584108781 3417596469919420344040793)
                    ·
                      refine ⟨2563197352439565258030595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417596469919420344040793 2563197352439565258030595)
                      ·
                        rfl

theorem cell23_4991809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4991809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991809 prefixEnd_4991809 := by exact prefixLift 4991809
  have htrace : WordTrace (prefixWord ++ tailWord_4991809) baseStart_4991809 baseEnd_4991809 := by
    simpa [prefixWord, tailWord_4991809, baseEnd_4991809] using wordTrace_append hprefix tailTrace_4991809
  have hstable : (prefixWord ++ tailWord_4991809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991809).length < 2 ^ (prefixWord ++ tailWord_4991809).sum := by decide
  have hdescent : baseEnd_4991809 < baseStart_4991809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991865 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 1, 3, 2]
def baseStart_4991865 : Nat := 118140960795 + 4991865 * 2 ^ 59
def prefixEnd_4991865 : Nat := 4983230072969 + 3 ^ 40 * 4991865 * 2
def baseEnd_4991865 : Nat := 2563226107356217038930337

theorem tailTrace_4991865 : CollatzResearch.WordTrace tailWord_4991865 prefixEnd_4991865 2563226107356217038930337 := by
  unfold tailWord_4991865
  simp only [CollatzResearch.WordTrace]
  refine ⟨182068274060333122512721049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121378849373555415008480699 182068274060333122512721049)
  ·
    refine ⟨136551205545249841884540787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182068274060333122512721049 136551205545249841884540787)
    ·
      refine ⟨204826808317874762826811181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136551205545249841884540787 204826808317874762826811181)
      ·
        refine ⟨76810053119203036060054193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204826808317874762826811181 76810053119203036060054193)
        ·
          refine ⟨57607539839402277045040645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76810053119203036060054193 57607539839402277045040645)
          ·
            refine ⟨10801413719887926945945121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57607539839402277045040645 10801413719887926945945121)
            ·
              refine ⟨8101060289915945209458841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10801413719887926945945121 8101060289915945209458841)
              ·
                refine ⟨6075795217436958907094131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8101060289915945209458841 6075795217436958907094131)
                ·
                  refine ⟨9113692826155438360641197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6075795217436958907094131 9113692826155438360641197)
                  ·
                    refine ⟨3417634809808289385240449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9113692826155438360641197 3417634809808289385240449)
                    ·
                      refine ⟨2563226107356217038930337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417634809808289385240449 2563226107356217038930337)
                      ·
                        rfl

theorem cell23_4991865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_4991865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991865 prefixEnd_4991865 := by exact prefixLift 4991865
  have htrace : WordTrace (prefixWord ++ tailWord_4991865) baseStart_4991865 baseEnd_4991865 := by
    simpa [prefixWord, tailWord_4991865, baseEnd_4991865] using wordTrace_append hprefix tailTrace_4991865
  have hstable : (prefixWord ++ tailWord_4991865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991865).length < 2 ^ (prefixWord ++ tailWord_4991865).sum := by decide
  have hdescent : baseEnd_4991865 < baseStart_4991865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991881 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_4991881 : Nat := 118140960795 + 4991881 * 2 ^ 59
def prefixEnd_4991881 : Nat := 4983230072969 + 3 ^ 40 * 4991881 * 2
def baseEnd_4991881 : Nat := 2563234323046688976330263

theorem tailTrace_4991881 : CollatzResearch.WordTrace tailWord_4991881 prefixEnd_4991881 2563234323046688976330263 := by
  unfold tailWord_4991881
  simp only [CollatzResearch.WordTrace]
  refine ⟨182068857628275157245303497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121379238418850104830202331 182068857628275157245303497)
  ·
    refine ⟨136551643221206367933977623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182068857628275157245303497 136551643221206367933977623)
    ·
      refine ⟨204827464831809551900966435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136551643221206367933977623 204827464831809551900966435)
      ·
        refine ⟨307241197247714327851449653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204827464831809551900966435 307241197247714327851449653)
        ·
          refine ⟨28803862241973218236073405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307241197247714327851449653 28803862241973218236073405)
          ·
            refine ⟨10801448340739956838527527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28803862241973218236073405 10801448340739956838527527)
            ·
              refine ⟨16202172511109935257791291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10801448340739956838527527 16202172511109935257791291)
              ·
                refine ⟨24303258766664902886686937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16202172511109935257791291 24303258766664902886686937)
                ·
                  refine ⟨18227444074998677165015203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24303258766664902886686937 18227444074998677165015203)
                  ·
                    refine ⟨27341166112498015747522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18227444074998677165015203 27341166112498015747522805)
                    ·
                      refine ⟨2563234323046688976330263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27341166112498015747522805 2563234323046688976330263)
                      ·
                        rfl

theorem cell23_4991881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_4991881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991881 prefixEnd_4991881 := by exact prefixLift 4991881
  have htrace : WordTrace (prefixWord ++ tailWord_4991881) baseStart_4991881 baseEnd_4991881 := by
    simpa [prefixWord, tailWord_4991881, baseEnd_4991881] using wordTrace_append hprefix tailTrace_4991881
  have hstable : (prefixWord ++ tailWord_4991881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991881).length < 2 ^ (prefixWord ++ tailWord_4991881).sum := by decide
  have hdescent : baseEnd_4991881 < baseStart_4991881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991884 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 9]
def baseStart_4991884 : Nat := 118140960795 + 4991884 * 2 ^ 59
def prefixEnd_4991884 : Nat := 4983230072969 + 3 ^ 40 * 4991884 * 2
def baseEnd_4991884 : Nat := 284803984832072496065861

theorem tailTrace_4991884 : CollatzResearch.WordTrace tailWord_4991884 prefixEnd_4991884 284803984832072496065861 := by
  unfold tailWord_4991884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91034483523632144378831353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121379311364842859171775137 91034483523632144378831353)
  ·
    refine ⟨68275862642724108284123515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91034483523632144378831353 68275862642724108284123515)
    ·
      refine ⟨102413793964086162426185273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68275862642724108284123515 102413793964086162426185273)
      ·
        refine ⟨76810345473064621819638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102413793964086162426185273 76810345473064621819638955)
        ·
          refine ⟨115215518209596932729458433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76810345473064621819638955 115215518209596932729458433)
          ·
            refine ⟨86411638657197699547093825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115215518209596932729458433 86411638657197699547093825)
            ·
              refine ⟨64808728992898274660320369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86411638657197699547093825 64808728992898274660320369)
              ·
                refine ⟨48606546744673705995240277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64808728992898274660320369 48606546744673705995240277)
                ·
                  refine ⟨284803984832072496065861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48606546744673705995240277 284803984832072496065861)
                  ·
                    rfl

theorem cell23_4991884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_4991884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991884 prefixEnd_4991884 := by exact prefixLift 4991884
  have htrace : WordTrace (prefixWord ++ tailWord_4991884) baseStart_4991884 baseEnd_4991884 := by
    simpa [prefixWord, tailWord_4991884, baseEnd_4991884] using wordTrace_append hprefix tailTrace_4991884
  have hstable : (prefixWord ++ tailWord_4991884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991884).length < 2 ^ (prefixWord ++ tailWord_4991884).sum := by decide
  have hdescent : baseEnd_4991884 < baseStart_4991884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991895 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4991895 : Nat := 118140960795 + 4991895 * 2 ^ 59
def prefixEnd_4991895 : Nat := 4983230072969 + 3 ^ 40 * 4991895 * 2
def baseEnd_4991895 : Nat := 2563241511775851921555199

theorem tailTrace_4991895 : CollatzResearch.WordTrace tailWord_4991895 prefixEnd_4991895 2563241511775851921555199 := by
  unfold tailWord_4991895
  simp only [CollatzResearch.WordTrace]
  refine ⟨182069368250224437636313139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121379578833482958424208759 182069368250224437636313139)
  ·
    refine ⟨273104052375336656454469709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182069368250224437636313139 273104052375336656454469709)
    ·
      refine ⟨102414019640751246170426141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273104052375336656454469709 102414019640751246170426141)
      ·
        refine ⟨38405257365281717313909803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102414019640751246170426141 38405257365281717313909803)
        ·
          refine ⟨57607886047922575970864705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38405257365281717313909803 57607886047922575970864705)
          ·
            refine ⟨43205914535941931978148529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57607886047922575970864705 43205914535941931978148529)
            ·
              refine ⟨32404435901956448983611397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43205914535941931978148529 32404435901956448983611397)
              ·
                refine ⟨6075831731616834184427137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32404435901956448983611397 6075831731616834184427137)
                ·
                  refine ⟨4556873798712625638320353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6075831731616834184427137 4556873798712625638320353)
                  ·
                    refine ⟨3417655349034469228740265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4556873798712625638320353 3417655349034469228740265)
                    ·
                      refine ⟨2563241511775851921555199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417655349034469228740265 2563241511775851921555199)
                      ·
                        rfl

theorem cell23_4991895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4991895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991895 prefixEnd_4991895 := by exact prefixLift 4991895
  have htrace : WordTrace (prefixWord ++ tailWord_4991895) baseStart_4991895 baseEnd_4991895 := by
    simpa [prefixWord, tailWord_4991895, baseEnd_4991895] using wordTrace_append hprefix tailTrace_4991895
  have hstable : (prefixWord ++ tailWord_4991895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991895).length < 2 ^ (prefixWord ++ tailWord_4991895).sum := by decide
  have hdescent : baseEnd_4991895 < baseStart_4991895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991978 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_4991978 : Nat := 118140960795 + 4991978 * 2 ^ 59
def prefixEnd_4991978 : Nat := 4983230072969 + 3 ^ 40 * 4991978 * 2
def baseEnd_4991978 : Nat := 854428043556725032272439

theorem tailTrace_4991978 : CollatzResearch.WordTrace tailWord_4991978 prefixEnd_4991978 854428043556725032272439 := by
  unfold tailWord_4991978
  simp only [CollatzResearch.WordTrace]
  refine ⟨45518098877230935702896147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121381597005949161874389725 45518098877230935702896147)
  ·
    refine ⟨68277148315846403554344221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45518098877230935702896147 68277148315846403554344221)
    ·
      refine ⟨25603930618442401332879083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68277148315846403554344221 25603930618442401332879083)
      ·
        refine ⟨38405895927663601999318625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25603930618442401332879083 38405895927663601999318625)
        ·
          refine ⟨28804421945747701499488969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38405895927663601999318625 28804421945747701499488969)
          ·
            refine ⟨21603316459310776124616727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28804421945747701499488969 21603316459310776124616727)
            ·
              refine ⟨32404974688966164186925091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21603316459310776124616727 32404974688966164186925091)
              ·
                refine ⟨48607462033449246280387637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32404974688966164186925091 48607462033449246280387637)
                ·
                  refine ⟨4556949565635866838786341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48607462033449246280387637 4556949565635866838786341)
                  ·
                    refine ⟨854428043556725032272439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556949565635866838786341 854428043556725032272439)
                    ·
                      rfl

theorem cell23_4991978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_4991978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991978 prefixEnd_4991978 := by exact prefixLift 4991978
  have htrace : WordTrace (prefixWord ++ tailWord_4991978) baseStart_4991978 baseEnd_4991978 := by
    simpa [prefixWord, tailWord_4991978, baseEnd_4991978] using wordTrace_append hprefix tailTrace_4991978
  have hstable : (prefixWord ++ tailWord_4991978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991978).length < 2 ^ (prefixWord ++ tailWord_4991978).sum := by decide
  have hdescent : baseEnd_4991978 < baseStart_4991978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991982 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4991982 : Nat := 118140960795 + 4991982 * 2 ^ 59
def prefixEnd_4991982 : Nat := 4983230072969 + 3 ^ 40 * 4991982 * 2
def baseEnd_4991982 : Nat := 854428728197597693722433

theorem tailTrace_4991982 : CollatzResearch.WordTrace tailWord_4991982 prefixEnd_4991982 854428728197597693722433 := by
  unfold tailWord_4991982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759067675113656436841275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121381694267272834329820133 22759067675113656436841275)
  ·
    refine ⟨34138601512670484655261913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759067675113656436841275 34138601512670484655261913)
    ·
      refine ⟨25603951134502863491446435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34138601512670484655261913 25603951134502863491446435)
      ·
        refine ⟨38405926701754295237169653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25603951134502863491446435 38405926701754295237169653)
        ·
          refine ⟨3600555628289465178484655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38405926701754295237169653 3600555628289465178484655)
          ·
            refine ⟨5400833442434197767726983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600555628289465178484655 5400833442434197767726983)
            ·
              refine ⟨8101250163651296651590475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400833442434197767726983 8101250163651296651590475)
              ·
                refine ⟨12151875245476944977385713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101250163651296651590475 12151875245476944977385713)
                ·
                  refine ⟨9113906434107708733039285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12151875245476944977385713 9113906434107708733039285)
                  ·
                    refine ⟨854428728197597693722433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9113906434107708733039285 854428728197597693722433)
                    ·
                      rfl

theorem cell23_4991982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4991982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991982 prefixEnd_4991982 := by exact prefixLift 4991982
  have htrace : WordTrace (prefixWord ++ tailWord_4991982) baseStart_4991982 baseEnd_4991982 := by
    simpa [prefixWord, tailWord_4991982, baseEnd_4991982] using wordTrace_append hprefix tailTrace_4991982
  have hstable : (prefixWord ++ tailWord_4991982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991982).length < 2 ^ (prefixWord ++ tailWord_4991982).sum := by decide
  have hdescent : baseEnd_4991982 < baseStart_4991982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4991985 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_4991985 : Nat := 118140960795 + 4991985 * 2 ^ 59
def prefixEnd_4991985 : Nat := 4983230072969 + 3 ^ 40 * 4991985 * 2
def baseEnd_4991985 : Nat := 2563287725034756569429785

theorem tailTrace_4991985 : CollatzResearch.WordTrace tailWord_4991985 prefixEnd_4991985 2563287725034756569429785 := by
  unfold tailWord_4991985
  simp only [CollatzResearch.WordTrace]
  refine ⟨182072650819898383007089409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121381767213265588671392939 182072650819898383007089409)
  ·
    refine ⟨136554488114923787255317057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182072650819898383007089409 136554488114923787255317057)
    ·
      refine ⟨102415866086192840441487793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136554488114923787255317057 102415866086192840441487793)
      ·
        refine ⟨76811899564644630331115845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102415866086192840441487793 76811899564644630331115845)
        ·
          refine ⟨14402231168370868187084221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76811899564644630331115845 14402231168370868187084221)
          ·
            refine ⟨5400836688139075570156583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14402231168370868187084221 5400836688139075570156583)
            ·
              refine ⟨8101255032208613355234875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400836688139075570156583 8101255032208613355234875)
              ·
                refine ⟨12151882548312920032852313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101255032208613355234875 12151882548312920032852313)
                ·
                  refine ⟨9113911911234690024639235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12151882548312920032852313 9113911911234690024639235)
                  ·
                    refine ⟨13670867866852035036958853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9113911911234690024639235 13670867866852035036958853)
                    ·
                      refine ⟨2563287725034756569429785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13670867866852035036958853 2563287725034756569429785)
                      ·
                        rfl

theorem cell23_4991985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_4991985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4991985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4991985 prefixEnd_4991985 := by exact prefixLift 4991985
  have htrace : WordTrace (prefixWord ++ tailWord_4991985) baseStart_4991985 baseEnd_4991985 := by
    simpa [prefixWord, tailWord_4991985, baseEnd_4991985] using wordTrace_append hprefix tailTrace_4991985
  have hstable : (prefixWord ++ tailWord_4991985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4991985).length < 2 ^ (prefixWord ++ tailWord_4991985).sum := by decide
  have hdescent : baseEnd_4991985 < baseStart_4991985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4991985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992008 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 6]
def baseStart_4992008 : Nat := 118140960795 + 4992008 * 2 ^ 59
def prefixEnd_4992008 : Nat := 4983230072969 + 3 ^ 40 * 4992008 * 2
def baseEnd_4992008 : Nat := 284811059454423331049131

theorem tailTrace_4992008 : CollatzResearch.WordTrace tailWord_4992008 prefixEnd_4992008 284811059454423331049131 := by
  unfold tailWord_4992008
  simp only [CollatzResearch.WordTrace]
  refine ⟨91036744849407528967588339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121382326465876705290117785 91036744849407528967588339)
  ·
    refine ⟨136555117274111293451382509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91036744849407528967588339 136555117274111293451382509)
    ·
      refine ⟨51208168977791735044268441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136555117274111293451382509 51208168977791735044268441)
      ·
        refine ⟨38406126733343801283201331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51208168977791735044268441 38406126733343801283201331)
        ·
          refine ⟨57609190100015701924801997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38406126733343801283201331 57609190100015701924801997)
          ·
            refine ⟨21603446287505888221800749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57609190100015701924801997 21603446287505888221800749)
            ·
              refine ⟨8101292357814708083175281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21603446287505888221800749 8101292357814708083175281)
              ·
                refine ⟨6075969268361031062381461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8101292357814708083175281 6075969268361031062381461)
                ·
                  refine ⟨284811059454423331049131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6075969268361031062381461 284811059454423331049131)
                  ·
                    rfl

theorem cell23_4992008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_4992008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992008 prefixEnd_4992008 := by exact prefixLift 4992008
  have htrace : WordTrace (prefixWord ++ tailWord_4992008) baseStart_4992008 baseEnd_4992008 := by
    simpa [prefixWord, tailWord_4992008, baseEnd_4992008] using wordTrace_append hprefix tailTrace_4992008
  have hstable : (prefixWord ++ tailWord_4992008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992008).length < 2 ^ (prefixWord ++ tailWord_4992008).sum := by decide
  have hdescent : baseEnd_4992008 < baseStart_4992008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992011 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_4992011 : Nat := 118140960795 + 4992011 * 2 ^ 59
def prefixEnd_4992011 : Nat := 4983230072969 + 3 ^ 40 * 4992011 * 2
def baseEnd_4992011 : Nat := 2563301075531773467704665

theorem tailTrace_4992011 : CollatzResearch.WordTrace tailWord_4992011 prefixEnd_4992011 2563301075531773467704665 := by
  unfold tailWord_4992011
  simp only [CollatzResearch.WordTrace]
  refine ⟨182073599117804189447535887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121382399411869459631690591 182073599117804189447535887)
  ·
    refine ⟨273110398676706284171303831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182073599117804189447535887 273110398676706284171303831)
    ·
      refine ⟨409665598015059426256955747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273110398676706284171303831 409665598015059426256955747)
      ·
        refine ⟨614498397022589139385433621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409665598015059426256955747 614498397022589139385433621)
        ·
          refine ⟨28804612360433865908692201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 614498397022589139385433621 28804612360433865908692201)
          ·
            refine ⟨21603459270325399431519151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28804612360433865908692201 21603459270325399431519151)
            ·
              refine ⟨32405188905488099147278727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21603459270325399431519151 32405188905488099147278727)
              ·
                refine ⟨48607783358232148720918091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32405188905488099147278727 48607783358232148720918091)
                ·
                  refine ⟨72911675037348223081377137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48607783358232148720918091 72911675037348223081377137)
                  ·
                    refine ⟨54683756278011167311032853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72911675037348223081377137 54683756278011167311032853)
                    ·
                      refine ⟨2563301075531773467704665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54683756278011167311032853 2563301075531773467704665)
                      ·
                        rfl

theorem cell23_4992011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_4992011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992011 prefixEnd_4992011 := by exact prefixLift 4992011
  have htrace : WordTrace (prefixWord ++ tailWord_4992011) baseStart_4992011 baseEnd_4992011 := by
    simpa [prefixWord, tailWord_4992011, baseEnd_4992011] using wordTrace_append hprefix tailTrace_4992011
  have hstable : (prefixWord ++ tailWord_4992011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992011).length < 2 ^ (prefixWord ++ tailWord_4992011).sum := by decide
  have hdescent : baseEnd_4992011 < baseStart_4992011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992035 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 3]
def baseStart_4992035 : Nat := 118140960795 + 4992035 * 2 ^ 59
def prefixEnd_4992035 : Nat := 4983230072969 + 3 ^ 40 * 4992035 * 2
def baseEnd_4992035 : Nat := 2563313399067481373804555

theorem tailTrace_4992035 : CollatzResearch.WordTrace tailWord_4992035 prefixEnd_4992035 2563313399067481373804555 := by
  unfold tailWord_4992035
  simp only [CollatzResearch.WordTrace]
  refine ⟨182074474469717241546409559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121382982979811494364273039 182074474469717241546409559)
  ·
    refine ⟨273111711704575862319614339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182074474469717241546409559 273111711704575862319614339)
    ·
      refine ⟨409667567556863793479421509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273111711704575862319614339 409667567556863793479421509)
      ·
        refine ⟨76812668916911961277391533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 409667567556863793479421509 76812668916911961277391533)
        ·
          refine ⟨28804750843841985479021825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76812668916911961277391533 28804750843841985479021825)
          ·
            refine ⟨21603563132881489109266369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28804750843841985479021825 21603563132881489109266369)
            ·
              refine ⟨16202672349661116831949777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21603563132881489109266369 16202672349661116831949777)
              ·
                refine ⟨12152004262245837623962333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16202672349661116831949777 12152004262245837623962333)
                ·
                  refine ⟨4557001598342189108985875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12152004262245837623962333 4557001598342189108985875)
                  ·
                    refine ⟨6835502397513283663478813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557001598342189108985875 6835502397513283663478813)
                    ·
                      refine ⟨2563313399067481373804555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6835502397513283663478813 2563313399067481373804555)
                      ·
                        rfl

theorem cell23_4992035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_4992035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992035 prefixEnd_4992035 := by exact prefixLift 4992035
  have htrace : WordTrace (prefixWord ++ tailWord_4992035) baseStart_4992035 baseEnd_4992035 := by
    simpa [prefixWord, tailWord_4992035, baseEnd_4992035] using wordTrace_append hprefix tailTrace_4992035
  have hstable : (prefixWord ++ tailWord_4992035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992035).length < 2 ^ (prefixWord ++ tailWord_4992035).sum := by decide
  have hdescent : baseEnd_4992035 < baseStart_4992035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992051 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 6]
def baseStart_4992051 : Nat := 118140960795 + 4992051 * 2 ^ 59
def prefixEnd_4992051 : Nat := 4983230072969 + 3 ^ 40 * 4992051 * 2
def baseEnd_4992051 : Nat := 854440538252651103734827

theorem tailTrace_4992051 : CollatzResearch.WordTrace tailWord_4992051 prefixEnd_4992051 854440538252651103734827 := by
  unfold tailWord_4992051
  simp only [CollatzResearch.WordTrace]
  refine ⟨182075058037659276278992007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121383372025106184185994671 182075058037659276278992007)
  ·
    refine ⟨273112587056488914418488011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182075058037659276278992007 273112587056488914418488011)
    ·
      refine ⟨409668880584733371627732017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273112587056488914418488011 409668880584733371627732017)
      ·
        refine ⟨307251660438550028720799013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409668880584733371627732017 307251660438550028720799013)
        ·
          refine ⟨57609686332228130385149815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307251660438550028720799013 57609686332228130385149815)
          ·
            refine ⟨86414529498342195577724723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57609686332228130385149815 86414529498342195577724723)
            ·
              refine ⟨129621794247513293366587085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86414529498342195577724723 129621794247513293366587085)
              ·
                refine ⟨48608172842817485012470157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129621794247513293366587085 48608172842817485012470157)
                ·
                  refine ⟨18228064816056556879676309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48608172842817485012470157 18228064816056556879676309)
                  ·
                    refine ⟨854440538252651103734827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18228064816056556879676309 854440538252651103734827)
                    ·
                      rfl

theorem cell23_4992051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_4992051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992051 prefixEnd_4992051 := by exact prefixLift 4992051
  have htrace : WordTrace (prefixWord ++ tailWord_4992051) baseStart_4992051 baseEnd_4992051 := by
    simpa [prefixWord, tailWord_4992051, baseEnd_4992051] using wordTrace_append hprefix tailTrace_4992051
  have hstable : (prefixWord ++ tailWord_4992051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992051).length < 2 ^ (prefixWord ++ tailWord_4992051).sum := by decide
  have hdescent : baseEnd_4992051 < baseStart_4992051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992062 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4992062 : Nat := 118140960795 + 4992062 * 2 ^ 59
def prefixEnd_4992062 : Nat := 4983230072969 + 3 ^ 40 * 4992062 * 2
def baseEnd_4992062 : Nat := 2563327263045152768166931

theorem tailTrace_4992062 : CollatzResearch.WordTrace tailWord_4992062 prefixEnd_4992062 2563327263045152768166931 := by
  unfold tailWord_4992062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759432405077428144705305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121383639493746283438428293 22759432405077428144705305)
  ·
    refine ⟨17069574303808071108528979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22759432405077428144705305 17069574303808071108528979)
    ·
      refine ⟨25604361455712106662793469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17069574303808071108528979 25604361455712106662793469)
      ·
        refine ⟨9601635545892039998547551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25604361455712106662793469 9601635545892039998547551)
        ·
          refine ⟨14402453318838059997821327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9601635545892039998547551 14402453318838059997821327)
          ·
            refine ⟨21603679978257089996731991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14402453318838059997821327 21603679978257089996731991)
            ·
              refine ⟨32405519967385634995097987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21603679978257089996731991 32405519967385634995097987)
              ·
                refine ⟨48608279951078452492646981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32405519967385634995097987 48608279951078452492646981)
                ·
                  refine ⟨9114052490827209842371309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48608279951078452492646981 9114052490827209842371309)
                  ·
                    refine ⟨3417769684060203690889241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9114052490827209842371309 3417769684060203690889241)
                    ·
                      refine ⟨2563327263045152768166931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417769684060203690889241 2563327263045152768166931)
                      ·
                        rfl

theorem cell23_4992062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4992062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992062 prefixEnd_4992062 := by exact prefixLift 4992062
  have htrace : WordTrace (prefixWord ++ tailWord_4992062) baseStart_4992062 baseEnd_4992062 := by
    simpa [prefixWord, tailWord_4992062, baseEnd_4992062] using wordTrace_append hprefix tailTrace_4992062
  have hstable : (prefixWord ++ tailWord_4992062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992062).length < 2 ^ (prefixWord ++ tailWord_4992062).sum := by decide
  have hdescent : baseEnd_4992062 < baseStart_4992062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992078 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4992078 : Nat := 118140960795 + 4992078 * 2 ^ 59
def prefixEnd_4992078 : Nat := 4983230072969 + 3 ^ 40 * 4992078 * 2
def baseEnd_4992078 : Nat := 2563335478735624705566857

theorem tailTrace_4992078 : CollatzResearch.WordTrace tailWord_4992078 prefixEnd_4992078 2563335478735624705566857 := by
  unfold tailWord_4992078
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759505351070182486278111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121384028539040973260149925 22759505351070182486278111)
  ·
    refine ⟨34139258026605273729417167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759505351070182486278111 34139258026605273729417167)
    ·
      refine ⟨51208887039907910594125751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34139258026605273729417167 51208887039907910594125751)
      ·
        refine ⟨76813330559861865891188627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51208887039907910594125751 76813330559861865891188627)
        ·
          refine ⟨115219995839792798836782941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76813330559861865891188627 115219995839792798836782941)
          ·
            refine ⟨43207498439922299563793603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115219995839792798836782941 43207498439922299563793603)
            ·
              refine ⟨64811247659883449345690405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43207498439922299563793603 64811247659883449345690405)
              ·
                refine ⟨12152108936228146752316951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64811247659883449345690405 12152108936228146752316951)
                ·
                  refine ⟨18228163404342220128475427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12152108936228146752316951 18228163404342220128475427)
                  ·
                    refine ⟨27342245106513330192713141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18228163404342220128475427 27342245106513330192713141)
                    ·
                      refine ⟨2563335478735624705566857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27342245106513330192713141 2563335478735624705566857)
                      ·
                        rfl

theorem cell23_4992078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4992078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992078 prefixEnd_4992078 := by exact prefixLift 4992078
  have htrace : WordTrace (prefixWord ++ tailWord_4992078) baseStart_4992078 baseEnd_4992078 := by
    simpa [prefixWord, tailWord_4992078, baseEnd_4992078] using wordTrace_append hprefix tailTrace_4992078
  have hstable : (prefixWord ++ tailWord_4992078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992078).length < 2 ^ (prefixWord ++ tailWord_4992078).sum := by decide
  have hdescent : baseEnd_4992078 < baseStart_4992078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992081 : List Nat := [1, 2, 2, 1, 3, 1, 3, 10]
def baseStart_4992081 : Nat := 118140960795 + 4992081 * 2 ^ 59
def prefixEnd_4992081 : Nat := 4983230072969 + 3 ^ 40 * 4992081 * 2
def baseEnd_4992081 : Nat := 94938408117688451623309

theorem tailTrace_4992081 : CollatzResearch.WordTrace tailWord_4992081 prefixEnd_4992081 94938408117688451623309 := by
  unfold tailWord_4992081
  simp only [CollatzResearch.WordTrace]
  refine ⟨182076152227550591402584097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121384101485033727601722731 182076152227550591402584097)
  ·
    refine ⟨136557114170662943551938073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182076152227550591402584097 136557114170662943551938073)
    ·
      refine ⟨102417835627997207663953555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136557114170662943551938073 102417835627997207663953555)
      ·
        refine ⟨153626753441995811495930333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102417835627997207663953555 153626753441995811495930333)
        ·
          refine ⟨57610032540748429310973875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153626753441995811495930333 57610032540748429310973875)
          ·
            refine ⟨86415048811122643966460813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57610032540748429310973875 86415048811122643966460813)
            ·
              refine ⟨32405643304170991487422805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86415048811122643966460813 32405643304170991487422805)
              ·
                refine ⟨94938408117688451623309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32405643304170991487422805 94938408117688451623309)
                ·
                  rfl

theorem cell23_4992081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 10].length) (baseStart_4992081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992081 prefixEnd_4992081 := by exact prefixLift 4992081
  have htrace : WordTrace (prefixWord ++ tailWord_4992081) baseStart_4992081 baseEnd_4992081 := by
    simpa [prefixWord, tailWord_4992081, baseEnd_4992081] using wordTrace_append hprefix tailTrace_4992081
  have hstable : (prefixWord ++ tailWord_4992081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992081).length < 2 ^ (prefixWord ++ tailWord_4992081).sum := by decide
  have hdescent : baseEnd_4992081 < baseStart_4992081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992085 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_4992085 : Nat := 118140960795 + 4992085 * 2 ^ 59
def prefixEnd_4992085 : Nat := 4983230072969 + 3 ^ 40 * 4992085 * 2
def baseEnd_4992085 : Nat := 854446357700068726059775

theorem tailTrace_4992085 : CollatzResearch.WordTrace tailWord_4992085 prefixEnd_4992085 854446357700068726059775 := by
  unfold tailWord_4992085
  simp only [CollatzResearch.WordTrace]
  refine ⟨182076298119536100085729709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121384198746357400057153139 182076298119536100085729709)
  ·
    refine ⟨68278611794826037532148641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182076298119536100085729709 68278611794826037532148641)
    ·
      refine ⟨51208958846119528149111481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68278611794826037532148641 51208958846119528149111481)
      ·
        refine ⟨38406719134589646111833611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51208958846119528149111481 38406719134589646111833611)
        ·
          refine ⟨57610078701884469167750417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38406719134589646111833611 57610078701884469167750417)
          ·
            refine ⟨43207559026413351875812813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57610078701884469167750417 43207559026413351875812813)
            ·
              refine ⟨16202834634905006953429805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43207559026413351875812813 16202834634905006953429805)
              ·
                refine ⟨6076062988089377607536177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16202834634905006953429805 6076062988089377607536177)
                ·
                  refine ⟨4557047241067033205652133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6076062988089377607536177 4557047241067033205652133)
                  ·
                    refine ⟨854446357700068726059775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4557047241067033205652133 854446357700068726059775)
                    ·
                      rfl

theorem cell23_4992085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_4992085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992085 prefixEnd_4992085 := by exact prefixLift 4992085
  have htrace : WordTrace (prefixWord ++ tailWord_4992085) baseStart_4992085 baseEnd_4992085 := by
    simpa [prefixWord, tailWord_4992085, baseEnd_4992085] using wordTrace_append hprefix tailTrace_4992085
  have hstable : (prefixWord ++ tailWord_4992085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992085).length < 2 ^ (prefixWord ++ tailWord_4992085).sum := by decide
  have hdescent : baseEnd_4992085 < baseStart_4992085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992088 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_4992088 : Nat := 118140960795 + 4992088 * 2 ^ 59
def prefixEnd_4992088 : Nat := 4983230072969 + 3 ^ 40 * 4992088 * 2
def baseEnd_4992088 : Nat := 2563340613542169666441811

theorem tailTrace_4992088 : CollatzResearch.WordTrace tailWord_4992088 prefixEnd_4992088 2563340613542169666441811 := by
  unfold tailWord_4992088
  simp only [CollatzResearch.WordTrace]
  refine ⟨91038203769262615799044459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121384271692350154398725945 91038203769262615799044459)
  ·
    refine ⟨136557305653893923698566689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91038203769262615799044459 136557305653893923698566689)
    ·
      refine ⟨102417979240420442773925017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136557305653893923698566689 102417979240420442773925017)
      ·
        refine ⟨76813484430315332080443763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102417979240420442773925017 76813484430315332080443763)
        ·
          refine ⟨115220226645472998120665645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76813484430315332080443763 115220226645472998120665645)
          ·
            refine ⟨43207584992052374295249617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115220226645472998120665645 43207584992052374295249617)
            ·
              refine ⟨32405688744039280721437213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43207584992052374295249617 32405688744039280721437213)
              ·
                refine ⟨12152133279014730270538955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32405688744039280721437213 12152133279014730270538955)
                ·
                  refine ⟨18228199918522095405808433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12152133279014730270538955 18228199918522095405808433)
                  ·
                    refine ⟨13671149938891571554356325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18228199918522095405808433 13671149938891571554356325)
                    ·
                      refine ⟨2563340613542169666441811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13671149938891571554356325 2563340613542169666441811)
                      ·
                        rfl

theorem cell23_4992088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_4992088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992088 prefixEnd_4992088 := by exact prefixLift 4992088
  have htrace : WordTrace (prefixWord ++ tailWord_4992088) baseStart_4992088 baseEnd_4992088 := by
    simpa [prefixWord, tailWord_4992088, baseEnd_4992088] using wordTrace_append hprefix tailTrace_4992088
  have hstable : (prefixWord ++ tailWord_4992088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992088).length < 2 ^ (prefixWord ++ tailWord_4992088).sum := by decide
  have hdescent : baseEnd_4992088 < baseStart_4992088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992092 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4992092 : Nat := 118140960795 + 4992092 * 2 ^ 59
def prefixEnd_4992092 : Nat := 4983230072969 + 3 ^ 40 * 4992092 * 2
def baseEnd_4992092 : Nat := 2563342667464787650791793

theorem tailTrace_4992092 : CollatzResearch.WordTrace tailWord_4992092 prefixEnd_4992092 2563342667464787650791793 := by
  unfold tailWord_4992092
  simp only [CollatzResearch.WordTrace]
  refine ⟨91038276715255370140617265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121384368953673826854156353 91038276715255370140617265)
  ·
    refine ⟨68278707536441527605462949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91038276715255370140617265 68278707536441527605462949)
    ·
      refine ⟨12802257663082786426024303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68278707536441527605462949 12802257663082786426024303)
      ·
        refine ⟨19203386494624179639036455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12802257663082786426024303 19203386494624179639036455)
        ·
          refine ⟨28805079741936269458554683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19203386494624179639036455 28805079741936269458554683)
          ·
            refine ⟨43207619612904404187832025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28805079741936269458554683 43207619612904404187832025)
            ·
              refine ⟨32405714709678303140874019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43207619612904404187832025 32405714709678303140874019)
              ·
                refine ⟨48608572064517454711311029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32405714709678303140874019 48608572064517454711311029)
                ·
                  refine ⟨4557053631048511379185409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48608572064517454711311029 4557053631048511379185409)
                  ·
                    refine ⟨3417790223286383534389057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557053631048511379185409 3417790223286383534389057)
                    ·
                      refine ⟨2563342667464787650791793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417790223286383534389057 2563342667464787650791793)
                      ·
                        rfl

theorem cell23_4992092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4992092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992092 prefixEnd_4992092 := by exact prefixLift 4992092
  have htrace : WordTrace (prefixWord ++ tailWord_4992092) baseStart_4992092 baseEnd_4992092 := by
    simpa [prefixWord, tailWord_4992092, baseEnd_4992092] using wordTrace_append hprefix tailTrace_4992092
  have hstable : (prefixWord ++ tailWord_4992092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992092).length < 2 ^ (prefixWord ++ tailWord_4992092).sum := by decide
  have hdescent : baseEnd_4992092 < baseStart_4992092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992112 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3]
def baseStart_4992112 : Nat := 118140960795 + 4992112 * 2 ^ 59
def prefixEnd_4992112 : Nat := 4983230072969 + 3 ^ 40 * 4992112 * 2
def baseEnd_4992112 : Nat := 2563352937077877572541701

theorem tailTrace_4992112 : CollatzResearch.WordTrace tailWord_4992112 prefixEnd_4992112 2563352937077877572541701 := by
  unfold tailWord_4992112
  simp only [CollatzResearch.WordTrace]
  refine ⟨91038641445219141848481295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121384855260292189131308393 91038641445219141848481295)
  ·
    refine ⟨136557962167828712772721943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91038641445219141848481295 136557962167828712772721943)
    ·
      refine ⟨204836943251743069159082915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136557962167828712772721943 204836943251743069159082915)
      ·
        refine ⟨307255414877614603738624373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204836943251743069159082915 307255414877614603738624373)
        ·
          refine ⟨28805195144776369100496035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307255414877614603738624373 28805195144776369100496035)
          ·
            refine ⟨43207792717164553650744053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28805195144776369100496035 43207792717164553650744053)
            ·
              refine ⟨4050730567234176904757255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43207792717164553650744053 4050730567234176904757255)
              ·
                refine ⟨6076095850851265357135883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050730567234176904757255 6076095850851265357135883)
                ·
                  refine ⟨9114143776276898035703825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6076095850851265357135883 9114143776276898035703825)
                  ·
                    refine ⟨6835607832207673526777869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9114143776276898035703825 6835607832207673526777869)
                    ·
                      refine ⟨2563352937077877572541701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6835607832207673526777869 2563352937077877572541701)
                      ·
                        rfl

theorem cell23_4992112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3].length) (baseStart_4992112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992112 prefixEnd_4992112 := by exact prefixLift 4992112
  have htrace : WordTrace (prefixWord ++ tailWord_4992112) baseStart_4992112 baseEnd_4992112 := by
    simpa [prefixWord, tailWord_4992112, baseEnd_4992112] using wordTrace_append hprefix tailTrace_4992112
  have hstable : (prefixWord ++ tailWord_4992112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992112).length < 2 ^ (prefixWord ++ tailWord_4992112).sum := by decide
  have hdescent : baseEnd_4992112 < baseStart_4992112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992142 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4992142 : Nat := 118140960795 + 4992142 * 2 ^ 59
def prefixEnd_4992142 : Nat := 4983230072969 + 3 ^ 40 * 4992142 * 2
def baseEnd_4992142 : Nat := 2563368341497512455166563

theorem tailTrace_4992142 : CollatzResearch.WordTrace tailWord_4992142 prefixEnd_4992142 2563368341497512455166563 := by
  unfold tailWord_4992142
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759797135041199852569335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121385584720219732547036453 22759797135041199852569335)
  ·
    refine ⟨34139695702561799778854003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759797135041199852569335 34139695702561799778854003)
    ·
      refine ⟨51209543553842699668281005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34139695702561799778854003 51209543553842699668281005)
      ·
        refine ⟨19203578832691012375605377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51209543553842699668281005 19203578832691012375605377)
        ·
          refine ⟨14402684124518259281704033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19203578832691012375605377 14402684124518259281704033)
          ·
            refine ⟨10802013093388694461278025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14402684124518259281704033 10802013093388694461278025)
            ·
              refine ⟨8101509820041520845958519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10802013093388694461278025 8101509820041520845958519)
              ·
                refine ⟨12152264730062281268937779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101509820041520845958519 12152264730062281268937779)
                ·
                  refine ⟨18228397095093421903406669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12152264730062281268937779 18228397095093421903406669)
                  ·
                    refine ⟨6835648910660033213777501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18228397095093421903406669 6835648910660033213777501)
                    ·
                      refine ⟨2563368341497512455166563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6835648910660033213777501 2563368341497512455166563)
                      ·
                        rfl

theorem cell23_4992142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4992142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992142 prefixEnd_4992142 := by exact prefixLift 4992142
  have htrace : WordTrace (prefixWord ++ tailWord_4992142) baseStart_4992142 baseEnd_4992142 := by
    simpa [prefixWord, tailWord_4992142, baseEnd_4992142] using wordTrace_append hprefix tailTrace_4992142
  have hstable : (prefixWord ++ tailWord_4992142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992142).length < 2 ^ (prefixWord ++ tailWord_4992142).sum := by decide
  have hdescent : baseEnd_4992142 < baseStart_4992142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992152 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4992152 : Nat := 118140960795 + 4992152 * 2 ^ 59
def prefixEnd_4992152 : Nat := 4983230072969 + 3 ^ 40 * 4992152 * 2
def baseEnd_4992152 : Nat := 2563373476304057416041517

theorem tailTrace_4992152 : CollatzResearch.WordTrace tailWord_4992152 prefixEnd_4992152 2563373476304057416041517 := by
  unfold tailWord_4992152
  simp only [CollatzResearch.WordTrace]
  refine ⟨91039370905146685264209355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121385827873528913685612473 91039370905146685264209355)
  ·
    refine ⟨136559056357720027896314033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91039370905146685264209355 136559056357720027896314033)
    ·
      refine ⟨102419292268290020922235525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136559056357720027896314033 102419292268290020922235525)
      ·
        refine ⟨19203617300304378922919161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102419292268290020922235525 19203617300304378922919161)
        ·
          refine ⟨14402712975228284192189371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19203617300304378922919161 14402712975228284192189371)
          ·
            refine ⟨21604069462842426288284057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14402712975228284192189371 21604069462842426288284057)
            ·
              refine ⟨16203052097131819716213043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21604069462842426288284057 16203052097131819716213043)
              ·
                refine ⟨24304578145697729574319565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16203052097131819716213043 24304578145697729574319565)
                ·
                  refine ⟨9114216804636648590369837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24304578145697729574319565 9114216804636648590369837)
                  ·
                    refine ⟨3417831301738743221388689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9114216804636648590369837 3417831301738743221388689)
                    ·
                      refine ⟨2563373476304057416041517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417831301738743221388689 2563373476304057416041517)
                      ·
                        rfl

theorem cell23_4992152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4992152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992152 prefixEnd_4992152 := by exact prefixLift 4992152
  have htrace : WordTrace (prefixWord ++ tailWord_4992152) baseStart_4992152 baseEnd_4992152 := by
    simpa [prefixWord, tailWord_4992152, baseEnd_4992152] using wordTrace_append hprefix tailTrace_4992152
  have hstable : (prefixWord ++ tailWord_4992152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992152).length < 2 ^ (prefixWord ++ tailWord_4992152).sum := by decide
  have hdescent : baseEnd_4992152 < baseStart_4992152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992235 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 2, 5]
def baseStart_4992235 : Nat := 118140960795 + 4992235 * 2 ^ 59
def prefixEnd_4992235 : Nat := 4983230072969 + 3 ^ 40 * 4992235 * 2
def baseEnd_4992235 : Nat := 854472031732793530434545

theorem tailTrace_4992235 : CollatzResearch.WordTrace tailWord_4992235 prefixEnd_4992235 854472031732793530434545 := by
  unfold tailWord_4992235
  simp only [CollatzResearch.WordTrace]
  refine ⟨182081769068992675703690159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121387846045995117135793439 182081769068992675703690159)
  ·
    refine ⟨273122653603489013555535239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182081769068992675703690159 273122653603489013555535239)
    ·
      refine ⟨409683980405233520333302859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273122653603489013555535239 409683980405233520333302859)
      ·
        refine ⟨614525970607850280499954289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409683980405233520333302859 614525970607850280499954289)
        ·
          refine ⟨460894477955887710374965717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614525970607850280499954289 460894477955887710374965717)
          ·
            refine ⟨10802214327091118211913259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 460894477955887710374965717 10802214327091118211913259)
            ·
              refine ⟨16203321490636677317869889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10802214327091118211913259 16203321490636677317869889)
              ·
                refine ⟨12152491117977507988402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16203321490636677317869889 12152491117977507988402417)
                ·
                  refine ⟨9114368338483130991301813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12152491117977507988402417 9114368338483130991301813)
                  ·
                    refine ⟨854472031732793530434545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9114368338483130991301813 854472031732793530434545)
                    ·
                      rfl

theorem cell23_4992235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].length) (baseStart_4992235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992235 prefixEnd_4992235 := by exact prefixLift 4992235
  have htrace : WordTrace (prefixWord ++ tailWord_4992235) baseStart_4992235 baseEnd_4992235 := by
    simpa [prefixWord, tailWord_4992235, baseEnd_4992235] using wordTrace_append hprefix tailTrace_4992235
  have hstable : (prefixWord ++ tailWord_4992235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992235).length < 2 ^ (prefixWord ++ tailWord_4992235).sum := by decide
  have hdescent : baseEnd_4992235 < baseStart_4992235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992239 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 5]
def baseStart_4992239 : Nat := 118140960795 + 4992239 * 2 ^ 59
def prefixEnd_4992239 : Nat := 4983230072969 + 3 ^ 40 * 4992239 * 2
def baseEnd_4992239 : Nat := 284824238791222063961513

theorem tailTrace_4992239 : CollatzResearch.WordTrace tailWord_4992239 prefixEnd_4992239 284824238791222063961513 := by
  unfold tailWord_4992239
  simp only [CollatzResearch.WordTrace]
  refine ⟨182081914960978184386835771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121387943307318789591223847 182081914960978184386835771)
  ·
    refine ⟨273122872441467276580253657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182081914960978184386835771 273122872441467276580253657)
    ·
      refine ⟨204842154331100457435190243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273122872441467276580253657 204842154331100457435190243)
      ·
        refine ⟨307263231496650686152785365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204842154331100457435190243 307263231496650686152785365)
        ·
          refine ⟨7201481988202750456705907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 307263231496650686152785365 7201481988202750456705907)
          ·
            refine ⟨10802222982304125685058861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7201481988202750456705907 10802222982304125685058861)
            ·
              refine ⟨4050833618364047131897073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10802222982304125685058861 4050833618364047131897073)
              ·
                refine ⟨3038125213773035348922805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050833618364047131897073 3038125213773035348922805)
                ·
                  refine ⟨284824238791222063961513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3038125213773035348922805 284824238791222063961513)
                  ·
                    rfl

theorem cell23_4992239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 5].length) (baseStart_4992239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992239 prefixEnd_4992239 := by exact prefixLift 4992239
  have htrace : WordTrace (prefixWord ++ tailWord_4992239) baseStart_4992239 baseEnd_4992239 := by
    simpa [prefixWord, tailWord_4992239, baseEnd_4992239] using wordTrace_append hprefix tailTrace_4992239
  have hstable : (prefixWord ++ tailWord_4992239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992239).length < 2 ^ (prefixWord ++ tailWord_4992239).sum := by decide
  have hdescent : baseEnd_4992239 < baseStart_4992239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992265 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_4992265 : Nat := 118140960795 + 4992265 * 2 ^ 59
def prefixEnd_4992265 : Nat := 4983230072969 + 3 ^ 40 * 4992265 * 2
def baseEnd_4992265 : Nat := 854477166539338491309499

theorem tailTrace_4992265 : CollatzResearch.WordTrace tailWord_4992265 prefixEnd_4992265 854477166539338491309499 := by
  unfold tailWord_4992265
  simp only [CollatzResearch.WordTrace]
  refine ⟨182082863258883990827282249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121388575505922660551521499 182082863258883990827282249)
  ·
    refine ⟨136562147444162993120461687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182082863258883990827282249 136562147444162993120461687)
    ·
      refine ⟨204843221166244489680692531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136562147444162993120461687 204843221166244489680692531)
      ·
        refine ⟨307264831749366734521038797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204843221166244489680692531 307264831749366734521038797)
        ·
          refine ⟨115224311906012525445389549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307264831749366734521038797 115224311906012525445389549)
          ·
            refine ⟨43209116964754697042021081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115224311906012525445389549 43209116964754697042021081)
            ·
              refine ⟨32406837723566022781515811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43209116964754697042021081 32406837723566022781515811)
              ·
                refine ⟨48610256585349034172273717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32406837723566022781515811 48610256585349034172273717)
                ·
                  refine ⟨4557211554876471953650661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48610256585349034172273717 4557211554876471953650661)
                  ·
                    refine ⟨854477166539338491309499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4557211554876471953650661 854477166539338491309499)
                    ·
                      rfl

theorem cell23_4992265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_4992265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992265 prefixEnd_4992265 := by exact prefixLift 4992265
  have htrace : WordTrace (prefixWord ++ tailWord_4992265) baseStart_4992265 baseEnd_4992265 := by
    simpa [prefixWord, tailWord_4992265, baseEnd_4992265] using wordTrace_append hprefix tailTrace_4992265
  have hstable : (prefixWord ++ tailWord_4992265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992265).length < 2 ^ (prefixWord ++ tailWord_4992265).sum := by decide
  have hdescent : baseEnd_4992265 < baseStart_4992265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992292 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4992292 : Nat := 118140960795 + 4992292 * 2 ^ 59
def prefixEnd_4992292 : Nat := 4983230072969 + 3 ^ 40 * 4992292 * 2
def baseEnd_4992292 : Nat := 2563445363595686868290873

theorem tailTrace_4992292 : CollatzResearch.WordTrace tailWord_4992292 prefixEnd_4992292 2563445363595686868290873 := by
  unfold tailWord_4992292
  simp only [CollatzResearch.WordTrace]
  refine ⟨91041924014893087219257565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121389232019857449625676753 91041924014893087219257565)
  ·
    refine ⟨34140721505584907707221587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91041924014893087219257565 34140721505584907707221587)
    ·
      refine ⟨51211082258377361560832381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34140721505584907707221587 51211082258377361560832381)
      ·
        refine ⟨19204155846891510585312143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51211082258377361560832381 19204155846891510585312143)
        ·
          refine ⟨28806233770337265877968215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19204155846891510585312143 28806233770337265877968215)
          ·
            refine ⟨43209350655505898816952323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28806233770337265877968215 43209350655505898816952323)
            ·
              refine ⟨64814025983258848225428485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43209350655505898816952323 64814025983258848225428485)
              ·
                refine ⟨12152629871861034042267841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64814025983258848225428485 12152629871861034042267841)
                ·
                  refine ⟨9114472403895775531700881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12152629871861034042267841 9114472403895775531700881)
                  ·
                    refine ⟨6835854302921831648775661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9114472403895775531700881 6835854302921831648775661)
                    ·
                      refine ⟨2563445363595686868290873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6835854302921831648775661 2563445363595686868290873)
                      ·
                        rfl

theorem cell23_4992292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4992292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992292 prefixEnd_4992292 := by exact prefixLift 4992292
  have htrace : WordTrace (prefixWord ++ tailWord_4992292) baseStart_4992292 baseEnd_4992292 := by
    simpa [prefixWord, tailWord_4992292, baseEnd_4992292] using wordTrace_append hprefix tailTrace_4992292
  have hstable : (prefixWord ++ tailWord_4992292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992292).length < 2 ^ (prefixWord ++ tailWord_4992292).sum := by decide
  have hdescent : baseEnd_4992292 < baseStart_4992292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992356 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_4992356 : Nat := 118140960795 + 4992356 * 2 ^ 59
def prefixEnd_4992356 : Nat := 4983230072969 + 3 ^ 40 * 4992356 * 2
def baseEnd_4992356 : Nat := 2563478226357574617890579

theorem tailTrace_4992356 : CollatzResearch.WordTrace tailWord_4992356 prefixEnd_4992356 2563478226357574617890579 := by
  unfold tailWord_4992356
  simp only [CollatzResearch.WordTrace]
  refine ⟨91043091150777156684422461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121390788201036208912563281 91043091150777156684422461)
  ·
    refine ⟨34141159181541433756658423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91043091150777156684422461 34141159181541433756658423)
    ·
      refine ⟨51211738772312150634987635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34141159181541433756658423 51211738772312150634987635)
      ·
        refine ⟨76817608158468225952481453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51211738772312150634987635 76817608158468225952481453)
        ·
          refine ⟨28806603059425584732180545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76817608158468225952481453 28806603059425584732180545)
          ·
            refine ⟨21604952294569188549135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28806603059425584732180545 21604952294569188549135409)
            ·
              refine ⟨16203714220926891411851557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21604952294569188549135409 16203714220926891411851557)
              ·
                refine ⟨3038196416423792139722167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16203714220926891411851557 3038196416423792139722167)
                ·
                  refine ⟨4557294624635688209583251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038196416423792139722167 4557294624635688209583251)
                  ·
                    refine ⟨6835941936953532314374877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557294624635688209583251 6835941936953532314374877)
                    ·
                      refine ⟨2563478226357574617890579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6835941936953532314374877 2563478226357574617890579)
                      ·
                        rfl

theorem cell23_4992356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_4992356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992356 prefixEnd_4992356 := by exact prefixLift 4992356
  have htrace : WordTrace (prefixWord ++ tailWord_4992356) baseStart_4992356 baseEnd_4992356 := by
    simpa [prefixWord, tailWord_4992356, baseEnd_4992356] using wordTrace_append hprefix tailTrace_4992356
  have hstable : (prefixWord ++ tailWord_4992356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992356).length < 2 ^ (prefixWord ++ tailWord_4992356).sum := by decide
  have hdescent : baseEnd_4992356 < baseStart_4992356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992375 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4992375 : Nat := 118140960795 + 4992375 * 2 ^ 59
def prefixEnd_4992375 : Nat := 4983230072969 + 3 ^ 40 * 4992375 * 2
def baseEnd_4992375 : Nat := 2563487982490010043552991

theorem tailTrace_4992375 : CollatzResearch.WordTrace tailWord_4992375 prefixEnd_4992375 2563487982490010043552991 := by
  unfold tailWord_4992375
  simp only [CollatzResearch.WordTrace]
  refine ⟨182086875288485479613786579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121391250192323653075857719 182086875288485479613786579)
  ·
    refine ⟨273130312932728219420679869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182086875288485479613786579 273130312932728219420679869)
    ·
      refine ⟨102423867349773082282754951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273130312932728219420679869 102423867349773082282754951)
      ·
        refine ⟨153635801024659623424132427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102423867349773082282754951 153635801024659623424132427)
        ·
          refine ⟨230453701536989435136198641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153635801024659623424132427 230453701536989435136198641)
          ·
            refine ⟨172840276152742076352148981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230453701536989435136198641 172840276152742076352148981)
            ·
              refine ⟨16203775889319569658013967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172840276152742076352148981 16203775889319569658013967)
              ·
                refine ⟨24305663833979354487020951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16203775889319569658013967 24305663833979354487020951)
                ·
                  refine ⟨36458495750969031730531427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24305663833979354487020951 36458495750969031730531427)
                  ·
                    refine ⟨54687743626453547595797141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36458495750969031730531427 54687743626453547595797141)
                    ·
                      refine ⟨2563487982490010043552991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54687743626453547595797141 2563487982490010043552991)
                      ·
                        rfl

theorem cell23_4992375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4992375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992375 prefixEnd_4992375 := by exact prefixLift 4992375
  have htrace : WordTrace (prefixWord ++ tailWord_4992375) baseStart_4992375 baseEnd_4992375 := by
    simpa [prefixWord, tailWord_4992375, baseEnd_4992375] using wordTrace_append hprefix tailTrace_4992375
  have hstable : (prefixWord ++ tailWord_4992375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992375).length < 2 ^ (prefixWord ++ tailWord_4992375).sum := by decide
  have hdescent : baseEnd_4992375 < baseStart_4992375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992379 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 3, 2, 2]
def baseStart_4992379 : Nat := 118140960795 + 4992379 * 2 ^ 59
def prefixEnd_4992379 : Nat := 4983230072969 + 3 ^ 40 * 4992379 * 2
def baseEnd_4992379 : Nat := 2563490036412628027902973

theorem tailTrace_4992379 : CollatzResearch.WordTrace tailWord_4992379 prefixEnd_4992379 2563490036412628027902973 := by
  unfold tailWord_4992379
  simp only [CollatzResearch.WordTrace]
  refine ⟨182087021180470988296932191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121391347453647325531288127 182087021180470988296932191)
  ·
    refine ⟨273130531770706482445398287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182087021180470988296932191 273130531770706482445398287)
    ·
      refine ⟨409695797656059723668097431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273130531770706482445398287 409695797656059723668097431)
      ·
        refine ⟨614543696484089585502146147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409695797656059723668097431 614543696484089585502146147)
        ·
          refine ⟨921815544726134378253219221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614543696484089585502146147 921815544726134378253219221)
          ·
            refine ⟨43210103659037548980619651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 921815544726134378253219221 43210103659037548980619651)
            ·
              refine ⟨64815155488556323470929477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43210103659037548980619651 64815155488556323470929477)
              ·
                refine ⟨12152841654104310650799277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64815155488556323470929477 12152841654104310650799277)
                ·
                  refine ⟨4557315620289116494049729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12152841654104310650799277 4557315620289116494049729)
                  ·
                    refine ⟨3417986715216837370537297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557315620289116494049729 3417986715216837370537297)
                    ·
                      refine ⟨2563490036412628027902973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3417986715216837370537297 2563490036412628027902973)
                      ·
                        rfl

theorem cell23_4992379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2, 2].length) (baseStart_4992379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992379 prefixEnd_4992379 := by exact prefixLift 4992379
  have htrace : WordTrace (prefixWord ++ tailWord_4992379) baseStart_4992379 baseEnd_4992379 := by
    simpa [prefixWord, tailWord_4992379, baseEnd_4992379] using wordTrace_append hprefix tailTrace_4992379
  have hstable : (prefixWord ++ tailWord_4992379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992379).length < 2 ^ (prefixWord ++ tailWord_4992379).sum := by decide
  have hdescent : baseEnd_4992379 < baseStart_4992379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992413 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4992413 : Nat := 118140960795 + 4992413 * 2 ^ 59
def prefixEnd_4992413 : Nat := 4983230072969 + 3 ^ 40 * 4992413 * 2
def baseEnd_4992413 : Nat := 2563507494754880894877817

theorem tailTrace_4992413 : CollatzResearch.WordTrace tailWord_4992413 prefixEnd_4992413 2563507494754880894877817 := by
  unfold tailWord_4992413
  simp only [CollatzResearch.WordTrace]
  refine ⟨182088261262347812103669893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121392174174898541402446595 182088261262347812103669893)
  ·
    refine ⟨34141548986690214769438105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182088261262347812103669893 34141548986690214769438105)
    ·
      refine ⟨25606161740017661077078579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34141548986690214769438105 25606161740017661077078579)
      ·
        refine ⟨38409242610026491615617869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25606161740017661077078579 38409242610026491615617869)
        ·
          refine ⟨14403465978759934355856701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38409242610026491615617869 14403465978759934355856701)
          ·
            refine ⟨5401299742034975383446263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14403465978759934355856701 5401299742034975383446263)
            ·
              refine ⟨8101949613052463075169395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401299742034975383446263 8101949613052463075169395)
              ·
                refine ⟨12152924419578694612754093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101949613052463075169395 12152924419578694612754093)
                ·
                  refine ⟨4557346657342010479782785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12152924419578694612754093 4557346657342010479782785)
                  ·
                    refine ⟨3418009993006507859837089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557346657342010479782785 3418009993006507859837089)
                    ·
                      refine ⟨2563507494754880894877817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418009993006507859837089 2563507494754880894877817)
                      ·
                        rfl

theorem cell23_4992413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4992413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992413 prefixEnd_4992413 := by exact prefixLift 4992413
  have htrace : WordTrace (prefixWord ++ tailWord_4992413) baseStart_4992413 baseEnd_4992413 := by
    simpa [prefixWord, tailWord_4992413, baseEnd_4992413] using wordTrace_append hprefix tailTrace_4992413
  have hstable : (prefixWord ++ tailWord_4992413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992413).length < 2 ^ (prefixWord ++ tailWord_4992413).sum := by decide
  have hdescent : baseEnd_4992413 < baseStart_4992413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992439 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_4992439 : Nat := 118140960795 + 4992439 * 2 ^ 59
def prefixEnd_4992439 : Nat := 4983230072969 + 3 ^ 40 * 4992439 * 2
def baseEnd_4992439 : Nat := 2563520845251897793152697

theorem tailTrace_4992439 : CollatzResearch.WordTrace tailWord_4992439 prefixEnd_4992439 2563520845251897793152697 := by
  unfold tailWord_4992439
  simp only [CollatzResearch.WordTrace]
  refine ⟨182089209560253618544116371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121392806373502412362744247 182089209560253618544116371)
  ·
    refine ⟨273133814340380427816174557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182089209560253618544116371 273133814340380427816174557)
    ·
      refine ⟨102425180377642660431065459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273133814340380427816174557 102425180377642660431065459)
      ·
        refine ⟨153637770566463990646598189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102425180377642660431065459 153637770566463990646598189)
        ·
          refine ⟨57614163962423996492474321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153637770566463990646598189 57614163962423996492474321)
          ·
            refine ⟨43210622971817997369355741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57614163962423996492474321 43210622971817997369355741)
            ·
              refine ⟨16203983614431749013508403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43210622971817997369355741 16203983614431749013508403)
              ·
                refine ⟨24305975421647623520262605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16203983614431749013508403 24305975421647623520262605)
                ·
                  refine ⟨9114740783117858820098477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24305975421647623520262605 9114740783117858820098477)
                  ·
                    refine ⟨3418027793669197057536929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9114740783117858820098477 3418027793669197057536929)
                    ·
                      refine ⟨2563520845251897793152697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418027793669197057536929 2563520845251897793152697)
                      ·
                        rfl

theorem cell23_4992439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_4992439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992439 prefixEnd_4992439 := by exact prefixLift 4992439
  have htrace : WordTrace (prefixWord ++ tailWord_4992439) baseStart_4992439 baseEnd_4992439 := by
    simpa [prefixWord, tailWord_4992439, baseEnd_4992439] using wordTrace_append hprefix tailTrace_4992439
  have hstable : (prefixWord ++ tailWord_4992439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992439).length < 2 ^ (prefixWord ++ tailWord_4992439).sum := by decide
  have hdescent : baseEnd_4992439 < baseStart_4992439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_4992465 : Nat := 118140960795 + 4992465 * 2 ^ 59
def prefixEnd_4992465 : Nat := 4983230072969 + 3 ^ 40 * 4992465 * 2
def baseEnd_4992465 : Nat := 2563534195748914691427577

theorem tailTrace_4992465 : CollatzResearch.WordTrace tailWord_4992465 prefixEnd_4992465 2563534195748914691427577 := by
  unfold tailWord_4992465
  simp only [CollatzResearch.WordTrace]
  refine ⟨182090157858159424984562849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121393438572106283323041899 182090157858159424984562849)
  ·
    refine ⟨136567618393619568738422137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182090157858159424984562849 136567618393619568738422137)
    ·
      refine ⟨102425713795214676553816603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136567618393619568738422137 102425713795214676553816603)
      ·
        refine ⟨153638570692822014830724905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102425713795214676553816603 153638570692822014830724905)
        ·
          refine ⟨115228928019616511123043679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153638570692822014830724905 115228928019616511123043679)
          ·
            refine ⟨172843392029424766684565519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115228928019616511123043679 172843392029424766684565519)
            ·
              refine ⟨259265088044137150026848279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172843392029424766684565519 259265088044137150026848279)
              ·
                refine ⟨388897632066205725040272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259265088044137150026848279 388897632066205725040272419)
                ·
                  refine ⟨583346448099308587560408629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388897632066205725040272419 583346448099308587560408629)
                  ·
                    refine ⟨54688729509310180083788309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 583346448099308587560408629 54688729509310180083788309)
                    ·
                      refine ⟨2563534195748914691427577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54688729509310180083788309 2563534195748914691427577)
                      ·
                        rfl

theorem cell23_4992465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_4992465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992465 prefixEnd_4992465 := by exact prefixLift 4992465
  have htrace : WordTrace (prefixWord ++ tailWord_4992465) baseStart_4992465 baseEnd_4992465 := by
    simpa [prefixWord, tailWord_4992465, baseEnd_4992465] using wordTrace_append hprefix tailTrace_4992465
  have hstable : (prefixWord ++ tailWord_4992465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992465).length < 2 ^ (prefixWord ++ tailWord_4992465).sum := by decide
  have hdescent : baseEnd_4992465 < baseStart_4992465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992469 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4992469 : Nat := 118140960795 + 4992469 * 2 ^ 59
def prefixEnd_4992469 : Nat := 4983230072969 + 3 ^ 40 * 4992469 * 2
def baseEnd_4992469 : Nat := 2563536249671532675777559

theorem tailTrace_4992469 : CollatzResearch.WordTrace tailWord_4992469 prefixEnd_4992469 2563536249671532675777559 := by
  unfold tailWord_4992469
  simp only [CollatzResearch.WordTrace]
  refine ⟨182090303750144933667708461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121393535833429955778472307 182090303750144933667708461)
  ·
    refine ⟨68283863906304350125390673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182090303750144933667708461 68283863906304350125390673)
    ·
      refine ⟨51212897929728262594043005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68283863906304350125390673 51212897929728262594043005)
      ·
        refine ⟨19204836723648098472766127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51212897929728262594043005 19204836723648098472766127)
        ·
          refine ⟨28807255085472147709149191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19204836723648098472766127 28807255085472147709149191)
          ·
            refine ⟨43210882628208221563723787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28807255085472147709149191 43210882628208221563723787)
            ·
              refine ⟨64816323942312332345585681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43210882628208221563723787 64816323942312332345585681)
              ·
                refine ⟨48612242956734249259189261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64816323942312332345585681 48612242956734249259189261)
                ·
                  refine ⟨18229591108775343472195973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48612242956734249259189261 18229591108775343472195973)
                  ·
                    refine ⟨3418048332895376901036745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18229591108775343472195973 3418048332895376901036745)
                    ·
                      refine ⟨2563536249671532675777559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418048332895376901036745 2563536249671532675777559)
                      ·
                        rfl

theorem cell23_4992469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4992469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992469 prefixEnd_4992469 := by exact prefixLift 4992469
  have htrace : WordTrace (prefixWord ++ tailWord_4992469) baseStart_4992469 baseEnd_4992469 := by
    simpa [prefixWord, tailWord_4992469, baseEnd_4992469] using wordTrace_append hprefix tailTrace_4992469
  have hstable : (prefixWord ++ tailWord_4992469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992469).length < 2 ^ (prefixWord ++ tailWord_4992469).sum := by decide
  have hdescent : baseEnd_4992469 < baseStart_4992469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992472 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_4992472 : Nat := 118140960795 + 4992472 * 2 ^ 59
def prefixEnd_4992472 : Nat := 4983230072969 + 3 ^ 40 * 4992472 * 2
def baseEnd_4992472 : Nat := 2563537790113496164040045

theorem tailTrace_4992472 : CollatzResearch.WordTrace tailWord_4992472 prefixEnd_4992472 2563537790113496164040045 := by
  unfold tailWord_4992472
  simp only [CollatzResearch.WordTrace]
  refine ⟨91045206584567032590033835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121393608779422710120045113 91045206584567032590033835)
  ·
    refine ⟨136567809876850548885050753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91045206584567032590033835 136567809876850548885050753)
    ·
      refine ⟨102425857407637911663788065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136567809876850548885050753 102425857407637911663788065)
      ·
        refine ⟨76819393055728433747841049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102425857407637911663788065 76819393055728433747841049)
        ·
          refine ⟨57614544791796325310880787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76819393055728433747841049 57614544791796325310880787)
          ·
            refine ⟨86421817187694487966321181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57614544791796325310880787 86421817187694487966321181)
            ·
              refine ⟨32408181445385432987370443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86421817187694487966321181 32408181445385432987370443)
              ·
                refine ⟨48612272168078149481055665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32408181445385432987370443 48612272168078149481055665)
                ·
                  refine ⟨36459204126058612110791749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48612272168078149481055665 36459204126058612110791749)
                  ·
                    refine ⟨6836100773635989770773453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36459204126058612110791749 6836100773635989770773453)
                    ·
                      refine ⟨2563537790113496164040045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836100773635989770773453 2563537790113496164040045)
                      ·
                        rfl

theorem cell23_4992472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_4992472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992472 prefixEnd_4992472 := by exact prefixLift 4992472
  have htrace : WordTrace (prefixWord ++ tailWord_4992472) baseStart_4992472 baseEnd_4992472 := by
    simpa [prefixWord, tailWord_4992472, baseEnd_4992472] using wordTrace_append hprefix tailTrace_4992472
  have hstable : (prefixWord ++ tailWord_4992472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992472).length < 2 ^ (prefixWord ++ tailWord_4992472).sum := by decide
  have hdescent : baseEnd_4992472 < baseStart_4992472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992509 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 5]
def baseStart_4992509 : Nat := 118140960795 + 4992509 * 2 ^ 59
def prefixEnd_4992509 : Nat := 4983230072969 + 3 ^ 40 * 4992509 * 2
def baseEnd_4992509 : Nat := 284839643210856946586375

theorem tailTrace_4992509 : CollatzResearch.WordTrace tailWord_4992509 prefixEnd_4992509 284839643210856946586375 := by
  unfold tailWord_4992509
  simp only [CollatzResearch.WordTrace]
  refine ⟨182091762670000020499164581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121394508446666680332776387 182091762670000020499164581)
  ·
    refine ⟨34142205500625003843593359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182091762670000020499164581 34142205500625003843593359)
    ·
      refine ⟨51213308250937505765390039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34142205500625003843593359 51213308250937505765390039)
      ·
        refine ⟨76819962376406258648085059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51213308250937505765390039 76819962376406258648085059)
        ·
          refine ⟨115229943564609387972127589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76819962376406258648085059 115229943564609387972127589)
          ·
            refine ⟨21605614418364260244773923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115229943564609387972127589 21605614418364260244773923)
            ·
              refine ⟨32408421627546390367160885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21605614418364260244773923 32408421627546390367160885)
              ·
                refine ⟨3038289527582474096921333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32408421627546390367160885 3038289527582474096921333)
                ·
                  refine ⟨284839643210856946586375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3038289527582474096921333 284839643210856946586375)
                  ·
                    rfl

theorem cell23_4992509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_4992509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992509 prefixEnd_4992509 := by exact prefixLift 4992509
  have htrace : WordTrace (prefixWord ++ tailWord_4992509) baseStart_4992509 baseEnd_4992509 := by
    simpa [prefixWord, tailWord_4992509, baseEnd_4992509] using wordTrace_append hprefix tailTrace_4992509
  have hstable : (prefixWord ++ tailWord_4992509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992509).length < 2 ^ (prefixWord ++ tailWord_4992509).sum := by decide
  have hdescent : baseEnd_4992509 < baseStart_4992509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992519 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4992519 : Nat := 118140960795 + 4992519 * 2 ^ 59
def prefixEnd_4992519 : Nat := 4983230072969 + 3 ^ 40 * 4992519 * 2
def baseEnd_4992519 : Nat := 2563561923704257480152329

theorem tailTrace_4992519 : CollatzResearch.WordTrace tailWord_4992519 prefixEnd_4992519 2563561923704257480152329 := by
  unfold tailWord_4992519
  simp only [CollatzResearch.WordTrace]
  refine ⟨182092127399963792207028611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121394751599975861471352407 182092127399963792207028611)
  ·
    refine ⟨273138191099945688310542917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182092127399963792207028611 273138191099945688310542917)
    ·
      refine ⟨51213410831239816558226797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273138191099945688310542917 51213410831239816558226797)
      ·
        refine ⟨19205029061714931209335049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51213410831239816558226797 19205029061714931209335049)
        ·
          refine ⟨14403771796286198407001287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19205029061714931209335049 14403771796286198407001287)
          ·
            refine ⟨21605657694429297610501931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14403771796286198407001287 21605657694429297610501931)
            ·
              refine ⟨32408486541643946415752897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21605657694429297610501931 32408486541643946415752897)
              ·
                refine ⟨24306364906232959811814673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32408486541643946415752897 24306364906232959811814673)
                ·
                  refine ⟨18229773679674719858861005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24306364906232959811814673 18229773679674719858861005)
                  ·
                    refine ⟨6836165129878019947072877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18229773679674719858861005 6836165129878019947072877)
                    ·
                      refine ⟨2563561923704257480152329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836165129878019947072877 2563561923704257480152329)
                      ·
                        rfl

theorem cell23_4992519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4992519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992519 prefixEnd_4992519 := by exact prefixLift 4992519
  have htrace : WordTrace (prefixWord ++ tailWord_4992519) baseStart_4992519 baseEnd_4992519 := by
    simpa [prefixWord, tailWord_4992519, baseEnd_4992519] using wordTrace_append hprefix tailTrace_4992519
  have hstable : (prefixWord ++ tailWord_4992519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992519).length < 2 ^ (prefixWord ++ tailWord_4992519).sum := by decide
  have hdescent : baseEnd_4992519 < baseStart_4992519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992562 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_4992562 : Nat := 118140960795 + 4992562 * 2 ^ 59
def prefixEnd_4992562 : Nat := 4983230072969 + 3 ^ 40 * 4992562 * 2
def baseEnd_4992562 : Nat := 2563584003372400811914631

theorem tailTrace_4992562 : CollatzResearch.WordTrace tailWord_4992562 prefixEnd_4992562 2563584003372400811914631 := by
  unfold tailWord_4992562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45523423934702002637710985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121395797159205340367229293 45523423934702002637710985)
  ·
    refine ⟨34142567951026501978283239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45523423934702002637710985 34142567951026501978283239)
    ·
      refine ⟨51213851926539752967424859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34142567951026501978283239 51213851926539752967424859)
      ·
        refine ⟨76820777889809629451137289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51213851926539752967424859 76820777889809629451137289)
        ·
          refine ⟨57615583417357222088352967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76820777889809629451137289 57615583417357222088352967)
          ·
            refine ⟨86423375126035833132529451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57615583417357222088352967 86423375126035833132529451)
            ·
              refine ⟨129635062689053749698794177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86423375126035833132529451 129635062689053749698794177)
              ·
                refine ⟨97226297016790312274095633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129635062689053749698794177 97226297016790312274095633)
                ·
                  refine ⟨72919722762592734205571725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97226297016790312274095633 72919722762592734205571725)
                  ·
                    refine ⟨27344896035972275327089397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72919722762592734205571725 27344896035972275327089397)
                    ·
                      refine ⟨2563584003372400811914631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27344896035972275327089397 2563584003372400811914631)
                      ·
                        rfl

theorem cell23_4992562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_4992562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992562 prefixEnd_4992562 := by exact prefixLift 4992562
  have htrace : WordTrace (prefixWord ++ tailWord_4992562) baseStart_4992562 baseEnd_4992562 := by
    simpa [prefixWord, tailWord_4992562, baseEnd_4992562] using wordTrace_append hprefix tailTrace_4992562
  have hstable : (prefixWord ++ tailWord_4992562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992562).length < 2 ^ (prefixWord ++ tailWord_4992562).sum := by decide
  have hdescent : baseEnd_4992562 < baseStart_4992562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992599 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 6]
def baseStart_4992599 : Nat := 118140960795 + 4992599 * 2 ^ 59
def prefixEnd_4992599 : Nat := 4983230072969 + 3 ^ 40 * 4992599 * 2
def baseEnd_4992599 : Nat := 284844778017401907461329

theorem tailTrace_4992599 : CollatzResearch.WordTrace tailWord_4992599 prefixEnd_4992599 284844778017401907461329 := by
  unfold tailWord_4992599
  simp only [CollatzResearch.WordTrace]
  refine ⟨182095045239673965869940851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121396696826449310579960567 182095045239673965869940851)
  ·
    refine ⟨273142567859510948804911277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182095045239673965869940851 273142567859510948804911277)
    ·
      refine ⟨102428462947316605801841729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273142567859510948804911277 102428462947316605801841729)
      ·
        refine ⟨76821347210487454351381297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102428462947316605801841729 76821347210487454351381297)
        ·
          refine ⟨57616010407865590763535973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76821347210487454351381297 57616010407865590763535973)
          ·
            refine ⟨10803001951474798268162995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57616010407865590763535973 10803001951474798268162995)
            ·
              refine ⟨16204502927212197402244493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10803001951474798268162995 16204502927212197402244493)
              ·
                refine ⟨6076688597704574025841685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16204502927212197402244493 6076688597704574025841685)
                ·
                  refine ⟨284844778017401907461329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6076688597704574025841685 284844778017401907461329)
                  ·
                    rfl

theorem cell23_4992599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 6].length) (baseStart_4992599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992599 prefixEnd_4992599 := by exact prefixLift 4992599
  have htrace : WordTrace (prefixWord ++ tailWord_4992599) baseStart_4992599 baseEnd_4992599 := by
    simpa [prefixWord, tailWord_4992599, baseEnd_4992599] using wordTrace_append hprefix tailTrace_4992599
  have hstable : (prefixWord ++ tailWord_4992599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992599).length < 2 ^ (prefixWord ++ tailWord_4992599).sum := by decide
  have hdescent : baseEnd_4992599 < baseStart_4992599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992602 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4992602 : Nat := 118140960795 + 4992602 * 2 ^ 59
def prefixEnd_4992602 : Nat := 4983230072969 + 3 ^ 40 * 4992602 * 2
def baseEnd_4992602 : Nat := 2563604542598580655414447

theorem tailTrace_4992602 : CollatzResearch.WordTrace tailWord_4992602 prefixEnd_4992602 2563604542598580655414447 := by
  unfold tailWord_4992602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45523788664665774345575015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121396769772442064921533373 45523788664665774345575015)
  ·
    refine ⟨68285682996998661518362523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45523788664665774345575015 68285682996998661518362523)
    ·
      refine ⟨102428524495497992277543785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68285682996998661518362523 102428524495497992277543785)
      ·
        refine ⟨76821393371623494208157839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102428524495497992277543785 76821393371623494208157839)
        ·
          refine ⟨115232090057435241312236759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76821393371623494208157839 115232090057435241312236759)
          ·
            refine ⟨172848135086152861968355139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115232090057435241312236759 172848135086152861968355139)
            ·
              refine ⟨259272202629229292952532709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172848135086152861968355139 259272202629229292952532709)
              ·
                refine ⟨48613537992980492428599883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259272202629229292952532709 48613537992980492428599883)
                ·
                  refine ⟨72920306989470738642899825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48613537992980492428599883 72920306989470738642899825)
                  ·
                    refine ⟨54690230242103053982174869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72920306989470738642899825 54690230242103053982174869)
                    ·
                      refine ⟨2563604542598580655414447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54690230242103053982174869 2563604542598580655414447)
                      ·
                        rfl

theorem cell23_4992602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4992602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992602 prefixEnd_4992602 := by exact prefixLift 4992602
  have htrace : WordTrace (prefixWord ++ tailWord_4992602) baseStart_4992602 baseEnd_4992602 := by
    simpa [prefixWord, tailWord_4992602, baseEnd_4992602] using wordTrace_append hprefix tailTrace_4992602
  have hstable : (prefixWord ++ tailWord_4992602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992602).length < 2 ^ (prefixWord ++ tailWord_4992602).sum := by decide
  have hdescent : baseEnd_4992602 < baseStart_4992602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992619 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 5, 2]
def baseStart_4992619 : Nat := 118140960795 + 4992619 * 2 ^ 59
def prefixEnd_4992619 : Nat := 4983230072969 + 3 ^ 40 * 4992619 * 2
def baseEnd_4992619 : Nat := 2563613271769707088901869

theorem tailTrace_4992619 : CollatzResearch.WordTrace tailWord_4992619 prefixEnd_4992619 2563613271769707088901869 := by
  unfold tailWord_4992619
  simp only [CollatzResearch.WordTrace]
  refine ⟨182095774699601509285668911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121397183133067672857112607 182095774699601509285668911)
  ·
    refine ⟨273143662049402263928503367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182095774699601509285668911 273143662049402263928503367)
    ·
      refine ⟨409715493074103395892755051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273143662049402263928503367 409715493074103395892755051)
      ·
        refine ⟨614573239611155093839132577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409715493074103395892755051 614573239611155093839132577)
        ·
          refine ⟨460929929708366320379349433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614573239611155093839132577 460929929708366320379349433)
          ·
            refine ⟨345697447281274740284512075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460929929708366320379349433 345697447281274740284512075)
            ·
              refine ⟨518546170921912110426768113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345697447281274740284512075 518546170921912110426768113)
              ·
                refine ⟨388909628191434082820076085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518546170921912110426768113 388909628191434082820076085)
                ·
                  refine ⟨36460277642946945264382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388909628191434082820076085 36460277642946945264382133)
                  ·
                    refine ⟨3418151029026276118535825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36460277642946945264382133 3418151029026276118535825)
                    ·
                      refine ⟨2563613271769707088901869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418151029026276118535825 2563613271769707088901869)
                      ·
                        rfl

theorem cell23_4992619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5, 2].length) (baseStart_4992619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992619 prefixEnd_4992619 := by exact prefixLift 4992619
  have htrace : WordTrace (prefixWord ++ tailWord_4992619) baseStart_4992619 baseEnd_4992619 := by
    simpa [prefixWord, tailWord_4992619, baseEnd_4992619] using wordTrace_append hprefix tailTrace_4992619
  have hstable : (prefixWord ++ tailWord_4992619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992619).length < 2 ^ (prefixWord ++ tailWord_4992619).sum := by decide
  have hdescent : baseEnd_4992619 < baseStart_4992619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992649 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_4992649 : Nat := 118140960795 + 4992649 * 2 ^ 59
def prefixEnd_4992649 : Nat := 4983230072969 + 3 ^ 40 * 4992649 * 2
def baseEnd_4992649 : Nat := 2563628676189341971526731

theorem tailTrace_4992649 : CollatzResearch.WordTrace tailWord_4992649 prefixEnd_4992649 2563628676189341971526731 := by
  unfold tailWord_4992649
  simp only [CollatzResearch.WordTrace]
  refine ⟨182096868889492824409261001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121397912592995216272840667 182096868889492824409261001)
  ·
    refine ⟨136572651667119618306945751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182096868889492824409261001 136572651667119618306945751)
    ·
      refine ⟨204858977500679427460418627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136572651667119618306945751 204858977500679427460418627)
      ·
        refine ⟨307288466251019141190627941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204858977500679427460418627 307288466251019141190627941)
        ·
          refine ⟨57616587422066088973242739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307288466251019141190627941 57616587422066088973242739)
          ·
            refine ⟨86424881133099133459864109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57616587422066088973242739 86424881133099133459864109)
            ·
              refine ⟨32409330424912175047449041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86424881133099133459864109 32409330424912175047449041)
              ·
                refine ⟨24306997818684131285586781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32409330424912175047449041 24306997818684131285586781)
                ·
                  refine ⟨9115124182006549232095043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24306997818684131285586781 9115124182006549232095043)
                  ·
                    refine ⟨13672686273009823848142565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9115124182006549232095043 13672686273009823848142565)
                    ·
                      refine ⟨2563628676189341971526731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13672686273009823848142565 2563628676189341971526731)
                      ·
                        rfl

theorem cell23_4992649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_4992649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992649 prefixEnd_4992649 := by exact prefixLift 4992649
  have htrace : WordTrace (prefixWord ++ tailWord_4992649) baseStart_4992649 baseEnd_4992649 := by
    simpa [prefixWord, tailWord_4992649, baseEnd_4992649] using wordTrace_append hprefix tailTrace_4992649
  have hstable : (prefixWord ++ tailWord_4992649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992649).length < 2 ^ (prefixWord ++ tailWord_4992649).sum := by decide
  have hdescent : baseEnd_4992649 < baseStart_4992649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992660 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4992660 : Nat := 118140960795 + 4992660 * 2 ^ 59
def prefixEnd_4992660 : Nat := 4983230072969 + 3 ^ 40 * 4992660 * 2
def baseEnd_4992660 : Nat := 2563634324476541428489181

theorem tailTrace_4992660 : CollatzResearch.WordTrace tailWord_4992660 prefixEnd_4992660 2563634324476541428489181 := by
  unfold tailWord_4992660
  simp only [CollatzResearch.WordTrace]
  refine ⟨91048635046226486643955717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121398180061635315525274289 91048635046226486643955717)
  ·
    refine ⟨17071619071167466245741697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91048635046226486643955717 17071619071167466245741697)
    ·
      refine ⟨12803714303375599684306273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17071619071167466245741697 12803714303375599684306273)
      ·
        refine ⟨9602785727531699763229705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12803714303375599684306273 9602785727531699763229705)
        ·
          refine ⟨7202089295648774822422279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9602785727531699763229705 7202089295648774822422279)
          ·
            refine ⟨10803133943473162233633419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7202089295648774822422279 10803133943473162233633419)
            ·
              refine ⟨16204700915209743350450129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10803133943473162233633419 16204700915209743350450129)
              ·
                refine ⟨12153525686407307512837597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16204700915209743350450129 12153525686407307512837597)
                ·
                  refine ⟨4557572132402740317314099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12153525686407307512837597 4557572132402740317314099)
                  ·
                    refine ⟨6836358198604110475971149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557572132402740317314099 6836358198604110475971149)
                    ·
                      refine ⟨2563634324476541428489181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836358198604110475971149 2563634324476541428489181)
                      ·
                        rfl

theorem cell23_4992660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4992660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992660 prefixEnd_4992660 := by exact prefixLift 4992660
  have htrace : WordTrace (prefixWord ++ tailWord_4992660) baseStart_4992660 baseEnd_4992660 := by
    simpa [prefixWord, tailWord_4992660, baseEnd_4992660] using wordTrace_append hprefix tailTrace_4992660
  have hstable : (prefixWord ++ tailWord_4992660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992660).length < 2 ^ (prefixWord ++ tailWord_4992660).sum := by decide
  have hdescent : baseEnd_4992660 < baseStart_4992660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992670 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4992670 : Nat := 118140960795 + 4992670 * 2 ^ 59
def prefixEnd_4992670 : Nat := 4983230072969 + 3 ^ 40 * 4992670 * 2
def baseEnd_4992670 : Nat := 2563639459283086389364135

theorem tailTrace_4992670 : CollatzResearch.WordTrace tailWord_4992670 prefixEnd_4992670 2563639459283086389364135 := by
  unfold tailWord_4992670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22762204352802093124471933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121398423214944496663850309 22762204352802093124471933)
  ·
    refine ⟨8535826632300784921676975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22762204352802093124471933 8535826632300784921676975)
    ·
      refine ⟨12803739948451177382515463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8535826632300784921676975 12803739948451177382515463)
      ·
        refine ⟨19205609922676766073773195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12803739948451177382515463 19205609922676766073773195)
        ·
          refine ⟨28808414884015149110659793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19205609922676766073773195 28808414884015149110659793)
          ·
            refine ⟨21606311163011361832994845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28808414884015149110659793 21606311163011361832994845)
            ·
              refine ⟨8102366686129260687373067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21606311163011361832994845 8102366686129260687373067)
              ·
                refine ⟨12153550029193891031059601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8102366686129260687373067 12153550029193891031059601)
                ·
                  refine ⟨9115162521895418273294701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12153550029193891031059601 9115162521895418273294701)
                  ·
                    refine ⟨3418185945710781852485513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9115162521895418273294701 3418185945710781852485513)
                    ·
                      refine ⟨2563639459283086389364135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418185945710781852485513 2563639459283086389364135)
                      ·
                        rfl

theorem cell23_4992670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4992670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992670 prefixEnd_4992670 := by exact prefixLift 4992670
  have htrace : WordTrace (prefixWord ++ tailWord_4992670) baseStart_4992670 baseEnd_4992670 := by
    simpa [prefixWord, tailWord_4992670, baseEnd_4992670] using wordTrace_append hprefix tailTrace_4992670
  have hstable : (prefixWord ++ tailWord_4992670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992670).length < 2 ^ (prefixWord ++ tailWord_4992670).sum := by decide
  have hdescent : baseEnd_4992670 < baseStart_4992670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992693 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4992693 : Nat := 118140960795 + 4992693 * 2 ^ 59
def prefixEnd_4992693 : Nat := 4983230072969 + 3 ^ 40 * 4992693 * 2
def baseEnd_4992693 : Nat := 854550423112713266458843

theorem tailTrace_4992693 : CollatzResearch.WordTrace tailWord_4992693 prefixEnd_4992693 854550423112713266458843 := by
  unfold tailWord_4992693
  simp only [CollatzResearch.WordTrace]
  refine ⟨182098473701333419923862733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121398982467555613282575155 182098473701333419923862733)
  ·
    refine ⟨68286927638000032471448525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182098473701333419923862733 68286927638000032471448525)
    ·
      refine ⟨25607597864250012176793197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68286927638000032471448525 25607597864250012176793197)
      ·
        refine ⟨9602849199093754566297449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25607597864250012176793197 9602849199093754566297449)
        ·
          refine ⟨7202136899320315924723087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9602849199093754566297449 7202136899320315924723087)
          ·
            refine ⟨10803205348980473887084631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7202136899320315924723087 10803205348980473887084631)
            ·
              refine ⟨16204808023470710830626947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10803205348980473887084631 16204808023470710830626947)
              ·
                refine ⟨24307212035206066245940421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16204808023470710830626947 24307212035206066245940421)
                ·
                  refine ⟨4557602256601137421113829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24307212035206066245940421 4557602256601137421113829)
                  ·
                    refine ⟨854550423112713266458843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4557602256601137421113829 854550423112713266458843)
                    ·
                      rfl

theorem cell23_4992693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4992693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992693 prefixEnd_4992693 := by exact prefixLift 4992693
  have htrace : WordTrace (prefixWord ++ tailWord_4992693) baseStart_4992693 baseEnd_4992693 := by
    simpa [prefixWord, tailWord_4992693, baseEnd_4992693] using wordTrace_append hprefix tailTrace_4992693
  have hstable : (prefixWord ++ tailWord_4992693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992693).length < 2 ^ (prefixWord ++ tailWord_4992693).sum := by decide
  have hdescent : baseEnd_4992693 < baseStart_4992693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992699 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3]
def baseStart_4992699 : Nat := 118140960795 + 4992699 * 2 ^ 59
def prefixEnd_4992699 : Nat := 4983230072969 + 3 ^ 40 * 4992699 * 2
def baseEnd_4992699 : Nat := 2563654350222066775901501

theorem tailTrace_4992699 : CollatzResearch.WordTrace tailWord_4992699 prefixEnd_4992699 2563654350222066775901501 := by
  unfold tailWord_4992699
  simp only [CollatzResearch.WordTrace]
  refine ⟨182098692539311682948581151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121399128359541121965720767 182098692539311682948581151)
  ·
    refine ⟨273148038808967524422871727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182098692539311682948581151 273148038808967524422871727)
    ·
      refine ⟨409722058213451286634307591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273148038808967524422871727 409722058213451286634307591)
      ·
        refine ⟨614583087320176929951461387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409722058213451286634307591 614583087320176929951461387)
        ·
          refine ⟨921874630980265394927192081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614583087320176929951461387 921874630980265394927192081)
          ·
            refine ⟨691405973235199046195394061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921874630980265394927192081 691405973235199046195394061)
            ·
              refine ⟨259277239963199642323272773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691405973235199046195394061 259277239963199642323272773)
              ·
                refine ⟨48614482493099932935613645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259277239963199642323272773 48614482493099932935613645)
                ·
                  refine ⟨18230430934912474850855117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48614482493099932935613645 18230430934912474850855117)
                  ·
                    refine ⟨6836411600592178069070669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18230430934912474850855117 6836411600592178069070669)
                    ·
                      refine ⟨2563654350222066775901501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836411600592178069070669 2563654350222066775901501)
                      ·
                        rfl

theorem cell23_4992699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].length) (baseStart_4992699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992699 prefixEnd_4992699 := by exact prefixLift 4992699
  have htrace : WordTrace (prefixWord ++ tailWord_4992699) baseStart_4992699 baseEnd_4992699 := by
    simpa [prefixWord, tailWord_4992699, baseEnd_4992699] using wordTrace_append hprefix tailTrace_4992699
  have hstable : (prefixWord ++ tailWord_4992699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992699).length < 2 ^ (prefixWord ++ tailWord_4992699).sum := by decide
  have hdescent : baseEnd_4992699 < baseStart_4992699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992700 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4992700 : Nat := 118140960795 + 4992700 * 2 ^ 59
def prefixEnd_4992700 : Nat := 4983230072969 + 3 ^ 40 * 4992700 * 2
def baseEnd_4992700 : Nat := 2563654863702721271988997

theorem tailTrace_4992700 : CollatzResearch.WordTrace tailWord_4992700 prefixEnd_4992700 2563654863702721271988997 := by
  unfold tailWord_4992700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91049364506154030059683777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121399152674872040079578369 91049364506154030059683777)
  ·
    refine ⟨68287023379615522544762833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91049364506154030059683777 68287023379615522544762833)
    ·
      refine ⟨51215267534711641908572125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68287023379615522544762833 51215267534711641908572125)
      ·
        refine ⟨19205725325516865715714547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51215267534711641908572125 19205725325516865715714547)
        ·
          refine ⟨28808587988275298573571821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19205725325516865715714547 28808587988275298573571821)
          ·
            refine ⟨10803220495603236965089433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28808587988275298573571821 10803220495603236965089433)
            ·
              refine ⟨8102415371702427723817075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10803220495603236965089433 8102415371702427723817075)
              ·
                refine ⟨12153623057553641585725613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8102415371702427723817075 12153623057553641585725613)
                ·
                  refine ⟨4557608646582615594647105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12153623057553641585725613 4557608646582615594647105)
                  ·
                    refine ⟨3418206484936961695985329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557608646582615594647105 3418206484936961695985329)
                    ·
                      refine ⟨2563654863702721271988997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418206484936961695985329 2563654863702721271988997)
                      ·
                        rfl

theorem cell23_4992700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4992700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992700 prefixEnd_4992700 := by exact prefixLift 4992700
  have htrace : WordTrace (prefixWord ++ tailWord_4992700) baseStart_4992700 baseEnd_4992700 := by
    simpa [prefixWord, tailWord_4992700, baseEnd_4992700] using wordTrace_append hprefix tailTrace_4992700
  have hstable : (prefixWord ++ tailWord_4992700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992700).length < 2 ^ (prefixWord ++ tailWord_4992700).sum := by decide
  have hdescent : baseEnd_4992700 < baseStart_4992700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992710 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4992710 : Nat := 118140960795 + 4992710 * 2 ^ 59
def prefixEnd_4992710 : Nat := 4983230072969 + 3 ^ 40 * 4992710 * 2
def baseEnd_4992710 : Nat := 854553332836422077621317

theorem tailTrace_4992710 : CollatzResearch.WordTrace tailWord_4992710 prefixEnd_4992710 854553332836422077621317 := by
  unfold tailWord_4992710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690596679445994744600987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121399395828181221218154389 5690596679445994744600987)
  ·
    refine ⟨8535895019168992116901481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690596679445994744600987 8535895019168992116901481)
    ·
      refine ⟨6401921264376744087676111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8535895019168992116901481 6401921264376744087676111)
      ·
        refine ⟨9602881896565116131514167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401921264376744087676111 9602881896565116131514167)
        ·
          refine ⟨14404322844847674197271251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9602881896565116131514167 14404322844847674197271251)
          ·
            refine ⟨21606484267271511295906877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14404322844847674197271251 21606484267271511295906877)
            ·
              refine ⟨8102431600226816735965079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21606484267271511295906877 8102431600226816735965079)
              ·
                refine ⟨12153647400340225103947619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8102431600226816735965079 12153647400340225103947619)
                ·
                  refine ⟨18230471100510337655921429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12153647400340225103947619 18230471100510337655921429)
                  ·
                    refine ⟨854553332836422077621317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18230471100510337655921429 854553332836422077621317)
                    ·
                      rfl

theorem cell23_4992710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4992710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992710 prefixEnd_4992710 := by exact prefixLift 4992710
  have htrace : WordTrace (prefixWord ++ tailWord_4992710) baseStart_4992710 baseEnd_4992710 := by
    simpa [prefixWord, tailWord_4992710, baseEnd_4992710] using wordTrace_append hprefix tailTrace_4992710
  have hstable : (prefixWord ++ tailWord_4992710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992710).length < 2 ^ (prefixWord ++ tailWord_4992710).sum := by decide
  have hdescent : baseEnd_4992710 < baseStart_4992710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992717 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4992717 : Nat := 118140960795 + 4992717 * 2 ^ 59
def prefixEnd_4992717 : Nat := 4983230072969 + 3 ^ 40 * 4992717 * 2
def baseEnd_4992717 : Nat := 2563663592873847705476419

theorem tailTrace_4992717 : CollatzResearch.WordTrace tailWord_4992717 prefixEnd_4992717 2563663592873847705476419 := by
  unfold tailWord_4992717
  simp only [CollatzResearch.WordTrace]
  refine ⟨182099349053246472022736405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121399566035497648015157603 182099349053246472022736405)
  ·
    refine ⟨8535906986870928376065769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182099349053246472022736405 8535906986870928376065769)
    ·
      refine ⟨6401930240153196282049327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8535906986870928376065769 6401930240153196282049327)
      ·
        refine ⟨9602895360229794423073991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401930240153196282049327 9602895360229794423073991)
        ·
          refine ⟨14404343040344691634610987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9602895360229794423073991 14404343040344691634610987)
          ·
            refine ⟨21606514560517037451916481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14404343040344691634610987 21606514560517037451916481)
            ·
              refine ⟨16204885920387778088937361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21606514560517037451916481 16204885920387778088937361)
              ·
                refine ⟨12153664440290833566703021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16204885920387778088937361 12153664440290833566703021)
                ·
                  refine ⟨4557624165109062587513633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12153664440290833566703021 4557624165109062587513633)
                  ·
                    refine ⟨3418218123831796940635225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557624165109062587513633 3418218123831796940635225)
                    ·
                      refine ⟨2563663592873847705476419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418218123831796940635225 2563663592873847705476419)
                      ·
                        rfl

theorem cell23_4992717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4992717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992717 prefixEnd_4992717 := by exact prefixLift 4992717
  have htrace : WordTrace (prefixWord ++ tailWord_4992717) baseStart_4992717 baseEnd_4992717 := by
    simpa [prefixWord, tailWord_4992717, baseEnd_4992717] using wordTrace_append hprefix tailTrace_4992717
  have hstable : (prefixWord ++ tailWord_4992717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992717).length < 2 ^ (prefixWord ++ tailWord_4992717).sum := by decide
  have hdescent : baseEnd_4992717 < baseStart_4992717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992729 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_4992729 : Nat := 118140960795 + 4992729 * 2 ^ 59
def prefixEnd_4992729 : Nat := 4983230072969 + 3 ^ 40 * 4992729 * 2
def baseEnd_4992729 : Nat := 2563669754641701658526363

theorem tailTrace_4992729 : CollatzResearch.WordTrace tailWord_4992729 prefixEnd_4992729 2563669754641701658526363 := by
  unfold tailWord_4992729
  simp only [CollatzResearch.WordTrace]
  refine ⟨182099786729202998072173241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121399857819468665381448827 182099786729202998072173241)
  ·
    refine ⟨136574840046902248554129931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182099786729202998072173241 136574840046902248554129931)
    ·
      refine ⟨204862260070353372831194897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136574840046902248554129931 204862260070353372831194897)
      ·
        refine ⟨153646695052765029623396173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204862260070353372831194897 153646695052765029623396173)
        ·
          refine ⟨57617510644786886108773565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153646695052765029623396173 57617510644786886108773565)
          ·
            refine ⟨21606566491795082290790087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57617510644786886108773565 21606566491795082290790087)
            ·
              refine ⟨32409849737692623436185131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21606566491795082290790087 32409849737692623436185131)
              ·
                refine ⟨48614774606538935154277697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32409849737692623436185131 48614774606538935154277697)
                ·
                  refine ⟨36461080954904201365708273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48614774606538935154277697 36461080954904201365708273)
                  ·
                    refine ⟨27345810716178151024281205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36461080954904201365708273 27345810716178151024281205)
                    ·
                      refine ⟨2563669754641701658526363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27345810716178151024281205 2563669754641701658526363)
                      ·
                        rfl

theorem cell23_4992729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_4992729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992729 prefixEnd_4992729 := by exact prefixLift 4992729
  have htrace : WordTrace (prefixWord ++ tailWord_4992729) baseStart_4992729 baseEnd_4992729 := by
    simpa [prefixWord, tailWord_4992729, baseEnd_4992729] using wordTrace_append hprefix tailTrace_4992729
  have hstable : (prefixWord ++ tailWord_4992729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992729).length < 2 ^ (prefixWord ++ tailWord_4992729).sum := by decide
  have hdescent : baseEnd_4992729 < baseStart_4992729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992779 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 7]
def baseStart_4992779 : Nat := 118140960795 + 4992779 * 2 ^ 59
def prefixEnd_4992779 : Nat := 4983230072969 + 3 ^ 40 * 4992779 * 2
def baseEnd_4992779 : Nat := 284855047630491829211237

theorem tailTrace_4992779 : CollatzResearch.WordTrace tailWord_4992779 prefixEnd_4992779 284855047630491829211237 := by
  unfold tailWord_4992779
  simp only [CollatzResearch.WordTrace]
  refine ⟨182101610379021856611493391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121401073586014571074328927 182101610379021856611493391)
  ·
    refine ⟨273152415568532784917240087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182101610379021856611493391 273152415568532784917240087)
    ·
      refine ⟨409728623352799177375860131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273152415568532784917240087 409728623352799177375860131)
      ·
        refine ⟨614592935029198766063790197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409728623352799177375860131 614592935029198766063790197)
        ·
          refine ⟨57618087658987384318480331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 614592935029198766063790197 57618087658987384318480331)
          ·
            refine ⟨86427131488481076477720497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57618087658987384318480331 86427131488481076477720497)
            ·
              refine ⟨64820348616360807358290373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86427131488481076477720497 64820348616360807358290373)
              ·
                refine ⟨12153815365567651379679445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64820348616360807358290373 12153815365567651379679445)
                ·
                  refine ⟨284855047630491829211237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12153815365567651379679445 284855047630491829211237)
                  ·
                    rfl

theorem cell23_4992779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 7].length) (baseStart_4992779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992779 prefixEnd_4992779 := by exact prefixLift 4992779
  have htrace : WordTrace (prefixWord ++ tailWord_4992779) baseStart_4992779 baseEnd_4992779 := by
    simpa [prefixWord, tailWord_4992779, baseEnd_4992779] using wordTrace_append hprefix tailTrace_4992779
  have hstable : (prefixWord ++ tailWord_4992779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992779).length < 2 ^ (prefixWord ++ tailWord_4992779).sum := by decide
  have hdescent : baseEnd_4992779 < baseStart_4992779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992863 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 4, 2]
def baseStart_4992863 : Nat := 118140960795 + 4992863 * 2 ^ 59
def prefixEnd_4992863 : Nat := 4983230072969 + 3 ^ 40 * 4992863 * 2
def baseEnd_4992863 : Nat := 2563738561049404134250747

theorem tailTrace_4992863 : CollatzResearch.WordTrace tailWord_4992863 prefixEnd_4992863 2563738561049404134250747 := by
  unfold tailWord_4992863
  simp only [CollatzResearch.WordTrace]
  refine ⟨182104674110717538957551243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121403116073811692638367495 182104674110717538957551243)
  ·
    refine ⟨273157011166076308436326865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182104674110717538957551243 273157011166076308436326865)
    ·
      refine ⟨204867758374557231327245149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273157011166076308436326865 204867758374557231327245149)
      ·
        refine ⟨76825409390458961747716931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204867758374557231327245149 76825409390458961747716931)
        ·
          refine ⟨115238114085688442621575397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76825409390458961747716931 115238114085688442621575397)
          ·
            refine ⟨21607146391066582991545387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115238114085688442621575397 21607146391066582991545387)
            ·
              refine ⟨32410719586599874487318081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21607146391066582991545387 32410719586599874487318081)
              ·
                refine ⟨24308039689949905865488561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32410719586599874487318081 24308039689949905865488561)
                ·
                  refine ⟨18231029767462429399116421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24308039689949905865488561 18231029767462429399116421)
                  ·
                    refine ⟨3418318081399205512334329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18231029767462429399116421 3418318081399205512334329)
                    ·
                      refine ⟨2563738561049404134250747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418318081399205512334329 2563738561049404134250747)
                      ·
                        rfl

theorem cell23_4992863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_4992863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992863 prefixEnd_4992863 := by exact prefixLift 4992863
  have htrace : WordTrace (prefixWord ++ tailWord_4992863) baseStart_4992863 baseEnd_4992863 := by
    simpa [prefixWord, tailWord_4992863, baseEnd_4992863] using wordTrace_append hprefix tailTrace_4992863
  have hstable : (prefixWord ++ tailWord_4992863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992863).length < 2 ^ (prefixWord ++ tailWord_4992863).sum := by decide
  have hdescent : baseEnd_4992863 < baseStart_4992863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992896 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_4992896 : Nat := 118140960795 + 4992896 * 2 ^ 59
def prefixEnd_4992896 : Nat := 4983230072969 + 3 ^ 40 * 4992896 * 2
def baseEnd_4992896 : Nat := 2563755505911002505138095

theorem tailTrace_4992896 : CollatzResearch.WordTrace tailWord_4992896 prefixEnd_4992896 2563755505911002505138095 := by
  unfold tailWord_4992896
  simp only [CollatzResearch.WordTrace]
  refine ⟨91052938859798992796751271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121403918479731990395668361 91052938859798992796751271)
  ·
    refine ⟨136579408289698489195126907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91052938859798992796751271 136579408289698489195126907)
    ·
      refine ⟨204869112434547733792690361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136579408289698489195126907 204869112434547733792690361)
      ·
        refine ⟨153651834325910800344517771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204869112434547733792690361 153651834325910800344517771)
        ·
          refine ⟨230477751488866200516776657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153651834325910800344517771 230477751488866200516776657)
          ·
            refine ⟨172858313616649650387582493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230477751488866200516776657 172858313616649650387582493)
            ·
              refine ⟨64821867606243618895343435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172858313616649650387582493 64821867606243618895343435)
              ·
                refine ⟨97232801409365428343015153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64821867606243618895343435 97232801409365428343015153)
                ·
                  refine ⟨72924601057024071257261365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97232801409365428343015153 72924601057024071257261365)
                  ·
                    refine ⟨6836681349096006680368253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72924601057024071257261365 6836681349096006680368253)
                    ·
                      refine ⟨2563755505911002505138095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836681349096006680368253 2563755505911002505138095)
                      ·
                        rfl

theorem cell23_4992896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_4992896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992896 prefixEnd_4992896 := by exact prefixLift 4992896
  have htrace : WordTrace (prefixWord ++ tailWord_4992896) baseStart_4992896 baseEnd_4992896 := by
    simpa [prefixWord, tailWord_4992896, baseEnd_4992896] using wordTrace_append hprefix tailTrace_4992896
  have hstable : (prefixWord ++ tailWord_4992896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992896).length < 2 ^ (prefixWord ++ tailWord_4992896).sum := by decide
  have hdescent : baseEnd_4992896 < baseStart_4992896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992913 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_4992913 : Nat := 118140960795 + 4992913 * 2 ^ 59
def prefixEnd_4992913 : Nat := 4983230072969 + 3 ^ 40 * 4992913 * 2
def baseEnd_4992913 : Nat := 2563764235082128938625517

theorem tailTrace_4992913 : CollatzResearch.WordTrace tailWord_4992913 prefixEnd_4992913 2563764235082128938625517 := by
  unfold tailWord_4992913
  simp only [CollatzResearch.WordTrace]
  refine ⟨182106497760536397496871393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121404331840357598331247595 182106497760536397496871393)
  ·
    refine ⟨136579873320402298122653545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182106497760536397496871393 136579873320402298122653545)
    ·
      refine ⟨102434904990301723591990159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136579873320402298122653545 102434904990301723591990159)
      ·
        refine ⟨153652357485452585387985239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102434904990301723591990159 153652357485452585387985239)
        ·
          refine ⟨230478536228178878081977859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153652357485452585387985239 230478536228178878081977859)
          ·
            refine ⟨345717804342268317122966789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230478536228178878081977859 345717804342268317122966789)
            ·
              refine ⟨64822088314175309460556273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 345717804342268317122966789 64822088314175309460556273)
              ·
                refine ⟨48616566235631482095417205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64822088314175309460556273 48616566235631482095417205)
                ·
                  refine ⟨4557803084590451446445363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48616566235631482095417205 4557803084590451446445363)
                  ·
                    refine ⟨6836704626885677169668045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557803084590451446445363 6836704626885677169668045)
                    ·
                      refine ⟨2563764235082128938625517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836704626885677169668045 2563764235082128938625517)
                      ·
                        rfl

theorem cell23_4992913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_4992913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992913 prefixEnd_4992913 := by exact prefixLift 4992913
  have htrace : WordTrace (prefixWord ++ tailWord_4992913) baseStart_4992913 baseEnd_4992913 := by
    simpa [prefixWord, tailWord_4992913, baseEnd_4992913] using wordTrace_append hprefix tailTrace_4992913
  have hstable : (prefixWord ++ tailWord_4992913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992913).length < 2 ^ (prefixWord ++ tailWord_4992913).sum := by decide
  have hdescent : baseEnd_4992913 < baseStart_4992913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992924 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_4992924 : Nat := 118140960795 + 4992924 * 2 ^ 59
def prefixEnd_4992924 : Nat := 4983230072969 + 3 ^ 40 * 4992924 * 2
def baseEnd_4992924 : Nat := 854589961123109465195989

theorem tailTrace_4992924 : CollatzResearch.WordTrace tailWord_4992924 prefixEnd_4992924 854589961123109465195989 := by
  unfold tailWord_4992924
  simp only [CollatzResearch.WordTrace]
  refine ⟨91053449481748273187760913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121404599308997697583681217 91053449481748273187760913)
  ·
    refine ⟨68290087111311204890820685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91053449481748273187760913 68290087111311204890820685)
    ·
      refine ⟨25608782666741701834057757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68290087111311204890820685 25608782666741701834057757)
      ·
        refine ⟨9603293500028138187771659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25608782666741701834057757 9603293500028138187771659)
        ·
          refine ⟨14404940250042207281657489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9603293500028138187771659 14404940250042207281657489)
          ·
            refine ⟨10803705187531655461243117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14404940250042207281657489 10803705187531655461243117)
            ·
              refine ⟨4051389445324370797966169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10803705187531655461243117 4051389445324370797966169)
              ·
                refine ⟨3038542083993278098474627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051389445324370797966169 3038542083993278098474627)
                ·
                  refine ⟨4557813125989917147711941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038542083993278098474627 4557813125989917147711941)
                  ·
                    refine ⟨854589961123109465195989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4557813125989917147711941 854589961123109465195989)
                    ·
                      rfl

theorem cell23_4992924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_4992924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992924 prefixEnd_4992924 := by exact prefixLift 4992924
  have htrace : WordTrace (prefixWord ++ tailWord_4992924) baseStart_4992924 baseEnd_4992924 := by
    simpa [prefixWord, tailWord_4992924, baseEnd_4992924] using wordTrace_append hprefix tailTrace_4992924
  have hstable : (prefixWord ++ tailWord_4992924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992924).length < 2 ^ (prefixWord ++ tailWord_4992924).sum := by decide
  have hdescent : baseEnd_4992924 < baseStart_4992924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992946 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_4992946 : Nat := 118140960795 + 4992946 * 2 ^ 59
def prefixEnd_4992946 : Nat := 4983230072969 + 3 ^ 40 * 4992946 * 2
def baseEnd_4992946 : Nat := 854593726647909103170955

theorem tailTrace_4992946 : CollatzResearch.WordTrace tailWord_4992946 prefixEnd_4992946 854593726647909103170955 := by
  unfold tailWord_4992946
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526925342354211033205673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121405134246277896088548461 45526925342354211033205673)
  ·
    refine ⟨34145194006765658274904255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45526925342354211033205673 34145194006765658274904255)
    ·
      refine ⟨51217791010148487412356383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34145194006765658274904255 51217791010148487412356383)
      ·
        refine ⟨76826686515222731118534575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51217791010148487412356383 76826686515222731118534575)
        ·
          refine ⟨115240029772834096677801863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76826686515222731118534575 115240029772834096677801863)
          ·
            refine ⟨172860044659251145016702795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115240029772834096677801863 172860044659251145016702795)
            ·
              refine ⟨259290066988876717525054193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172860044659251145016702795 259290066988876717525054193)
              ·
                refine ⟨194467550241657538143790645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259290066988876717525054193 194467550241657538143790645)
                ·
                  refine ⟨18231332835155394200980373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194467550241657538143790645 18231332835155394200980373)
                  ·
                    refine ⟨854593726647909103170955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18231332835155394200980373 854593726647909103170955)
                    ·
                      rfl

theorem cell23_4992946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_4992946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992946 prefixEnd_4992946 := by exact prefixLift 4992946
  have htrace : WordTrace (prefixWord ++ tailWord_4992946) baseStart_4992946 baseEnd_4992946 := by
    simpa [prefixWord, tailWord_4992946, baseEnd_4992946] using wordTrace_append hprefix tailTrace_4992946
  have hstable : (prefixWord ++ tailWord_4992946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992946).length < 2 ^ (prefixWord ++ tailWord_4992946).sum := by decide
  have hdescent : baseEnd_4992946 < baseStart_4992946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992953 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4992953 : Nat := 118140960795 + 4992953 * 2 ^ 59
def prefixEnd_4992953 : Nat := 4983230072969 + 3 ^ 40 * 4992953 * 2
def baseEnd_4992953 : Nat := 2563784774308308782125333

theorem tailTrace_4992953 : CollatzResearch.WordTrace tailWord_4992953 prefixEnd_4992953 2563784774308308782125333 := by
  unfold tailWord_4992953
  simp only [CollatzResearch.WordTrace]
  refine ⟨182107956680391484328327513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121405304453594322885551675 182107956680391484328327513)
  ·
    refine ⟨136580967510293613246245635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182107956680391484328327513 136580967510293613246245635)
    ·
      refine ⟨204871451265440419869368453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136580967510293613246245635 204871451265440419869368453)
      ·
        refine ⟨38413397112270078725506585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204871451265440419869368453 38413397112270078725506585)
        ·
          refine ⟨28810047834202559044129939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38413397112270078725506585 28810047834202559044129939)
          ·
            refine ⟨43215071751303838566194909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28810047834202559044129939 43215071751303838566194909)
            ·
              refine ⟨16205651906738939462323091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43215071751303838566194909 16205651906738939462323091)
              ·
                refine ⟨24308477860108409193484637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16205651906738939462323091 24308477860108409193484637)
                ·
                  refine ⟨9115679197540653447556739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24308477860108409193484637 9115679197540653447556739)
                  ·
                    refine ⟨13673518796310980171335109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9115679197540653447556739 13673518796310980171335109)
                    ·
                      refine ⟨2563784774308308782125333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13673518796310980171335109 2563784774308308782125333)
                      ·
                        rfl

theorem cell23_4992953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4992953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992953 prefixEnd_4992953 := by exact prefixLift 4992953
  have htrace : WordTrace (prefixWord ++ tailWord_4992953) baseStart_4992953 baseEnd_4992953 := by
    simpa [prefixWord, tailWord_4992953, baseEnd_4992953] using wordTrace_append hprefix tailTrace_4992953
  have hstable : (prefixWord ++ tailWord_4992953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992953).length < 2 ^ (prefixWord ++ tailWord_4992953).sum := by decide
  have hdescent : baseEnd_4992953 < baseStart_4992953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992957 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4992957 : Nat := 118140960795 + 4992957 * 2 ^ 59
def prefixEnd_4992957 : Nat := 4983230072969 + 3 ^ 40 * 4992957 * 2
def baseEnd_4992957 : Nat := 2563786828230926766475315

theorem tailTrace_4992957 : CollatzResearch.WordTrace tailWord_4992957 prefixEnd_4992957 2563786828230926766475315 := by
  unfold tailWord_4992957
  simp only [CollatzResearch.WordTrace]
  refine ⟨182108102572376993011473125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121405401714917995340982083 182108102572376993011473125)
  ·
    refine ⟨34145269232320686189651211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182108102572376993011473125 34145269232320686189651211)
    ·
      refine ⟨51217903848481029284476817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34145269232320686189651211 51217903848481029284476817)
      ·
        refine ⟨38413427886360771963357613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51217903848481029284476817 38413427886360771963357613)
        ·
          refine ⟨14405035457385289486259105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38413427886360771963357613 14405035457385289486259105)
          ·
            refine ⟨10803776593038967114694329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14405035457385289486259105 10803776593038967114694329)
            ·
              refine ⟨8102832444779225336020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10803776593038967114694329 8102832444779225336020747)
              ·
                refine ⟨12154248667168838004031121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8102832444779225336020747 12154248667168838004031121)
                ·
                  refine ⟨9115686500376628503023341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12154248667168838004031121 9115686500376628503023341)
                  ·
                    refine ⟨3418382437641235688633753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9115686500376628503023341 3418382437641235688633753)
                    ·
                      refine ⟨2563786828230926766475315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418382437641235688633753 2563786828230926766475315)
                      ·
                        rfl

theorem cell23_4992957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4992957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992957 prefixEnd_4992957 := by exact prefixLift 4992957
  have htrace : WordTrace (prefixWord ++ tailWord_4992957) baseStart_4992957 baseEnd_4992957 := by
    simpa [prefixWord, tailWord_4992957, baseEnd_4992957] using wordTrace_append hprefix tailTrace_4992957
  have hstable : (prefixWord ++ tailWord_4992957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992957).length < 2 ^ (prefixWord ++ tailWord_4992957).sum := by decide
  have hdescent : baseEnd_4992957 < baseStart_4992957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4992981 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4992981 : Nat := 118140960795 + 4992981 * 2 ^ 59
def prefixEnd_4992981 : Nat := 4983230072969 + 3 ^ 40 * 4992981 * 2
def baseEnd_4992981 : Nat := 2563799151766634672575205

theorem tailTrace_4992981 : CollatzResearch.WordTrace tailWord_4992981 prefixEnd_4992981 2563799151766634672575205 := by
  unfold tailWord_4992981
  simp only [CollatzResearch.WordTrace]
  refine ⟨182108977924290045110346797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121405985282860030073564531 182108977924290045110346797)
  ·
    refine ⟨68290866721608766916380049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182108977924290045110346797 68290866721608766916380049)
    ·
      refine ⟨51218150041206575187285037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68290866721608766916380049 51218150041206575187285037)
      ·
        refine ⟨19206806265452465695231889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51218150041206575187285037 19206806265452465695231889)
        ·
          refine ⟨14405104699089349271423917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19206806265452465695231889 14405104699089349271423917)
          ·
            refine ⟨5401914262158505976783969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14405104699089349271423917 5401914262158505976783969)
            ·
              refine ⟨4051435696618879482587977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401914262158505976783969 4051435696618879482587977)
              ·
                refine ⟨3038576772464159611940983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051435696618879482587977 3038576772464159611940983)
                ·
                  refine ⟨4557865158696239417911475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038576772464159611940983 4557865158696239417911475)
                  ·
                    refine ⟨6836797738044359126867213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557865158696239417911475 6836797738044359126867213)
                    ·
                      refine ⟨2563799151766634672575205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836797738044359126867213 2563799151766634672575205)
                      ·
                        rfl

theorem cell23_4992981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4992981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4992981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4992981 prefixEnd_4992981 := by exact prefixLift 4992981
  have htrace : WordTrace (prefixWord ++ tailWord_4992981) baseStart_4992981 baseEnd_4992981 := by
    simpa [prefixWord, tailWord_4992981, baseEnd_4992981] using wordTrace_append hprefix tailTrace_4992981
  have hstable : (prefixWord ++ tailWord_4992981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4992981).length < 2 ^ (prefixWord ++ tailWord_4992981).sum := by decide
  have hdescent : baseEnd_4992981 < baseStart_4992981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4992981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993020 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_4993020 : Nat := 118140960795 + 4993020 * 2 ^ 59
def prefixEnd_4993020 : Nat := 4983230072969 + 3 ^ 40 * 4993020 * 2
def baseEnd_4993020 : Nat := 2563819177512160019987525

theorem tailTrace_4993020 : CollatzResearch.WordTrace tailWord_4993020 prefixEnd_4993020 2563819177512160019987525 := by
  unfold tailWord_4993020
  simp only [CollatzResearch.WordTrace]
  refine ⟨91055200185574377385508257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121406933580765836514011009 91055200185574377385508257)
  ·
    refine ⟨68291400139180783039131193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91055200185574377385508257 68291400139180783039131193)
    ·
      refine ⟨51218550104385587279348395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68291400139180783039131193 51218550104385587279348395)
      ·
        refine ⟨76827825156578380919022593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51218550104385587279348395 76827825156578380919022593)
        ·
          refine ⟨57620868867433785689266945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76827825156578380919022593 57620868867433785689266945)
          ·
            refine ⟨43215651650575339266950209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57620868867433785689266945 43215651650575339266950209)
            ·
              refine ⟨32411738737931504450212657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43215651650575339266950209 32411738737931504450212657)
              ·
                refine ⟨24308804053448628337659493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32411738737931504450212657 24308804053448628337659493)
                ·
                  refine ⟨4557900760021617813311155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24308804053448628337659493 4557900760021617813311155)
                  ·
                    refine ⟨6836851140032426719966733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557900760021617813311155 6836851140032426719966733)
                    ·
                      refine ⟨2563819177512160019987525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6836851140032426719966733 2563819177512160019987525)
                      ·
                        rfl

theorem cell23_4993020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_4993020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993020 prefixEnd_4993020 := by exact prefixLift 4993020
  have htrace : WordTrace (prefixWord ++ tailWord_4993020) baseStart_4993020 baseEnd_4993020 := by
    simpa [prefixWord, tailWord_4993020, baseEnd_4993020] using wordTrace_append hprefix tailTrace_4993020
  have hstable : (prefixWord ++ tailWord_4993020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993020).length < 2 ^ (prefixWord ++ tailWord_4993020).sum := by decide
  have hdescent : baseEnd_4993020 < baseStart_4993020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993077 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_4993077 : Nat := 118140960795 + 4993077 * 2 ^ 59
def prefixEnd_4993077 : Nat := 4983230072969 + 3 ^ 40 * 4993077 * 2
def baseEnd_4993077 : Nat := 2563848445909466296974763

theorem tailTrace_4993077 : CollatzResearch.WordTrace tailWord_4993077 prefixEnd_4993077 2563848445909466296974763 := by
  unfold tailWord_4993077
  simp only [CollatzResearch.WordTrace]
  refine ⟨182112479331942253505841485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121408319554628169003894323 182112479331942253505841485)
  ·
    refine ⟨68292179749478345064690557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182112479331942253505841485 68292179749478345064690557)
    ·
      refine ⟨25609567406054379399258959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68292179749478345064690557 25609567406054379399258959)
      ·
        refine ⟨38414351109081569098888439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25609567406054379399258959 38414351109081569098888439)
        ·
          refine ⟨57621526663622353648332659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38414351109081569098888439 57621526663622353648332659)
          ·
            refine ⟨86432289995433530472498989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57621526663622353648332659 86432289995433530472498989)
            ·
              refine ⟨32412108748287573927187121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86432289995433530472498989 32412108748287573927187121)
              ·
                refine ⟨24309081561215680445390341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32412108748287573927187121 24309081561215680445390341)
                ·
                  refine ⟨4557952792727940083510689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24309081561215680445390341 4557952792727940083510689)
                  ·
                    refine ⟨3418464594545955062633017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557952792727940083510689 3418464594545955062633017)
                    ·
                      refine ⟨2563848445909466296974763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418464594545955062633017 2563848445909466296974763)
                      ·
                        rfl

theorem cell23_4993077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_4993077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993077 prefixEnd_4993077 := by exact prefixLift 4993077
  have htrace : WordTrace (prefixWord ++ tailWord_4993077) baseStart_4993077 baseEnd_4993077 := by
    simpa [prefixWord, tailWord_4993077, baseEnd_4993077] using wordTrace_append hprefix tailTrace_4993077
  have hstable : (prefixWord ++ tailWord_4993077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993077).length < 2 ^ (prefixWord ++ tailWord_4993077).sum := by decide
  have hdescent : baseEnd_4993077 < baseStart_4993077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993080 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_4993080 : Nat := 118140960795 + 4993080 * 2 ^ 59
def prefixEnd_4993080 : Nat := 4983230072969 + 3 ^ 40 * 4993080 * 2
def baseEnd_4993080 : Nat := 2563849986351429785237249

theorem tailTrace_4993080 : CollatzResearch.WordTrace tailWord_4993080 prefixEnd_4993080 2563849986351429785237249 := by
  unfold tailWord_4993080
  simp only [CollatzResearch.WordTrace]
  refine ⟨91056294375465692509100347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121408392500620923345467129 91056294375465692509100347)
  ·
    refine ⟨136584441563198538763650521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91056294375465692509100347 136584441563198538763650521)
    ·
      refine ⟨102438331172398904072737891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136584441563198538763650521 102438331172398904072737891)
      ·
        refine ⟨153657496758598356109106837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102438331172398904072737891 153657496758598356109106837)
        ·
          refine ⟨7202695160559297942614383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153657496758598356109106837 7202695160559297942614383)
          ·
            refine ⟨10804042740838946913921575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7202695160559297942614383 10804042740838946913921575)
            ·
              refine ⟨16206064111258420370882363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804042740838946913921575 16206064111258420370882363)
              ·
                refine ⟨24309096166887630556323545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16206064111258420370882363 24309096166887630556323545)
                ·
                  refine ⟨18231822125165722917242659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24309096166887630556323545 18231822125165722917242659)
                  ·
                    refine ⟨27347733187748584375863989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18231822125165722917242659 27347733187748584375863989)
                    ·
                      refine ⟨2563849986351429785237249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27347733187748584375863989 2563849986351429785237249)
                      ·
                        rfl

theorem cell23_4993080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_4993080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993080 prefixEnd_4993080 := by exact prefixLift 4993080
  have htrace : WordTrace (prefixWord ++ tailWord_4993080) baseStart_4993080 baseEnd_4993080 := by
    simpa [prefixWord, tailWord_4993080, baseEnd_4993080] using wordTrace_append hprefix tailTrace_4993080
  have hstable : (prefixWord ++ tailWord_4993080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993080).length < 2 ^ (prefixWord ++ tailWord_4993080).sum := by decide
  have hdescent : baseEnd_4993080 < baseStart_4993080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993100 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 5]
def baseStart_4993100 : Nat := 118140960795 + 4993100 * 2 ^ 59
def prefixEnd_4993100 : Nat := 4983230072969 + 3 ^ 40 * 4993100 * 2
def baseEnd_4993100 : Nat := 284873361773835522998573

theorem tailTrace_4993100 : CollatzResearch.WordTrace tailWord_4993100 prefixEnd_4993100 284873361773835522998573 := by
  unfold tailWord_4993100
  simp only [CollatzResearch.WordTrace]
  refine ⟨91056659105429464216964377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121408878807239285622619169 91056659105429464216964377)
  ·
    refine ⟨68292494329072098162723283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91056659105429464216964377 68292494329072098162723283)
    ·
      refine ⟨102438741493608147244084925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68292494329072098162723283 102438741493608147244084925)
      ·
        refine ⟨38414528060103055216531847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102438741493608147244084925 38414528060103055216531847)
        ·
          refine ⟨57621792090154582824797771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38414528060103055216531847 57621792090154582824797771)
          ·
            refine ⟨86432688135231874237196657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57621792090154582824797771 86432688135231874237196657)
            ·
              refine ⟨64824516101423905677897493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86432688135231874237196657 64824516101423905677897493)
              ·
                refine ⟨3038649192254245578651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64824516101423905677897493 3038649192254245578651445)
                ·
                  refine ⟨284873361773835522998573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3038649192254245578651445 284873361773835522998573)
                  ·
                    rfl

theorem cell23_4993100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_4993100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993100 prefixEnd_4993100 := by exact prefixLift 4993100
  have htrace : WordTrace (prefixWord ++ tailWord_4993100) baseStart_4993100 baseEnd_4993100 := by
    simpa [prefixWord, tailWord_4993100, baseEnd_4993100] using wordTrace_append hprefix tailTrace_4993100
  have hstable : (prefixWord ++ tailWord_4993100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993100).length < 2 ^ (prefixWord ++ tailWord_4993100).sum := by decide
  have hdescent : baseEnd_4993100 < baseStart_4993100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993113 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_4993113 : Nat := 118140960795 + 4993113 * 2 ^ 59
def prefixEnd_4993113 : Nat := 4983230072969 + 3 ^ 40 * 4993113 * 2
def baseEnd_4993113 : Nat := 854622310404342718708199

theorem tailTrace_4993113 : CollatzResearch.WordTrace tailWord_4993113 prefixEnd_4993113 854622310404342718708199 := by
  unfold tailWord_4993113
  simp only [CollatzResearch.WordTrace]
  refine ⟨182113792359811831654151993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121409194906541221102767995 182113792359811831654151993)
  ·
    refine ⟨136585344269858873740613995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182113792359811831654151993 136585344269858873740613995)
    ·
      refine ⟨204878016404788310610920993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136585344269858873740613995 204878016404788310610920993)
      ·
        refine ⟨153658512303591232958190745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204878016404788310610920993 153658512303591232958190745)
        ·
          refine ⟨115243884227693424718643059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153658512303591232958190745 115243884227693424718643059)
          ·
            refine ⟨172865826341540137077964589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115243884227693424718643059 172865826341540137077964589)
            ·
              refine ⟨64824684878077551404236721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172865826341540137077964589 64824684878077551404236721)
              ·
                refine ⟨48618513658558163553177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64824684878077551404236721 48618513658558163553177541)
                ·
                  refine ⟨9115971310979655666220789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48618513658558163553177541 9115971310979655666220789)
                  ·
                    refine ⟨854622310404342718708199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9115971310979655666220789 854622310404342718708199)
                    ·
                      rfl

theorem cell23_4993113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_4993113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993113 prefixEnd_4993113 := by exact prefixLift 4993113
  have htrace : WordTrace (prefixWord ++ tailWord_4993113) baseStart_4993113 baseEnd_4993113 := by
    simpa [prefixWord, tailWord_4993113, baseEnd_4993113] using wordTrace_append hprefix tailTrace_4993113
  have hstable : (prefixWord ++ tailWord_4993113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993113).length < 2 ^ (prefixWord ++ tailWord_4993113).sum := by decide
  have hdescent : baseEnd_4993113 < baseStart_4993113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993163 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_4993163 : Nat := 118140960795 + 4993163 * 2 ^ 59
def prefixEnd_4993163 : Nat := 4983230072969 + 3 ^ 40 * 4993163 * 2
def baseEnd_4993163 : Nat := 2563892605245752960499367

theorem tailTrace_4993163 : CollatzResearch.WordTrace tailWord_4993163 prefixEnd_4993163 2563892605245752960499367 := by
  unfold tailWord_4993163
  simp only [CollatzResearch.WordTrace]
  refine ⟨182115616009630690193472143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121410410673087126795648095 182115616009630690193472143)
  ·
    refine ⟨273173424014446035290208215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182115616009630690193472143 273173424014446035290208215)
    ·
      refine ⟨409760136021669052935312323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273173424014446035290208215 409760136021669052935312323)
      ·
        refine ⟨614640204032503579402968485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409760136021669052935312323 614640204032503579402968485)
        ·
          refine ⟨115245038256094421138056591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614640204032503579402968485 115245038256094421138056591)
          ·
            refine ⟨172867557384141631707084887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115245038256094421138056591 172867557384141631707084887)
            ·
              refine ⟨259301336076212447560627331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172867557384141631707084887 259301336076212447560627331)
              ·
                refine ⟨388952004114318671340940997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259301336076212447560627331 388952004114318671340940997)
                ·
                  refine ⟨72928500771434750876426437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388952004114318671340940997 72928500771434750876426437)
                  ·
                    refine ⟨13674093894644015789329957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72928500771434750876426437 13674093894644015789329957)
                    ·
                      refine ⟨2563892605245752960499367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13674093894644015789329957 2563892605245752960499367)
                      ·
                        rfl

theorem cell23_4993163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_4993163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993163 prefixEnd_4993163 := by exact prefixLift 4993163
  have htrace : WordTrace (prefixWord ++ tailWord_4993163) baseStart_4993163 baseEnd_4993163 := by
    simpa [prefixWord, tailWord_4993163, baseEnd_4993163] using wordTrace_append hprefix tailTrace_4993163
  have hstable : (prefixWord ++ tailWord_4993163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993163).length < 2 ^ (prefixWord ++ tailWord_4993163).sum := by decide
  have hdescent : baseEnd_4993163 < baseStart_4993163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993207 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 6]
def baseStart_4993207 : Nat := 118140960795 + 4993207 * 2 ^ 59
def prefixEnd_4993207 : Nat := 4983230072969 + 3 ^ 40 * 4993207 * 2
def baseEnd_4993207 : Nat := 284879466488283420927685

theorem tailTrace_4993207 : CollatzResearch.WordTrace tailWord_4993207 prefixEnd_4993207 284879466488283420927685 := by
  unfold tailWord_4993207
  simp only [CollatzResearch.WordTrace]
  refine ⟨182117220821471285708073875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121411480547647523805382583 182117220821471285708073875)
  ·
    refine ⟨273175831232206928562110813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182117220821471285708073875 273175831232206928562110813)
    ·
      refine ⟨102440936712077598210791555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273175831232206928562110813 102440936712077598210791555)
      ·
        refine ⟨153661405068116397316187333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102440936712077598210791555 153661405068116397316187333)
        ·
          refine ⟨28811513450271824496785125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153661405068116397316187333 28811513450271824496785125)
          ·
            refine ⟨5402158771925967093147211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28811513450271824496785125 5402158771925967093147211)
            ·
              refine ⟨8103238157888950639720817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402158771925967093147211 8103238157888950639720817)
              ·
                refine ⟨6077428618416712979790613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8103238157888950639720817 6077428618416712979790613)
                ·
                  refine ⟨284879466488283420927685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6077428618416712979790613 284879466488283420927685)
                  ·
                    rfl

theorem cell23_4993207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 6].length) (baseStart_4993207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993207 prefixEnd_4993207 := by exact prefixLift 4993207
  have htrace : WordTrace (prefixWord ++ tailWord_4993207) baseStart_4993207 baseEnd_4993207 := by
    simpa [prefixWord, tailWord_4993207, baseEnd_4993207] using wordTrace_append hprefix tailTrace_4993207
  have hstable : (prefixWord ++ tailWord_4993207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993207).length < 2 ^ (prefixWord ++ tailWord_4993207).sum := by decide
  have hdescent : baseEnd_4993207 < baseStart_4993207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993234 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_4993234 : Nat := 118140960795 + 4993234 * 2 ^ 59
def prefixEnd_4993234 : Nat := 4983230072969 + 3 ^ 40 * 4993234 * 2
def baseEnd_4993234 : Nat := 2563929062372222182711541

theorem tailTrace_4993234 : CollatzResearch.WordTrace tailWord_4993234 prefixEnd_4993234 2563929062372222182711541 := by
  unfold tailWord_4993234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45529551398093367329826689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121412137061582312879537837 45529551398093367329826689)
  ·
    refine ⟨34147163548570025497370017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45529551398093367329826689 34147163548570025497370017)
    ·
      refine ⟨25610372661427519123027513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34147163548570025497370017 25610372661427519123027513)
      ·
        refine ⟨19207779496070639342270635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25610372661427519123027513 19207779496070639342270635)
        ·
          refine ⟨28811669244105959013405953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19207779496070639342270635 28811669244105959013405953)
          ·
            refine ⟨21608751933079469260054465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28811669244105959013405953 21608751933079469260054465)
            ·
              refine ⟨16206563949809601945040849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21608751933079469260054465 16206563949809601945040849)
              ·
                refine ⟨12154922962357201458780637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16206563949809601945040849 12154922962357201458780637)
                ·
                  refine ⟨4558096110883950547042739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12154922962357201458780637 4558096110883950547042739)
                  ·
                    refine ⟨6837144166325925820564109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558096110883950547042739 6837144166325925820564109)
                    ·
                      refine ⟨2563929062372222182711541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837144166325925820564109 2563929062372222182711541)
                      ·
                        rfl

theorem cell23_4993234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_4993234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993234 prefixEnd_4993234 := by exact prefixLift 4993234
  have htrace : WordTrace (prefixWord ++ tailWord_4993234) baseStart_4993234 baseEnd_4993234 := by
    simpa [prefixWord, tailWord_4993234, baseEnd_4993234] using wordTrace_append hprefix tailTrace_4993234
  have hstable : (prefixWord ++ tailWord_4993234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993234).length < 2 ^ (prefixWord ++ tailWord_4993234).sum := by decide
  have hdescent : baseEnd_4993234 < baseStart_4993234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993261 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4993261 : Nat := 118140960795 + 4993261 * 2 ^ 59
def prefixEnd_4993261 : Nat := 4983230072969 + 3 ^ 40 * 4993261 * 2
def baseEnd_4993261 : Nat := 2563942926349893577073917

theorem tailTrace_4993261 : CollatzResearch.WordTrace tailWord_4993261 prefixEnd_4993261 2563942926349893577073917 := by
  unfold tailWord_4993261
  simp only [CollatzResearch.WordTrace]
  refine ⟨182119190363275652930539637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121412793575517101953693091 182119190363275652930539637)
  ·
    refine ⟨17073674096557092462238091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182119190363275652930539637 17073674096557092462238091)
    ·
      refine ⟨25610511144835638693357137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17073674096557092462238091 25610511144835638693357137)
      ·
        refine ⟨19207883358626729020017853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25610511144835638693357137 19207883358626729020017853)
        ·
          refine ⟨7202956259485023382506695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19207883358626729020017853 7202956259485023382506695)
          ·
            refine ⟨10804434389227535073760043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7202956259485023382506695 10804434389227535073760043)
            ·
              refine ⟨16206651583841302610640065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804434389227535073760043 16206651583841302610640065)
              ·
                refine ⟨12154988687880976957980049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16206651583841302610640065 12154988687880976957980049)
                ·
                  refine ⟨9116241515910732718485037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12154988687880976957980049 9116241515910732718485037)
                  ·
                    refine ⟨3418590568466524769431889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9116241515910732718485037 3418590568466524769431889)
                    ·
                      refine ⟨2563942926349893577073917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418590568466524769431889 2563942926349893577073917)
                      ·
                        rfl

theorem cell23_4993261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4993261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993261 prefixEnd_4993261 := by exact prefixLift 4993261
  have htrace : WordTrace (prefixWord ++ tailWord_4993261) baseStart_4993261 baseEnd_4993261 := by
    simpa [prefixWord, tailWord_4993261, baseEnd_4993261] using wordTrace_append hprefix tailTrace_4993261
  have hstable : (prefixWord ++ tailWord_4993261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993261).length < 2 ^ (prefixWord ++ tailWord_4993261).sum := by decide
  have hdescent : baseEnd_4993261 < baseStart_4993261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993267 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 2, 4]
def baseStart_4993267 : Nat := 118140960795 + 4993267 * 2 ^ 59
def prefixEnd_4993267 : Nat := 4983230072969 + 3 ^ 40 * 4993267 * 2
def baseEnd_4993267 : Nat := 854648669077940184532963

theorem tailTrace_4993267 : CollatzResearch.WordTrace tailWord_4993267 prefixEnd_4993267 854648669077940184532963 := by
  unfold tailWord_4993267
  simp only [CollatzResearch.WordTrace]
  refine ⟨182119409201253915955258055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121412939467502610636838703 182119409201253915955258055)
  ·
    refine ⟨273179113801880873932887083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182119409201253915955258055 273179113801880873932887083)
    ·
      refine ⟨409768670702821310899330625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273179113801880873932887083 409768670702821310899330625)
      ·
        refine ⟨307326503027115983174497969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409768670702821310899330625 307326503027115983174497969)
        ·
          refine ⟨230494877270336987380873477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307326503027115983174497969 230494877270336987380873477)
          ·
            refine ⟨43217789488188185133913777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230494877270336987380873477 43217789488188185133913777)
            ·
              refine ⟨32413342116141138850435333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43217789488188185133913777 32413342116141138850435333)
              ·
                refine ⟨6077501646776463534456625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32413342116141138850435333 6077501646776463534456625)
                ·
                  refine ⟨4558126235082347650842469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077501646776463534456625 4558126235082347650842469)
                  ·
                    refine ⟨854648669077940184532963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558126235082347650842469 854648669077940184532963)
                    ·
                      rfl

theorem cell23_4993267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 4].length) (baseStart_4993267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993267 prefixEnd_4993267 := by exact prefixLift 4993267
  have htrace : WordTrace (prefixWord ++ tailWord_4993267) baseStart_4993267 baseEnd_4993267 := by
    simpa [prefixWord, tailWord_4993267, baseEnd_4993267] using wordTrace_append hprefix tailTrace_4993267
  have hstable : (prefixWord ++ tailWord_4993267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993267).length < 2 ^ (prefixWord ++ tailWord_4993267).sum := by decide
  have hdescent : baseEnd_4993267 < baseStart_4993267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993307 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 3]
def baseStart_4993307 : Nat := 118140960795 + 4993307 * 2 ^ 59
def prefixEnd_4993307 : Nat := 4983230072969 + 3 ^ 40 * 4993307 * 2
def baseEnd_4993307 : Nat := 2563966546460000397098705

theorem tailTrace_4993307 : CollatzResearch.WordTrace tailWord_4993307 prefixEnd_4993307 2563966546460000397098705 := by
  unfold tailWord_4993307
  simp only [CollatzResearch.WordTrace]
  refine ⟨182120868121109002786714175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121413912080739335191142783 182120868121109002786714175)
  ·
    refine ⟨273181302181663504180071263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182120868121109002786714175 273181302181663504180071263)
    ·
      refine ⟨409771953272495256270106895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273181302181663504180071263 409771953272495256270106895)
      ·
        refine ⟨614657929908742884405160343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409771953272495256270106895 614657929908742884405160343)
        ·
          refine ⟨921986894863114326607740515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614657929908742884405160343 921986894863114326607740515)
          ·
            refine ⟨1382980342294671489911610773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921986894863114326607740515 1382980342294671489911610773)
            ·
              refine ⟨64827203545062726089606755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1382980342294671489911610773 64827203545062726089606755)
              ·
                refine ⟨97240805317594089134410133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64827203545062726089606755 97240805317594089134410133)
                ·
                  refine ⟨4558162749262222928175475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97240805317594089134410133 4558162749262222928175475)
                  ·
                    refine ⟨6837244123893334392263213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558162749262222928175475 6837244123893334392263213)
                    ·
                      refine ⟨2563966546460000397098705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837244123893334392263213 2563966546460000397098705)
                      ·
                        rfl

theorem cell23_4993307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 3].length) (baseStart_4993307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993307 prefixEnd_4993307 := by exact prefixLift 4993307
  have htrace : WordTrace (prefixWord ++ tailWord_4993307) baseStart_4993307 baseEnd_4993307 := by
    simpa [prefixWord, tailWord_4993307, baseEnd_4993307] using wordTrace_append hprefix tailTrace_4993307
  have hstable : (prefixWord ++ tailWord_4993307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993307).length < 2 ^ (prefixWord ++ tailWord_4993307).sum := by decide
  have hdescent : baseEnd_4993307 < baseStart_4993307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993311 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 1, 2, 3]
def baseStart_4993311 : Nat := 118140960795 + 4993311 * 2 ^ 59
def prefixEnd_4993311 : Nat := 4983230072969 + 3 ^ 40 * 4993311 * 2
def baseEnd_4993311 : Nat := 2563968600382618381448687

theorem tailTrace_4993311 : CollatzResearch.WordTrace tailWord_4993311 prefixEnd_4993311 2563968600382618381448687 := by
  unfold tailWord_4993311
  simp only [CollatzResearch.WordTrace]
  refine ⟨182121014013094511469859787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121414009342063007646573191 182121014013094511469859787)
  ·
    refine ⟨273181521019641767204789681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182121014013094511469859787 273181521019641767204789681)
    ·
      refine ⟨204886140764731325403592261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273181521019641767204789681 204886140764731325403592261)
      ·
        refine ⟨38416151393387123513173549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204886140764731325403592261 38416151393387123513173549)
        ·
          refine ⟨14406056772520171317440081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38416151393387123513173549 14406056772520171317440081)
          ·
            refine ⟨10804542579390128488080061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14406056772520171317440081 10804542579390128488080061)
            ·
              refine ⟨4051703467271298183030023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10804542579390128488080061 4051703467271298183030023)
              ·
                refine ⟨6077555200906947274545035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051703467271298183030023 6077555200906947274545035)
                ·
                  refine ⟨9116332801360420911817553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077555200906947274545035 9116332801360420911817553)
                  ·
                    refine ⟨6837249601020315683863165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9116332801360420911817553 6837249601020315683863165)
                    ·
                      refine ⟨2563968600382618381448687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837249601020315683863165 2563968600382618381448687)
                      ·
                        rfl

theorem cell23_4993311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_4993311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993311 prefixEnd_4993311 := by exact prefixLift 4993311
  have htrace : WordTrace (prefixWord ++ tailWord_4993311) baseStart_4993311 baseEnd_4993311 := by
    simpa [prefixWord, tailWord_4993311, baseEnd_4993311] using wordTrace_append hprefix tailTrace_4993311
  have hstable : (prefixWord ++ tailWord_4993311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993311).length < 2 ^ (prefixWord ++ tailWord_4993311).sum := by decide
  have hdescent : baseEnd_4993311 < baseStart_4993311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993319 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4993319 : Nat := 118140960795 + 4993319 * 2 ^ 59
def prefixEnd_4993319 : Nat := 4983230072969 + 3 ^ 40 * 4993319 * 2
def baseEnd_4993319 : Nat := 2563972708227854350148651

theorem tailTrace_4993319 : CollatzResearch.WordTrace tailWord_4993319 prefixEnd_4993319 2563972708227854350148651 := by
  unfold tailWord_4993319
  simp only [CollatzResearch.WordTrace]
  refine ⟨182121305797065528836151011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121414203864710352557434007 182121305797065528836151011)
  ·
    refine ⟨273181958695598293254226517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182121305797065528836151011 273181958695598293254226517)
    ·
      refine ⟨3201351078464042499072967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 273181958695598293254226517 3201351078464042499072967)
      ·
        refine ⟨4802026617696063748609451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201351078464042499072967 4802026617696063748609451)
        ·
          refine ⟨7203039926544095622914177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802026617696063748609451 7203039926544095622914177)
          ·
            refine ⟨5402279944908071717185633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7203039926544095622914177 5402279944908071717185633)
            ·
              refine ⟨4051709958681053787889225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5402279944908071717185633 4051709958681053787889225)
              ·
                refine ⟨3038782469010790340916919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051709958681053787889225 3038782469010790340916919)
                ·
                  refine ⟨4558173703516185511375379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038782469010790340916919 4558173703516185511375379)
                  ·
                    refine ⟨6837260555274278267063069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558173703516185511375379 6837260555274278267063069)
                    ·
                      refine ⟨2563972708227854350148651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837260555274278267063069 2563972708227854350148651)
                      ·
                        rfl

theorem cell23_4993319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4993319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993319 prefixEnd_4993319 := by exact prefixLift 4993319
  have htrace : WordTrace (prefixWord ++ tailWord_4993319) baseStart_4993319 baseEnd_4993319 := by
    simpa [prefixWord, tailWord_4993319, baseEnd_4993319] using wordTrace_append hprefix tailTrace_4993319
  have hstable : (prefixWord ++ tailWord_4993319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993319).length < 2 ^ (prefixWord ++ tailWord_4993319).sum := by decide
  have hdescent : baseEnd_4993319 < baseStart_4993319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993324 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_4993324 : Nat := 118140960795 + 4993324 * 2 ^ 59
def prefixEnd_4993324 : Nat := 4983230072969 + 3 ^ 40 * 4993324 * 2
def baseEnd_4993324 : Nat := 2563975275631126830586127

theorem tailTrace_4993324 : CollatzResearch.WordTrace tailWord_4993324 prefixEnd_4993324 2563975275631126830586127 := by
  unfold tailWord_4993324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91060744081023707345041513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121414325441364943126722017 91060744081023707345041513)
  ·
    refine ⟨68295558060767780508781135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91060744081023707345041513 68295558060767780508781135)
    ·
      refine ⟨102443337091151670763171703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68295558060767780508781135 102443337091151670763171703)
      ·
        refine ⟨153665005636727506144757555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102443337091151670763171703 153665005636727506144757555)
        ·
          refine ⟨230497508455091259217136333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153665005636727506144757555 230497508455091259217136333)
          ·
            refine ⟨86436565670659222206426125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230497508455091259217136333 86436565670659222206426125)
            ·
              refine ⟨32413712126497208327409797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86436565670659222206426125 32413712126497208327409797)
              ·
                refine ⟨6077571023718226561389337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32413712126497208327409797 6077571023718226561389337)
                ·
                  refine ⟨4558178267788669921042003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077571023718226561389337 4558178267788669921042003)
                  ·
                    refine ⟨6837267401683004881563005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558178267788669921042003 6837267401683004881563005)
                    ·
                      refine ⟨2563975275631126830586127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837267401683004881563005 2563975275631126830586127)
                      ·
                        rfl

theorem cell23_4993324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_4993324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993324 prefixEnd_4993324 := by exact prefixLift 4993324
  have htrace : WordTrace (prefixWord ++ tailWord_4993324) baseStart_4993324 baseEnd_4993324 := by
    simpa [prefixWord, tailWord_4993324, baseEnd_4993324] using wordTrace_append hprefix tailTrace_4993324
  have hstable : (prefixWord ++ tailWord_4993324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993324).length < 2 ^ (prefixWord ++ tailWord_4993324).sum := by decide
  have hdescent : baseEnd_4993324 < baseStart_4993324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993370 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_4993370 : Nat := 118140960795 + 4993370 * 2 ^ 59
def prefixEnd_4993370 : Nat := 4983230072969 + 3 ^ 40 * 4993370 * 2
def baseEnd_4993370 : Nat := 284888766193470405623435

theorem tailTrace_4993370 : CollatzResearch.WordTrace tailWord_4993370 prefixEnd_4993370 284888766193470405623435 := by
  unfold tailWord_4993370
  simp only [CollatzResearch.WordTrace]
  refine ⟨45530791479970191136564391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121415443946587176364171709 45530791479970191136564391)
  ·
    refine ⟨68296187219955286704846587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45530791479970191136564391 68296187219955286704846587)
    ·
      refine ⟨102444280829932930057269881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68296187219955286704846587 102444280829932930057269881)
      ·
        refine ⟨76833210622449697542952411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102444280829932930057269881 76833210622449697542952411)
        ·
          refine ⟨115249815933674546314428617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76833210622449697542952411 115249815933674546314428617)
          ·
            refine ⟨86437361950255909735821463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115249815933674546314428617 86437361950255909735821463)
            ·
              refine ⟨129656042925383864603732195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86437361950255909735821463 129656042925383864603732195)
              ·
                refine ⟨194484064388075796905598293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129656042925383864603732195 194484064388075796905598293)
                ·
                  refine ⟨284888766193470405623435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 194484064388075796905598293 284888766193470405623435)
                  ·
                    rfl

theorem cell23_4993370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_4993370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993370 prefixEnd_4993370 := by exact prefixLift 4993370
  have htrace : WordTrace (prefixWord ++ tailWord_4993370) baseStart_4993370 baseEnd_4993370 := by
    simpa [prefixWord, tailWord_4993370, baseEnd_4993370] using wordTrace_append hprefix tailTrace_4993370
  have hstable : (prefixWord ++ tailWord_4993370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993370).length < 2 ^ (prefixWord ++ tailWord_4993370).sum := by decide
  have hdescent : baseEnd_4993370 < baseStart_4993370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993381 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_4993381 : Nat := 118140960795 + 4993381 * 2 ^ 59
def prefixEnd_4993381 : Nat := 4983230072969 + 3 ^ 40 * 4993381 * 2
def baseEnd_4993381 : Nat := 2564004544028433107573365

theorem tailTrace_4993381 : CollatzResearch.WordTrace tailWord_4993381 prefixEnd_4993381 2564004544028433107573365 := by
  unfold tailWord_4993381
  simp only [CollatzResearch.WordTrace]
  refine ⟨182123567122840913424907997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121415711415227275616605331 182123567122840913424907997)
  ·
    refine ⟨68296337671065342534340499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182123567122840913424907997 68296337671065342534340499)
    ·
      refine ⟨102444506506598013801510749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68296337671065342534340499 102444506506598013801510749)
      ·
        refine ⟨38416689939974255175566531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102444506506598013801510749 38416689939974255175566531)
        ·
          refine ⟨57625034909961382763349797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38416689939974255175566531 57625034909961382763349797)
          ·
            refine ⟨10804694045617759268128087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57625034909961382763349797 10804694045617759268128087)
            ·
              refine ⟨16207041068426638902192131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804694045617759268128087 16207041068426638902192131)
              ·
                refine ⟨24310561602639958353288197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16207041068426638902192131 24310561602639958353288197)
                ·
                  refine ⟨4558230300494992191241537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24310561602639958353288197 4558230300494992191241537)
                  ·
                    refine ⟨3418672725371244143431153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558230300494992191241537 3418672725371244143431153)
                    ·
                      refine ⟨2564004544028433107573365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418672725371244143431153 2564004544028433107573365)
                      ·
                        rfl

theorem cell23_4993381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_4993381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993381 prefixEnd_4993381 := by exact prefixLift 4993381
  have htrace : WordTrace (prefixWord ++ tailWord_4993381) baseStart_4993381 baseEnd_4993381 := by
    simpa [prefixWord, tailWord_4993381, baseEnd_4993381] using wordTrace_append hprefix tailTrace_4993381
  have hstable : (prefixWord ++ tailWord_4993381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993381).length < 2 ^ (prefixWord ++ tailWord_4993381).sum := by decide
  have hdescent : baseEnd_4993381 < baseStart_4993381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993417 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_4993417 : Nat := 118140960795 + 4993417 * 2 ^ 59
def prefixEnd_4993417 : Nat := 4983230072969 + 3 ^ 40 * 4993417 * 2
def baseEnd_4993417 : Nat := 854674343110664988907733

theorem tailTrace_4993417 : CollatzResearch.WordTrace tailWord_4993417 prefixEnd_4993417 854674343110664988907733 := by
  unfold tailWord_4993417
  simp only [CollatzResearch.WordTrace]
  refine ⟨182124880150710491573218505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121416586767140327715479003 182124880150710491573218505)
  ·
    refine ⟨136593660113032868679913879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182124880150710491573218505 136593660113032868679913879)
    ·
      refine ⟨204890490169549303019870819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136593660113032868679913879 204890490169549303019870819)
      ·
        refine ⟨307335735254323954529806229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204890490169549303019870819 307335735254323954529806229)
        ·
          refine ⟨14406362590046435368584667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 307335735254323954529806229 14406362590046435368584667)
          ·
            refine ⟨21609543885069653052877001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14406362590046435368584667 21609543885069653052877001)
            ·
              refine ⟨16207157913802239789657751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21609543885069653052877001 16207157913802239789657751)
              ·
                refine ⟨24310736870703359684486627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16207157913802239789657751 24310736870703359684486627)
                ·
                  refine ⟨36466105306055039526729941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24310736870703359684486627 36466105306055039526729941)
                  ·
                    refine ⟨854674343110664988907733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36466105306055039526729941 854674343110664988907733)
                    ·
                      rfl

theorem cell23_4993417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_4993417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993417 prefixEnd_4993417 := by exact prefixLift 4993417
  have htrace : WordTrace (prefixWord ++ tailWord_4993417) baseStart_4993417 baseEnd_4993417 := by
    simpa [prefixWord, tailWord_4993417, baseEnd_4993417] using wordTrace_append hprefix tailTrace_4993417
  have hstable : (prefixWord ++ tailWord_4993417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993417).length < 2 ^ (prefixWord ++ tailWord_4993417).sum := by decide
  have hdescent : baseEnd_4993417 < baseStart_4993417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993434 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_4993434 : Nat := 118140960795 + 4993434 * 2 ^ 59
def prefixEnd_4993434 : Nat := 4983230072969 + 3 ^ 40 * 4993434 * 2
def baseEnd_4993434 : Nat := 854677252834373800070207

theorem tailTrace_4993434 : CollatzResearch.WordTrace tailWord_4993434 prefixEnd_4993434 854677252834373800070207 := by
  unfold tailWord_4993434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45531375047912225869146839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121417000127765935651058237 45531375047912225869146839)
  ·
    refine ⟨68297062571868338803720259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45531375047912225869146839 68297062571868338803720259)
    ·
      refine ⟨102445593857802508205580389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68297062571868338803720259 102445593857802508205580389)
      ·
        refine ⟨19208548848337970288546323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102445593857802508205580389 19208548848337970288546323)
        ·
          refine ⟨28812823272506955432819485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19208548848337970288546323 28812823272506955432819485)
          ·
            refine ⟨10804808727190108287307307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28812823272506955432819485 10804808727190108287307307)
            ·
              refine ⟨16207213090785162430960961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804808727190108287307307 16207213090785162430960961)
              ·
                refine ⟨12155409818088871823220721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16207213090785162430960961 12155409818088871823220721)
                ·
                  refine ⟨9116557363566653867415541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12155409818088871823220721 9116557363566653867415541)
                  ·
                    refine ⟨854677252834373800070207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9116557363566653867415541 854677252834373800070207)
                    ·
                      rfl

theorem cell23_4993434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_4993434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993434 prefixEnd_4993434 := by exact prefixLift 4993434
  have htrace : WordTrace (prefixWord ++ tailWord_4993434) baseStart_4993434 baseEnd_4993434 := by
    simpa [prefixWord, tailWord_4993434, baseEnd_4993434] using wordTrace_append hprefix tailTrace_4993434
  have hstable : (prefixWord ++ tailWord_4993434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993434).length < 2 ^ (prefixWord ++ tailWord_4993434).sum := by decide
  have hdescent : baseEnd_4993434 < baseStart_4993434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993497 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4993497 : Nat := 118140960795 + 4993497 * 2 ^ 59
def prefixEnd_4993497 : Nat := 4983230072969 + 3 ^ 40 * 4993497 * 2
def baseEnd_4993497 : Nat := 2564064107784354653722831

theorem tailTrace_4993497 : CollatzResearch.WordTrace tailWord_4993497 prefixEnd_4993497 2564064107784354653722831 := by
  unfold tailWord_4993497
  simp only [CollatzResearch.WordTrace]
  refine ⟨182127797990420665236130745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121418531993613776824087163 182127797990420665236130745)
  ·
    refine ⟨136595848492815498927098059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182127797990420665236130745 136595848492815498927098059)
    ·
      refine ⟨204893772739223248390647089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136595848492815498927098059 204893772739223248390647089)
      ·
        refine ⟨153670329554417436292985317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204893772739223248390647089 153670329554417436292985317)
        ·
          refine ⟨28813186791453269304934747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153670329554417436292985317 28813186791453269304934747)
          ·
            refine ⟨43219780187179903957402121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28813186791453269304934747 43219780187179903957402121)
            ·
              refine ⟨32414835140384927968051591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43219780187179903957402121 32414835140384927968051591)
              ·
                refine ⟨48622252710577391952077387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32414835140384927968051591 48622252710577391952077387)
                ·
                  refine ⟨72933379065866087928116081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48622252710577391952077387 72933379065866087928116081)
                  ·
                    refine ⟨54700034299399565946087061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72933379065866087928116081 54700034299399565946087061)
                    ·
                      refine ⟨2564064107784354653722831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54700034299399565946087061 2564064107784354653722831)
                      ·
                        rfl

theorem cell23_4993497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4993497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993497 prefixEnd_4993497 := by exact prefixLift 4993497
  have htrace : WordTrace (prefixWord ++ tailWord_4993497) baseStart_4993497 baseEnd_4993497 := by
    simpa [prefixWord, tailWord_4993497, baseEnd_4993497] using wordTrace_append hprefix tailTrace_4993497
  have hstable : (prefixWord ++ tailWord_4993497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993497).length < 2 ^ (prefixWord ++ tailWord_4993497).sum := by decide
  have hdescent : baseEnd_4993497 < baseStart_4993497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993521 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_4993521 : Nat := 118140960795 + 4993521 * 2 ^ 59
def prefixEnd_4993521 : Nat := 4983230072969 + 3 ^ 40 * 4993521 * 2
def baseEnd_4993521 : Nat := 2564076431320062559822721

theorem tailTrace_4993521 : CollatzResearch.WordTrace tailWord_4993521 prefixEnd_4993521 2564076431320062559822721 := by
  unfold tailWord_4993521
  simp only [CollatzResearch.WordTrace]
  refine ⟨182128673342333717335004417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121419115561555811556669611 182128673342333717335004417)
  ·
    refine ⟨136596505006750288001253313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182128673342333717335004417 136596505006750288001253313)
    ·
      refine ⟨102447378755062716000939985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136596505006750288001253313 102447378755062716000939985)
      ·
        refine ⟨76835534066297037000704989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102447378755062716000939985 76835534066297037000704989)
        ·
          refine ⟨28813325274861388875264371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76835534066297037000704989 28813325274861388875264371)
          ·
            refine ⟨43219987912292083312896557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28813325274861388875264371 43219987912292083312896557)
            ·
              refine ⟨16207495467109531242336209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43219987912292083312896557 16207495467109531242336209)
              ·
                refine ⟨12155621600332148431752157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16207495467109531242336209 12155621600332148431752157)
                ·
                  refine ⟨4558358100124555661907059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12155621600332148431752157 4558358100124555661907059)
                  ·
                    refine ⟨6837537150186833492860589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558358100124555661907059 6837537150186833492860589)
                    ·
                      refine ⟨2564076431320062559822721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837537150186833492860589 2564076431320062559822721)
                      ·
                        rfl

theorem cell23_4993521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_4993521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993521 prefixEnd_4993521 := by exact prefixLift 4993521
  have htrace : WordTrace (prefixWord ++ tailWord_4993521) baseStart_4993521 baseEnd_4993521 := by
    simpa [prefixWord, tailWord_4993521, baseEnd_4993521] using wordTrace_append hprefix tailTrace_4993521
  have hstable : (prefixWord ++ tailWord_4993521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993521).length < 2 ^ (prefixWord ++ tailWord_4993521).sum := by decide
  have hdescent : baseEnd_4993521 < baseStart_4993521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993525 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4993525 : Nat := 118140960795 + 4993525 * 2 ^ 59
def prefixEnd_4993525 : Nat := 4983230072969 + 3 ^ 40 * 4993525 * 2
def baseEnd_4993525 : Nat := 2564078485242680544172703

theorem tailTrace_4993525 : CollatzResearch.WordTrace tailWord_4993525 prefixEnd_4993525 2564078485242680544172703 := by
  unfold tailWord_4993525
  simp only [CollatzResearch.WordTrace]
  refine ⟨182128819234319226018150029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121419212822879484012100019 182128819234319226018150029)
  ·
    refine ⟨68298307212869709756806261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182128819234319226018150029 68298307212869709756806261)
    ·
      refine ⟨6402966301206535289700587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68298307212869709756806261 6402966301206535289700587)
      ·
        refine ⟨9604449451809802934550881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6402966301206535289700587 9604449451809802934550881)
        ·
          refine ⟨7203337088857352200913161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9604449451809802934550881 7203337088857352200913161)
          ·
            refine ⟨5402502816643014150684871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7203337088857352200913161 5402502816643014150684871)
            ·
              refine ⟨8103754224964521226027307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402502816643014150684871 8103754224964521226027307)
              ·
                refine ⟨12155631337446781839040961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8103754224964521226027307 12155631337446781839040961)
                ·
                  refine ⟨9116723503085086379280721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12155631337446781839040961 9116723503085086379280721)
                  ·
                    refine ⟨6837542627313814784460541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9116723503085086379280721 6837542627313814784460541)
                    ·
                      refine ⟨2564078485242680544172703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837542627313814784460541 2564078485242680544172703)
                      ·
                        rfl

theorem cell23_4993525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4993525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993525 prefixEnd_4993525 := by exact prefixLift 4993525
  have htrace : WordTrace (prefixWord ++ tailWord_4993525) baseStart_4993525 baseEnd_4993525 := by
    simpa [prefixWord, tailWord_4993525, baseEnd_4993525] using wordTrace_append hprefix tailTrace_4993525
  have hstable : (prefixWord ++ tailWord_4993525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993525).length < 2 ^ (prefixWord ++ tailWord_4993525).sum := by decide
  have hdescent : baseEnd_4993525 < baseStart_4993525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993541 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_4993541 : Nat := 118140960795 + 4993541 * 2 ^ 59
def prefixEnd_4993541 : Nat := 4983230072969 + 3 ^ 40 * 4993541 * 2
def baseEnd_4993541 : Nat := 854695566977717493857543

theorem tailTrace_4993541 : CollatzResearch.WordTrace tailWord_4993541 prefixEnd_4993541 854695566977717493857543 := by
  unfold tailWord_4993541
  simp only [CollatzResearch.WordTrace]
  refine ⟨182129402802261260750732477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121419601868174173833821651 182129402802261260750732477)
  ·
    refine ⟨68298526050847972781524679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182129402802261260750732477 68298526050847972781524679)
    ·
      refine ⟨102447789076271959172287019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68298526050847972781524679 102447789076271959172287019)
      ·
        refine ⟨153671683614407938758430529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102447789076271959172287019 153671683614407938758430529)
        ·
          refine ⟨115253762710805954068822897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153671683614407938758430529 115253762710805954068822897)
          ·
            refine ⟨86440322033104465551617173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115253762710805954068822897 86440322033104465551617173)
            ·
              refine ⟨4051890095301771822732055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86440322033104465551617173 4051890095301771822732055)
              ·
                refine ⟨6077835142952657734098083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051890095301771822732055 6077835142952657734098083)
                ·
                  refine ⟨9116752714428986601147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077835142952657734098083 9116752714428986601147125)
                  ·
                    refine ⟨854695566977717493857543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9116752714428986601147125 854695566977717493857543)
                    ·
                      rfl

theorem cell23_4993541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_4993541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993541 prefixEnd_4993541 := by exact prefixLift 4993541
  have htrace : WordTrace (prefixWord ++ tailWord_4993541) baseStart_4993541 baseEnd_4993541 := by
    simpa [prefixWord, tailWord_4993541, baseEnd_4993541] using wordTrace_append hprefix tailTrace_4993541
  have hstable : (prefixWord ++ tailWord_4993541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993541).length < 2 ^ (prefixWord ++ tailWord_4993541).sum := by decide
  have hdescent : baseEnd_4993541 < baseStart_4993541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993561 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 7, 2, 2]
def baseStart_4993561 : Nat := 118140960795 + 4993561 * 2 ^ 59
def prefixEnd_4993561 : Nat := 4983230072969 + 3 ^ 40 * 4993561 * 2
def baseEnd_4993561 : Nat := 2564096970546242403322537

theorem tailTrace_4993561 : CollatzResearch.WordTrace tailWord_4993561 prefixEnd_4993561 2564096970546242403322537 := by
  unfold tailWord_4993561
  simp only [CollatzResearch.WordTrace]
  refine ⟨182130132262188804166460537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121420088174792536110973691 182130132262188804166460537)
  ·
    refine ⟨136597599196641603124845403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182130132262188804166460537 136597599196641603124845403)
    ·
      refine ⟨204896398794962404687268105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136597599196641603124845403 204896398794962404687268105)
      ·
        refine ⟨153672299096221803515451079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204896398794962404687268105 153672299096221803515451079)
        ·
          refine ⟨230508448644332705273176619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153672299096221803515451079 230508448644332705273176619)
          ·
            refine ⟨345762672966499057909764929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230508448644332705273176619 345762672966499057909764929)
            ·
              refine ⟨259322004724874293432323697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345762672966499057909764929 259322004724874293432323697)
              ·
                refine ⟨194491503543655720074242773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259322004724874293432323697 194491503543655720074242773)
                ·
                  refine ⟨4558394614304430939240065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 194491503543655720074242773 4558394614304430939240065)
                  ·
                    refine ⟨3418795960728323204430049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558394614304430939240065 3418795960728323204430049)
                    ·
                      refine ⟨2564096970546242403322537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418795960728323204430049 2564096970546242403322537)
                      ·
                        rfl

theorem cell23_4993561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_4993561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993561 prefixEnd_4993561 := by exact prefixLift 4993561
  have htrace : WordTrace (prefixWord ++ tailWord_4993561) baseStart_4993561 baseEnd_4993561 := by
    simpa [prefixWord, tailWord_4993561, baseEnd_4993561] using wordTrace_append hprefix tailTrace_4993561
  have hstable : (prefixWord ++ tailWord_4993561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993561).length < 2 ^ (prefixWord ++ tailWord_4993561).sum := by decide
  have hdescent : baseEnd_4993561 < baseStart_4993561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993564 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4993564 : Nat := 118140960795 + 4993564 * 2 ^ 59
def prefixEnd_4993564 : Nat := 4983230072969 + 3 ^ 40 * 4993564 * 2
def baseEnd_4993564 : Nat := 2564098510988205891585023

theorem tailTrace_4993564 : CollatzResearch.WordTrace tailWord_4993564 prefixEnd_4993564 2564098510988205891585023 := by
  unfold tailWord_4993564
  simp only [CollatzResearch.WordTrace]
  refine ⟨91065120840588967839409873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121420161120785290452546497 91065120840588967839409873)
  ·
    refine ⟨68298840630441725879557405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91065120840588967839409873 68298840630441725879557405)
    ·
      refine ⟨25612065236415647204834027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68298840630441725879557405 25612065236415647204834027)
      ·
        refine ⟨38418097854623470807251041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25612065236415647204834027 38418097854623470807251041)
        ·
          refine ⟨28813573390967603105438281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38418097854623470807251041 28813573390967603105438281)
          ·
            refine ⟨21610180043225702329078711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28813573390967603105438281 21610180043225702329078711)
            ·
              refine ⟨32415270064838553493618067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21610180043225702329078711 32415270064838553493618067)
              ·
                refine ⟨48622905097257830240427101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32415270064838553493618067 48622905097257830240427101)
                ·
                  refine ⟨18233589411471686340160163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48622905097257830240427101 18233589411471686340160163)
                  ·
                    refine ⟨27350384117207529510240245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18233589411471686340160163 27350384117207529510240245)
                    ·
                      refine ⟨2564098510988205891585023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27350384117207529510240245 2564098510988205891585023)
                      ·
                        rfl

theorem cell23_4993564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4993564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993564 prefixEnd_4993564 := by exact prefixLift 4993564
  have htrace : WordTrace (prefixWord ++ tailWord_4993564) baseStart_4993564 baseEnd_4993564 := by
    simpa [prefixWord, tailWord_4993564, baseEnd_4993564] using wordTrace_append hprefix tailTrace_4993564
  have hstable : (prefixWord ++ tailWord_4993564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993564).length < 2 ^ (prefixWord ++ tailWord_4993564).sum := by decide
  have hdescent : baseEnd_4993564 < baseStart_4993564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993567 : List Nat := [1, 1, 2, 4, 1, 1, 1, 12]
def baseStart_4993567 : Nat := 118140960795 + 4993567 * 2 ^ 59
def prefixEnd_4993567 : Nat := 4983230072969 + 3 ^ 40 * 4993567 * 2
def baseEnd_4993567 : Nat := 94966668571487754809167

theorem tailTrace_4993567 : CollatzResearch.WordTrace tailWord_4993567 prefixEnd_4993567 94966668571487754809167 := by
  unfold tailWord_4993567
  simp only [CollatzResearch.WordTrace]
  refine ⟨182130351100167067191178955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121420234066778044794119303 182130351100167067191178955)
  ·
    refine ⟨273195526650250600786768433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182130351100167067191178955 273195526650250600786768433)
    ·
      refine ⟨204896644987687950590076325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273195526650250600786768433 204896644987687950590076325)
      ·
        refine ⟨38418120935191490735639311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204896644987687950590076325 38418120935191490735639311)
        ·
          refine ⟨57627181402787236103458967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38418120935191490735639311 57627181402787236103458967)
          ·
            refine ⟨86440772104180854155188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57627181402787236103458967 86440772104180854155188451)
            ·
              refine ⟨129661158156271281232782677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86440772104180854155188451 129661158156271281232782677)
              ·
                refine ⟨94966668571487754809167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 129661158156271281232782677 94966668571487754809167)
                ·
                  rfl

theorem cell23_4993567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 12].length) (baseStart_4993567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993567 prefixEnd_4993567 := by exact prefixLift 4993567
  have htrace : WordTrace (prefixWord ++ tailWord_4993567) baseStart_4993567 baseEnd_4993567 := by
    simpa [prefixWord, tailWord_4993567, baseEnd_4993567] using wordTrace_append hprefix tailTrace_4993567
  have hstable : (prefixWord ++ tailWord_4993567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993567).length < 2 ^ (prefixWord ++ tailWord_4993567).sum := by decide
  have hdescent : baseEnd_4993567 < baseStart_4993567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993571 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 6]
def baseStart_4993571 : Nat := 118140960795 + 4993571 * 2 ^ 59
def prefixEnd_4993571 : Nat := 4983230072969 + 3 ^ 40 * 4993571 * 2
def baseEnd_4993571 : Nat := 854700701784262454732497

theorem tailTrace_4993571 : CollatzResearch.WordTrace tailWord_4993571 prefixEnd_4993571 854700701784262454732497 := by
  unfold tailWord_4993571
  simp only [CollatzResearch.WordTrace]
  refine ⟨182130496992152575874324567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121420331328101717249549711 182130496992152575874324567)
  ·
    refine ⟨273195745488228863811486851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182130496992152575874324567 273195745488228863811486851)
    ·
      refine ⟨409793618232343295717230277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273195745488228863811486851 409793618232343295717230277)
      ·
        refine ⟨76836303418564367946980677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 409793618232343295717230277 76836303418564367946980677)
        ·
          refine ⟨14406806890980818990058877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76836303418564367946980677 14406806890980818990058877)
          ·
            refine ⟨5402552584117807121272079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14406806890980818990058877 5402552584117807121272079)
            ·
              refine ⟨8103828876176710681908119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402552584117807121272079 8103828876176710681908119)
              ·
                refine ⟨12155743314265066022862179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8103828876176710681908119 12155743314265066022862179)
                ·
                  refine ⟨18233614971397599034293269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12155743314265066022862179 18233614971397599034293269)
                  ·
                    refine ⟨854700701784262454732497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18233614971397599034293269 854700701784262454732497)
                    ·
                      rfl

theorem cell23_4993571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 6].length) (baseStart_4993571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993571 prefixEnd_4993571 := by exact prefixLift 4993571
  have htrace : WordTrace (prefixWord ++ tailWord_4993571) baseStart_4993571 baseEnd_4993571 := by
    simpa [prefixWord, tailWord_4993571, baseEnd_4993571] using wordTrace_append hprefix tailTrace_4993571
  have hstable : (prefixWord ++ tailWord_4993571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993571).length < 2 ^ (prefixWord ++ tailWord_4993571).sum := by decide
  have hdescent : baseEnd_4993571 < baseStart_4993571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993575 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4993575 : Nat := 118140960795 + 4993575 * 2 ^ 59
def prefixEnd_4993575 : Nat := 4983230072969 + 3 ^ 40 * 4993575 * 2
def baseEnd_4993575 : Nat := 854701386425135116182491

theorem tailTrace_4993575 : CollatzResearch.WordTrace tailWord_4993575 prefixEnd_4993575 854701386425135116182491 := by
  unfold tailWord_4993575
  simp only [CollatzResearch.WordTrace]
  refine ⟨182130642884138084557470179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121420428589425389704980119 182130642884138084557470179)
  ·
    refine ⟨273195964326207126836205269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182130642884138084557470179 273195964326207126836205269)
    ·
      refine ⟨6403030413895479535223561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 273195964326207126836205269 6403030413895479535223561)
      ·
        refine ⟨4802272810421609651417671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403030413895479535223561 4802272810421609651417671)
        ·
          refine ⟨7203409215632414477126507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802272810421609651417671 7203409215632414477126507)
          ·
            refine ⟨10805113823448621715689761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203409215632414477126507 10805113823448621715689761)
            ·
              refine ⟨8103835367586466286767321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10805113823448621715689761 8103835367586466286767321)
              ·
                refine ⟨6077876525689849715075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8103835367586466286767321 6077876525689849715075491)
                ·
                  refine ⟨9116814788534774572613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077876525689849715075491 9116814788534774572613237)
                  ·
                    refine ⟨854701386425135116182491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9116814788534774572613237 854701386425135116182491)
                    ·
                      rfl

theorem cell23_4993575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4993575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993575 prefixEnd_4993575 := by exact prefixLift 4993575
  have htrace : WordTrace (prefixWord ++ tailWord_4993575) baseStart_4993575 baseEnd_4993575 := by
    simpa [prefixWord, tailWord_4993575, baseEnd_4993575] using wordTrace_append hprefix tailTrace_4993575
  have hstable : (prefixWord ++ tailWord_4993575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993575).length < 2 ^ (prefixWord ++ tailWord_4993575).sum := by decide
  have hdescent : baseEnd_4993575 < baseStart_4993575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993578 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4993578 : Nat := 118140960795 + 4993578 * 2 ^ 59
def prefixEnd_4993578 : Nat := 4983230072969 + 3 ^ 40 * 4993578 * 2
def baseEnd_4993578 : Nat := 2564105699717368836809959

theorem tailTrace_4993578 : CollatzResearch.WordTrace tailWord_4993578 prefixEnd_4993578 2564105699717368836809959 := by
  unfold tailWord_4993578
  simp only [CollatzResearch.WordTrace]
  refine ⟨45532688075781804017457347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121420501535418144046552925 45532688075781804017457347)
  ·
    refine ⟨68299032113672706026186021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45532688075781804017457347 68299032113672706026186021)
    ·
      refine ⟨12806068521313632379909879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68299032113672706026186021 12806068521313632379909879)
      ·
        refine ⟨19209102781970448569864819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12806068521313632379909879 19209102781970448569864819)
        ·
          refine ⟨28813654172955672854797229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209102781970448569864819 28813654172955672854797229)
          ·
            refine ⟨10805120314858377320548961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28813654172955672854797229 10805120314858377320548961)
            ·
              refine ⟨8103840236143782990411721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10805120314858377320548961 8103840236143782990411721)
              ·
                refine ⟨6077880177107837242808791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8103840236143782990411721 6077880177107837242808791)
                ·
                  refine ⟨9116820265661755864213187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077880177107837242808791 9116820265661755864213187)
                  ·
                    refine ⟨13675230398492633796319781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9116820265661755864213187 13675230398492633796319781)
                    ·
                      refine ⟨2564105699717368836809959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13675230398492633796319781 2564105699717368836809959)
                      ·
                        rfl

theorem cell23_4993578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4993578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993578 prefixEnd_4993578 := by exact prefixLift 4993578
  have htrace : WordTrace (prefixWord ++ tailWord_4993578) baseStart_4993578 baseEnd_4993578 := by
    simpa [prefixWord, tailWord_4993578, baseEnd_4993578] using wordTrace_append hprefix tailTrace_4993578
  have hstable : (prefixWord ++ tailWord_4993578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993578).length < 2 ^ (prefixWord ++ tailWord_4993578).sum := by decide
  have hdescent : baseEnd_4993578 < baseStart_4993578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993584 : List Nat := [2, 1, 1, 1, 2, 3, 6, 7]
def baseStart_4993584 : Nat := 118140960795 + 4993584 * 2 ^ 59
def prefixEnd_4993584 : Nat := 4983230072969 + 3 ^ 40 * 4993584 * 2
def baseEnd_4993584 : Nat := 94966991874122067160553

theorem tailTrace_4993584 : CollatzResearch.WordTrace tailWord_4993584 prefixEnd_4993584 94966991874122067160553 := by
  unfold tailWord_4993584
  simp only [CollatzResearch.WordTrace]
  refine ⟨91065485570552739547273903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121420647427403652729698537 91065485570552739547273903)
  ·
    refine ⟨136598228355829109320910855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91065485570552739547273903 136598228355829109320910855)
    ·
      refine ⟨204897342533743663981366283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136598228355829109320910855 204897342533743663981366283)
      ·
        refine ⟨307346013800615495972049425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204897342533743663981366283 307346013800615495972049425)
        ·
          refine ⟨230509510350461621979037069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307346013800615495972049425 230509510350461621979037069)
          ·
            refine ⟨86441066381423108242138901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230509510350461621979037069 86441066381423108242138901)
            ·
              refine ⟨4051924986629208198850261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86441066381423108242138901 4051924986629208198850261)
              ·
                refine ⟨94966991874122067160553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4051924986629208198850261 94966991874122067160553)
                ·
                  rfl

theorem cell23_4993584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 7].length) (baseStart_4993584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993584 prefixEnd_4993584 := by exact prefixLift 4993584
  have htrace : WordTrace (prefixWord ++ tailWord_4993584) baseStart_4993584 baseEnd_4993584 := by
    simpa [prefixWord, tailWord_4993584, baseEnd_4993584] using wordTrace_append hprefix tailTrace_4993584
  have hstable : (prefixWord ++ tailWord_4993584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993584).length < 2 ^ (prefixWord ++ tailWord_4993584).sum := by decide
  have hdescent : baseEnd_4993584 < baseStart_4993584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993611 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 3]
def baseStart_4993611 : Nat := 118140960795 + 4993611 * 2 ^ 59
def prefixEnd_4993611 : Nat := 4983230072969 + 3 ^ 40 * 4993611 * 2
def baseEnd_4993611 : Nat := 2564122644578967207697307

theorem tailTrace_4993611 : CollatzResearch.WordTrace tailWord_4993611 prefixEnd_4993611 2564122644578967207697307 := by
  unfold tailWord_4993611
  simp only [CollatzResearch.WordTrace]
  refine ⟨182131955912007662705780687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121421303941338441803853791 182131955912007662705780687)
  ·
    refine ⟨273197933868011494058671031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182131955912007662705780687 273197933868011494058671031)
    ·
      refine ⟨409796900802017241088006547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273197933868011494058671031 409796900802017241088006547)
      ·
        refine ⟨614695351203025861632009821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409796900802017241088006547 614695351203025861632009821)
        ·
          refine ⟨230510756701134698112003683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 614695351203025861632009821 230510756701134698112003683)
          ·
            refine ⟨345766135051702047168005525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230510756701134698112003683 345766135051702047168005525)
            ·
              refine ⟨16207787580548533461000259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 345766135051702047168005525 16207787580548533461000259)
              ·
                refine ⟨24311681370822800191500389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16207787580548533461000259 24311681370822800191500389)
                ·
                  refine ⟨4558440257029275035906323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24311681370822800191500389 4558440257029275035906323)
                  ·
                    refine ⟨6837660385543912553859485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558440257029275035906323 6837660385543912553859485)
                    ·
                      refine ⟨2564122644578967207697307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837660385543912553859485 2564122644578967207697307)
                      ·
                        rfl

theorem cell23_4993611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 3].length) (baseStart_4993611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993611 prefixEnd_4993611 := by exact prefixLift 4993611
  have htrace : WordTrace (prefixWord ++ tailWord_4993611) baseStart_4993611 baseEnd_4993611 := by
    simpa [prefixWord, tailWord_4993611, baseEnd_4993611] using wordTrace_append hprefix tailTrace_4993611
  have hstable : (prefixWord ++ tailWord_4993611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993611).length < 2 ^ (prefixWord ++ tailWord_4993611).sum := by decide
  have hdescent : baseEnd_4993611 < baseStart_4993611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993612 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4993612 : Nat := 118140960795 + 4993612 * 2 ^ 59
def prefixEnd_4993612 : Nat := 4983230072969 + 3 ^ 40 * 4993612 * 2
def baseEnd_4993612 : Nat := 2564123158059621703784803

theorem tailTrace_4993612 : CollatzResearch.WordTrace tailWord_4993612 prefixEnd_4993612 2564123158059621703784803 := by
  unfold tailWord_4993612
  simp only [CollatzResearch.WordTrace]
  refine ⟨91065996192502019938283545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121421328256669359917711393 91065996192502019938283545)
  ·
    refine ⟨68299497144376514953712659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91065996192502019938283545 68299497144376514953712659)
    ·
      refine ⟨102449245716564772430568989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68299497144376514953712659 102449245716564772430568989)
      ·
        refine ⟨38418467143711789661463371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102449245716564772430568989 38418467143711789661463371)
        ·
          refine ⟨57627700715567684492195057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38418467143711789661463371 57627700715567684492195057)
          ·
            refine ⟨43220775536675763369146293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57627700715567684492195057 43220775536675763369146293)
            ·
              refine ⟨4051947706563352815857465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43220775536675763369146293 4051947706563352815857465)
              ·
                refine ⟨3038960779922514611893099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051947706563352815857465 3038960779922514611893099)
                ·
                  refine ⟨4558441169883771917839649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038960779922514611893099 4558441169883771917839649)
                  ·
                    refine ⟨3418830877412828938379737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558441169883771917839649 3418830877412828938379737)
                    ·
                      refine ⟨2564123158059621703784803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418830877412828938379737 2564123158059621703784803)
                      ·
                        rfl

theorem cell23_4993612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4993612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993612 prefixEnd_4993612 := by exact prefixLift 4993612
  have htrace : WordTrace (prefixWord ++ tailWord_4993612) baseStart_4993612 baseEnd_4993612 := by
    simpa [prefixWord, tailWord_4993612, baseEnd_4993612] using wordTrace_append hprefix tailTrace_4993612
  have hstable : (prefixWord ++ tailWord_4993612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993612).length < 2 ^ (prefixWord ++ tailWord_4993612).sum := by decide
  have hdescent : baseEnd_4993612 < baseStart_4993612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993706 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4993706 : Nat := 118140960795 + 4993706 * 2 ^ 59
def prefixEnd_4993706 : Nat := 4983230072969 + 3 ^ 40 * 4993706 * 2
def baseEnd_4993706 : Nat := 2564171425241144336009371

theorem tailTrace_4993706 : CollatzResearch.WordTrace tailWord_4993706 prefixEnd_4993706 2564171425241144336009371 := by
  unfold tailWord_4993706
  simp only [CollatzResearch.WordTrace]
  refine ⟨45533855211665873482622243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121423613897775662620325981 45533855211665873482622243)
  ·
    refine ⟨68300782817498810223933365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45533855211665873482622243 68300782817498810223933365)
    ·
      refine ⟨6403198389140513458493753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68300782817498810223933365 6403198389140513458493753)
      ·
        refine ⟨4802398791855385093870315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403198389140513458493753 4802398791855385093870315)
        ·
          refine ⟨7203598187783077640805473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802398791855385093870315 7203598187783077640805473)
          ·
            refine ⟨5402698640837308230604105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7203598187783077640805473 5402698640837308230604105)
            ·
              refine ⟨4052023980627981172953079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5402698640837308230604105 4052023980627981172953079)
              ·
                refine ⟨6078035970941971759429619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052023980627981172953079 6078035970941971759429619)
                ·
                  refine ⟨9117053956412957639144429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6078035970941971759429619 9117053956412957639144429)
                  ·
                    refine ⟨3418895233654859114679161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9117053956412957639144429 3418895233654859114679161)
                    ·
                      refine ⟨2564171425241144336009371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418895233654859114679161 2564171425241144336009371)
                      ·
                        rfl

theorem cell23_4993706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4993706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993706 prefixEnd_4993706 := by exact prefixLift 4993706
  have htrace : WordTrace (prefixWord ++ tailWord_4993706) baseStart_4993706 baseEnd_4993706 := by
    simpa [prefixWord, tailWord_4993706, baseEnd_4993706] using wordTrace_append hprefix tailTrace_4993706
  have hstable : (prefixWord ++ tailWord_4993706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993706).length < 2 ^ (prefixWord ++ tailWord_4993706).sum := by decide
  have hdescent : baseEnd_4993706 < baseStart_4993706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993719 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_4993719 : Nat := 118140960795 + 4993719 * 2 ^ 59
def prefixEnd_4993719 : Nat := 4983230072969 + 3 ^ 40 * 4993719 * 2
def baseEnd_4993719 : Nat := 2564178100489652785146811

theorem tailTrace_4993719 : CollatzResearch.WordTrace tailWord_4993719 prefixEnd_4993719 2564178100489652785146811 := by
  unfold tailWord_4993719
  simp only [CollatzResearch.WordTrace]
  refine ⟨182135894995616397150712211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121423929997077598100474807 182135894995616397150712211)
  ·
    refine ⟨273203842493424595726068317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182135894995616397150712211 273203842493424595726068317)
    ·
      refine ⟨102451440935034223397275619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273203842493424595726068317 102451440935034223397275619)
      ·
        refine ⟨153677161402551335095913429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102451440935034223397275619 153677161402551335095913429)
        ·
          refine ⟨3601808470372296916310471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 153677161402551335095913429 3601808470372296916310471)
          ·
            refine ⟨5402712705558445374465707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601808470372296916310471 5402712705558445374465707)
            ·
              refine ⟨8104069058337668061698561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402712705558445374465707 8104069058337668061698561)
              ·
                refine ⟨6078051793753251046273921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8104069058337668061698561 6078051793753251046273921)
                ·
                  refine ⟨4558538845314938284705441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078051793753251046273921 4558538845314938284705441)
                  ·
                    refine ⟨3418904133986203713529081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558538845314938284705441 3418904133986203713529081)
                    ·
                      refine ⟨2564178100489652785146811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3418904133986203713529081 2564178100489652785146811)
                      ·
                        rfl

theorem cell23_4993719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_4993719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993719 prefixEnd_4993719 := by exact prefixLift 4993719
  have htrace : WordTrace (prefixWord ++ tailWord_4993719) baseStart_4993719 baseEnd_4993719 := by
    simpa [prefixWord, tailWord_4993719, baseEnd_4993719] using wordTrace_append hprefix tailTrace_4993719
  have hstable : (prefixWord ++ tailWord_4993719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993719).length < 2 ^ (prefixWord ++ tailWord_4993719).sum := by decide
  have hdescent : baseEnd_4993719 < baseStart_4993719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993744 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_4993744 : Nat := 118140960795 + 4993744 * 2 ^ 59
def prefixEnd_4993744 : Nat := 4983230072969 + 3 ^ 40 * 4993744 * 2
def baseEnd_4993744 : Nat := 2564190937506015187334195

theorem tailTrace_4993744 : CollatzResearch.WordTrace tailWord_4993744 prefixEnd_4993744 2564190937506015187334195 := by
  unfold tailWord_4993744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91068403410262913210186143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121424537880350550946914857 91068403410262913210186143)
  ·
    refine ⟨136602605115394369815279215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91068403410262913210186143 136602605115394369815279215)
    ·
      refine ⟨204903907673091554722918823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136602605115394369815279215 204903907673091554722918823)
      ·
        refine ⟨307355861509637332084378235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204903907673091554722918823 307355861509637332084378235)
        ·
          refine ⟨461033792264455998126567353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307355861509637332084378235 461033792264455998126567353)
          ·
            refine ⟨345775344198341998594925515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461033792264455998126567353 345775344198341998594925515)
            ·
              refine ⟨518663016297512997892388273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345775344198341998594925515 518663016297512997892388273)
              ·
                refine ⟨388997262223134748419291205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518663016297512997892388273 388997262223134748419291205)
                ·
                  refine ⟨72936986666837765328617101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388997262223134748419291205 72936986666837765328617101)
                  ·
                    refine ⟨27351370000064161998231413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72936986666837765328617101 27351370000064161998231413)
                    ·
                      refine ⟨2564190937506015187334195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27351370000064161998231413 2564190937506015187334195)
                      ·
                        rfl

theorem cell23_4993744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_4993744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993744 prefixEnd_4993744 := by exact prefixLift 4993744
  have htrace : WordTrace (prefixWord ++ tailWord_4993744) baseStart_4993744 baseEnd_4993744 := by
    simpa [prefixWord, tailWord_4993744, baseEnd_4993744] using wordTrace_append hprefix tailTrace_4993744
  have hstable : (prefixWord ++ tailWord_4993744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993744).length < 2 ^ (prefixWord ++ tailWord_4993744).sum := by decide
  have hdescent : baseEnd_4993744 < baseStart_4993744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993778 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4993778 : Nat := 118140960795 + 4993778 * 2 ^ 59
def prefixEnd_4993778 : Nat := 4983230072969 + 3 ^ 40 * 4993778 * 2
def baseEnd_4993778 : Nat := 2564208395848268054309039

theorem tailTrace_4993778 : CollatzResearch.WordTrace tailWord_4993778 prefixEnd_4993778 2564208395848268054309039 := by
  unfold tailWord_4993778
  simp only [CollatzResearch.WordTrace]
  refine ⟨45534511725600662556777497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121425364601601766818073325 45534511725600662556777497)
  ·
    refine ⟨34150883794200496917583123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45534511725600662556777497 34150883794200496917583123)
    ·
      refine ⟨51226325691300745376374685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34150883794200496917583123 51226325691300745376374685)
      ·
        refine ⟨19209872134237779516140507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51226325691300745376374685 19209872134237779516140507)
        ·
          refine ⟨28814808201356669274210761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209872134237779516140507 28814808201356669274210761)
          ·
            refine ⟨21611106151017501955658071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28814808201356669274210761 21611106151017501955658071)
            ·
              refine ⟨32416659226526252933487107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21611106151017501955658071 32416659226526252933487107)
              ·
                refine ⟨48624988839789379400230661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32416659226526252933487107 48624988839789379400230661)
                ·
                  refine ⟨9117185407460508637543249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48624988839789379400230661 9117185407460508637543249)
                  ·
                    refine ⟨6837889055595381478157437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9117185407460508637543249 6837889055595381478157437)
                    ·
                      refine ⟨2564208395848268054309039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837889055595381478157437 2564208395848268054309039)
                      ·
                        rfl

theorem cell23_4993778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4993778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993778 prefixEnd_4993778 := by exact prefixLift 4993778
  have htrace : WordTrace (prefixWord ++ tailWord_4993778) baseStart_4993778 baseEnd_4993778 := by
    simpa [prefixWord, tailWord_4993778, baseEnd_4993778] using wordTrace_append hprefix tailTrace_4993778
  have hstable : (prefixWord ++ tailWord_4993778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993778).length < 2 ^ (prefixWord ++ tailWord_4993778).sum := by decide
  have hdescent : baseEnd_4993778 < baseStart_4993778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993811 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 3, 5]
def baseStart_4993811 : Nat := 118140960795 + 4993811 * 2 ^ 59
def prefixEnd_4993811 : Nat := 4983230072969 + 3 ^ 40 * 4993811 * 2
def baseEnd_4993811 : Nat := 854741780236622141732129

theorem tailTrace_4993811 : CollatzResearch.WordTrace tailWord_4993811 prefixEnd_4993811 854741780236622141732129 := by
  unfold tailWord_4993811
  simp only [CollatzResearch.WordTrace]
  refine ⟨182139250511283096863061287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121426167007522064575374191 182139250511283096863061287)
  ·
    refine ⟨273208875766924645294591931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182139250511283096863061287 273208875766924645294591931)
    ·
      refine ⟨409813313650386967941887897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273208875766924645294591931 409813313650386967941887897)
      ·
        refine ⟨307359985237790225956415923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409813313650386967941887897 307359985237790225956415923)
        ·
          refine ⟨461039977856685338934623885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307359985237790225956415923 461039977856685338934623885)
          ·
            refine ⟨172889991696257002100483957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461039977856685338934623885 172889991696257002100483957)
            ·
              refine ⟨16208436721524093946920371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172889991696257002100483957 16208436721524093946920371)
              ·
                refine ⟨24312655082286140920380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16208436721524093946920371 24312655082286140920380557)
                ·
                  refine ⟨9117245655857302845142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24312655082286140920380557 9117245655857302845142709)
                  ·
                    refine ⟨854741780236622141732129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9117245655857302845142709 854741780236622141732129)
                    ·
                      rfl

theorem cell23_4993811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].length) (baseStart_4993811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993811 prefixEnd_4993811 := by exact prefixLift 4993811
  have htrace : WordTrace (prefixWord ++ tailWord_4993811) baseStart_4993811 baseEnd_4993811 := by
    simpa [prefixWord, tailWord_4993811, baseEnd_4993811] using wordTrace_append hprefix tailTrace_4993811
  have hstable : (prefixWord ++ tailWord_4993811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993811).length < 2 ^ (prefixWord ++ tailWord_4993811).sum := by decide
  have hdescent : baseEnd_4993811 < baseStart_4993811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993841 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_4993841 : Nat := 118140960795 + 4993841 * 2 ^ 59
def prefixEnd_4993841 : Nat := 4983230072969 + 3 ^ 40 * 4993841 * 2
def baseEnd_4993841 : Nat := 854746915043167102607083

theorem tailTrace_4993841 : CollatzResearch.WordTrace tailWord_4993841 prefixEnd_4993841 854746915043167102607083 := by
  unfold tailWord_4993841
  simp only [CollatzResearch.WordTrace]
  refine ⟨182140344701174411986653377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121426896467449607991102251 182140344701174411986653377)
  ·
    refine ⟨136605258525880808989990033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182140344701174411986653377 136605258525880808989990033)
    ·
      refine ⟨102453943894410606742492525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136605258525880808989990033 102453943894410606742492525)
      ·
        refine ⟨38420228960403977528434697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102453943894410606742492525 38420228960403977528434697)
        ·
          refine ⟨28815171720302983146326023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38420228960403977528434697 28815171720302983146326023)
          ·
            refine ⟨43222757580454474719489035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28815171720302983146326023 43222757580454474719489035)
            ·
              refine ⟨64834136370681712079233553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43222757580454474719489035 64834136370681712079233553)
              ·
                refine ⟨48625602278011284059425165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64834136370681712079233553 48625602278011284059425165)
                ·
                  refine ⟨18234600854254231522284437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48625602278011284059425165 18234600854254231522284437)
                  ·
                    refine ⟨854746915043167102607083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18234600854254231522284437 854746915043167102607083)
                    ·
                      rfl

theorem cell23_4993841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_4993841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993841 prefixEnd_4993841 := by exact prefixLift 4993841
  have htrace : WordTrace (prefixWord ++ tailWord_4993841) baseStart_4993841 baseEnd_4993841 := by
    simpa [prefixWord, tailWord_4993841, baseEnd_4993841] using wordTrace_append hprefix tailTrace_4993841
  have hstable : (prefixWord ++ tailWord_4993841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993841).length < 2 ^ (prefixWord ++ tailWord_4993841).sum := by decide
  have hdescent : baseEnd_4993841 < baseStart_4993841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993842 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_4993842 : Nat := 118140960795 + 4993842 * 2 ^ 59
def prefixEnd_4993842 : Nat := 4983230072969 + 3 ^ 40 * 4993842 * 2
def baseEnd_4993842 : Nat := 2564241258610155803908745

theorem tailTrace_4993842 : CollatzResearch.WordTrace tailWord_4993842 prefixEnd_4993842 2564241258610155803908745 := by
  unfold tailWord_4993842
  simp only [CollatzResearch.WordTrace]
  refine ⟨45535095293542697289359945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121426920782780526104959853 45535095293542697289359945)
  ·
    refine ⟨34151321470157022967019959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45535095293542697289359945 34151321470157022967019959)
    ·
      refine ⟨51226982205235534450529939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34151321470157022967019959 51226982205235534450529939)
      ·
        refine ⟨76840473307853301675794909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51226982205235534450529939 76840473307853301675794909)
        ·
          refine ⟨28815177490444988128423091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76840473307853301675794909 28815177490444988128423091)
          ·
            refine ⟨43222766235667482192634637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28815177490444988128423091 43222766235667482192634637)
            ·
              refine ⟨16208537338375305822237989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43222766235667482192634637 16208537338375305822237989)
              ·
                refine ⟨3039100750945369841669623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16208537338375305822237989 3039100750945369841669623)
                ·
                  refine ⟨4558651126418054762504435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039100750945369841669623 4558651126418054762504435)
                  ·
                    refine ⟨6837976689627082143756653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558651126418054762504435 6837976689627082143756653)
                    ·
                      refine ⟨2564241258610155803908745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6837976689627082143756653 2564241258610155803908745)
                      ·
                        rfl

theorem cell23_4993842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_4993842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993842 prefixEnd_4993842 := by exact prefixLift 4993842
  have htrace : WordTrace (prefixWord ++ tailWord_4993842) baseStart_4993842 baseEnd_4993842 := by
    simpa [prefixWord, tailWord_4993842, baseEnd_4993842] using wordTrace_append hprefix tailTrace_4993842
  have hstable : (prefixWord ++ tailWord_4993842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993842).length < 2 ^ (prefixWord ++ tailWord_4993842).sum := by decide
  have hdescent : baseEnd_4993842 < baseStart_4993842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993865 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 5, 2, 2]
def baseStart_4993865 : Nat := 118140960795 + 4993865 * 2 ^ 59
def prefixEnd_4993865 : Nat := 4983230072969 + 3 ^ 40 * 4993865 * 2
def baseEnd_4993865 : Nat := 2564253068665209213921139

theorem tailTrace_4993865 : CollatzResearch.WordTrace tailWord_4993865 prefixEnd_4993865 2564253068665209213921139 := by
  unfold tailWord_4993865
  simp only [CollatzResearch.WordTrace]
  refine ⟨182141220053087464085527049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121427480035391642723684699 182141220053087464085527049)
  ·
    refine ⟨136605915039815598064145287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182141220053087464085527049 136605915039815598064145287)
    ·
      refine ⟨204908872559723397096217931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136605915039815598064145287 204908872559723397096217931)
      ·
        refine ⟨307363308839585095644326897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204908872559723397096217931 307363308839585095644326897)
        ·
          refine ⟨230522481629688821733245173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307363308839585095644326897 230522481629688821733245173)
          ·
            refine ⟨21611482652783327037491735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230522481629688821733245173 21611482652783327037491735)
            ·
              refine ⟨32417223979174990556237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21611482652783327037491735 32417223979174990556237603)
              ·
                refine ⟨48625835968762485834356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32417223979174990556237603 48625835968762485834356405)
                ·
                  refine ⟨4558672122071483046970913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48625835968762485834356405 4558672122071483046970913)
                  ·
                    refine ⟨3419004091553612285228185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558672122071483046970913 3419004091553612285228185)
                    ·
                      refine ⟨2564253068665209213921139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419004091553612285228185 2564253068665209213921139)
                      ·
                        rfl

theorem cell23_4993865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2, 2].length) (baseStart_4993865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993865 prefixEnd_4993865 := by exact prefixLift 4993865
  have htrace : WordTrace (prefixWord ++ tailWord_4993865) baseStart_4993865 baseEnd_4993865 := by
    simpa [prefixWord, tailWord_4993865, baseEnd_4993865] using wordTrace_append hprefix tailTrace_4993865
  have hstable : (prefixWord ++ tailWord_4993865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993865).length < 2 ^ (prefixWord ++ tailWord_4993865).sum := by decide
  have hdescent : baseEnd_4993865 < baseStart_4993865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993882 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_4993882 : Nat := 118140960795 + 4993882 * 2 ^ 59
def prefixEnd_4993882 : Nat := 4983230072969 + 3 ^ 40 * 4993882 * 2
def baseEnd_4993882 : Nat := 2564261797836335647408561

theorem tailTrace_4993882 : CollatzResearch.WordTrace tailWord_4993882 prefixEnd_4993882 2564261797836335647408561 := by
  unfold tailWord_4993882
  simp only [CollatzResearch.WordTrace]
  refine ⟨45535460023506468997223975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121427893396017250659263933 45535460023506468997223975)
  ·
    refine ⟨68303190035259703495835963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45535460023506468997223975 68303190035259703495835963)
    ·
      refine ⟨102454785052889555243753945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68303190035259703495835963 102454785052889555243753945)
      ·
        refine ⟨76841088789667166432815459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102454785052889555243753945 76841088789667166432815459)
        ·
          refine ⟨115261633184500749649223189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76841088789667166432815459 115261633184500749649223189)
          ·
            refine ⟨5402889055523472639807337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115261633184500749649223189 5402889055523472639807337)
            ·
              refine ⟨4052166791642604479855503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5402889055523472639807337 4052166791642604479855503)
              ·
                refine ⟨6078250187463906719783255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052166791642604479855503 6078250187463906719783255)
                ·
                  refine ⟨9117375281195860079674883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6078250187463906719783255 9117375281195860079674883)
                  ·
                    refine ⟨13676062921793790119512325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9117375281195860079674883 13676062921793790119512325)
                    ·
                      refine ⟨2564261797836335647408561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13676062921793790119512325 2564261797836335647408561)
                      ·
                        rfl

theorem cell23_4993882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_4993882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993882 prefixEnd_4993882 := by exact prefixLift 4993882
  have htrace : WordTrace (prefixWord ++ tailWord_4993882) baseStart_4993882 baseEnd_4993882 := by
    simpa [prefixWord, tailWord_4993882, baseEnd_4993882] using wordTrace_append hprefix tailTrace_4993882
  have hstable : (prefixWord ++ tailWord_4993882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993882).length < 2 ^ (prefixWord ++ tailWord_4993882).sum := by decide
  have hdescent : baseEnd_4993882 < baseStart_4993882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993892 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_4993892 : Nat := 118140960795 + 4993892 * 2 ^ 59
def prefixEnd_4993892 : Nat := 4983230072969 + 3 ^ 40 * 4993892 * 2
def baseEnd_4993892 : Nat := 854755644214293536094505

theorem tailTrace_4993892 : CollatzResearch.WordTrace tailWord_4993892 prefixEnd_4993892 854755644214293536094505 := by
  unfold tailWord_4993892
  simp only [CollatzResearch.WordTrace]
  refine ⟨91071102411994823848379965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121428136549326431797839953 91071102411994823848379965)
  ·
    refine ⟨34151663404498058943142487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91071102411994823848379965 34151663404498058943142487)
    ·
      refine ⟨51227495106747088414713731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34151663404498058943142487 51227495106747088414713731)
      ·
        refine ⟨76841242660120632622070597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51227495106747088414713731 76841242660120632622070597)
        ·
          refine ⟨14407732998772618616638237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76841242660120632622070597 14407732998772618616638237)
          ·
            refine ⟨5402899874539731981239339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14407732998772618616638237 5402899874539731981239339)
            ·
              refine ⟨8104349811809597971859009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402899874539731981239339 8104349811809597971859009)
              ·
                refine ⟨6078262358857198478894257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8104349811809597971859009 6078262358857198478894257)
                ·
                  refine ⟨4558696769142898859170693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078262358857198478894257 4558696769142898859170693)
                  ·
                    refine ⟨854755644214293536094505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558696769142898859170693 854755644214293536094505)
                    ·
                      rfl

theorem cell23_4993892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_4993892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993892 prefixEnd_4993892 := by exact prefixLift 4993892
  have htrace : WordTrace (prefixWord ++ tailWord_4993892) baseStart_4993892 baseEnd_4993892 := by
    simpa [prefixWord, tailWord_4993892, baseEnd_4993892] using wordTrace_append hprefix tailTrace_4993892
  have hstable : (prefixWord ++ tailWord_4993892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993892).length < 2 ^ (prefixWord ++ tailWord_4993892).sum := by decide
  have hdescent : baseEnd_4993892 < baseStart_4993892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993911 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_4993911 : Nat := 118140960795 + 4993911 * 2 ^ 59
def prefixEnd_4993911 : Nat := 4983230072969 + 3 ^ 40 * 4993911 * 2
def baseEnd_4993911 : Nat := 2564276688775316033945927

theorem tailTrace_4993911 : CollatzResearch.WordTrace tailWord_4993911 prefixEnd_4993911 2564276688775316033945927 := by
  unfold tailWord_4993911
  simp only [CollatzResearch.WordTrace]
  refine ⟨182142897810920813941701587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121428598540613875961134391 182142897810920813941701587)
  ·
    refine ⟨273214346716381220912552381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182142897810920813941701587 273214346716381220912552381)
    ·
      refine ⟨102455380018642957842207143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273214346716381220912552381 102455380018642957842207143)
      ·
        refine ⟨153683070027964436763310715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102455380018642957842207143 153683070027964436763310715)
        ·
          refine ⟨230524605041946655144966073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153683070027964436763310715 230524605041946655144966073)
          ·
            refine ⟨172893453781459991358724555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230524605041946655144966073 172893453781459991358724555)
            ·
              refine ⟨259340180672189987038086833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172893453781459991358724555 259340180672189987038086833)
              ·
                refine ⟨194505135504142490278565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259340180672189987038086833 194505135504142490278565125)
                ·
                  refine ⟨36469712907026716927230961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194505135504142490278565125 36469712907026716927230961)
                  ·
                    refine ⟨27352284680270037695423221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36469712907026716927230961 27352284680270037695423221)
                    ·
                      refine ⟨2564276688775316033945927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27352284680270037695423221 2564276688775316033945927)
                      ·
                        rfl

theorem cell23_4993911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_4993911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993911 prefixEnd_4993911 := by exact prefixLift 4993911
  have htrace : WordTrace (prefixWord ++ tailWord_4993911) baseStart_4993911 baseEnd_4993911 := by
    simpa [prefixWord, tailWord_4993911, baseEnd_4993911] using wordTrace_append hprefix tailTrace_4993911
  have hstable : (prefixWord ++ tailWord_4993911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993911).length < 2 ^ (prefixWord ++ tailWord_4993911).sum := by decide
  have hdescent : baseEnd_4993911 < baseStart_4993911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993915 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 3]
def baseStart_4993915 : Nat := 118140960795 + 4993915 * 2 ^ 59
def prefixEnd_4993915 : Nat := 4983230072969 + 3 ^ 40 * 4993915 * 2
def baseEnd_4993915 : Nat := 2564278742697934018295909

theorem tailTrace_4993915 : CollatzResearch.WordTrace tailWord_4993915 prefixEnd_4993915 2564278742697934018295909 := by
  unfold tailWord_4993915
  simp only [CollatzResearch.WordTrace]
  refine ⟨182143043702906322624847199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121428695801937548416564799 182143043702906322624847199)
  ·
    refine ⟨273214565554359483937270799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182143043702906322624847199 273214565554359483937270799)
    ·
      refine ⟨409821848331539225905906199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273214565554359483937270799 409821848331539225905906199)
      ·
        refine ⟨614732772497308838858859299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409821848331539225905906199 614732772497308838858859299)
        ·
          refine ⟨922099158745963258288288949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614732772497308838858859299 922099158745963258288288949)
          ·
            refine ⟨86446796132434055464527089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 922099158745963258288288949 86446796132434055464527089)
            ·
              refine ⟨64835097099325541598395317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86446796132434055464527089 64835097099325541598395317)
              ·
                refine ⟨6078290353061769524849561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64835097099325541598395317 6078290353061769524849561)
                ·
                  refine ⟨4558717764796327143637171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078290353061769524849561 4558717764796327143637171)
                  ·
                    refine ⟨6838076647194490715455757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558717764796327143637171 6838076647194490715455757)
                    ·
                      refine ⟨2564278742697934018295909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838076647194490715455757 2564278742697934018295909)
                      ·
                        rfl

theorem cell23_4993915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 3].length) (baseStart_4993915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993915 prefixEnd_4993915 := by exact prefixLift 4993915
  have htrace : WordTrace (prefixWord ++ tailWord_4993915) baseStart_4993915 baseEnd_4993915 := by
    simpa [prefixWord, tailWord_4993915, baseEnd_4993915] using wordTrace_append hprefix tailTrace_4993915
  have hstable : (prefixWord ++ tailWord_4993915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993915).length < 2 ^ (prefixWord ++ tailWord_4993915).sum := by decide
  have hdescent : baseEnd_4993915 < baseStart_4993915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993922 : List Nat := [3, 4, 2, 2, 1, 1, 1, 9]
def baseStart_4993922 : Nat := 118140960795 + 4993922 * 2 ^ 59
def prefixEnd_4993922 : Nat := 4983230072969 + 3 ^ 40 * 4993922 * 2
def baseEnd_4993922 : Nat := 94973419891204277441051

theorem tailTrace_4993922 : CollatzResearch.WordTrace tailWord_4993922 prefixEnd_4993922 94973419891204277441051 := by
  unfold tailWord_4993922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45535824753470240705088005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121428866009253975213568013 45535824753470240705088005)
  ·
    refine ⟨8537967141275670132204001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45535824753470240705088005 8537967141275670132204001)
    ·
      refine ⟨6403475355956752599153001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8537967141275670132204001 6403475355956752599153001)
      ·
        refine ⟨4802606516967564449364751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403475355956752599153001 4802606516967564449364751)
        ·
          refine ⟨7203909775451346674047127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802606516967564449364751 7203909775451346674047127)
          ·
            refine ⟨10805864663177020011070691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203909775451346674047127 10805864663177020011070691)
            ·
              refine ⟨16208796994765530016606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10805864663177020011070691 16208796994765530016606037)
              ·
                refine ⟨94973419891204277441051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16208796994765530016606037 94973419891204277441051)
                ·
                  rfl

theorem cell23_4993922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_4993922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993922 prefixEnd_4993922 := by exact prefixLift 4993922
  have htrace : WordTrace (prefixWord ++ tailWord_4993922) baseStart_4993922 baseEnd_4993922 := by
    simpa [prefixWord, tailWord_4993922, baseEnd_4993922] using wordTrace_append hprefix tailTrace_4993922
  have hstable : (prefixWord ++ tailWord_4993922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993922).length < 2 ^ (prefixWord ++ tailWord_4993922).sum := by decide
  have hdescent : baseEnd_4993922 < baseStart_4993922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993928 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4993928 : Nat := 118140960795 + 4993928 * 2 ^ 59
def prefixEnd_4993928 : Nat := 4983230072969 + 3 ^ 40 * 4993928 * 2
def baseEnd_4993928 : Nat := 2564285417946442467433349

theorem tailTrace_4993928 : CollatzResearch.WordTrace tailWord_4993928 prefixEnd_4993928 2564285417946442467433349 := by
  unfold tailWord_4993928
  simp only [CollatzResearch.WordTrace]
  refine ⟨91071758925929612922535219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121429011901239483896713625 91071758925929612922535219)
  ·
    refine ⟨136607638388894419383802829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91071758925929612922535219 136607638388894419383802829)
    ·
      refine ⟨51227864395835407268926061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136607638388894419383802829 51227864395835407268926061)
      ·
        refine ⟨19210449148438277725847273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51227864395835407268926061 19210449148438277725847273)
        ·
          refine ⟨14407836861328708294385455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19210449148438277725847273 14407836861328708294385455)
          ·
            refine ⟨21611755291993062441578183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407836861328708294385455 21611755291993062441578183)
            ·
              refine ⟨32417632937989593662367275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21611755291993062441578183 32417632937989593662367275)
              ·
                refine ⟨48626449406984390493550913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32417632937989593662367275 48626449406984390493550913)
                ·
                  refine ⟨36469837055238292870163185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48626449406984390493550913 36469837055238292870163185)
                  ·
                    refine ⟨27352377791428719652622389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36469837055238292870163185 27352377791428719652622389)
                    ·
                      refine ⟨2564285417946442467433349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27352377791428719652622389 2564285417946442467433349)
                      ·
                        rfl

theorem cell23_4993928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4993928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993928 prefixEnd_4993928 := by exact prefixLift 4993928
  have htrace : WordTrace (prefixWord ++ tailWord_4993928) baseStart_4993928 baseEnd_4993928 := by
    simpa [prefixWord, tailWord_4993928, baseEnd_4993928] using wordTrace_append hprefix tailTrace_4993928
  have hstable : (prefixWord ++ tailWord_4993928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993928).length < 2 ^ (prefixWord ++ tailWord_4993928).sum := by decide
  have hdescent : baseEnd_4993928 < baseStart_4993928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4993931 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 8]
def baseStart_4993931 : Nat := 118140960795 + 4993931 * 2 ^ 59
def prefixEnd_4993931 : Nat := 4983230072969 + 3 ^ 40 * 4993931 * 2
def baseEnd_4993931 : Nat := 854762319462801985231945

theorem tailTrace_4993931 : CollatzResearch.WordTrace tailWord_4993931 prefixEnd_4993931 854762319462801985231945 := by
  unfold tailWord_4993931
  simp only [CollatzResearch.WordTrace]
  refine ⟨182143627270848357357429647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121429084847232238238286431 182143627270848357357429647)
  ·
    refine ⟨273215440906272536036144471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182143627270848357357429647 273215440906272536036144471)
    ·
      refine ⟨409823161359408804054216707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273215440906272536036144471 409823161359408804054216707)
      ·
        refine ⟨614734742039113206081325061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409823161359408804054216707 614734742039113206081325061)
        ·
          refine ⟨115262764132333726140248449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614734742039113206081325061 115262764132333726140248449)
          ·
            refine ⟨86447073099250294605186337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115262764132333726140248449 86447073099250294605186337)
            ·
              refine ⟨64835304824437720953889753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86447073099250294605186337 64835304824437720953889753)
              ·
                refine ⟨48626478618328290715417315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64835304824437720953889753 48626478618328290715417315)
                ·
                  refine ⟨72939717927492436073125973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48626478618328290715417315 72939717927492436073125973)
                  ·
                    refine ⟨854762319462801985231945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72939717927492436073125973 854762319462801985231945)
                    ·
                      rfl

theorem cell23_4993931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_4993931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4993931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4993931 prefixEnd_4993931 := by exact prefixLift 4993931
  have htrace : WordTrace (prefixWord ++ tailWord_4993931) baseStart_4993931 baseEnd_4993931 := by
    simpa [prefixWord, tailWord_4993931, baseEnd_4993931] using wordTrace_append hprefix tailTrace_4993931
  have hstable : (prefixWord ++ tailWord_4993931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4993931).length < 2 ^ (prefixWord ++ tailWord_4993931).sum := by decide
  have hdescent : baseEnd_4993931 < baseStart_4993931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4993931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994006 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4994006 : Nat := 118140960795 + 4994006 * 2 ^ 59
def prefixEnd_4994006 : Nat := 4983230072969 + 3 ^ 40 * 4994006 * 2
def baseEnd_4994006 : Nat := 2564325469437493162257991

theorem tailTrace_4994006 : CollatzResearch.WordTrace tailWord_4994006 prefixEnd_4994006 2564325469437493162257991 := by
  unfold tailWord_4994006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384147671598540322900617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121430908497051096777606581 11384147671598540322900617)
  ·
    refine ⟨8538110753698905242175463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11384147671598540322900617 8538110753698905242175463)
    ·
      refine ⟨12807166130548357863263195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8538110753698905242175463 12807166130548357863263195)
      ·
        refine ⟨19210749195822536794894793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12807166130548357863263195 19210749195822536794894793)
        ·
          refine ⟨14408061896866902596171095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19210749195822536794894793 14408061896866902596171095)
          ·
            refine ⟨21612092845300353894256643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14408061896866902596171095 21612092845300353894256643)
            ·
              refine ⟨32418139267950530841384965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21612092845300353894256643 32418139267950530841384965)
              ·
                refine ⟨6078401112740724532759681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32418139267950530841384965 6078401112740724532759681)
                ·
                  refine ⟨4558800834555543399569761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078401112740724532759681 4558800834555543399569761)
                  ·
                    refine ⟨3419100625916657549677321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558800834555543399569761 3419100625916657549677321)
                    ·
                      refine ⟨2564325469437493162257991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419100625916657549677321 2564325469437493162257991)
                      ·
                        rfl

theorem cell23_4994006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4994006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994006 prefixEnd_4994006 := by exact prefixLift 4994006
  have htrace : WordTrace (prefixWord ++ tailWord_4994006) baseStart_4994006 baseEnd_4994006 := by
    simpa [prefixWord, tailWord_4994006, baseEnd_4994006] using wordTrace_append hprefix tailTrace_4994006
  have hstable : (prefixWord ++ tailWord_4994006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994006).length < 2 ^ (prefixWord ++ tailWord_4994006).sum := by decide
  have hdescent : baseEnd_4994006 < baseStart_4994006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994045 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_4994045 : Nat := 118140960795 + 4994045 * 2 ^ 59
def prefixEnd_4994045 : Nat := 4983230072969 + 3 ^ 40 * 4994045 * 2
def baseEnd_4994045 : Nat := 2564345495183018509670311

theorem tailTrace_4994045 : CollatzResearch.WordTrace tailWord_4994045 prefixEnd_4994045 2564345495183018509670311 := by
  unfold tailWord_4994045
  simp only [CollatzResearch.WordTrace]
  refine ⟨182147785192435354827079589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121431856794956903218053059 182147785192435354827079589)
  ·
    refine ⟨34152709723581629030077423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182147785192435354827079589 34152709723581629030077423)
    ·
      refine ⟨51229064585372443545116135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34152709723581629030077423 51229064585372443545116135)
      ·
        refine ⟨76843596878058665317674203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51229064585372443545116135 76843596878058665317674203)
        ·
          refine ⟨115265395317087997976511305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76843596878058665317674203 115265395317087997976511305)
          ·
            refine ⟨86449046487815998482383479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115265395317087997976511305 86449046487815998482383479)
            ·
              refine ⟨129673569731723997723575219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86449046487815998482383479 129673569731723997723575219)
              ·
                refine ⟨194510354597585996585362829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129673569731723997723575219 194510354597585996585362829)
                ·
                  refine ⟨72941382974094748719511061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194510354597585996585362829 72941382974094748719511061)
                  ·
                    refine ⟨3419127326910691346227081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72941382974094748719511061 3419127326910691346227081)
                    ·
                      refine ⟨2564345495183018509670311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419127326910691346227081 2564345495183018509670311)
                      ·
                        rfl

theorem cell23_4994045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_4994045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994045 prefixEnd_4994045 := by exact prefixLift 4994045
  have htrace : WordTrace (prefixWord ++ tailWord_4994045) baseStart_4994045 baseEnd_4994045 := by
    simpa [prefixWord, tailWord_4994045, baseEnd_4994045] using wordTrace_append hprefix tailTrace_4994045
  have hstable : (prefixWord ++ tailWord_4994045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994045).length < 2 ^ (prefixWord ++ tailWord_4994045).sum := by decide
  have hdescent : baseEnd_4994045 < baseStart_4994045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994055 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 5, 4]
def baseStart_4994055 : Nat := 118140960795 + 4994055 * 2 ^ 59
def prefixEnd_4994055 : Nat := 4983230072969 + 3 ^ 40 * 4994055 * 2
def baseEnd_4994055 : Nat := 854783543329854490181755

theorem tailTrace_4994055 : CollatzResearch.WordTrace tailWord_4994055 prefixEnd_4994055 854783543329854490181755 := by
  unfold tailWord_4994055
  simp only [CollatzResearch.WordTrace]
  refine ⟨182148149922399126534943619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121432099948266084356629079 182148149922399126534943619)
  ·
    refine ⟨273222224883598689802415429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182148149922399126534943619 273222224883598689802415429)
    ·
      refine ⟨51229167165674754337952893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273222224883598689802415429 51229167165674754337952893)
      ·
        refine ⟨19210937687128032876732335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51229167165674754337952893 19210937687128032876732335)
        ·
          refine ⟨28816406530692049315098503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19210937687128032876732335 28816406530692049315098503)
          ·
            refine ⟨43224609796038073972647755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28816406530692049315098503 43224609796038073972647755)
            ·
              refine ⟨64836914694057110958971633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43224609796038073972647755 64836914694057110958971633)
              ·
                refine ⟨48627686020542833219228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64836914694057110958971633 48627686020542833219228725)
                ·
                  refine ⟨4558845564425890614302693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48627686020542833219228725 4558845564425890614302693)
                  ·
                    refine ⟨854783543329854490181755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558845564425890614302693 854783543329854490181755)
                    ·
                      rfl

theorem cell23_4994055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_4994055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994055 prefixEnd_4994055 := by exact prefixLift 4994055
  have htrace : WordTrace (prefixWord ++ tailWord_4994055) baseStart_4994055 baseEnd_4994055 := by
    simpa [prefixWord, tailWord_4994055, baseEnd_4994055] using wordTrace_append hprefix tailTrace_4994055
  have hstable : (prefixWord ++ tailWord_4994055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994055).length < 2 ^ (prefixWord ++ tailWord_4994055).sum := by decide
  have hdescent : baseEnd_4994055 < baseStart_4994055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994062 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4994062 : Nat := 118140960795 + 4994062 * 2 ^ 59
def prefixEnd_4994062 : Nat := 4983230072969 + 3 ^ 40 * 4994062 * 2
def baseEnd_4994062 : Nat := 2564354224354144943157733

theorem tailTrace_4994062 : CollatzResearch.WordTrace tailWord_4994062 prefixEnd_4994062 2564354224354144943157733 := by
  unfold tailWord_4994062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768550654171720841306055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121432270155582511153632293 22768550654171720841306055)
  ·
    refine ⟨34152825981257581261959083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22768550654171720841306055 34152825981257581261959083)
    ·
      refine ⟨51229238971886371892938625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34152825981257581261959083 51229238971886371892938625)
      ·
        refine ⟨38421929228914778919703969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51229238971886371892938625 38421929228914778919703969)
        ·
          refine ⟨28816446921686084189777977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38421929228914778919703969 28816446921686084189777977)
          ·
            refine ⟨21612335191264563142333483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28816446921686084189777977 21612335191264563142333483)
            ·
              refine ⟨32418502786896844713500225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21612335191264563142333483 32418502786896844713500225)
              ·
                refine ⟨24313877090172633535125169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32418502786896844713500225 24313877090172633535125169)
                ·
                  refine ⟨18235407817629475151343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24313877090172633535125169 18235407817629475151343877)
                  ·
                    refine ⟨3419138965805526590876977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18235407817629475151343877 3419138965805526590876977)
                    ·
                      refine ⟨2564354224354144943157733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419138965805526590876977 2564354224354144943157733)
                      ·
                        rfl

theorem cell23_4994062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4994062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994062 prefixEnd_4994062 := by exact prefixLift 4994062
  have htrace : WordTrace (prefixWord ++ tailWord_4994062) baseStart_4994062 baseEnd_4994062 := by
    simpa [prefixWord, tailWord_4994062, baseEnd_4994062] using wordTrace_append hprefix tailTrace_4994062
  have hstable : (prefixWord ++ tailWord_4994062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994062).length < 2 ^ (prefixWord ++ tailWord_4994062).sum := by decide
  have hdescent : baseEnd_4994062 < baseStart_4994062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_4994065 : Nat := 118140960795 + 4994065 * 2 ^ 59
def prefixEnd_4994065 : Nat := 4983230072969 + 3 ^ 40 * 4994065 * 2
def baseEnd_4994065 : Nat := 2564355764796108431420219

theorem tailTrace_4994065 : CollatzResearch.WordTrace tailWord_4994065 prefixEnd_4994065 2564355764796108431420219 := by
  unfold tailWord_4994065
  simp only [CollatzResearch.WordTrace]
  refine ⟨182148514652362898242807649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121432343101575265495205099 182148514652362898242807649)
  ·
    refine ⟨136611385989272173682105737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182148514652362898242807649 136611385989272173682105737)
    ·
      refine ⟨102458539491954130261579303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136611385989272173682105737 102458539491954130261579303)
      ·
        refine ⟨153687809237931195392368955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102458539491954130261579303 153687809237931195392368955)
        ·
          refine ⟨230531713856896793088553433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153687809237931195392368955 230531713856896793088553433)
          ·
            refine ⟨172898785392672594816415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230531713856896793088553433 172898785392672594816415075)
            ·
              refine ⟨259348178089008892224622613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172898785392672594816415075 259348178089008892224622613)
              ·
                refine ⟨12156945847922291823029185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259348178089008892224622613 12156945847922291823029185)
                ·
                  refine ⟨9117709385941718867271889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12156945847922291823029185 9117709385941718867271889)
                  ·
                    refine ⟨6838282039456289150453917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9117709385941718867271889 6838282039456289150453917)
                    ·
                      refine ⟨2564355764796108431420219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838282039456289150453917 2564355764796108431420219)
                      ·
                        rfl

theorem cell23_4994065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_4994065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994065 prefixEnd_4994065 := by exact prefixLift 4994065
  have htrace : WordTrace (prefixWord ++ tailWord_4994065) baseStart_4994065 baseEnd_4994065 := by
    simpa [prefixWord, tailWord_4994065, baseEnd_4994065] using wordTrace_append hprefix tailTrace_4994065
  have hstable : (prefixWord ++ tailWord_4994065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994065).length < 2 ^ (prefixWord ++ tailWord_4994065).sum := by decide
  have hdescent : baseEnd_4994065 < baseStart_4994065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994072 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_4994072 : Nat := 118140960795 + 4994072 * 2 ^ 59
def prefixEnd_4994072 : Nat := 4983230072969 + 3 ^ 40 * 4994072 * 2
def baseEnd_4994072 : Nat := 854786453053563301344229

theorem tailTrace_4994072 : CollatzResearch.WordTrace tailWord_4994072 prefixEnd_4994072 854786453053563301344229 := by
  unfold tailWord_4994072
  simp only [CollatzResearch.WordTrace]
  refine ⟨91074384981668769219156235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121432513308891692292208313 91074384981668769219156235)
  ·
    refine ⟨136611577472503153828734353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91074384981668769219156235 136611577472503153828734353)
    ·
      refine ⟨102458683104377365371550765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136611577472503153828734353 102458683104377365371550765)
      ·
        refine ⟨38422006164141512014331537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102458683104377365371550765 38422006164141512014331537)
        ·
          refine ⟨28816504623106134010748653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38422006164141512014331537 28816504623106134010748653)
          ·
            refine ⟨10806189233664800254030745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28816504623106134010748653 10806189233664800254030745)
            ·
              refine ⟨8104641925248600190523059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10806189233664800254030745 8104641925248600190523059)
              ·
                refine ⟨12156962887872900285784589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8104641925248600190523059 12156962887872900285784589)
                ·
                  refine ⟨4558861082952337607169221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12156962887872900285784589 4558861082952337607169221)
                  ·
                    refine ⟨854786453053563301344229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558861082952337607169221 854786453053563301344229)
                    ·
                      rfl

theorem cell23_4994072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_4994072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994072 prefixEnd_4994072 := by exact prefixLift 4994072
  have htrace : WordTrace (prefixWord ++ tailWord_4994072) baseStart_4994072 baseEnd_4994072 := by
    simpa [prefixWord, tailWord_4994072, baseEnd_4994072] using wordTrace_append hprefix tailTrace_4994072
  have hstable : (prefixWord ++ tailWord_4994072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994072).length < 2 ^ (prefixWord ++ tailWord_4994072).sum := by decide
  have hdescent : baseEnd_4994072 < baseStart_4994072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994115 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 1, 5]
def baseStart_4994115 : Nat := 118140960795 + 4994115 * 2 ^ 59
def prefixEnd_4994115 : Nat := 4983230072969 + 3 ^ 40 * 4994115 * 2
def baseEnd_4994115 : Nat := 854793812942944411931663

theorem tailTrace_4994115 : CollatzResearch.WordTrace tailWord_4994115 prefixEnd_4994115 854793812942944411931663 := by
  unfold tailWord_4994115
  simp only [CollatzResearch.WordTrace]
  refine ⟨182150338302181756782127799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121433558868121171188085199 182150338302181756782127799)
  ·
    refine ⟨273225507453272635173191699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182150338302181756782127799 273225507453272635173191699)
    ·
      refine ⟨409838261179908952759787549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273225507453272635173191699 409838261179908952759787549)
      ·
        refine ⟨153689347942465857284920331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409838261179908952759787549 153689347942465857284920331)
        ·
          refine ⟨230534021913698785927380497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153689347942465857284920331 230534021913698785927380497)
          ·
            refine ⟨172900516435274089445535373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230534021913698785927380497 172900516435274089445535373)
            ·
              refine ⟨64837693663227783542075765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172900516435274089445535373 64837693663227783542075765)
              ·
                refine ⟨6078533780927604707069603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64837693663227783542075765 6078533780927604707069603)
                ·
                  refine ⟨9117800671391407060604405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6078533780927604707069603 9117800671391407060604405)
                  ·
                    refine ⟨854793812942944411931663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9117800671391407060604405 854793812942944411931663)
                    ·
                      rfl

theorem cell23_4994115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 5].length) (baseStart_4994115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994115 prefixEnd_4994115 := by exact prefixLift 4994115
  have htrace : WordTrace (prefixWord ++ tailWord_4994115) baseStart_4994115 baseEnd_4994115 := by
    simpa [prefixWord, tailWord_4994115, baseEnd_4994115] using wordTrace_append hprefix tailTrace_4994115
  have hstable : (prefixWord ++ tailWord_4994115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994115).length < 2 ^ (prefixWord ++ tailWord_4994115).sum := by decide
  have hdescent : baseEnd_4994115 < baseStart_4994115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994122 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_4994122 : Nat := 118140960795 + 4994122 * 2 ^ 59
def prefixEnd_4994122 : Nat := 4983230072969 + 3 ^ 40 * 4994122 * 2
def baseEnd_4994122 : Nat := 2564385033193414708407457

theorem tailTrace_4994122 : CollatzResearch.WordTrace tailWord_4994122 prefixEnd_4994122 2564385033193414708407457 := by
  unfold tailWord_4994122
  simp only [CollatzResearch.WordTrace]
  refine ⟨45537648403289099244408155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121433729075437597985088413 45537648403289099244408155)
  ·
    refine ⟨68306472604933648866612233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45537648403289099244408155 68306472604933648866612233)
    ·
      refine ⟨51229854453700236649959175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68306472604933648866612233 51229854453700236649959175)
      ·
        refine ⟨76844781680550354974938763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51229854453700236649959175 76844781680550354974938763)
        ·
          refine ⟨115267172520825532462408145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76844781680550354974938763 115267172520825532462408145)
          ·
            refine ⟨86450379390619149346806109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115267172520825532462408145 86450379390619149346806109)
            ·
              refine ⟨32418892271482181005052291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86450379390619149346806109 32418892271482181005052291)
              ·
                refine ⟨48628338407223271507578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32418892271482181005052291 48628338407223271507578437)
                ·
                  refine ⟨9117813451354363407670957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48628338407223271507578437 9117813451354363407670957)
                  ·
                    refine ⟨3419180044257886277876609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9117813451354363407670957 3419180044257886277876609)
                    ·
                      refine ⟨2564385033193414708407457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419180044257886277876609 2564385033193414708407457)
                      ·
                        rfl

theorem cell23_4994122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_4994122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994122 prefixEnd_4994122 := by exact prefixLift 4994122
  have htrace : WordTrace (prefixWord ++ tailWord_4994122) baseStart_4994122 baseEnd_4994122 := by
    simpa [prefixWord, tailWord_4994122, baseEnd_4994122] using wordTrace_append hprefix tailTrace_4994122
  have hstable : (prefixWord ++ tailWord_4994122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994122).length < 2 ^ (prefixWord ++ tailWord_4994122).sum := by decide
  have hdescent : baseEnd_4994122 < baseStart_4994122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994129 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_4994129 : Nat := 118140960795 + 4994129 * 2 ^ 59
def prefixEnd_4994129 : Nat := 4983230072969 + 3 ^ 40 * 4994129 * 2
def baseEnd_4994129 : Nat := 2564388627557996181019925

theorem tailTrace_4994129 : CollatzResearch.WordTrace tailWord_4994129 prefixEnd_4994129 2564388627557996181019925 := by
  unfold tailWord_4994129
  simp only [CollatzResearch.WordTrace]
  refine ⟨182150848924131037173137441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121433899282754024782091627 182150848924131037173137441)
  ·
    refine ⟨136613136693098277879853081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182150848924131037173137441 136613136693098277879853081)
    ·
      refine ⟨102459852519823708409889811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136613136693098277879853081 102459852519823708409889811)
      ·
        refine ⟨153689778779735562614834717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102459852519823708409889811 153689778779735562614834717)
        ·
          refine ⟨57633667042400835980563019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153689778779735562614834717 57633667042400835980563019)
          ·
            refine ⟨86450500563601253970844529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57633667042400835980563019 86450500563601253970844529)
            ·
              refine ⟨64837875422700940478133397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86450500563601253970844529 64837875422700940478133397)
              ·
                refine ⟨3039275410439106584912503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64837875422700940478133397 3039275410439106584912503)
                ·
                  refine ⟨4558913115658659877368755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039275410439106584912503 4558913115658659877368755)
                  ·
                    refine ⟨6838369673487989816053133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558913115658659877368755 6838369673487989816053133)
                    ·
                      refine ⟨2564388627557996181019925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838369673487989816053133 2564388627557996181019925)
                      ·
                        rfl

theorem cell23_4994129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_4994129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994129 prefixEnd_4994129 := by exact prefixLift 4994129
  have htrace : WordTrace (prefixWord ++ tailWord_4994129) baseStart_4994129 baseEnd_4994129 := by
    simpa [prefixWord, tailWord_4994129, baseEnd_4994129] using wordTrace_append hprefix tailTrace_4994129
  have hstable : (prefixWord ++ tailWord_4994129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994129).length < 2 ^ (prefixWord ++ tailWord_4994129).sum := by decide
  have hdescent : baseEnd_4994129 < baseStart_4994129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994135 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4994135 : Nat := 118140960795 + 4994135 * 2 ^ 59
def prefixEnd_4994135 : Nat := 4983230072969 + 3 ^ 40 * 4994135 * 2
def baseEnd_4994135 : Nat := 2564391708441923157544897

theorem tailTrace_4994135 : CollatzResearch.WordTrace tailWord_4994135 prefixEnd_4994135 2564391708441923157544897 := by
  unfold tailWord_4994135
  simp only [CollatzResearch.WordTrace]
  refine ⟨182151067762109300197855859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121434045174739533465237239 182151067762109300197855859)
  ·
    refine ⟨273226601643163950296783789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182151067762109300197855859 273226601643163950296783789)
    ·
      refine ⟨102459975616186481361293921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273226601643163950296783789 102459975616186481361293921)
      ·
        refine ⟨76844981712139861020970441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102459975616186481361293921 76844981712139861020970441)
        ·
          refine ⟨57633736284104895765727831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76844981712139861020970441 57633736284104895765727831)
          ·
            refine ⟨86450604426157343648591747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57633736284104895765727831 86450604426157343648591747)
            ·
              refine ⟨129675906639236015472887621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86450604426157343648591747 129675906639236015472887621)
              ·
                refine ⟨24314232494856752901166429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129675906639236015472887621 24314232494856752901166429)
                ·
                  refine ⟨9117837185571282337937411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24314232494856752901166429 9117837185571282337937411)
                  ·
                    refine ⟨13676755778356923506906117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9117837185571282337937411 13676755778356923506906117)
                    ·
                      refine ⟨2564391708441923157544897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13676755778356923506906117 2564391708441923157544897)
                      ·
                        rfl

theorem cell23_4994135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4994135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994135 prefixEnd_4994135 := by exact prefixLift 4994135
  have htrace : WordTrace (prefixWord ++ tailWord_4994135) baseStart_4994135 baseEnd_4994135 := by
    simpa [prefixWord, tailWord_4994135, baseEnd_4994135] using wordTrace_append hprefix tailTrace_4994135
  have hstable : (prefixWord ++ tailWord_4994135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994135).length < 2 ^ (prefixWord ++ tailWord_4994135).sum := by decide
  have hdescent : baseEnd_4994135 < baseStart_4994135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994174 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4994174 : Nat := 118140960795 + 4994174 * 2 ^ 59
def prefixEnd_4994174 : Nat := 4983230072969 + 3 ^ 40 * 4994174 * 2
def baseEnd_4994174 : Nat := 854803911395816168319073

theorem tailTrace_4994174 : CollatzResearch.WordTrace tailWord_4994174 prefixEnd_4994174 854803911395816168319073 := by
  unfold tailWord_4994174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22769061276121001232315697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121434993472645339905683717 22769061276121001232315697)
  ·
    refine ⟨17076795957090750924236773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22769061276121001232315697 17076795957090750924236773)
    ·
      refine ⟨3201899241954515798294395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17076795957090750924236773 3201899241954515798294395)
      ·
        refine ⟨4802848862931773697441593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201899241954515798294395 4802848862931773697441593)
        ·
          refine ⟨3602136647198830273081195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4802848862931773697441593 3602136647198830273081195)
          ·
            refine ⟨5403204970798245409621793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602136647198830273081195 5403204970798245409621793)
            ·
              refine ⟨4052403728098684057216345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403204970798245409621793 4052403728098684057216345)
              ·
                refine ⟨3039302796074013042912259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052403728098684057216345 3039302796074013042912259)
                ·
                  refine ⟨4558954194111019564368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039302796074013042912259 4558954194111019564368389)
                  ·
                    refine ⟨854803911395816168319073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558954194111019564368389 854803911395816168319073)
                    ·
                      rfl

theorem cell23_4994174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4994174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994174 prefixEnd_4994174 := by exact prefixLift 4994174
  have htrace : WordTrace (prefixWord ++ tailWord_4994174) baseStart_4994174 baseEnd_4994174 := by
    simpa [prefixWord, tailWord_4994174, baseEnd_4994174] using wordTrace_append hprefix tailTrace_4994174
  have hstable : (prefixWord ++ tailWord_4994174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994174).length < 2 ^ (prefixWord ++ tailWord_4994174).sum := by decide
  have hdescent : baseEnd_4994174 < baseStart_4994174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994205 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4994205 : Nat := 118140960795 + 4994205 * 2 ^ 59
def prefixEnd_4994205 : Nat := 4983230072969 + 3 ^ 40 * 4994205 * 2
def baseEnd_4994205 : Nat := 854809217362579294556525

theorem tailTrace_4994205 : CollatzResearch.WordTrace tailWord_4994205 prefixEnd_4994205 854809217362579294556525 := by
  unfold tailWord_4994205
  simp only [CollatzResearch.WordTrace]
  refine ⟨182153620871855702152904069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121435747247903801435269379 182153620871855702152904069)
  ·
    refine ⟨34153803913472944153669513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182153620871855702152904069 34153803913472944153669513)
    ·
      refine ⟨25615352935104708115252135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34153803913472944153669513 25615352935104708115252135)
      ·
        refine ⟨38423029402657062172878203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25615352935104708115252135 38423029402657062172878203)
        ·
          refine ⟨57634544103985593259317305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38423029402657062172878203 57634544103985593259317305)
          ·
            refine ⟨43225908077989194944487979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57634544103985593259317305 43225908077989194944487979)
            ·
              refine ⟨64838862116983792416731969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43225908077989194944487979 64838862116983792416731969)
              ·
                refine ⟨48629146587737844312548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64838862116983792416731969 48629146587737844312548977)
                ·
                  refine ⟨36471859940803383234411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48629146587737844312548977 36471859940803383234411733)
                  ·
                    refine ⟨854809217362579294556525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36471859940803383234411733 854809217362579294556525)
                    ·
                      rfl

theorem cell23_4994205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4994205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994205 prefixEnd_4994205 := by exact prefixLift 4994205
  have htrace : WordTrace (prefixWord ++ tailWord_4994205) baseStart_4994205 baseEnd_4994205 := by
    simpa [prefixWord, tailWord_4994205, baseEnd_4994205] using wordTrace_append hprefix tailTrace_4994205
  have hstable : (prefixWord ++ tailWord_4994205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994205).length < 2 ^ (prefixWord ++ tailWord_4994205).sum := by decide
  have hdescent : baseEnd_4994205 < baseStart_4994205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994230 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4994230 : Nat := 118140960795 + 4994230 * 2 ^ 59
def prefixEnd_4994230 : Nat := 4983230072969 + 3 ^ 40 * 4994230 * 2
def baseEnd_4994230 : Nat := 854813496368033428618987

theorem tailTrace_4994230 : CollatzResearch.WordTrace tailWord_4994230 prefixEnd_4994230 854813496368033428618987 := by
  unfold tailWord_4994230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384658293547820713910259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121436355131176754281709429 11384658293547820713910259)
  ·
    refine ⟨17076987440321731070865389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11384658293547820713910259 17076987440321731070865389)
    ·
      refine ⟨6403870290120649151574521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17076987440321731070865389 6403870290120649151574521)
      ·
        refine ⟨4802902717590486863680891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403870290120649151574521 4802902717590486863680891)
        ·
          refine ⟨7204354076385730295521337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802902717590486863680891 7204354076385730295521337)
          ·
            refine ⟨5403265557289297721641003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7204354076385730295521337 5403265557289297721641003)
            ·
              refine ⟨8104898335933946582461505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403265557289297721641003 8104898335933946582461505)
              ·
                refine ⟨6078673751950459936846129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8104898335933946582461505 6078673751950459936846129)
                ·
                  refine ⟨4559005313962844952634597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078673751950459936846129 4559005313962844952634597)
                  ·
                    refine ⟨854813496368033428618987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559005313962844952634597 854813496368033428618987)
                    ·
                      rfl

theorem cell23_4994230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4994230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994230 prefixEnd_4994230 := by exact prefixLift 4994230
  have htrace : WordTrace (prefixWord ++ tailWord_4994230) baseStart_4994230 baseEnd_4994230 := by
    simpa [prefixWord, tailWord_4994230, baseEnd_4994230] using wordTrace_append hprefix tailTrace_4994230
  have hstable : (prefixWord ++ tailWord_4994230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994230).length < 2 ^ (prefixWord ++ tailWord_4994230).sum := by decide
  have hdescent : baseEnd_4994230 < baseStart_4994230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994236 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4994236 : Nat := 118140960795 + 4994236 * 2 ^ 59
def prefixEnd_4994236 : Nat := 4983230072969 + 3 ^ 40 * 4994236 * 2
def baseEnd_4994236 : Nat := 2564443569988027262381933

theorem tailTrace_4994236 : CollatzResearch.WordTrace tailWord_4994236 prefixEnd_4994236 2564443569988027262381933 := by
  unfold tailWord_4994236
  simp only [CollatzResearch.WordTrace]
  refine ⟨91077375767371697223641281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121436501023162262964855041 91077375767371697223641281)
  ·
    refine ⟨68308031825528772917730961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91077375767371697223641281 68308031825528772917730961)
    ·
      refine ⟨51231023869146579688298221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68308031825528772917730961 51231023869146579688298221)
      ·
        refine ⟨19211633950929967383111833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51231023869146579688298221 19211633950929967383111833)
        ·
          refine ⟨14408725463197475537333875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19211633950929967383111833 14408725463197475537333875)
          ·
            refine ⟨21613088194796213306000813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14408725463197475537333875 21613088194796213306000813)
            ·
              refine ⟨8104908073048579989750305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21613088194796213306000813 8104908073048579989750305)
              ·
                refine ⟨6078681054786434992312729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8104908073048579989750305 6078681054786434992312729)
                ·
                  refine ⟨4559010791089826244234547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078681054786434992312729 4559010791089826244234547)
                  ·
                    refine ⟨6838516186634739366351821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559010791089826244234547 6838516186634739366351821)
                    ·
                      refine ⟨2564443569988027262381933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838516186634739366351821 2564443569988027262381933)
                      ·
                        rfl

theorem cell23_4994236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4994236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994236 prefixEnd_4994236 := by exact prefixLift 4994236
  have htrace : WordTrace (prefixWord ++ tailWord_4994236) baseStart_4994236 baseEnd_4994236 := by
    simpa [prefixWord, tailWord_4994236, baseEnd_4994236] using wordTrace_append hprefix tailTrace_4994236
  have hstable : (prefixWord ++ tailWord_4994236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994236).length < 2 ^ (prefixWord ++ tailWord_4994236).sum := by decide
  have hdescent : baseEnd_4994236 < baseStart_4994236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_4994245 : Nat := 118140960795 + 4994245 * 2 ^ 59
def prefixEnd_4994245 : Nat := 4983230072969 + 3 ^ 40 * 4994245 * 2
def baseEnd_4994245 : Nat := 2564448191313917727169391

theorem tailTrace_4994245 : CollatzResearch.WordTrace tailWord_4994245 prefixEnd_4994245 2564448191313917727169391 := by
  unfold tailWord_4994245
  simp only [CollatzResearch.WordTrace]
  refine ⟨182155079791710788984360189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121436719861140525989573459 182155079791710788984360189)
  ·
    refine ⟨68308154921891545869135071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182155079791710788984360189 68308154921891545869135071)
    ·
      refine ⟨102462232382837318803702607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68308154921891545869135071 102462232382837318803702607)
      ·
        refine ⟨153693348574255978205553911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102462232382837318803702607 153693348574255978205553911)
        ·
          refine ⟨230540022861383967308330867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153693348574255978205553911 230540022861383967308330867)
          ·
            refine ⟨345810034292075950962496301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230540022861383967308330867 345810034292075950962496301)
            ·
              refine ⟨129678762859528481610936113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345810034292075950962496301 129678762859528481610936113)
              ·
                refine ⟨97259072144646361208202085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129678762859528481610936113 97259072144646361208202085)
                ·
                  refine ⟨18236076027121192726537891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97259072144646361208202085 18236076027121192726537891)
                  ·
                    refine ⟨27354114040681789089806837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18236076027121192726537891 27354114040681789089806837)
                    ·
                      refine ⟨2564448191313917727169391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27354114040681789089806837 2564448191313917727169391)
                      ·
                        rfl

theorem cell23_4994245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_4994245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994245 prefixEnd_4994245 := by exact prefixLift 4994245
  have htrace : WordTrace (prefixWord ++ tailWord_4994245) baseStart_4994245 baseEnd_4994245 := by
    simpa [prefixWord, tailWord_4994245, baseEnd_4994245] using wordTrace_append hprefix tailTrace_4994245
  have hstable : (prefixWord ++ tailWord_4994245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994245).length < 2 ^ (prefixWord ++ tailWord_4994245).sum := by decide
  have hdescent : baseEnd_4994245 < baseStart_4994245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994255 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_4994255 : Nat := 118140960795 + 4994255 * 2 ^ 59
def prefixEnd_4994255 : Nat := 4983230072969 + 3 ^ 40 * 4994255 * 2
def baseEnd_4994255 : Nat := 2564453326120462688044345

theorem tailTrace_4994255 : CollatzResearch.WordTrace tailWord_4994255 prefixEnd_4994255 2564453326120462688044345 := by
  unfold tailWord_4994255
  simp only [CollatzResearch.WordTrace]
  refine ⟨182155444521674560692224219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121436963014449707128149479 182155444521674560692224219)
  ·
    refine ⟨273233166782511841038336329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182155444521674560692224219 273233166782511841038336329)
    ·
      refine ⟨204924875086883880778752247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273233166782511841038336329 204924875086883880778752247)
      ·
        refine ⟨307387312630325821168128371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204924875086883880778752247 307387312630325821168128371)
        ·
          refine ⟨461080968945488731752192557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307387312630325821168128371 461080968945488731752192557)
          ·
            refine ⟨172905363354558274407072209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461080968945488731752192557 172905363354558274407072209)
            ·
              refine ⟨129679022515918705805304157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172905363354558274407072209 129679022515918705805304157)
              ·
                refine ⟨48629633443469514676989059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129679022515918705805304157 48629633443469514676989059)
                ·
                  refine ⟨72944450165204272015483589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48629633443469514676989059 72944450165204272015483589)
                  ·
                    refine ⟨13677084405975801002903173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72944450165204272015483589 13677084405975801002903173)
                    ·
                      refine ⟨2564453326120462688044345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13677084405975801002903173 2564453326120462688044345)
                      ·
                        rfl

theorem cell23_4994255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_4994255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994255 prefixEnd_4994255 := by exact prefixLift 4994255
  have htrace : WordTrace (prefixWord ++ tailWord_4994255) baseStart_4994255 baseEnd_4994255 := by
    simpa [prefixWord, tailWord_4994255, baseEnd_4994255] using wordTrace_append hprefix tailTrace_4994255
  have hstable : (prefixWord ++ tailWord_4994255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994255).length < 2 ^ (prefixWord ++ tailWord_4994255).sum := by decide
  have hdescent : baseEnd_4994255 < baseStart_4994255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994279 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4994279 : Nat := 118140960795 + 4994279 * 2 ^ 59
def prefixEnd_4994279 : Nat := 4983230072969 + 3 ^ 40 * 4994279 * 2
def baseEnd_4994279 : Nat := 2564465649656170594144235

theorem tailTrace_4994279 : CollatzResearch.WordTrace tailWord_4994279 prefixEnd_4994279 2564465649656170594144235 := by
  unfold tailWord_4994279
  simp only [CollatzResearch.WordTrace]
  refine ⟨182156319873587612791097891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121437546582391741860731927 182156319873587612791097891)
  ·
    refine ⟨273234479810381419186646837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182156319873587612791097891 273234479810381419186646837)
    ·
      refine ⟨25615732482223258048748141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273234479810381419186646837 25615732482223258048748141)
      ·
        refine ⟨9605899680833721768280553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25615732482223258048748141 9605899680833721768280553)
        ·
          refine ⟨7204424760625291326210415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9605899680833721768280553 7204424760625291326210415)
          ·
            refine ⟨10806637140937936989315623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204424760625291326210415 10806637140937936989315623)
            ·
              refine ⟨16209955711406905483973435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10806637140937936989315623 16209955711406905483973435)
              ·
                refine ⟨24314933567110358225960153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16209955711406905483973435 24314933567110358225960153)
                ·
                  refine ⟨18236200175332768669470115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24314933567110358225960153 18236200175332768669470115)
                  ·
                    refine ⟨27354300262999153004205173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18236200175332768669470115 27354300262999153004205173)
                    ·
                      refine ⟨2564465649656170594144235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27354300262999153004205173 2564465649656170594144235)
                      ·
                        rfl

theorem cell23_4994279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4994279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994279 prefixEnd_4994279 := by exact prefixLift 4994279
  have htrace : WordTrace (prefixWord ++ tailWord_4994279) baseStart_4994279 baseEnd_4994279 := by
    simpa [prefixWord, tailWord_4994279, baseEnd_4994279] using wordTrace_append hprefix tailTrace_4994279
  have hstable : (prefixWord ++ tailWord_4994279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994279).length < 2 ^ (prefixWord ++ tailWord_4994279).sum := by decide
  have hdescent : baseEnd_4994279 < baseStart_4994279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994332 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4994332 : Nat := 118140960795 + 4994332 * 2 ^ 59
def prefixEnd_4994332 : Nat := 4983230072969 + 3 ^ 40 * 4994332 * 2
def baseEnd_4994332 : Nat := 2564492864130858886781491

theorem tailTrace_4994332 : CollatzResearch.WordTrace tailWord_4994332 prefixEnd_4994332 2564492864130858886781491 := by
  unfold tailWord_4994332
  simp only [CollatzResearch.WordTrace]
  refine ⟨91079126471197801421388625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121438835294930401895184833 91079126471197801421388625)
  ·
    refine ⟨68309344853398351066041469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91079126471197801421388625 68309344853398351066041469)
    ·
      refine ⟨25616004320024381649765551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68309344853398351066041469 25616004320024381649765551)
      ·
        refine ⟨38424006480036572474648327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25616004320024381649765551 38424006480036572474648327)
        ·
          refine ⟨57636009720054858711972491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38424006480036572474648327 57636009720054858711972491)
          ·
            refine ⟨86454014580082288067958737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57636009720054858711972491 86454014580082288067958737)
            ·
              refine ⟨64840510935061716050969053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86454014580082288067958737 64840510935061716050969053)
              ·
                refine ⟨24315191600648143519113395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64840510935061716050969053 24315191600648143519113395)
                ·
                  refine ⟨36472787400972215278670093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24315191600648143519113395 36472787400972215278670093)
                  ·
                    refine ⟨13677295275364580729501285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36472787400972215278670093 13677295275364580729501285)
                    ·
                      refine ⟨2564492864130858886781491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13677295275364580729501285 2564492864130858886781491)
                      ·
                        rfl

theorem cell23_4994332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4994332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994332 prefixEnd_4994332 := by exact prefixLift 4994332
  have htrace : WordTrace (prefixWord ++ tailWord_4994332) baseStart_4994332 baseEnd_4994332 := by
    simpa [prefixWord, tailWord_4994332, baseEnd_4994332] using wordTrace_append hprefix tailTrace_4994332
  have hstable : (prefixWord ++ tailWord_4994332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994332).length < 2 ^ (prefixWord ++ tailWord_4994332).sum := by decide
  have hdescent : baseEnd_4994332 < baseStart_4994332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994366 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4994366 : Nat := 118140960795 + 4994366 * 2 ^ 59
def prefixEnd_4994366 : Nat := 4983230072969 + 3 ^ 40 * 4994366 * 2
def baseEnd_4994366 : Nat := 2564510322473111753756335

theorem tailTrace_4994366 : CollatzResearch.WordTrace tailWord_4994366 prefixEnd_4994366 2564510322473111753756335 := by
  unfold tailWord_4994366
  simp only [CollatzResearch.WordTrace]
  refine ⟨22769936628034053331189369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121439662016181617766343301 22769936628034053331189369)
  ·
    refine ⟨17077452471025539998392027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22769936628034053331189369 17077452471025539998392027)
    ·
      refine ⟨25616178706538309997588041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17077452471025539998392027 25616178706538309997588041)
      ·
        refine ⟨19212134029903732498191031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25616178706538309997588041 19212134029903732498191031)
        ·
          refine ⟨28818201044855598747286547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19212134029903732498191031 28818201044855598747286547)
          ·
            refine ⟨43227301567283398120929821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28818201044855598747286547 43227301567283398120929821)
            ·
              refine ⟨16210238087731274295348683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43227301567283398120929821 16210238087731274295348683)
              ·
                refine ⟨24315357131596911443023025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16210238087731274295348683 24315357131596911443023025)
                ·
                  refine ⟨18236517848697683582267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24315357131596911443023025 18236517848697683582267269)
                  ·
                    refine ⟨3419347096630815671675113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18236517848697683582267269 3419347096630815671675113)
                    ·
                      refine ⟨2564510322473111753756335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419347096630815671675113 2564510322473111753756335)
                      ·
                        rfl

theorem cell23_4994366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4994366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994366 prefixEnd_4994366 := by exact prefixLift 4994366
  have htrace : WordTrace (prefixWord ++ tailWord_4994366) baseStart_4994366 baseEnd_4994366 := by
    simpa [prefixWord, tailWord_4994366, baseEnd_4994366] using wordTrace_append hprefix tailTrace_4994366
  have hstable : (prefixWord ++ tailWord_4994366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994366).length < 2 ^ (prefixWord ++ tailWord_4994366).sum := by decide
  have hdescent : baseEnd_4994366 < baseStart_4994366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994399 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_4994399 : Nat := 118140960795 + 4994399 * 2 ^ 59
def prefixEnd_4994399 : Nat := 4983230072969 + 3 ^ 40 * 4994399 * 2
def baseEnd_4994399 : Nat := 2564527267334710124643683

theorem tailTrace_4994399 : CollatzResearch.WordTrace tailWord_4994399 prefixEnd_4994399 2564527267334710124643683 := by
  unfold tailWord_4994399
  simp only [CollatzResearch.WordTrace]
  refine ⟨182160696633152873285466251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121440464422101915523644167 182160696633152873285466251)
  ·
    refine ⟨273241044949729309928199377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182160696633152873285466251 273241044949729309928199377)
    ·
      refine ⟨204930783712296982446149533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273241044949729309928199377 204930783712296982446149533)
      ·
        refine ⟨76849043892111368417306075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204930783712296982446149533 76849043892111368417306075)
        ·
          refine ⟨115273565838167052625959113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76849043892111368417306075 115273565838167052625959113)
          ·
            refine ⟨86455174378625289469469335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115273565838167052625959113 86455174378625289469469335)
            ·
              refine ⟨129682761567937934204204003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86455174378625289469469335 129682761567937934204204003)
              ·
                refine ⟨194524142351906901306306005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129682761567937934204204003 194524142351906901306306005)
                ·
                  refine ⟨4559159586372817999366547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 194524142351906901306306005 4559159586372817999366547)
                  ·
                    refine ⟨6838739379559226999049821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559159586372817999366547 6838739379559226999049821)
                    ·
                      refine ⟨2564527267334710124643683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838739379559226999049821 2564527267334710124643683)
                      ·
                        rfl

theorem cell23_4994399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_4994399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994399 prefixEnd_4994399 := by exact prefixLift 4994399
  have htrace : WordTrace (prefixWord ++ tailWord_4994399) baseStart_4994399 baseEnd_4994399 := by
    simpa [prefixWord, tailWord_4994399, baseEnd_4994399] using wordTrace_append hprefix tailTrace_4994399
  have hstable : (prefixWord ++ tailWord_4994399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994399).length < 2 ^ (prefixWord ++ tailWord_4994399).sum := by decide
  have hdescent : baseEnd_4994399 < baseStart_4994399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994416 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_4994416 : Nat := 118140960795 + 4994416 * 2 ^ 59
def prefixEnd_4994416 : Nat := 4983230072969 + 3 ^ 40 * 4994416 * 2
def baseEnd_4994416 : Nat := 2564535996505836558131105

theorem tailTrace_4994416 : CollatzResearch.WordTrace tailWord_4994416 prefixEnd_4994416 2564535996505836558131105 := by
  unfold tailWord_4994416
  simp only [CollatzResearch.WordTrace]
  refine ⟨91080658337045642594417551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121440877782727523459223401 91080658337045642594417551)
  ·
    refine ⟨136620987505568463891626327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91080658337045642594417551 136620987505568463891626327)
    ·
      refine ⟨204931481258352695837439491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136620987505568463891626327 204931481258352695837439491)
      ·
        refine ⟨307397221887529043756159237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204931481258352695837439491 307397221887529043756159237)
        ·
          refine ⟨57636979103911695704279857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307397221887529043756159237 57636979103911695704279857)
          ·
            refine ⟨43227734327933771778209893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57636979103911695704279857 43227734327933771778209893)
            ·
              refine ⟨8105200186487582208414355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43227734327933771778209893 8105200186487582208414355)
              ·
                refine ⟨12157800279731373312621533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105200186487582208414355 12157800279731373312621533)
                ·
                  refine ⟨4559175104899264992233075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12157800279731373312621533 4559175104899264992233075)
                  ·
                    refine ⟨6838762657348897488349613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559175104899264992233075 6838762657348897488349613)
                    ·
                      refine ⟨2564535996505836558131105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838762657348897488349613 2564535996505836558131105)
                      ·
                        rfl

theorem cell23_4994416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_4994416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994416 prefixEnd_4994416 := by exact prefixLift 4994416
  have htrace : WordTrace (prefixWord ++ tailWord_4994416) baseStart_4994416 baseEnd_4994416 := by
    simpa [prefixWord, tailWord_4994416, baseEnd_4994416] using wordTrace_append hprefix tailTrace_4994416
  have hstable : (prefixWord ++ tailWord_4994416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994416).length < 2 ^ (prefixWord ++ tailWord_4994416).sum := by decide
  have hdescent : baseEnd_4994416 < baseStart_4994416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994436 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4994436 : Nat := 118140960795 + 4994436 * 2 ^ 59
def prefixEnd_4994436 : Nat := 4983230072969 + 3 ^ 40 * 4994436 * 2
def baseEnd_4994436 : Nat := 854848755372975493293671

theorem tailTrace_4994436 : CollatzResearch.WordTrace tailWord_4994436 prefixEnd_4994436 854848755372975493293671 := by
  unfold tailWord_4994436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91081023067009414302281581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121441364089345885736375441 91081023067009414302281581)
  ·
    refine ⟨34155383650128530363355593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91081023067009414302281581 34155383650128530363355593)
    ·
      refine ⟨25616537737596397772516695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34155383650128530363355593 25616537737596397772516695)
      ·
        refine ⟨38424806606394596658775043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25616537737596397772516695 38424806606394596658775043)
        ·
          refine ⟨57637209909591894988162565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38424806606394596658775043 57637209909591894988162565)
          ·
            refine ⟨10806976858048480310280481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57637209909591894988162565 10806976858048480310280481)
            ·
              refine ⟨8105232643536360232710361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10806976858048480310280481 8105232643536360232710361)
              ·
                refine ⟨6078924482652270174532771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8105232643536360232710361 6078924482652270174532771)
                ·
                  refine ⟨9118386723978405261799157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6078924482652270174532771 9118386723978405261799157)
                  ·
                    refine ⟨854848755372975493293671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9118386723978405261799157 854848755372975493293671)
                    ·
                      rfl

theorem cell23_4994436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4994436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994436 prefixEnd_4994436 := by exact prefixLift 4994436
  have htrace : WordTrace (prefixWord ++ tailWord_4994436) baseStart_4994436 baseEnd_4994436 := by
    simpa [prefixWord, tailWord_4994436, baseEnd_4994436] using wordTrace_append hprefix tailTrace_4994436
  have hstable : (prefixWord ++ tailWord_4994436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994436).length < 2 ^ (prefixWord ++ tailWord_4994436).sum := by decide
  have hdescent : baseEnd_4994436 < baseStart_4994436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994460 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4994460 : Nat := 118140960795 + 4994460 * 2 ^ 59
def prefixEnd_4994460 : Nat := 4983230072969 + 3 ^ 40 * 4994460 * 2
def baseEnd_4994460 : Nat := 2564558589654634385980903

theorem tailTrace_4994460 : CollatzResearch.WordTrace tailWord_4994460 prefixEnd_4994460 2564558589654634385980903 := by
  unfold tailWord_4994460
  simp only [CollatzResearch.WordTrace]
  refine ⟨91081460742965940351718417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121441947657287920468957889 91081460742965940351718417)
  ·
    refine ⟨68311095557224455263788813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91081460742965940351718417 68311095557224455263788813)
    ·
      refine ⟨25616660833959170723920805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68311095557224455263788813 25616660833959170723920805)
      ·
        refine ⟨4803123906367344510735151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25616660833959170723920805 4803123906367344510735151)
        ·
          refine ⟨7204685859551016766102727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803123906367344510735151 7204685859551016766102727)
          ·
            refine ⟨10807028789326525149154091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204685859551016766102727 10807028789326525149154091)
            ·
              refine ⟨16210543183989787723731137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807028789326525149154091 16210543183989787723731137)
              ·
                refine ⟨12157907387992340792798353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16210543183989787723731137 12157907387992340792798353)
                ·
                  refine ⟨9118430540994255594598765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12157907387992340792798353 9118430540994255594598765)
                  ·
                    refine ⟨3419411452872845847974537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9118430540994255594598765 3419411452872845847974537)
                    ·
                      refine ⟨2564558589654634385980903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419411452872845847974537 2564558589654634385980903)
                      ·
                        rfl

theorem cell23_4994460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4994460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994460 prefixEnd_4994460 := by exact prefixLift 4994460
  have htrace : WordTrace (prefixWord ++ tailWord_4994460) baseStart_4994460 baseEnd_4994460 := by
    simpa [prefixWord, tailWord_4994460, baseEnd_4994460] using wordTrace_append hprefix tailTrace_4994460
  have hstable : (prefixWord ++ tailWord_4994460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994460).length < 2 ^ (prefixWord ++ tailWord_4994460).sum := by decide
  have hdescent : baseEnd_4994460 < baseStart_4994460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994466 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4994466 : Nat := 118140960795 + 4994466 * 2 ^ 59
def prefixEnd_4994466 : Nat := 4983230072969 + 3 ^ 40 * 4994466 * 2
def baseEnd_4994466 : Nat := 854853890179520454168625

theorem tailTrace_4994466 : CollatzResearch.WordTrace tailWord_4994466 prefixEnd_4994466 854853890179520454168625 := by
  unfold tailWord_4994466
  simp only [CollatzResearch.WordTrace]
  refine ⟨45540785080977535932038813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121442093549273429152103501 45540785080977535932038813)
  ·
    refine ⟨17077794405366575974514555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45540785080977535932038813 17077794405366575974514555)
    ·
      refine ⟨25616691608049863961771833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17077794405366575974514555 25616691608049863961771833)
      ·
        refine ⟨19212518706037397971328875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25616691608049863961771833 19212518706037397971328875)
        ·
          refine ⟨28818778059056096956993313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19212518706037397971328875 28818778059056096956993313)
          ·
            refine ⟨21614083544292072717744985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28818778059056096956993313 21614083544292072717744985)
            ·
              refine ⟨16210562658219054538308739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21614083544292072717744985 16210562658219054538308739)
              ·
                refine ⟨24315843987328581807463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16210562658219054538308739 24315843987328581807463109)
                ·
                  refine ⟨4559220747624109088899333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24315843987328581807463109 4559220747624109088899333)
                  ·
                    refine ⟨854853890179520454168625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559220747624109088899333 854853890179520454168625)
                    ·
                      rfl

theorem cell23_4994466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4994466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994466 prefixEnd_4994466 := by exact prefixLift 4994466
  have htrace : WordTrace (prefixWord ++ tailWord_4994466) baseStart_4994466 baseEnd_4994466 := by
    simpa [prefixWord, tailWord_4994466, baseEnd_4994466] using wordTrace_append hprefix tailTrace_4994466
  have hstable : (prefixWord ++ tailWord_4994466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994466).length < 2 ^ (prefixWord ++ tailWord_4994466).sum := by decide
  have hdescent : baseEnd_4994466 < baseStart_4994466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994506 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_4994506 : Nat := 118140960795 + 4994506 * 2 ^ 59
def prefixEnd_4994506 : Nat := 4983230072969 + 3 ^ 40 * 4994506 * 2
def baseEnd_4994506 : Nat := 2564582209764741206005691

theorem tailTrace_4994506 : CollatzResearch.WordTrace tailWord_4994506 prefixEnd_4994506 2564582209764741206005691 := by
  unfold tailWord_4994506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541149810941307639902843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121443066162510153706407581 45541149810941307639902843)
  ·
    refine ⟨68311724716411961459854265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45541149810941307639902843 68311724716411961459854265)
    ·
      refine ⟨51233793537308971094890699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68311724716411961459854265 51233793537308971094890699)
      ·
        refine ⟨76850690305963456642336049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51233793537308971094890699 76850690305963456642336049)
        ·
          refine ⟨57638017729472592481752037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76850690305963456642336049 57638017729472592481752037)
          ·
            refine ⟨10807128324276111090328507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57638017729472592481752037 10807128324276111090328507)
            ·
              refine ⟨16210692486414166635492761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807128324276111090328507 16210692486414166635492761)
              ·
                refine ⟨12158019364810624976619571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16210692486414166635492761 12158019364810624976619571)
                ·
                  refine ⟨18237029047215937464929357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158019364810624976619571 18237029047215937464929357)
                  ·
                    refine ⟨6838885892705976549348509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18237029047215937464929357 6838885892705976549348509)
                    ·
                      refine ⟨2564582209764741206005691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6838885892705976549348509 2564582209764741206005691)
                      ·
                        rfl

theorem cell23_4994506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_4994506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994506 prefixEnd_4994506 := by exact prefixLift 4994506
  have htrace : WordTrace (prefixWord ++ tailWord_4994506) baseStart_4994506 baseEnd_4994506 := by
    simpa [prefixWord, tailWord_4994506, baseEnd_4994506] using wordTrace_append hprefix tailTrace_4994506
  have hstable : (prefixWord ++ tailWord_4994506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994506).length < 2 ^ (prefixWord ++ tailWord_4994506).sum := by decide
  have hdescent : baseEnd_4994506 < baseStart_4994506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994512 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_4994512 : Nat := 118140960795 + 4994512 * 2 ^ 59
def prefixEnd_4994512 : Nat := 4983230072969 + 3 ^ 40 * 4994512 * 2
def baseEnd_4994512 : Nat := 2564585290648668182530663

theorem tailTrace_4994512 : CollatzResearch.WordTrace tailWord_4994512 prefixEnd_4994512 2564585290648668182530663 := by
  unfold tailWord_4994512
  simp only [CollatzResearch.WordTrace]
  refine ⟨91082409040871746792164895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121443212054495662389553193 91082409040871746792164895)
  ·
    refine ⟨136623613561307620188247343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91082409040871746792164895 136623613561307620188247343)
    ·
      refine ⟨204935420341961430282371015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136623613561307620188247343 204935420341961430282371015)
      ·
        refine ⟨307403130512942145423556523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204935420341961430282371015 307403130512942145423556523)
        ·
          refine ⟨461104695769413218135334785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307403130512942145423556523 461104695769413218135334785)
          ·
            refine ⟨345828521827059913601501089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461104695769413218135334785 345828521827059913601501089)
            ·
              refine ⟨259371391370294935201125817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345828521827059913601501089 259371391370294935201125817)
              ·
                refine ⟨194528543527721201400844363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259371391370294935201125817 194528543527721201400844363)
                ·
                  refine ⟨291792815291581802101266545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194528543527721201400844363 291792815291581802101266545)
                  ·
                    refine ⟨218844611468686351575949909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291792815291581802101266545 218844611468686351575949909)
                    ·
                      refine ⟨2564585290648668182530663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 218844611468686351575949909 2564585290648668182530663)
                      ·
                        rfl

theorem cell23_4994512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_4994512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994512 prefixEnd_4994512 := by exact prefixLift 4994512
  have htrace : WordTrace (prefixWord ++ tailWord_4994512) baseStart_4994512 baseEnd_4994512 := by
    simpa [prefixWord, tailWord_4994512, baseEnd_4994512] using wordTrace_append hprefix tailTrace_4994512
  have hstable : (prefixWord ++ tailWord_4994512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994512).length < 2 ^ (prefixWord ++ tailWord_4994512).sum := by decide
  have hdescent : baseEnd_4994512 < baseStart_4994512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994529 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4994529 : Nat := 118140960795 + 4994529 * 2 ^ 59
def prefixEnd_4994529 : Nat := 4983230072969 + 3 ^ 40 * 4994529 * 2
def baseEnd_4994529 : Nat := 2564594019819794616018085

theorem tailTrace_4994529 : CollatzResearch.WordTrace tailWord_4994529 prefixEnd_4994529 2564594019819794616018085 := by
  unfold tailWord_4994529
  simp only [CollatzResearch.WordTrace]
  refine ⟨182165438122681905487698641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121443625415121270325132427 182165438122681905487698641)
  ·
    refine ⟨136624078592011429115773981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182165438122681905487698641 136624078592011429115773981)
    ·
      refine ⟨51234029472004285918415243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136624078592011429115773981 51234029472004285918415243)
      ·
        refine ⟨76851044208006428877622865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51234029472004285918415243 76851044208006428877622865)
        ·
          refine ⟨57638283156004821658217149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76851044208006428877622865 57638283156004821658217149)
          ·
            refine ⟨21614356183501808121831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57638283156004821658217149 21614356183501808121831431)
            ·
              refine ⟨32421534275252712182747147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614356183501808121831431 32421534275252712182747147)
              ·
                refine ⟨48632301412879068274120721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32421534275252712182747147 48632301412879068274120721)
                ·
                  refine ⟨36474226059659301205590541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48632301412879068274120721 36474226059659301205590541)
                  ·
                    refine ⟨13677834772372237952096453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36474226059659301205590541 13677834772372237952096453)
                    ·
                      refine ⟨2564594019819794616018085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13677834772372237952096453 2564594019819794616018085)
                      ·
                        rfl

theorem cell23_4994529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4994529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994529 prefixEnd_4994529 := by exact prefixLift 4994529
  have htrace : WordTrace (prefixWord ++ tailWord_4994529) baseStart_4994529 baseEnd_4994529 := by
    simpa [prefixWord, tailWord_4994529, baseEnd_4994529] using wordTrace_append hprefix tailTrace_4994529
  have hstable : (prefixWord ++ tailWord_4994529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994529).length < 2 ^ (prefixWord ++ tailWord_4994529).sum := by decide
  have hdescent : baseEnd_4994529 < baseStart_4994529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994533 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4994533 : Nat := 118140960795 + 4994533 * 2 ^ 59
def prefixEnd_4994533 : Nat := 4983230072969 + 3 ^ 40 * 4994533 * 2
def baseEnd_4994533 : Nat := 2564596073742412600368067

theorem tailTrace_4994533 : CollatzResearch.WordTrace tailWord_4994533 prefixEnd_4994533 2564596073742412600368067 := by
  unfold tailWord_4994533
  simp only [CollatzResearch.WordTrace]
  refine ⟨182165584014667414170844253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121443722676444942780562835 182165584014667414170844253)
  ·
    refine ⟨68312094005500280314066595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182165584014667414170844253 68312094005500280314066595)
    ·
      refine ⟨102468141008250420471099893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68312094005500280314066595 102468141008250420471099893)
      ·
        refine ⟨9606388219523476919165615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102468141008250420471099893 9606388219523476919165615)
        ·
          refine ⟨14409582329285215378748423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9606388219523476919165615 14409582329285215378748423)
          ·
            refine ⟨21614373493927823068122635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14409582329285215378748423 21614373493927823068122635)
            ·
              refine ⟨32421560240891734602183953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614373493927823068122635 32421560240891734602183953)
              ·
                refine ⟨24316170180668800951637965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32421560240891734602183953 24316170180668800951637965)
                ·
                  refine ⟨9118563817750800356864237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24316170180668800951637965 9118563817750800356864237)
                  ·
                    refine ⟨3419461431656550133824089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9118563817750800356864237 3419461431656550133824089)
                    ·
                      refine ⟨2564596073742412600368067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419461431656550133824089 2564596073742412600368067)
                      ·
                        rfl

theorem cell23_4994533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4994533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994533 prefixEnd_4994533 := by exact prefixLift 4994533
  have htrace : WordTrace (prefixWord ++ tailWord_4994533) baseStart_4994533 baseEnd_4994533 := by
    simpa [prefixWord, tailWord_4994533, baseEnd_4994533] using wordTrace_append hprefix tailTrace_4994533
  have hstable : (prefixWord ++ tailWord_4994533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994533).length < 2 ^ (prefixWord ++ tailWord_4994533).sum := by decide
  have hdescent : baseEnd_4994533 < baseStart_4994533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994567 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4994567 : Nat := 118140960795 + 4994567 * 2 ^ 59
def prefixEnd_4994567 : Nat := 4983230072969 + 3 ^ 40 * 4994567 * 2
def baseEnd_4994567 : Nat := 2564613532084665467342911

theorem tailTrace_4994567 : CollatzResearch.WordTrace tailWord_4994567 prefixEnd_4994567 2564613532084665467342911 := by
  unfold tailWord_4994567
  simp only [CollatzResearch.WordTrace]
  refine ⟨182166824096544237977581955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121444549397696158651721303 182166824096544237977581955)
  ·
    refine ⟨273250236144816356966372933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182166824096544237977581955 273250236144816356966372933)
    ·
      refine ⟨51234419277153066931194925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273250236144816356966372933 51234419277153066931194925)
      ·
        refine ⟨19212907228932400099198097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51234419277153066931194925 19212907228932400099198097)
        ·
          refine ⟨14409680421699300074398573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19212907228932400099198097 14409680421699300074398573)
          ·
            refine ⟨5403630158137237527899465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14409680421699300074398573 5403630158137237527899465)
            ·
              refine ⟨4052722618602928145924599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403630158137237527899465 4052722618602928145924599)
              ·
                refine ⟨6079083927904392218886899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052722618602928145924599 6079083927904392218886899)
                ·
                  refine ⟨9118625891856588328330349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079083927904392218886899 9118625891856588328330349)
                  ·
                    refine ⟨3419484709446220623123881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9118625891856588328330349 3419484709446220623123881)
                    ·
                      refine ⟨2564613532084665467342911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419484709446220623123881 2564613532084665467342911)
                      ·
                        rfl

theorem cell23_4994567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4994567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994567 prefixEnd_4994567 := by exact prefixLift 4994567
  have htrace : WordTrace (prefixWord ++ tailWord_4994567) baseStart_4994567 baseEnd_4994567 := by
    simpa [prefixWord, tailWord_4994567, baseEnd_4994567] using wordTrace_append hprefix tailTrace_4994567
  have hstable : (prefixWord ++ tailWord_4994567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994567).length < 2 ^ (prefixWord ++ tailWord_4994567).sum := by decide
  have hdescent : baseEnd_4994567 < baseStart_4994567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994609 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_4994609 : Nat := 118140960795 + 4994609 * 2 ^ 59
def prefixEnd_4994609 : Nat := 4983230072969 + 3 ^ 40 * 4994609 * 2
def baseEnd_4994609 : Nat := 2564635098272154303017717

theorem tailTrace_4994609 : CollatzResearch.WordTrace tailWord_4994609 prefixEnd_4994609 2564635098272154303017717 := by
  unfold tailWord_4994609
  simp only [CollatzResearch.WordTrace]
  refine ⟨182168355962392079150610881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121445570641594719433740587 182168355962392079150610881)
  ·
    refine ⟨136626266971794059362958161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182168355962392079150610881 136626266971794059362958161)
    ·
      refine ⟨102469700228845544522218621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136626266971794059362958161 102469700228845544522218621)
      ·
        refine ⟨38426137585817079195831983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102469700228845544522218621 38426137585817079195831983)
        ·
          refine ⟨57639206378725618793747975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38426137585817079195831983 57639206378725618793747975)
          ·
            refine ⟨86458809568088428190621963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57639206378725618793747975 86458809568088428190621963)
            ·
              refine ⟨129688214352132642285932945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86458809568088428190621963 129688214352132642285932945)
              ·
                refine ⟨97266160764099481714449709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129688214352132642285932945 97266160764099481714449709)
                ·
                  refine ⟨36474810286537305642918641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97266160764099481714449709 36474810286537305642918641)
                  ·
                    refine ⟨27356107714902979232188981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36474810286537305642918641 27356107714902979232188981)
                    ·
                      refine ⟨2564635098272154303017717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27356107714902979232188981 2564635098272154303017717)
                      ·
                        rfl

theorem cell23_4994609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_4994609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994609 prefixEnd_4994609 := by exact prefixLift 4994609
  have htrace : WordTrace (prefixWord ++ tailWord_4994609) baseStart_4994609 baseEnd_4994609 := by
    simpa [prefixWord, tailWord_4994609, baseEnd_4994609] using wordTrace_append hprefix tailTrace_4994609
  have hstable : (prefixWord ++ tailWord_4994609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994609).length < 2 ^ (prefixWord ++ tailWord_4994609).sum := by decide
  have hdescent : baseEnd_4994609 < baseStart_4994609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994620 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 5]
def baseStart_4994620 : Nat := 118140960795 + 4994620 * 2 ^ 59
def prefixEnd_4994620 : Nat := 4983230072969 + 3 ^ 40 * 4994620 * 2
def baseEnd_4994620 : Nat := 284960082951039306664463

theorem tailTrace_4994620 : CollatzResearch.WordTrace tailWord_4994620 prefixEnd_4994620 284960082951039306664463 := by
  unfold tailWord_4994620
  simp only [CollatzResearch.WordTrace]
  refine ⟨91084378582676114014630657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121445838110234818686174209 91084378582676114014630657)
  ·
    refine ⟨68313283937007085510972993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91084378582676114014630657 68313283937007085510972993)
    ·
      refine ⟨51234962952755314133229745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68313283937007085510972993 51234962952755314133229745)
      ·
        refine ⟨38426222214566485599922309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51234962952755314133229745 38426222214566485599922309)
        ·
          refine ⟨7204916665231216049985433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38426222214566485599922309 7204916665231216049985433)
          ·
            refine ⟨5403687498923412037489075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7204916665231216049985433 5403687498923412037489075)
            ·
              refine ⟨8105531248385118056233613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403687498923412037489075 8105531248385118056233613)
              ·
                refine ⟨3039574218144419271087605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8105531248385118056233613 3039574218144419271087605)
                ·
                  refine ⟨284960082951039306664463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3039574218144419271087605 284960082951039306664463)
                  ·
                    rfl

theorem cell23_4994620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_4994620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994620 prefixEnd_4994620 := by exact prefixLift 4994620
  have htrace : WordTrace (prefixWord ++ tailWord_4994620) baseStart_4994620 baseEnd_4994620 := by
    simpa [prefixWord, tailWord_4994620, baseEnd_4994620] using wordTrace_append hprefix tailTrace_4994620
  have hstable : (prefixWord ++ tailWord_4994620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994620).length < 2 ^ (prefixWord ++ tailWord_4994620).sum := by decide
  have hdescent : baseEnd_4994620 < baseStart_4994620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994636 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4994636 : Nat := 118140960795 + 4994636 * 2 ^ 59
def prefixEnd_4994636 : Nat := 4983230072969 + 3 ^ 40 * 4994636 * 2
def baseEnd_4994636 : Nat := 2564648962249825697380093

theorem tailTrace_4994636 : CollatzResearch.WordTrace tailWord_4994636 prefixEnd_4994636 2564648962249825697380093 := by
  unfold tailWord_4994636
  simp only [CollatzResearch.WordTrace]
  refine ⟨91084670366647131380921881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121446227155529508507895841 91084670366647131380921881)
  ·
    refine ⟨68313502774985348535691411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91084670366647131380921881 68313502774985348535691411)
    ·
      refine ⟨102470254162478022803537117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68313502774985348535691411 102470254162478022803537117)
      ·
        refine ⟨38426345310929258551326419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102470254162478022803537117 38426345310929258551326419)
        ·
          refine ⟨57639517966393887826989629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38426345310929258551326419 57639517966393887826989629)
          ·
            refine ⟨21614819237397707935121111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57639517966393887826989629 21614819237397707935121111)
            ·
              refine ⟨32422228856096561902681667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614819237397707935121111 32422228856096561902681667)
              ·
                refine ⟨48633343284144842854022501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32422228856096561902681667 48633343284144842854022501)
                ·
                  refine ⟨9118751865777158035129219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48633343284144842854022501 9118751865777158035129219)
                  ·
                    refine ⟨13678127798665737052693829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9118751865777158035129219 13678127798665737052693829)
                    ·
                      refine ⟨2564648962249825697380093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13678127798665737052693829 2564648962249825697380093)
                      ·
                        rfl

theorem cell23_4994636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4994636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994636 prefixEnd_4994636 := by exact prefixLift 4994636
  have htrace : WordTrace (prefixWord ++ tailWord_4994636) baseStart_4994636 baseEnd_4994636 := by
    simpa [prefixWord, tailWord_4994636, baseEnd_4994636] using wordTrace_append hprefix tailTrace_4994636
  have hstable : (prefixWord ++ tailWord_4994636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994636).length < 2 ^ (prefixWord ++ tailWord_4994636).sum := by decide
  have hdescent : baseEnd_4994636 < baseStart_4994636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994637 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4994637 : Nat := 118140960795 + 4994637 * 2 ^ 59
def prefixEnd_4994637 : Nat := 4983230072969 + 3 ^ 40 * 4994637 * 2
def baseEnd_4994637 : Nat := 284961052858942243718621

theorem tailTrace_4994637 : CollatzResearch.WordTrace tailWord_4994637 prefixEnd_4994637 284961052858942243718621 := by
  unfold tailWord_4994637
  simp only [CollatzResearch.WordTrace]
  refine ⟨182169377206290639932630165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121446251470860426621753443 182169377206290639932630165)
  ·
    refine ⟨8539189556544873746842039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182169377206290639932630165 8539189556544873746842039)
    ·
      refine ⟨12808784334817310620263059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539189556544873746842039 12808784334817310620263059)
      ·
        refine ⟨19213176502225965930394589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808784334817310620263059 19213176502225965930394589)
        ·
          refine ⟨7204941188334737223897971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19213176502225965930394589 7204941188334737223897971)
          ·
            refine ⟨10807411782502105835846957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204941188334737223897971 10807411782502105835846957)
            ·
              refine ⟨4052779418438289688442609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10807411782502105835846957 4052779418438289688442609)
              ·
                refine ⟨3039584563828717266331957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052779418438289688442609 3039584563828717266331957)
                ·
                  refine ⟨284961052858942243718621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3039584563828717266331957 284961052858942243718621)
                  ·
                    rfl

theorem cell23_4994637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4994637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994637 prefixEnd_4994637 := by exact prefixLift 4994637
  have htrace : WordTrace (prefixWord ++ tailWord_4994637) baseStart_4994637 baseEnd_4994637 := by
    simpa [prefixWord, tailWord_4994637, baseEnd_4994637] using wordTrace_append hprefix tailTrace_4994637
  have hstable : (prefixWord ++ tailWord_4994637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994637).length < 2 ^ (prefixWord ++ tailWord_4994637).sum := by decide
  have hdescent : baseEnd_4994637 < baseStart_4994637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994649 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4994649 : Nat := 118140960795 + 4994649 * 2 ^ 59
def prefixEnd_4994649 : Nat := 4983230072969 + 3 ^ 40 * 4994649 * 2
def baseEnd_4994649 : Nat := 2564655637498334146517533

theorem tailTrace_4994649 : CollatzResearch.WordTrace tailWord_4994649 prefixEnd_4994649 2564655637498334146517533 := by
  unfold tailWord_4994649
  simp only [CollatzResearch.WordTrace]
  refine ⟨182169814882247165982067001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121446543254831443988044667 182169814882247165982067001)
  ·
    refine ⟨136627361161685374486550251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182169814882247165982067001 136627361161685374486550251)
    ·
      refine ⟨204941041742528061729825377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136627361161685374486550251 204941041742528061729825377)
      ·
        refine ⟨153705781306896046297369033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204941041742528061729825377 153705781306896046297369033)
        ·
          refine ⟨115279335980172034723026775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153705781306896046297369033 115279335980172034723026775)
          ·
            refine ⟨172919003970258052084540163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115279335980172034723026775 172919003970258052084540163)
            ·
              refine ⟨259378505955387078126810245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172919003970258052084540163 259378505955387078126810245)
              ·
                refine ⟨48633469866635077148776921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259378505955387078126810245 48633469866635077148776921)
                ·
                  refine ⟨36475102399976307861582691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48633469866635077148776921 36475102399976307861582691)
                  ·
                    refine ⟨54712653599964461792374037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36475102399976307861582691 54712653599964461792374037)
                    ·
                      refine ⟨2564655637498334146517533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54712653599964461792374037 2564655637498334146517533)
                      ·
                        rfl

theorem cell23_4994649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4994649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994649 prefixEnd_4994649 := by exact prefixLift 4994649
  have htrace : WordTrace (prefixWord ++ tailWord_4994649) baseStart_4994649 baseEnd_4994649 := by
    simpa [prefixWord, tailWord_4994649, baseEnd_4994649] using wordTrace_append hprefix tailTrace_4994649
  have hstable : (prefixWord ++ tailWord_4994649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994649).length < 2 ^ (prefixWord ++ tailWord_4994649).sum := by decide
  have hdescent : baseEnd_4994649 < baseStart_4994649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994656 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_4994656 : Nat := 118140960795 + 4994656 * 2 ^ 59
def prefixEnd_4994656 : Nat := 4983230072969 + 3 ^ 40 * 4994656 * 2
def baseEnd_4994656 : Nat := 2564659231862915619130001

theorem tailTrace_4994656 : CollatzResearch.WordTrace tailWord_4994656 prefixEnd_4994656 2564659231862915619130001 := by
  unfold tailWord_4994656
  simp only [CollatzResearch.WordTrace]
  refine ⟨91085035096610903088785911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121446713462147870785047881 91085035096610903088785911)
  ·
    refine ⟨136627552644916354633178867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91085035096610903088785911 136627552644916354633178867)
    ·
      refine ⟨204941328967374531949768301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136627552644916354633178867 204941328967374531949768301)
      ·
        refine ⟨76852998362765449481163113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204941328967374531949768301 76852998362765449481163113)
        ·
          refine ⟨57639748772074087110872335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76852998362765449481163113 57639748772074087110872335)
          ·
            refine ⟨86459623158111130666308503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57639748772074087110872335 86459623158111130666308503)
            ·
              refine ⟨129689434737166695999462755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86459623158111130666308503 129689434737166695999462755)
              ·
                refine ⟨194534152105750043999194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129689434737166695999462755 194534152105750043999194133)
                ·
                  refine ⟨9118788379957033312462225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194534152105750043999194133 9118788379957033312462225)
                  ·
                    refine ⟨6839091284967774984346669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9118788379957033312462225 6839091284967774984346669)
                    ·
                      refine ⟨2564659231862915619130001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839091284967774984346669 2564659231862915619130001)
                      ·
                        rfl

theorem cell23_4994656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_4994656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994656 prefixEnd_4994656 := by exact prefixLift 4994656
  have htrace : WordTrace (prefixWord ++ tailWord_4994656) baseStart_4994656 baseEnd_4994656 := by
    simpa [prefixWord, tailWord_4994656, baseEnd_4994656] using wordTrace_append hprefix tailTrace_4994656
  have hstable : (prefixWord ++ tailWord_4994656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994656).length < 2 ^ (prefixWord ++ tailWord_4994656).sum := by decide
  have hdescent : baseEnd_4994656 < baseStart_4994656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994670 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4994670 : Nat := 118140960795 + 4994670 * 2 ^ 59
def prefixEnd_4994670 : Nat := 4983230072969 + 3 ^ 40 * 4994670 * 2
def baseEnd_4994670 : Nat := 2564666420592078564354937

theorem tailTrace_4994670 : CollatzResearch.WordTrace tailWord_4994670 prefixEnd_4994670 2564666420592078564354937 := by
  unfold tailWord_4994670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771322601896385821072683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121447053876780724379054309 22771322601896385821072683)
  ·
    refine ⟨34156983902844578731609025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771322601896385821072683 34156983902844578731609025)
    ·
      refine ⟨25617737927133434048706769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34156983902844578731609025 25617737927133434048706769)
      ·
        refine ⟨19213303445350075536530077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25617737927133434048706769 19213303445350075536530077)
        ·
          refine ⟨7204988792006278326198779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19213303445350075536530077 7204988792006278326198779)
          ·
            refine ⟨10807483188009417489298169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204988792006278326198779 10807483188009417489298169)
            ·
              refine ⟨8105612391007063116973627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10807483188009417489298169 8105612391007063116973627)
              ·
                refine ⟨12158418586510594675460441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105612391007063116973627 12158418586510594675460441)
                ·
                  refine ⟨9118813939882946006595331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12158418586510594675460441 9118813939882946006595331)
                  ·
                    refine ⟨13678220909824419009892997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9118813939882946006595331 13678220909824419009892997)
                    ·
                      refine ⟨2564666420592078564354937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13678220909824419009892997 2564666420592078564354937)
                      ·
                        rfl

theorem cell23_4994670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4994670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994670 prefixEnd_4994670 := by exact prefixLift 4994670
  have htrace : WordTrace (prefixWord ++ tailWord_4994670) baseStart_4994670 baseEnd_4994670 := by
    simpa [prefixWord, tailWord_4994670, baseEnd_4994670] using wordTrace_append hprefix tailTrace_4994670
  have hstable : (prefixWord ++ tailWord_4994670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994670).length < 2 ^ (prefixWord ++ tailWord_4994670).sum := by decide
  have hdescent : baseEnd_4994670 < baseStart_4994670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994679 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_4994679 : Nat := 118140960795 + 4994679 * 2 ^ 59
def prefixEnd_4994679 : Nat := 4983230072969 + 3 ^ 40 * 4994679 * 2
def baseEnd_4994679 : Nat := 2564671041917969029142395

theorem tailTrace_4994679 : CollatzResearch.WordTrace tailWord_4994679 prefixEnd_4994679 2564671041917969029142395 := by
  unfold tailWord_4994679
  simp only [CollatzResearch.WordTrace]
  refine ⟨182170909072138481105659091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121447272714758987403772727 182170909072138481105659091)
  ·
    refine ⟨273256363608207721658488637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182170909072138481105659091 273256363608207721658488637)
    ·
      refine ⟨102471136353077895621933239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273256363608207721658488637 102471136353077895621933239)
      ·
        refine ⟨153706704529616843432899859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102471136353077895621933239 153706704529616843432899859)
        ·
          refine ⟨230560056794425265149349789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153706704529616843432899859 230560056794425265149349789)
          ·
            refine ⟨86460021297909474431006171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230560056794425265149349789 86460021297909474431006171)
            ·
              refine ⟨129690031946864211646509257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86460021297909474431006171 129690031946864211646509257)
              ·
                refine ⟨97267523960148158734881943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129690031946864211646509257 97267523960148158734881943)
                ·
                  refine ⟨145901285940222238102322915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97267523960148158734881943 145901285940222238102322915)
                  ·
                    refine ⟨218851928910333357153484373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145901285940222238102322915 218851928910333357153484373)
                    ·
                      refine ⟨2564671041917969029142395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 218851928910333357153484373 2564671041917969029142395)
                      ·
                        rfl

theorem cell23_4994679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_4994679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994679 prefixEnd_4994679 := by exact prefixLift 4994679
  have htrace : WordTrace (prefixWord ++ tailWord_4994679) baseStart_4994679 baseEnd_4994679 := by
    simpa [prefixWord, tailWord_4994679, baseEnd_4994679] using wordTrace_append hprefix tailTrace_4994679
  have hstable : (prefixWord ++ tailWord_4994679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994679).length < 2 ^ (prefixWord ++ tailWord_4994679).sum := by decide
  have hdescent : baseEnd_4994679 < baseStart_4994679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994720 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_4994720 : Nat := 118140960795 + 4994720 * 2 ^ 59
def prefixEnd_4994720 : Nat := 4983230072969 + 3 ^ 40 * 4994720 * 2
def baseEnd_4994720 : Nat := 2564692094624803368729707

theorem tailTrace_4994720 : CollatzResearch.WordTrace tailWord_4994720 prefixEnd_4994720 2564692094624803368729707 := by
  unfold tailWord_4994720
  simp only [CollatzResearch.WordTrace]
  refine ⟨91086202232494972553950807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121448269643326630071934409 91086202232494972553950807)
  ·
    refine ⟨136629303348742458830926211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91086202232494972553950807 136629303348742458830926211)
    ·
      refine ⟨204943955023113688246389317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136629303348742458830926211 204943955023113688246389317)
      ·
        refine ⟨38426991566833816546197997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204943955023113688246389317 38426991566833816546197997)
        ·
          refine ⟨14410121837562681204824249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38426991566833816546197997 14410121837562681204824249)
          ·
            refine ⟨10807591378172010903618187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14410121837562681204824249 10807591378172010903618187)
            ·
              refine ⟨16211387067258016355427281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807591378172010903618187 16211387067258016355427281)
              ·
                refine ⟨12158540300443512266570461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16211387067258016355427281 12158540300443512266570461)
                ·
                  refine ⟨4559452612666317099963923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12158540300443512266570461 4559452612666317099963923)
                  ·
                    refine ⟨6839178918999475649945885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559452612666317099963923 6839178918999475649945885)
                    ·
                      refine ⟨2564692094624803368729707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839178918999475649945885 2564692094624803368729707)
                      ·
                        rfl

theorem cell23_4994720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_4994720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994720 prefixEnd_4994720 := by exact prefixLift 4994720
  have htrace : WordTrace (prefixWord ++ tailWord_4994720) baseStart_4994720 baseEnd_4994720 := by
    simpa [prefixWord, tailWord_4994720, baseEnd_4994720] using wordTrace_append hprefix tailTrace_4994720
  have hstable : (prefixWord ++ tailWord_4994720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994720).length < 2 ^ (prefixWord ++ tailWord_4994720).sum := by decide
  have hdescent : baseEnd_4994720 < baseStart_4994720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994736 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_4994736 : Nat := 118140960795 + 4994736 * 2 ^ 59
def prefixEnd_4994736 : Nat := 4983230072969 + 3 ^ 40 * 4994736 * 2
def baseEnd_4994736 : Nat := 854900103438425102043211

theorem tailTrace_4994736 : CollatzResearch.WordTrace tailWord_4994736 prefixEnd_4994736 854900103438425102043211 := by
  unfold tailWord_4994736
  simp only [CollatzResearch.WordTrace]
  refine ⟨91086494016465989920242031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121448658688621319893656041 91086494016465989920242031)
  ·
    refine ⟨136629741024698984880363047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91086494016465989920242031 136629741024698984880363047)
    ·
      refine ⟨204944611537048477320544571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136629741024698984880363047 204944611537048477320544571)
      ·
        refine ⟨307416917305572715980816857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204944611537048477320544571 307416917305572715980816857)
        ·
          refine ⟨230562687979179536985612643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307416917305572715980816857 230562687979179536985612643)
          ·
            refine ⟨345844031968769305478418965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230562687979179536985612643 345844031968769305478418965)
            ·
              refine ⟨16211438998536061194300889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 345844031968769305478418965 16211438998536061194300889)
              ·
                refine ⟨12158579248902045895725667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16211438998536061194300889 12158579248902045895725667)
                ·
                  refine ⟨18237868873353068843588501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158579248902045895725667 18237868873353068843588501)
                  ·
                    refine ⟨854900103438425102043211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18237868873353068843588501 854900103438425102043211)
                    ·
                      rfl

theorem cell23_4994736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_4994736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994736 prefixEnd_4994736 := by exact prefixLift 4994736
  have htrace : WordTrace (prefixWord ++ tailWord_4994736) baseStart_4994736 baseEnd_4994736 := by
    simpa [prefixWord, tailWord_4994736, baseEnd_4994736] using wordTrace_append hprefix tailTrace_4994736
  have hstable : (prefixWord ++ tailWord_4994736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994736).length < 2 ^ (prefixWord ++ tailWord_4994736).sum := by decide
  have hdescent : baseEnd_4994736 < baseStart_4994736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994766 : List Nat := [4, 1, 1, 1, 3, 1, 2, 10]
def baseStart_4994766 : Nat := 118140960795 + 4994766 * 2 ^ 59
def prefixEnd_4994766 : Nat := 4983230072969 + 3 ^ 40 * 4994766 * 2
def baseEnd_4994766 : Nat := 94989470916107784768685

theorem tailTrace_4994766 : CollatzResearch.WordTrace tailWord_4994766 prefixEnd_4994766 94989470916107784768685 := by
  unfold tailWord_4994766
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771760277852911870509519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121449388148548863309384101 22771760277852911870509519)
  ·
    refine ⟨34157640416779367805764279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771760277852911870509519 34157640416779367805764279)
    ·
      refine ⟨51236460625169051708646419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34157640416779367805764279 51236460625169051708646419)
      ·
        refine ⟨76854690937753577562969629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51236460625169051708646419 76854690937753577562969629)
        ·
          refine ⟨28820509101657591586113611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76854690937753577562969629 28820509101657591586113611)
          ·
            refine ⟨43230763652486387379170417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28820509101657591586113611 43230763652486387379170417)
            ·
              refine ⟨32423072739364790534377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43230763652486387379170417 32423072739364790534377813)
              ·
                refine ⟨94989470916107784768685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32423072739364790534377813 94989470916107784768685)
                ·
                  rfl

theorem cell23_4994766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_4994766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994766 prefixEnd_4994766 := by exact prefixLift 4994766
  have htrace : WordTrace (prefixWord ++ tailWord_4994766) baseStart_4994766 baseEnd_4994766 := by
    simpa [prefixWord, tailWord_4994766, baseEnd_4994766] using wordTrace_append hprefix tailTrace_4994766
  have hstable : (prefixWord ++ tailWord_4994766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994766).length < 2 ^ (prefixWord ++ tailWord_4994766).sum := by decide
  have hdescent : baseEnd_4994766 < baseStart_4994766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994770 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_4994770 : Nat := 118140960795 + 4994770 * 2 ^ 59
def prefixEnd_4994770 : Nat := 4983230072969 + 3 ^ 40 * 4994770 * 2
def baseEnd_4994770 : Nat := 854905922885842724368159

theorem tailTrace_4994770 : CollatzResearch.WordTrace tailWord_4994770 prefixEnd_4994770 854905922885842724368159 := by
  unfold tailWord_4994770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45543557028702200911805441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121449485409872535764814509 45543557028702200911805441)
  ·
    refine ⟨34157667771526650683854081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45543557028702200911805441 34157667771526650683854081)
    ·
      refine ⟨25618250828644988012890561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34157667771526650683854081 25618250828644988012890561)
      ·
        refine ⟨19213688121483741009667921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25618250828644988012890561 19213688121483741009667921)
        ·
          refine ⟨14410266091112805757250941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19213688121483741009667921 14410266091112805757250941)
          ·
            refine ⟨5403849784167302158969103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14410266091112805757250941 5403849784167302158969103)
            ·
              refine ⟨8105774676250953238453655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403849784167302158969103 8105774676250953238453655)
              ·
                refine ⟨12158662014376429857680483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105774676250953238453655 12158662014376429857680483)
                ·
                  refine ⟨18237993021564644786520725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158662014376429857680483 18237993021564644786520725)
                  ·
                    refine ⟨854905922885842724368159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18237993021564644786520725 854905922885842724368159)
                    ·
                      rfl

theorem cell23_4994770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_4994770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994770 prefixEnd_4994770 := by exact prefixLift 4994770
  have htrace : WordTrace (prefixWord ++ tailWord_4994770) baseStart_4994770 baseEnd_4994770 := by
    simpa [prefixWord, tailWord_4994770, baseEnd_4994770] using wordTrace_append hprefix tailTrace_4994770
  have hstable : (prefixWord ++ tailWord_4994770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994770).length < 2 ^ (prefixWord ++ tailWord_4994770).sum := by decide
  have hdescent : baseEnd_4994770 < baseStart_4994770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994774 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4994774 : Nat := 118140960795 + 4994774 * 2 ^ 59
def prefixEnd_4994774 : Nat := 4983230072969 + 3 ^ 40 * 4994774 * 2
def baseEnd_4994774 : Nat := 854906607526715385818153

theorem tailTrace_4994774 : CollatzResearch.WordTrace tailWord_4994774 prefixEnd_4994774 854906607526715385818153 := by
  unfold tailWord_4994774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385898375424644520647961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121449582671196208220244917 11385898375424644520647961)
  ·
    refine ⟨8539423781568483390485971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11385898375424644520647961 8539423781568483390485971)
    ·
      refine ⟨12809135672352725085728957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539423781568483390485971 12809135672352725085728957)
      ·
        refine ⟨4803425877132271907148359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12809135672352725085728957 4803425877132271907148359)
        ·
          refine ⟨7205138815698407860722539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803425877132271907148359 7205138815698407860722539)
          ·
            refine ⟨10807708223547611791083809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7205138815698407860722539 10807708223547611791083809)
            ·
              refine ⟨8105781167660708843312857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10807708223547611791083809 8105781167660708843312857)
              ·
                refine ⟨6079335875745531632484643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8105781167660708843312857 6079335875745531632484643)
                ·
                  refine ⟨9119003813618297448726965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079335875745531632484643 9119003813618297448726965)
                  ·
                    refine ⟨854906607526715385818153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9119003813618297448726965 854906607526715385818153)
                    ·
                      rfl

theorem cell23_4994774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4994774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994774 prefixEnd_4994774 := by exact prefixLift 4994774
  have htrace : WordTrace (prefixWord ++ tailWord_4994774) baseStart_4994774 baseEnd_4994774 := by
    simpa [prefixWord, tailWord_4994774, baseEnd_4994774] using wordTrace_append hprefix tailTrace_4994774
  have hstable : (prefixWord ++ tailWord_4994774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994774).length < 2 ^ (prefixWord ++ tailWord_4994774).sum := by decide
  have hdescent : baseEnd_4994774 < baseStart_4994774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994794 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_4994794 : Nat := 118140960795 + 4994794 * 2 ^ 59
def prefixEnd_4994794 : Nat := 4983230072969 + 3 ^ 40 * 4994794 * 2
def baseEnd_4994794 : Nat := 2564730092193236079204367

theorem tailTrace_4994794 : CollatzResearch.WordTrace tailWord_4994794 prefixEnd_4994794 2564730092193236079204367 := by
  unfold tailWord_4994794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45543775866680463936523859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121450068977814570497396957 45543775866680463936523859)
  ·
    refine ⟨68315663800020695904785789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45543775866680463936523859 68315663800020695904785789)
    ·
      refine ⟨25618373925007760964294671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68315663800020695904785789 25618373925007760964294671)
      ·
        refine ⟨38427560887511641446442007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25618373925007760964294671 38427560887511641446442007)
        ·
          refine ⟨57641341331267462169663011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38427560887511641446442007 57641341331267462169663011)
          ·
            refine ⟨86462011996901193254494517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57641341331267462169663011 86462011996901193254494517)
            ·
              refine ⟨8105813624709486867608861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86462011996901193254494517 8105813624709486867608861)
              ·
                refine ⟨3039680109266057575353323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8105813624709486867608861 3039680109266057575353323)
                ·
                  refine ⟨4559520163899086363029985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039680109266057575353323 4559520163899086363029985)
                  ·
                    refine ⟨3419640122924314772272489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4559520163899086363029985 3419640122924314772272489)
                    ·
                      refine ⟨2564730092193236079204367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419640122924314772272489 2564730092193236079204367)
                      ·
                        rfl

theorem cell23_4994794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_4994794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994794 prefixEnd_4994794 := by exact prefixLift 4994794
  have htrace : WordTrace (prefixWord ++ tailWord_4994794) baseStart_4994794 baseEnd_4994794 := by
    simpa [prefixWord, tailWord_4994794, baseEnd_4994794] using wordTrace_append hprefix tailTrace_4994794
  have hstable : (prefixWord ++ tailWord_4994794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994794).length < 2 ^ (prefixWord ++ tailWord_4994794).sum := by decide
  have hdescent : baseEnd_4994794 < baseStart_4994794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994810 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_4994810 : Nat := 118140960795 + 4994810 * 2 ^ 59
def prefixEnd_4994810 : Nat := 4983230072969 + 3 ^ 40 * 4994810 * 2
def baseEnd_4994810 : Nat := 2564738307883708016604293

theorem tailTrace_4994810 : CollatzResearch.WordTrace tailWord_4994810 prefixEnd_4994810 2564738307883708016604293 := by
  unfold tailWord_4994810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45543921758665972619669471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121450458023109260319118589 45543921758665972619669471)
  ·
    refine ⟨68315882637998958929504207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45543921758665972619669471 68315882637998958929504207)
    ·
      refine ⟨102473823956998438394256311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68315882637998958929504207 102473823956998438394256311)
      ·
        refine ⟨153710735935497657591384467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102473823956998438394256311 153710735935497657591384467)
        ·
          refine ⟨230566103903246486387076701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153710735935497657591384467 230566103903246486387076701)
          ·
            refine ⟨86462288963717432395153763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230566103903246486387076701 86462288963717432395153763)
            ·
              refine ⟨129693433445576148592730645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86462288963717432395153763 129693433445576148592730645)
              ·
                refine ⟨6079379692761381965284249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129693433445576148592730645 6079379692761381965284249)
                ·
                  refine ⟨4559534769571036473963187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079379692761381965284249 4559534769571036473963187)
                  ·
                    refine ⟨6839302154356554710944781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559534769571036473963187 6839302154356554710944781)
                    ·
                      refine ⟨2564738307883708016604293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839302154356554710944781 2564738307883708016604293)
                      ·
                        rfl

theorem cell23_4994810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_4994810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994810 prefixEnd_4994810 := by exact prefixLift 4994810
  have htrace : WordTrace (prefixWord ++ tailWord_4994810) baseStart_4994810 baseEnd_4994810 := by
    simpa [prefixWord, tailWord_4994810, baseEnd_4994810] using wordTrace_append hprefix tailTrace_4994810
  have hstable : (prefixWord ++ tailWord_4994810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994810).length < 2 ^ (prefixWord ++ tailWord_4994810).sum := by decide
  have hdescent : baseEnd_4994810 < baseStart_4994810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994816 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4994816 : Nat := 118140960795 + 4994816 * 2 ^ 59
def prefixEnd_4994816 : Nat := 4983230072969 + 3 ^ 40 * 4994816 * 2
def baseEnd_4994816 : Nat := 2564741388767634993129265

theorem tailTrace_4994816 : CollatzResearch.WordTrace tailWord_4994816 prefixEnd_4994816 2564741388767634993129265 := by
  unfold tailWord_4994816
  simp only [CollatzResearch.WordTrace]
  refine ⟨91087952936321076751698151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121450603915094769002264201 91087952936321076751698151)
  ·
    refine ⟨136631929404481615127547227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91087952936321076751698151 136631929404481615127547227)
    ·
      refine ⟨204947894106722422691320841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136631929404481615127547227 204947894106722422691320841)
      ·
        refine ⟨153710920580041817018490631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204947894106722422691320841 153710920580041817018490631)
        ·
          refine ⟨230566380870062725527735947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153710920580041817018490631 230566380870062725527735947)
          ·
            refine ⟨345849571305094088291603921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230566380870062725527735947 345849571305094088291603921)
            ·
              refine ⟨259387178478820566218702941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345849571305094088291603921 259387178478820566218702941)
              ·
                refine ⟨97270191929557712332013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259387178478820566218702941 97270191929557712332013603)
                ·
                  refine ⟨145905287894336568498020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97270191929557712332013603 145905287894336568498020405)
                  ·
                    refine ⟨13678620740094053296689413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145905287894336568498020405 13678620740094053296689413)
                    ·
                      refine ⟨2564741388767634993129265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13678620740094053296689413 2564741388767634993129265)
                      ·
                        rfl

theorem cell23_4994816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4994816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994816 prefixEnd_4994816 := by exact prefixLift 4994816
  have htrace : WordTrace (prefixWord ++ tailWord_4994816) baseStart_4994816 baseEnd_4994816 := by
    simpa [prefixWord, tailWord_4994816, baseEnd_4994816] using wordTrace_append hprefix tailTrace_4994816
  have hstable : (prefixWord ++ tailWord_4994816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994816).length < 2 ^ (prefixWord ++ tailWord_4994816).sum := by decide
  have hdescent : baseEnd_4994816 < baseStart_4994816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994827 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 2, 1, 3]
def baseStart_4994827 : Nat := 118140960795 + 4994827 * 2 ^ 59
def prefixEnd_4994827 : Nat := 4983230072969 + 3 ^ 40 * 4994827 * 2
def baseEnd_4994827 : Nat := 2564747037054834450091715

theorem tailTrace_4994827 : CollatzResearch.WordTrace tailWord_4994827 prefixEnd_4994827 2564747037054834450091715 := by
  unfold tailWord_4994827
  simp only [CollatzResearch.WordTrace]
  refine ⟨182176307075602302382046735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121450871383734868254697823 182176307075602302382046735)
  ·
    refine ⟨273264460613403453573070103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182176307075602302382046735 273264460613403453573070103)
    ·
      refine ⟨409896690920105180359605155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273264460613403453573070103 409896690920105180359605155)
      ·
        refine ⟨614845036380157770539407733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409896690920105180359605155 614845036380157770539407733)
        ·
          refine ⟨57641722160639790988069475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 614845036380157770539407733 57641722160639790988069475)
          ·
            refine ⟨86462583240959686482104213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57641722160639790988069475 86462583240959686482104213)
            ·
              refine ⟨4052933589419985303848635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86462583240959686482104213 4052933589419985303848635)
              ·
                refine ⟨6079400384129977955772953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052933589419985303848635 6079400384129977955772953)
                ·
                  refine ⟨4559550288097483466829715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079400384129977955772953 4559550288097483466829715)
                  ·
                    refine ⟨6839325432146225200244573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559550288097483466829715 6839325432146225200244573)
                    ·
                      refine ⟨2564747037054834450091715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839325432146225200244573 2564747037054834450091715)
                      ·
                        rfl

theorem cell23_4994827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 1, 3].length) (baseStart_4994827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994827 prefixEnd_4994827 := by exact prefixLift 4994827
  have htrace : WordTrace (prefixWord ++ tailWord_4994827) baseStart_4994827 baseEnd_4994827 := by
    simpa [prefixWord, tailWord_4994827, baseEnd_4994827] using wordTrace_append hprefix tailTrace_4994827
  have hstable : (prefixWord ++ tailWord_4994827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994827).length < 2 ^ (prefixWord ++ tailWord_4994827).sum := by decide
  have hdescent : baseEnd_4994827 < baseStart_4994827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994837 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_4994837 : Nat := 118140960795 + 4994837 * 2 ^ 59
def prefixEnd_4994837 : Nat := 4983230072969 + 3 ^ 40 * 4994837 * 2
def baseEnd_4994837 : Nat := 2564752171861379410966669

theorem tailTrace_4994837 : CollatzResearch.WordTrace tailWord_4994837 prefixEnd_4994837 2564752171861379410966669 := by
  unfold tailWord_4994837
  simp only [CollatzResearch.WordTrace]
  refine ⟨182176671805566074089910765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121451114537044049393273843 182176671805566074089910765)
  ·
    refine ⟨68316251927087277783716537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182176671805566074089910765 68316251927087277783716537)
    ·
      refine ⟨51237188945315458337787403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68316251927087277783716537 51237188945315458337787403)
      ·
        refine ⟨76855783417973187506681105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51237188945315458337787403 76855783417973187506681105)
        ·
          refine ⟨57641837563479890630010829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76855783417973187506681105 57641837563479890630010829)
          ·
            refine ⟨21615689086304958986254061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57641837563479890630010829 21615689086304958986254061)
            ·
              refine ⟨8105883407364359619845273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21615689086304958986254061 8105883407364359619845273)
              ·
                refine ⟨6079412555523269714883955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8105883407364359619845273 6079412555523269714883955)
                ·
                  refine ⟨9119118833284904572325933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079412555523269714883955 9119118833284904572325933)
                  ·
                    refine ⟨3419669562481839214622225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9119118833284904572325933 3419669562481839214622225)
                    ·
                      refine ⟨2564752171861379410966669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3419669562481839214622225 2564752171861379410966669)
                      ·
                        rfl

theorem cell23_4994837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_4994837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994837 prefixEnd_4994837 := by exact prefixLift 4994837
  have htrace : WordTrace (prefixWord ++ tailWord_4994837) baseStart_4994837 baseEnd_4994837 := by
    simpa [prefixWord, tailWord_4994837, baseEnd_4994837] using wordTrace_append hprefix tailTrace_4994837
  have hstable : (prefixWord ++ tailWord_4994837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994837).length < 2 ^ (prefixWord ++ tailWord_4994837).sum := by decide
  have hdescent : baseEnd_4994837 < baseStart_4994837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994853 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_4994853 : Nat := 118140960795 + 4994853 * 2 ^ 59
def prefixEnd_4994853 : Nat := 4983230072969 + 3 ^ 40 * 4994853 * 2
def baseEnd_4994853 : Nat := 2564760387551851348366595

theorem tailTrace_4994853 : CollatzResearch.WordTrace tailWord_4994853 prefixEnd_4994853 2564760387551851348366595 := by
  unfold tailWord_4994853
  simp only [CollatzResearch.WordTrace]
  refine ⟨182177255373508108822493213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121451503582338739214995475 182177255373508108822493213)
  ·
    refine ⟨68316470765065540808434955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182177255373508108822493213 68316470765065540808434955)
    ·
      refine ⟨102474706147598311212652433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68316470765065540808434955 102474706147598311212652433)
      ·
        refine ⟨76856029610698733409489325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102474706147598311212652433 76856029610698733409489325)
        ·
          refine ⟨28821011104012025028558497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76856029610698733409489325 28821011104012025028558497)
          ·
            refine ⟨21615758328009018771418873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28821011104012025028558497 21615758328009018771418873)
            ·
              refine ⟨16211818746006764078564155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21615758328009018771418873 16211818746006764078564155)
              ·
                refine ⟨24317728119010146117846233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16211818746006764078564155 24317728119010146117846233)
                ·
                  refine ⟨18238296089257609588384675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24317728119010146117846233 18238296089257609588384675)
                  ·
                    refine ⟨27357444133886414382577013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18238296089257609588384675 27357444133886414382577013)
                    ·
                      refine ⟨2564760387551851348366595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27357444133886414382577013 2564760387551851348366595)
                      ·
                        rfl

theorem cell23_4994853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_4994853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994853 prefixEnd_4994853 := by exact prefixLift 4994853
  have htrace : WordTrace (prefixWord ++ tailWord_4994853) baseStart_4994853 baseEnd_4994853 := by
    simpa [prefixWord, tailWord_4994853, baseEnd_4994853] using wordTrace_append hprefix tailTrace_4994853
  have hstable : (prefixWord ++ tailWord_4994853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994853).length < 2 ^ (prefixWord ++ tailWord_4994853).sum := by decide
  have hdescent : baseEnd_4994853 < baseStart_4994853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994883 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3]
def baseStart_4994883 : Nat := 118140960795 + 4994883 * 2 ^ 59
def prefixEnd_4994883 : Nat := 4983230072969 + 3 ^ 40 * 4994883 * 2
def baseEnd_4994883 : Nat := 2564775791971486230991457

theorem tailTrace_4994883 : CollatzResearch.WordTrace tailWord_4994883 prefixEnd_4994883 2564775791971486230991457 := by
  unfold tailWord_4994883
  simp only [CollatzResearch.WordTrace]
  refine ⟨182178349563399423946085303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121452233042266282630723535 182178349563399423946085303)
  ·
    refine ⟨273267524345099135919127955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182178349563399423946085303 273267524345099135919127955)
    ·
      refine ⟨409901286517648703878691933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273267524345099135919127955 409901286517648703878691933)
      ·
        refine ⟨153712982444118263954509475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409901286517648703878691933 153712982444118263954509475)
        ·
          refine ⟨230569473666177395931764213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153712982444118263954509475 230569473666177395931764213)
          ·
            refine ⟨21615888156204130868602895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230569473666177395931764213 21615888156204130868602895)
            ·
              refine ⟨32423832234306196302904343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21615888156204130868602895 32423832234306196302904343)
              ·
                refine ⟨48635748351459294454356515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32423832234306196302904343 48635748351459294454356515)
                ·
                  refine ⟨72953622527188941681534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48635748351459294454356515 72953622527188941681534773)
                  ·
                    refine ⟨6839402111923963282643885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72953622527188941681534773 6839402111923963282643885)
                    ·
                      refine ⟨2564775791971486230991457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839402111923963282643885 2564775791971486230991457)
                      ·
                        rfl

theorem cell23_4994883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_4994883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994883 prefixEnd_4994883 := by exact prefixLift 4994883
  have htrace : WordTrace (prefixWord ++ tailWord_4994883) baseStart_4994883 baseEnd_4994883 := by
    simpa [prefixWord, tailWord_4994883, baseEnd_4994883] using wordTrace_append hprefix tailTrace_4994883
  have hstable : (prefixWord ++ tailWord_4994883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994883).length < 2 ^ (prefixWord ++ tailWord_4994883).sum := by decide
  have hdescent : baseEnd_4994883 < baseStart_4994883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994923 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4]
def baseStart_4994923 : Nat := 118140960795 + 4994923 * 2 ^ 59
def prefixEnd_4994923 : Nat := 4983230072969 + 3 ^ 40 * 4994923 * 2
def baseEnd_4994923 : Nat := 2564796331197666074491273

theorem tailTrace_4994923 : CollatzResearch.WordTrace tailWord_4994923 prefixEnd_4994923 2564796331197666074491273 := by
  unfold tailWord_4994923
  simp only [CollatzResearch.WordTrace]
  refine ⟨182179808483254510777541423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121453205655503007185027615 182179808483254510777541423)
  ·
    refine ⟨273269712724881766166312135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182179808483254510777541423 273269712724881766166312135)
    ·
      refine ⟨409904569087322649249468203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273269712724881766166312135 409904569087322649249468203)
      ·
        refine ⟨614856853630983973874202305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409904569087322649249468203 614856853630983973874202305)
        ·
          refine ⟨461142640223237980405651729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614856853630983973874202305 461142640223237980405651729)
          ·
            refine ⟨345856980167428485304238797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461142640223237980405651729 345856980167428485304238797)
            ·
              refine ⟨129696367562785681989089549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345856980167428485304238797 129696367562785681989089549)
              ·
                refine ⟨48636137836044630745908581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129696367562785681989089549 48636137836044630745908581)
                ·
                  refine ⟨9119275844258368264857859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48636137836044630745908581 9119275844258368264857859)
                  ·
                    refine ⟨13678913766387552397286789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9119275844258368264857859 13678913766387552397286789)
                    ·
                      refine ⟨2564796331197666074491273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13678913766387552397286789 2564796331197666074491273)
                      ·
                        rfl

theorem cell23_4994923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_4994923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994923 prefixEnd_4994923 := by exact prefixLift 4994923
  have htrace : WordTrace (prefixWord ++ tailWord_4994923) baseStart_4994923 baseEnd_4994923 := by
    simpa [prefixWord, tailWord_4994923, baseEnd_4994923] using wordTrace_append hprefix tailTrace_4994923
  have hstable : (prefixWord ++ tailWord_4994923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994923).length < 2 ^ (prefixWord ++ tailWord_4994923).sum := by decide
  have hdescent : baseEnd_4994923 < baseStart_4994923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994953 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_4994953 : Nat := 118140960795 + 4994953 * 2 ^ 59
def prefixEnd_4994953 : Nat := 4983230072969 + 3 ^ 40 * 4994953 * 2
def baseEnd_4994953 : Nat := 2564811735617300957116135

theorem tailTrace_4994953 : CollatzResearch.WordTrace tailWord_4994953 prefixEnd_4994953 2564811735617300957116135 := by
  unfold tailWord_4994953
  simp only [CollatzResearch.WordTrace]
  refine ⟨182180902673145825901133513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121453935115430550600755675 182180902673145825901133513)
  ·
    refine ⟨136635677004859369425850135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182180902673145825901133513 136635677004859369425850135)
    ·
      refine ⟨204953515507289054138775203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136635677004859369425850135 204953515507289054138775203)
      ·
        refine ⟨307430273260933581208162805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204953515507289054138775203 307430273260933581208162805)
        ·
          refine ⟨28821588118212523238265263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307430273260933581208162805 28821588118212523238265263)
          ·
            refine ⟨43232382177318784857397895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28821588118212523238265263 43232382177318784857397895)
            ·
              refine ⟨64848573265978177286096843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43232382177318784857397895 64848573265978177286096843)
              ·
                refine ⟨97272859898967265929145265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64848573265978177286096843 97272859898967265929145265)
                ·
                  refine ⟨72954644924225449446858949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97272859898967265929145265 72954644924225449446858949)
                  ·
                    refine ⟨13678995923292271771286053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72954644924225449446858949 13678995923292271771286053)
                    ·
                      refine ⟨2564811735617300957116135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13678995923292271771286053 2564811735617300957116135)
                      ·
                        rfl

theorem cell23_4994953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_4994953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994953 prefixEnd_4994953 := by exact prefixLift 4994953
  have htrace : WordTrace (prefixWord ++ tailWord_4994953) baseStart_4994953 baseEnd_4994953 := by
    simpa [prefixWord, tailWord_4994953, baseEnd_4994953] using wordTrace_append hprefix tailTrace_4994953
  have hstable : (prefixWord ++ tailWord_4994953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994953).length < 2 ^ (prefixWord ++ tailWord_4994953).sum := by decide
  have hdescent : baseEnd_4994953 < baseStart_4994953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994997 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 6]
def baseStart_4994997 : Nat := 118140960795 + 4994997 * 2 ^ 59
def prefixEnd_4994997 : Nat := 4983230072969 + 3 ^ 40 * 4994997 * 2
def baseEnd_4994997 : Nat := 284981592085122087218437

theorem tailTrace_4994997 : CollatzResearch.WordTrace tailWord_4994997 prefixEnd_4994997 284981592085122087218437 := by
  unfold tailWord_4994997
  simp only [CollatzResearch.WordTrace]
  refine ⟨182182507484986421415735245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121455004989990947610490163 182182507484986421415735245)
  ·
    refine ⟨68318440306869908030900717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182182507484986421415735245 68318440306869908030900717)
    ·
      refine ⟨25619415115076215511587769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68318440306869908030900717 25619415115076215511587769)
      ·
        refine ⟨19214561336307161633690827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25619415115076215511587769 19214561336307161633690827)
        ·
          refine ⟨28821842004460742450536241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19214561336307161633690827 28821842004460742450536241)
          ·
            refine ⟨21616381503345556837902181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28821842004460742450536241 21616381503345556837902181)
            ·
              refine ⟨4053071531877291907106659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21616381503345556837902181 4053071531877291907106659)
              ·
                refine ⟨6079607297815937860659989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053071531877291907106659 6079607297815937860659989)
                ·
                  refine ⟨284981592085122087218437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6079607297815937860659989 284981592085122087218437)
                  ·
                    rfl

theorem cell23_4994997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_4994997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4994997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4994997 prefixEnd_4994997 := by exact prefixLift 4994997
  have htrace : WordTrace (prefixWord ++ tailWord_4994997) baseStart_4994997 baseEnd_4994997 := by
    simpa [prefixWord, tailWord_4994997, baseEnd_4994997] using wordTrace_append hprefix tailTrace_4994997
  have hstable : (prefixWord ++ tailWord_4994997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994997).length < 2 ^ (prefixWord ++ tailWord_4994997).sum := by decide
  have hdescent : baseEnd_4994997 < baseStart_4994997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995040 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_4995040 : Nat := 118140960795 + 4995040 * 2 ^ 59
def prefixEnd_4995040 : Nat := 4983230072969 + 3 ^ 40 * 4995040 * 2
def baseEnd_4995040 : Nat := 854952136144747372242745

theorem tailTrace_4995040 : CollatzResearch.WordTrace tailWord_4995040 prefixEnd_4995040 854952136144747372242745 := by
  unfold tailWord_4995040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91092037911915319879775287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121456050549220426506367049 91092037911915319879775287)
  ·
    refine ⟨136638056867872979819662931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91092037911915319879775287 136638056867872979819662931)
    ·
      refine ⟨204957085301809469729494397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136638056867872979819662931 204957085301809469729494397)
      ·
        refine ⟨76858906988178551148560399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204957085301809469729494397 76858906988178551148560399)
        ·
          refine ⟨115288360482267826722840599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76858906988178551148560399 115288360482267826722840599)
          ·
            refine ⟨172932540723401740084260899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115288360482267826722840599 172932540723401740084260899)
            ·
              refine ⟨259398811085102610126391349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172932540723401740084260899 259398811085102610126391349)
              ·
                refine ⟨24318638539228369699349189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259398811085102610126391349 24318638539228369699349189)
                ·
                  refine ⟨4559744726105319318627973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24318638539228369699349189 4559744726105319318627973)
                  ·
                    refine ⟨854952136144747372242745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559744726105319318627973 854952136144747372242745)
                    ·
                      rfl

theorem cell23_4995040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_4995040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995040 prefixEnd_4995040 := by exact prefixLift 4995040
  have htrace : WordTrace (prefixWord ++ tailWord_4995040) baseStart_4995040 baseEnd_4995040 := by
    simpa [prefixWord, tailWord_4995040, baseEnd_4995040] using wordTrace_append hprefix tailTrace_4995040
  have hstable : (prefixWord ++ tailWord_4995040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995040).length < 2 ^ (prefixWord ++ tailWord_4995040).sum := by decide
  have hdescent : baseEnd_4995040 < baseStart_4995040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
