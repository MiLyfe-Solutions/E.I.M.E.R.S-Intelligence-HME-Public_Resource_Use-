import V185TrunkScan20Chunk015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_96069 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 2]
def baseStart_96069 : Nat := 118140960795 + 96069 * 2 ^ 59
def prefixEnd_96069 : Nat := 4983230072969 + 3 ^ 40 * 96069 * 2
def baseEnd_96069 : Nat := 43848509330568767373949

theorem tailTrace_96069 : CollatzResearch.WordTrace tailWord_96069 prefixEnd_96069 43848509330568767373949 := by
  unfold tailWord_96069
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503924288965895124059261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2335949525977263416039507 3503924288965895124059261)
  ·
    refine ⟨1313971608362210671522223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3503924288965895124059261 1313971608362210671522223)
    ·
      refine ⟨1970957412543316007283335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313971608362210671522223 1970957412543316007283335)
      ·
        refine ⟨2956436118814974010925003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970957412543316007283335 2956436118814974010925003)
        ·
          refine ⟨4434654178222461016387505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956436118814974010925003 4434654178222461016387505)
          ·
            refine ⟨3325990633666845762290629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434654178222461016387505 3325990633666845762290629)
            ·
              refine ⟨623623243812533580429493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3325990633666845762290629 623623243812533580429493)
              ·
                refine ⟨58464679107425023165265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623623243812533580429493 58464679107425023165265)
                ·
                  refine ⟨43848509330568767373949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58464679107425023165265 43848509330568767373949)
                  ·
                    rfl

theorem cell20_96069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_96069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96069 prefixEnd_96069 := by exact prefixLift 96069
  have htrace : WordTrace (prefixWord ++ tailWord_96069) baseStart_96069 baseEnd_96069 := by
    simpa [prefixWord, tailWord_96069, baseEnd_96069] using wordTrace_append hprefix tailTrace_96069
  have hstable : (prefixWord ++ tailWord_96069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96069).length < 2 ^ (prefixWord ++ tailWord_96069).sum := by decide
  have hdescent : baseEnd_96069 < baseStart_96069 := by decide
  rcases family_descends (prefixWord ++ tailWord_96069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96076 : List Nat := [2, 2, 1, 3, 5, 7]
def baseStart_96076 : Nat := 118140960795 + 96076 * 2 ^ 59
def prefixEnd_96076 : Nat := 4983230072969 + 3 ^ 40 * 96076 * 2
def baseEnd_96076 : Nat := 1624137197085476079281

theorem tailTrace_96076 : CollatzResearch.WordTrace tailWord_96076 prefixEnd_96076 1624137197085476079281 := by
  unfold tailWord_96076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752089799970267659782041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2336119733293690213042721 1752089799970267659782041)
  ·
    refine ⟨1314067349977700744836531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1752089799970267659782041 1314067349977700744836531)
    ·
      refine ⟨1971101024966551117254797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314067349977700744836531 1971101024966551117254797)
      ·
        refine ⟨739162884362456668970549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1971101024966551117254797 739162884362456668970549)
        ·
          refine ⟨69296520408980312715989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 739162884362456668970549 69296520408980312715989)
          ·
            refine ⟨1624137197085476079281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69296520408980312715989 1624137197085476079281)
            ·
              rfl

theorem cell20_96076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 7].length) (baseStart_96076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96076 prefixEnd_96076 := by exact prefixLift 96076
  have htrace : WordTrace (prefixWord ++ tailWord_96076) baseStart_96076 baseEnd_96076 := by
    simpa [prefixWord, tailWord_96076, baseEnd_96076] using wordTrace_append hprefix tailTrace_96076
  have hstable : (prefixWord ++ tailWord_96076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96076).length < 2 ^ (prefixWord ++ tailWord_96076).sum := by decide
  have hdescent : baseEnd_96076 < baseStart_96076 := by decide
  rcases family_descends (prefixWord ++ tailWord_96076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96090 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_96090 : Nat := 118140960795 + 96090 * 2 ^ 59
def prefixEnd_96090 : Nat := 4983230072969 + 3 ^ 40 * 96090 * 2
def baseEnd_96090 : Nat := 43858094302786027673863

theorem tailTrace_96090 : CollatzResearch.WordTrace tailWord_96090 prefixEnd_96090 43858094302786027673863 := by
  unfold tailWord_96090
  simp only [CollatzResearch.WordTrace]
  refine ⟨876172555472453927643431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2336460147926543807049149 876172555472453927643431)
  ·
    refine ⟨1314258833208680891465147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876172555472453927643431 1314258833208680891465147)
    ·
      refine ⟨1971388249813021337197721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314258833208680891465147 1971388249813021337197721)
      ·
        refine ⟨1478541187359766002898291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971388249813021337197721 1478541187359766002898291)
        ·
          refine ⟨2217811781039649004347437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478541187359766002898291 2217811781039649004347437)
          ·
            refine ⟨831679417889868376630289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2217811781039649004347437 831679417889868376630289)
            ·
              refine ⟨623759563417401282472717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831679417889868376630289 623759563417401282472717)
              ·
                refine ⟨233909836281525480927269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623759563417401282472717 233909836281525480927269)
                ·
                  refine ⟨43858094302786027673863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233909836281525480927269 43858094302786027673863)
                  ·
                    rfl

theorem cell20_96090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_96090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96090 prefixEnd_96090 := by exact prefixLift 96090
  have htrace : WordTrace (prefixWord ++ tailWord_96090) baseStart_96090 baseEnd_96090 := by
    simpa [prefixWord, tailWord_96090, baseEnd_96090] using wordTrace_append hprefix tailTrace_96090
  have hstable : (prefixWord ++ tailWord_96090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96090).length < 2 ^ (prefixWord ++ tailWord_96090).sum := by decide
  have hdescent : baseEnd_96090 < baseStart_96090 := by decide
  rcases family_descends (prefixWord ++ tailWord_96090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96138 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_96138 : Nat := 118140960795 + 96138 * 2 ^ 59
def prefixEnd_96138 : Nat := 4983230072969 + 3 ^ 40 * 96138 * 2
def baseEnd_96138 : Nat := 43880002810711194073667

theorem tailTrace_96138 : CollatzResearch.WordTrace tailWord_96138 prefixEnd_96138 43880002810711194073667 := by
  unfold tailWord_96138
  simp only [CollatzResearch.WordTrace]
  refine ⟨876610231428979977080267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2337627283810613272214045 876610231428979977080267)
  ·
    refine ⟨1314915347143469965620401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876610231428979977080267 1314915347143469965620401)
    ·
      refine ⟨986186510357602474215301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1314915347143469965620401 986186510357602474215301)
      ·
        refine ⟨184909970692050463915369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 986186510357602474215301 184909970692050463915369)
        ·
          refine ⟨138682478019037847936527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184909970692050463915369 138682478019037847936527)
          ·
            refine ⟨208023717028556771904791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138682478019037847936527 208023717028556771904791)
            ·
              refine ⟨312035575542835157857187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208023717028556771904791 312035575542835157857187)
              ·
                refine ⟨468053363314252736785781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312035575542835157857187 468053363314252736785781)
                ·
                  refine ⟨43880002810711194073667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468053363314252736785781 43880002810711194073667)
                  ·
                    rfl

theorem cell20_96138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_96138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96138 prefixEnd_96138 := by exact prefixLift 96138
  have htrace : WordTrace (prefixWord ++ tailWord_96138) baseStart_96138 baseEnd_96138 := by
    simpa [prefixWord, tailWord_96138, baseEnd_96138] using wordTrace_append hprefix tailTrace_96138
  have hstable : (prefixWord ++ tailWord_96138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96138).length < 2 ^ (prefixWord ++ tailWord_96138).sum := by decide
  have hdescent : baseEnd_96138 < baseStart_96138 := by decide
  rcases family_descends (prefixWord ++ tailWord_96138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96145 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 2]
def baseStart_96145 : Nat := 118140960795 + 96145 * 2 ^ 59
def prefixEnd_96145 : Nat := 4983230072969 + 3 ^ 40 * 96145 * 2
def baseEnd_96145 : Nat := 43883197801450280840305

theorem tailTrace_96145 : CollatzResearch.WordTrace tailWord_96145 prefixEnd_96145 43883197801450280840305 := by
  unfold tailWord_96145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506696236690560103825889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2337797491127040069217259 3506696236690560103825889)
  ·
    refine ⟨2630022177517920077869417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3506696236690560103825889 2630022177517920077869417)
    ·
      refine ⟨1972516633138440058402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2630022177517920077869417 1972516633138440058402063)
      ·
        refine ⟨2958774949707660087603095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972516633138440058402063 2958774949707660087603095)
        ·
          refine ⟨4438162424561490131404643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958774949707660087603095 4438162424561490131404643)
          ·
            refine ⟨6657243636842235197106965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438162424561490131404643 6657243636842235197106965)
            ·
              refine ⟨312058295476979774864389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6657243636842235197106965 312058295476979774864389)
              ·
                refine ⟨58510930401933707787073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312058295476979774864389 58510930401933707787073)
                ·
                  refine ⟨43883197801450280840305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58510930401933707787073 43883197801450280840305)
                  ·
                    rfl

theorem cell20_96145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_96145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96145 prefixEnd_96145 := by exact prefixLift 96145
  have htrace : WordTrace (prefixWord ++ tailWord_96145) baseStart_96145 baseEnd_96145 := by
    simpa [prefixWord, tailWord_96145, baseEnd_96145] using wordTrace_append hprefix tailTrace_96145
  have hstable : (prefixWord ++ tailWord_96145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96145).length < 2 ^ (prefixWord ++ tailWord_96145).sum := by decide
  have hdescent : baseEnd_96145 < baseStart_96145 := by decide
  rcases family_descends (prefixWord ++ tailWord_96145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96187 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_96187 : Nat := 118140960795 + 96187 * 2 ^ 59
def prefixEnd_96187 : Nat := 4983230072969 + 3 ^ 40 * 96187 * 2
def baseEnd_96187 : Nat := 43902367745884801440133

theorem tailTrace_96187 : CollatzResearch.WordTrace tailWord_96187 prefixEnd_96187 43902367745884801440133 := by
  unfold tailWord_96187
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508228102538401276854815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2338818735025600851236543 3508228102538401276854815)
  ·
    refine ⟨5262342153807601915282223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3508228102538401276854815 5262342153807601915282223)
    ·
      refine ⟨7893513230711402872923335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262342153807601915282223 7893513230711402872923335)
      ·
        refine ⟨11840269846067104309385003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893513230711402872923335 11840269846067104309385003)
        ·
          refine ⟨17760404769100656464077505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840269846067104309385003 17760404769100656464077505)
          ·
            refine ⟨13320303576825492348058129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17760404769100656464077505 13320303576825492348058129)
            ·
              refine ⟨9990227682619119261043597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13320303576825492348058129 9990227682619119261043597)
              ·
                refine ⟨3746335380982169722891349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9990227682619119261043597 3746335380982169722891349)
                ·
                  refine ⟨43902367745884801440133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3746335380982169722891349 43902367745884801440133)
                  ·
                    rfl

theorem cell20_96187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_96187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96187 prefixEnd_96187 := by exact prefixLift 96187
  have htrace : WordTrace (prefixWord ++ tailWord_96187) baseStart_96187 baseEnd_96187 := by
    simpa [prefixWord, tailWord_96187, baseEnd_96187] using wordTrace_append hprefix tailTrace_96187
  have hstable : (prefixWord ++ tailWord_96187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96187).length < 2 ^ (prefixWord ++ tailWord_96187).sum := by decide
  have hdescent : baseEnd_96187 < baseStart_96187 := by decide
  rcases family_descends (prefixWord ++ tailWord_96187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96190 : List Nat := [4, 2, 1, 1, 1, 5, 6]
def baseStart_96190 : Nat := 118140960795 + 96190 * 2 ^ 59
def prefixEnd_96190 : Nat := 4983230072969 + 3 ^ 40 * 96190 * 2
def baseEnd_96190 : Nat := 4878193003070013815569

theorem tailTrace_96190 : CollatzResearch.WordTrace tailWord_96190 prefixEnd_96190 4878193003070013815569 := by
  unfold tailWord_96190
  simp only [CollatzResearch.WordTrace]
  refine ⟨438542190190941598651753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2338891681018355192809349 438542190190941598651753)
  ·
    refine ⟨328906642643206198988815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 438542190190941598651753 328906642643206198988815)
    ·
      refine ⟨493359963964809298483223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328906642643206198988815 493359963964809298483223)
      ·
        refine ⟨740039945947213947724835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493359963964809298483223 740039945947213947724835)
        ·
          refine ⟨1110059918920820921587253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740039945947213947724835 1110059918920820921587253)
          ·
            refine ⟨104068117398826961398805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1110059918920820921587253 104068117398826961398805)
            ·
              refine ⟨4878193003070013815569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104068117398826961398805 4878193003070013815569)
              ·
                rfl

theorem cell20_96190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_96190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96190 prefixEnd_96190 := by exact prefixLift 96190
  have htrace : WordTrace (prefixWord ++ tailWord_96190) baseStart_96190 baseEnd_96190 := by
    simpa [prefixWord, tailWord_96190, baseEnd_96190] using wordTrace_append hprefix tailTrace_96190
  have hstable : (prefixWord ++ tailWord_96190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96190).length < 2 ^ (prefixWord ++ tailWord_96190).sum := by decide
  have hdescent : baseEnd_96190 < baseStart_96190 := by decide
  rcases family_descends (prefixWord ++ tailWord_96190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96210 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_96210 : Nat := 118140960795 + 96210 * 2 ^ 59
def prefixEnd_96210 : Nat := 4983230072969 + 3 ^ 40 * 96210 * 2
def baseEnd_96210 : Nat := 43912865572598943673373

theorem tailTrace_96210 : CollatzResearch.WordTrace tailWord_96210 prefixEnd_96210 43912865572598943673373 := by
  unfold tailWord_96210
  simp only [CollatzResearch.WordTrace]
  refine ⟨877266745363769051235521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2339377987636717469961389 877266745363769051235521)
  ·
    refine ⟨657950059022826788426641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 877266745363769051235521 657950059022826788426641)
    ·
      refine ⟨493462544267120091319981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 657950059022826788426641 493462544267120091319981)
      ·
        refine ⟨185048454100170034244993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493462544267120091319981 185048454100170034244993)
        ·
          refine ⟨138786340575127525683745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185048454100170034244993 138786340575127525683745)
          ·
            refine ⟨104089755431345644262809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138786340575127525683745 104089755431345644262809)
            ·
              refine ⟨78067316573509233197107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104089755431345644262809 78067316573509233197107)
              ·
                refine ⟨117100974860263849795661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78067316573509233197107 117100974860263849795661)
                ·
                  refine ⟨43912865572598943673373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117100974860263849795661 43912865572598943673373)
                  ·
                    rfl

theorem cell20_96210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_96210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96210 prefixEnd_96210 := by exact prefixLift 96210
  have htrace : WordTrace (prefixWord ++ tailWord_96210) baseStart_96210 baseEnd_96210 := by
    simpa [prefixWord, tailWord_96210, baseEnd_96210] using wordTrace_append hprefix tailTrace_96210
  have hstable : (prefixWord ++ tailWord_96210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96210).length < 2 ^ (prefixWord ++ tailWord_96210).sum := by decide
  have hdescent : baseEnd_96210 < baseStart_96210 := by decide
  rcases family_descends (prefixWord ++ tailWord_96210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96280 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_96280 : Nat := 118140960795 + 96280 * 2 ^ 59
def prefixEnd_96280 : Nat := 4983230072969 + 3 ^ 40 * 96280 * 2
def baseEnd_96280 : Nat := 43944815479989811339753

theorem tailTrace_96280 : CollatzResearch.WordTrace tailWord_96280 prefixEnd_96280 43944815479989811339753 := by
  unfold tailWord_96280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755810045600739079995147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2341080060800985439993529 1755810045600739079995147)
  ·
    refine ⟨2633715068401108619992721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755810045600739079995147 2633715068401108619992721)
    ·
      refine ⟨1975286301300831464994541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2633715068401108619992721 1975286301300831464994541)
      ·
        refine ⟨740732362987811799372953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1975286301300831464994541 740732362987811799372953)
        ·
          refine ⟨555549272240858849529715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740732362987811799372953 555549272240858849529715)
          ·
            refine ⟨833323908361288274294573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555549272240858849529715 833323908361288274294573)
            ·
              refine ⟨312496465635483102860465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833323908361288274294573 312496465635483102860465)
              ·
                refine ⟨234372349226612327145349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312496465635483102860465 234372349226612327145349)
                ·
                  refine ⟨43944815479989811339753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234372349226612327145349 43944815479989811339753)
                  ·
                    rfl

theorem cell20_96280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_96280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96280 prefixEnd_96280 := by exact prefixLift 96280
  have htrace : WordTrace (prefixWord ++ tailWord_96280) baseStart_96280 baseEnd_96280 := by
    simpa [prefixWord, tailWord_96280, baseEnd_96280] using wordTrace_append hprefix tailTrace_96280
  have hstable : (prefixWord ++ tailWord_96280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96280).length < 2 ^ (prefixWord ++ tailWord_96280).sum := by decide
  have hdescent : baseEnd_96280 < baseStart_96280 := by decide
  rcases family_descends (prefixWord ++ tailWord_96280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96311 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_96311 : Nat := 118140960795 + 96311 * 2 ^ 59
def prefixEnd_96311 : Nat := 4983230072969 + 3 ^ 40 * 96311 * 2
def baseEnd_96311 : Nat := 43958964724691481306293

theorem tailTrace_96311 : CollatzResearch.WordTrace tailWord_96311 prefixEnd_96311 43958964724691481306293 := by
  unfold tailWord_96311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512750754089170454368787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2341833836059446969579191 3512750754089170454368787)
  ·
    refine ⟨5269126131133755681553181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512750754089170454368787 5269126131133755681553181)
    ·
      refine ⟨1975922299175158380582443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5269126131133755681553181 1975922299175158380582443)
      ·
        refine ⟨2963883448762737570873665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975922299175158380582443 2963883448762737570873665)
        ·
          refine ⟨2222912586572053178155249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963883448762737570873665 2222912586572053178155249)
          ·
            refine ⟨1667184439929039883616437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222912586572053178155249 1667184439929039883616437)
            ·
              refine ⟨156298541243347489089041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1667184439929039883616437 156298541243347489089041)
              ·
                refine ⟨117223905932510616816781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156298541243347489089041 117223905932510616816781)
                ·
                  refine ⟨43958964724691481306293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117223905932510616816781 43958964724691481306293)
                  ·
                    rfl

theorem cell20_96311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_96311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96311 prefixEnd_96311 := by exact prefixLift 96311
  have htrace : WordTrace (prefixWord ++ tailWord_96311) baseStart_96311 baseEnd_96311 := by
    simpa [prefixWord, tailWord_96311, baseEnd_96311] using wordTrace_append hprefix tailTrace_96311
  have hstable : (prefixWord ++ tailWord_96311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96311).length < 2 ^ (prefixWord ++ tailWord_96311).sum := by decide
  have hdescent : baseEnd_96311 < baseStart_96311 := by decide
  rcases family_descends (prefixWord ++ tailWord_96311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96338 : List Nat := [3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_96338 : Nat := 118140960795 + 96338 * 2 ^ 59
def prefixEnd_96338 : Nat := 4983230072969 + 3 ^ 40 * 96338 * 2
def baseEnd_96338 : Nat := 14657096086799795802061

theorem tailTrace_96338 : CollatzResearch.WordTrace tailWord_96338 prefixEnd_96338 14657096086799795802061 := by
  unfold tailWord_96338
  simp only [CollatzResearch.WordTrace]
  refine ⟨878433881247838516400417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2342490349994236043734445 878433881247838516400417)
  ·
    refine ⟨658825410935878887300313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 878433881247838516400417 658825410935878887300313)
    ·
      refine ⟨494119058201909165475235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 658825410935878887300313 494119058201909165475235)
      ·
        refine ⟨741178587302863748212853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494119058201909165475235 741178587302863748212853)
        ·
          refine ⟨69485492559643476394955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 741178587302863748212853 69485492559643476394955)
          ·
            refine ⟨104228238839465214592433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69485492559643476394955 104228238839465214592433)
            ·
              refine ⟨78171179129598910944325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104228238839465214592433 78171179129598910944325)
              ·
                refine ⟨14657096086799795802061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78171179129598910944325 14657096086799795802061)
                ·
                  rfl

theorem cell20_96338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_96338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96338 prefixEnd_96338 := by exact prefixLift 96338
  have htrace : WordTrace (prefixWord ++ tailWord_96338) baseStart_96338 baseEnd_96338 := by
    simpa [prefixWord, tailWord_96338, baseEnd_96338] using wordTrace_append hprefix tailTrace_96338
  have hstable : (prefixWord ++ tailWord_96338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96338).length < 2 ^ (prefixWord ++ tailWord_96338).sum := by decide
  have hdescent : baseEnd_96338 < baseStart_96338 := by decide
  rcases family_descends (prefixWord ++ tailWord_96338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96352 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_96352 : Nat := 118140960795 + 96352 * 2 ^ 59
def prefixEnd_96352 : Nat := 4983230072969 + 3 ^ 40 * 96352 * 2
def baseEnd_96352 : Nat := 43977678241877560939459

theorem tailTrace_96352 : CollatzResearch.WordTrace tailWord_96352 prefixEnd_96352 43977678241877560939459 := by
  unfold tailWord_96352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757123073470317228305655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2342830764627089637740873 1757123073470317228305655)
  ·
    refine ⟨2635684610205475842458483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1757123073470317228305655 2635684610205475842458483)
    ·
      refine ⟨3953526915308213763687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635684610205475842458483 3953526915308213763687725)
      ·
        refine ⟨1482572593240580161382897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3953526915308213763687725 1482572593240580161382897)
        ·
          refine ⟨1111929444930435121037173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482572593240580161382897 1111929444930435121037173)
          ·
            refine ⟨104243385462228292597235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1111929444930435121037173 104243385462228292597235)
            ·
              refine ⟨156365078193342438895853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104243385462228292597235 156365078193342438895853)
              ·
                refine ⟨58636904322503414585945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156365078193342438895853 58636904322503414585945)
                ·
                  refine ⟨43977678241877560939459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58636904322503414585945 43977678241877560939459)
                  ·
                    rfl

theorem cell20_96352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_96352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96352 prefixEnd_96352 := by exact prefixLift 96352
  have htrace : WordTrace (prefixWord ++ tailWord_96352) baseStart_96352 baseEnd_96352 := by
    simpa [prefixWord, tailWord_96352, baseEnd_96352] using wordTrace_append hprefix tailTrace_96352
  have hstable : (prefixWord ++ tailWord_96352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96352).length < 2 ^ (prefixWord ++ tailWord_96352).sum := by decide
  have hdescent : baseEnd_96352 < baseStart_96352 := by decide
  rcases family_descends (prefixWord ++ tailWord_96352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96387 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_96387 : Nat := 118140960795 + 96387 * 2 ^ 59
def prefixEnd_96387 : Nat := 4983230072969 + 3 ^ 40 * 96387 * 2
def baseEnd_96387 : Nat := 43993653195572994772649

theorem tailTrace_96387 : CollatzResearch.WordTrace tailWord_96387 prefixEnd_96387 43993653195572994772649 := by
  unfold tailWord_96387
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515522701813835434135415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343681801209223622756943 3515522701813835434135415)
  ·
    refine ⟨5273284052720753151203123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515522701813835434135415 5273284052720753151203123)
    ·
      refine ⟨7909926079081129726804685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273284052720753151203123 7909926079081129726804685)
      ·
        refine ⟨2966222279655423647551757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7909926079081129726804685 2966222279655423647551757)
        ·
          refine ⟨1112333354870783867831909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2966222279655423647551757 1112333354870783867831909)
          ·
            refine ⟨208562504038271975218483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1112333354870783867831909 208562504038271975218483)
            ·
              refine ⟨312843756057407962827725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208562504038271975218483 312843756057407962827725)
              ·
                refine ⟨117316408521527986060397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312843756057407962827725 117316408521527986060397)
                ·
                  refine ⟨43993653195572994772649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117316408521527986060397 43993653195572994772649)
                  ·
                    rfl

theorem cell20_96387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_96387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96387 prefixEnd_96387 := by exact prefixLift 96387
  have htrace : WordTrace (prefixWord ++ tailWord_96387) baseStart_96387 baseEnd_96387 := by
    simpa [prefixWord, tailWord_96387, baseEnd_96387] using wordTrace_append hprefix tailTrace_96387
  have hstable : (prefixWord ++ tailWord_96387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96387).length < 2 ^ (prefixWord ++ tailWord_96387).sum := by decide
  have hdescent : baseEnd_96387 < baseStart_96387 := by decide
  rcases family_descends (prefixWord ++ tailWord_96387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96439 : List Nat := [1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_96439 : Nat := 118140960795 + 96439 * 2 ^ 59
def prefixEnd_96439 : Nat := 4983230072969 + 3 ^ 40 * 96439 * 2
def baseEnd_96439 : Nat := 14672462470830641679701

theorem tailTrace_96439 : CollatzResearch.WordTrace tailWord_96439 prefixEnd_96439 14672462470830641679701 := by
  unfold tailWord_96439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517419297625448315028371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2344946198416965543352247 3517419297625448315028371)
  ·
    refine ⟨5276128946438172472542557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517419297625448315028371 5276128946438172472542557)
    ·
      refine ⟨1978548354914314677203459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5276128946438172472542557 1978548354914314677203459)
      ·
        refine ⟨2967822532371472015805189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978548354914314677203459 2967822532371472015805189)
        ·
          refine ⟨556466724819651002963473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2967822532371472015805189 556466724819651002963473)
          ·
            refine ⟨417350043614738252222605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556466724819651002963473 417350043614738252222605)
            ·
              refine ⟨156506266355526844583477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417350043614738252222605 156506266355526844583477)
              ·
                refine ⟨14672462470830641679701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156506266355526844583477 14672462470830641679701)
                ·
                  rfl

theorem cell20_96439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_96439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96439 prefixEnd_96439 := by exact prefixLift 96439
  have htrace : WordTrace (prefixWord ++ tailWord_96439) baseStart_96439 baseEnd_96439 := by
    simpa [prefixWord, tailWord_96439, baseEnd_96439] using wordTrace_append hprefix tailTrace_96439
  have hstable : (prefixWord ++ tailWord_96439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96439).length < 2 ^ (prefixWord ++ tailWord_96439).sum := by decide
  have hdescent : baseEnd_96439 < baseStart_96439 := by decide
  rcases family_descends (prefixWord ++ tailWord_96439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96453 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_96453 : Nat := 118140960795 + 96453 * 2 ^ 59
def prefixEnd_96453 : Nat := 4983230072969 + 3 ^ 40 * 96453 * 2
def baseEnd_96453 : Nat := 44023777393970098572379

theorem tailTrace_96453 : CollatzResearch.WordTrace tailWord_96453 prefixEnd_96453 44023777393970098572379 := by
  unfold tailWord_96453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517929919574728706038013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2345286613049819137358675 3517929919574728706038013)
  ·
    refine ⟨1319223719840523264764255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3517929919574728706038013 1319223719840523264764255)
    ·
      refine ⟨1978835579760784897146383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319223719840523264764255 1978835579760784897146383)
      ·
        refine ⟨2968253369641177345719575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978835579760784897146383 2968253369641177345719575)
        ·
          refine ⟨4452380054461766018579363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968253369641177345719575 4452380054461766018579363)
          ·
            refine ⟨6678570081692649027869045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452380054461766018579363 6678570081692649027869045)
            ·
              refine ⟨626115945158685846362723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6678570081692649027869045 626115945158685846362723)
              ·
                refine ⟨939173917738028769544085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626115945158685846362723 939173917738028769544085)
                ·
                  refine ⟨44023777393970098572379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 939173917738028769544085 44023777393970098572379)
                  ·
                    rfl

theorem cell20_96453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_96453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96453 prefixEnd_96453 := by exact prefixLift 96453
  have htrace : WordTrace (prefixWord ++ tailWord_96453) baseStart_96453 baseEnd_96453 := by
    simpa [prefixWord, tailWord_96453, baseEnd_96453] using wordTrace_append hprefix tailTrace_96453
  have hstable : (prefixWord ++ tailWord_96453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96453).length < 2 ^ (prefixWord ++ tailWord_96453).sum := by decide
  have hdescent : baseEnd_96453 < baseStart_96453 := by decide
  rcases family_descends (prefixWord ++ tailWord_96453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96466 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_96466 : Nat := 118140960795 + 96466 * 2 ^ 59
def prefixEnd_96466 : Nat := 4983230072969 + 3 ^ 40 * 96466 * 2
def baseEnd_96466 : Nat := 44029710948199831138993

theorem tailTrace_96466 : CollatzResearch.WordTrace tailWord_96466 prefixEnd_96466 44029710948199831138993 := by
  unfold tailWord_96466
  simp only [CollatzResearch.WordTrace]
  refine ⟨879601017131907981565313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2345602712351754617507501 879601017131907981565313)
  ·
    refine ⟨659700762848930986173985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 879601017131907981565313 659700762848930986173985)
    ·
      refine ⟨494775572136698239630489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 659700762848930986173985 494775572136698239630489)
      ·
        refine ⟨371081679102523679722867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494775572136698239630489 371081679102523679722867)
        ·
          refine ⟨556622518653785519584301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371081679102523679722867 556622518653785519584301)
          ·
            refine ⟨208733444495169569844113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556622518653785519584301 208733444495169569844113)
            ·
              refine ⟨156550083371377177383085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208733444495169569844113 156550083371377177383085)
              ·
                refine ⟨58706281264266441518657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156550083371377177383085 58706281264266441518657)
                ·
                  refine ⟨44029710948199831138993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58706281264266441518657 44029710948199831138993)
                  ·
                    rfl

theorem cell20_96466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_96466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96466 prefixEnd_96466 := by exact prefixLift 96466
  have htrace : WordTrace (prefixWord ++ tailWord_96466) baseStart_96466 baseEnd_96466 := by
    simpa [prefixWord, tailWord_96466, baseEnd_96466] using wordTrace_append hprefix tailTrace_96466
  have hstable : (prefixWord ++ tailWord_96466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96466).length < 2 ^ (prefixWord ++ tailWord_96466).sum := by decide
  have hdescent : baseEnd_96466 < baseStart_96466 := by decide
  rcases family_descends (prefixWord ++ tailWord_96466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96476 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_96476 : Nat := 118140960795 + 96476 * 2 ^ 59
def prefixEnd_96476 : Nat := 4983230072969 + 3 ^ 40 * 96476 * 2
def baseEnd_96476 : Nat := 44034275220684240805619

theorem tailTrace_96476 : CollatzResearch.WordTrace tailWord_96476 prefixEnd_96476 44034275220684240805619 := by
  unfold tailWord_96476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759384399245701817062641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2345845865660935756083521 1759384399245701817062641)
  ·
    refine ⟨1319538299434276362796981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1759384399245701817062641 1319538299434276362796981)
    ·
      refine ⟨123706715571963409012217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1319538299434276362796981 123706715571963409012217)
      ·
        refine ⟨92780036678972556759163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123706715571963409012217 92780036678972556759163)
        ·
          refine ⟨139170055018458835138745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92780036678972556759163 139170055018458835138745)
          ·
            refine ⟨104377541263844126354059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139170055018458835138745 104377541263844126354059)
            ·
              refine ⟨156566311895766189531089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104377541263844126354059 156566311895766189531089)
              ·
                refine ⟨117424733921824642148317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156566311895766189531089 117424733921824642148317)
                ·
                  refine ⟨44034275220684240805619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117424733921824642148317 44034275220684240805619)
                  ·
                    rfl

theorem cell20_96476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_96476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96476 prefixEnd_96476 := by exact prefixLift 96476
  have htrace : WordTrace (prefixWord ++ tailWord_96476) baseStart_96476 baseEnd_96476 := by
    simpa [prefixWord, tailWord_96476, baseEnd_96476] using wordTrace_append hprefix tailTrace_96476
  have hstable : (prefixWord ++ tailWord_96476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96476).length < 2 ^ (prefixWord ++ tailWord_96476).sum := by decide
  have hdescent : baseEnd_96476 < baseStart_96476 := by decide
  rcases family_descends (prefixWord ++ tailWord_96476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96487 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_96487 : Nat := 118140960795 + 96487 * 2 ^ 59
def prefixEnd_96487 : Nat := 4983230072969 + 3 ^ 40 * 96487 * 2
def baseEnd_96487 : Nat := 44039295920417091438907

theorem tailTrace_96487 : CollatzResearch.WordTrace tailWord_96487 prefixEnd_96487 44039295920417091438907 := by
  unfold tailWord_96487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519170001451552512775715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2346113334301035008517143 3519170001451552512775715)
  ·
    refine ⟨5278755002177328769163573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519170001451552512775715 5278755002177328769163573)
    ·
      refine ⟨494883281454124572109085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5278755002177328769163573 494883281454124572109085)
      ·
        refine ⟨185581230545296714540907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494883281454124572109085 185581230545296714540907)
        ·
          refine ⟨278371845817945071811361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185581230545296714540907 278371845817945071811361)
          ·
            refine ⟨208778884363458803858521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278371845817945071811361 208778884363458803858521)
            ·
              refine ⟨156584163272594102893891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208778884363458803858521 156584163272594102893891)
              ·
                refine ⟨234876244908891154340837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156584163272594102893891 234876244908891154340837)
                ·
                  refine ⟨44039295920417091438907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234876244908891154340837 44039295920417091438907)
                  ·
                    rfl

theorem cell20_96487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_96487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96487 prefixEnd_96487 := by exact prefixLift 96487
  have htrace : WordTrace (prefixWord ++ tailWord_96487) baseStart_96487 baseEnd_96487 := by
    simpa [prefixWord, tailWord_96487, baseEnd_96487] using wordTrace_append hprefix tailTrace_96487
  have hstable : (prefixWord ++ tailWord_96487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96487).length < 2 ^ (prefixWord ++ tailWord_96487).sum := by decide
  have hdescent : baseEnd_96487 < baseStart_96487 := by decide
  rcases family_descends (prefixWord ++ tailWord_96487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96508 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_96508 : Nat := 118140960795 + 96508 * 2 ^ 59
def prefixEnd_96508 : Nat := 4983230072969 + 3 ^ 40 * 96508 * 2
def baseEnd_96508 : Nat := 44048880892634351738821

theorem tailTrace_96508 : CollatzResearch.WordTrace tailWord_96508 prefixEnd_96508 44048880892634351738821 := by
  unfold tailWord_96508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759967967187736549645089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2346623956250315399526785 1759967967187736549645089)
  ·
    refine ⟨1319975975390802412233817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1759967967187736549645089 1319975975390802412233817)
    ·
      refine ⟨989981981543101809175363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1319975975390802412233817 989981981543101809175363)
      ·
        refine ⟨1484972972314652713763045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989981981543101809175363 1484972972314652713763045)
        ·
          refine ⟨278432432308997383830571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1484972972314652713763045 278432432308997383830571)
          ·
            refine ⟨417648648463496075745857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278432432308997383830571 417648648463496075745857)
            ·
              refine ⟨313236486347622056809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417648648463496075745857 313236486347622056809393)
              ·
                refine ⟨234927364760716542607045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313236486347622056809393 234927364760716542607045)
                ·
                  refine ⟨44048880892634351738821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234927364760716542607045 44048880892634351738821)
                  ·
                    rfl

theorem cell20_96508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_96508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96508 prefixEnd_96508 := by exact prefixLift 96508
  have htrace : WordTrace (prefixWord ++ tailWord_96508) baseStart_96508 baseEnd_96508 := by
    simpa [prefixWord, tailWord_96508, baseEnd_96508] using wordTrace_append hprefix tailTrace_96508
  have hstable : (prefixWord ++ tailWord_96508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96508).length < 2 ^ (prefixWord ++ tailWord_96508).sum := by decide
  have hdescent : baseEnd_96508 < baseStart_96508 := by decide
  rcases family_descends (prefixWord ++ tailWord_96508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96522 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_96522 : Nat := 118140960795 + 96522 * 2 ^ 59
def prefixEnd_96522 : Nat := 4983230072969 + 3 ^ 40 * 96522 * 2
def baseEnd_96522 : Nat := 44055270874112525272097

theorem tailTrace_96522 : CollatzResearch.WordTrace tailWord_96522 prefixEnd_96522 44055270874112525272097 := by
  unfold tailWord_96522
  simp only [CollatzResearch.WordTrace]
  refine ⟨880111639081188372574955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2346964370883168993533213 880111639081188372574955)
  ·
    refine ⟨1320167458621782558862433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 880111639081188372574955 1320167458621782558862433)
    ·
      refine ⟨990125593966336919146825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1320167458621782558862433 990125593966336919146825)
      ·
        refine ⟨742594195474752689360119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990125593966336919146825 742594195474752689360119)
        ·
          refine ⟨1113891293212129034040179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742594195474752689360119 1113891293212129034040179)
          ·
            refine ⟨1670836939818193551060269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113891293212129034040179 1670836939818193551060269)
            ·
              refine ⟨626563852431822581647601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670836939818193551060269 626563852431822581647601)
              ·
                refine ⟨469922889323866936235701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626563852431822581647601 469922889323866936235701)
                ·
                  refine ⟨44055270874112525272097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 469922889323866936235701 44055270874112525272097)
                  ·
                    rfl

theorem cell20_96522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_96522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96522 prefixEnd_96522 := by exact prefixLift 96522
  have htrace : WordTrace (prefixWord ++ tailWord_96522) baseStart_96522 baseEnd_96522 := by
    simpa [prefixWord, tailWord_96522, baseEnd_96522] using wordTrace_append hprefix tailTrace_96522
  have hstable : (prefixWord ++ tailWord_96522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96522).length < 2 ^ (prefixWord ++ tailWord_96522).sum := by decide
  have hdescent : baseEnd_96522 < baseStart_96522 := by decide
  rcases family_descends (prefixWord ++ tailWord_96522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96542 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_96542 : Nat := 118140960795 + 96542 * 2 ^ 59
def prefixEnd_96542 : Nat := 4983230072969 + 3 ^ 40 * 96542 * 2
def baseEnd_96542 : Nat := 44064399419081344605349

theorem tailTrace_96542 : CollatzResearch.WordTrace tailWord_96542 prefixEnd_96542 44064399419081344605349 := by
  unfold tailWord_96542
  simp only [CollatzResearch.WordTrace]
  refine ⟨440147002031537113253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2347450677501531270685253 440147002031537113253485)
  ·
    refine ⟨165055125761826417470057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 440147002031537113253485 165055125761826417470057)
    ·
      refine ⟨123791344321369813102543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165055125761826417470057 123791344321369813102543)
      ·
        refine ⟨185687016482054719653815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123791344321369813102543 185687016482054719653815)
        ·
          refine ⟨278530524723082079480723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185687016482054719653815 278530524723082079480723)
          ·
            refine ⟨417795787084623119221085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278530524723082079480723 417795787084623119221085)
            ·
              refine ⟨156673420156733669707907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417795787084623119221085 156673420156733669707907)
              ·
                refine ⟨235010130235100504561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156673420156733669707907 235010130235100504561861)
                ·
                  refine ⟨44064399419081344605349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235010130235100504561861 44064399419081344605349)
                  ·
                    rfl

theorem cell20_96542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_96542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96542 prefixEnd_96542 := by exact prefixLift 96542
  have htrace : WordTrace (prefixWord ++ tailWord_96542) baseStart_96542 baseEnd_96542 := by
    simpa [prefixWord, tailWord_96542, baseEnd_96542] using wordTrace_append hprefix tailTrace_96542
  have hstable : (prefixWord ++ tailWord_96542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96542).length < 2 ^ (prefixWord ++ tailWord_96542).sum := by decide
  have hdescent : baseEnd_96542 < baseStart_96542 := by decide
  rcases family_descends (prefixWord ++ tailWord_96542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96552 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_96552 : Nat := 118140960795 + 96552 * 2 ^ 59
def prefixEnd_96552 : Nat := 4983230072969 + 3 ^ 40 * 96552 * 2
def baseEnd_96552 : Nat := 44068963691565754271975

theorem tailTrace_96552 : CollatzResearch.WordTrace tailWord_96552 prefixEnd_96552 44068963691565754271975 := by
  unfold tailWord_96552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760770373108034306945955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2347693830810712409261273 1760770373108034306945955)
  ·
    refine ⟨2641155559662051460418933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760770373108034306945955 2641155559662051460418933)
    ·
      refine ⟨247608333718317324414275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2641155559662051460418933 247608333718317324414275)
      ·
        refine ⟨371412500577475986621413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247608333718317324414275 371412500577475986621413)
        ·
          refine ⟨69639843858276747491515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371412500577475986621413 69639843858276747491515)
          ·
            refine ⟨104459765787415121237273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69639843858276747491515 104459765787415121237273)
            ·
              refine ⟨78344824340561340927955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104459765787415121237273 78344824340561340927955)
              ·
                refine ⟨117517236510842011391933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78344824340561340927955 117517236510842011391933)
                ·
                  refine ⟨44068963691565754271975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117517236510842011391933 44068963691565754271975)
                  ·
                    rfl

theorem cell20_96552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_96552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96552 prefixEnd_96552 := by exact prefixLift 96552
  have htrace : WordTrace (prefixWord ++ tailWord_96552) baseStart_96552 baseEnd_96552 := by
    simpa [prefixWord, tailWord_96552, baseEnd_96552] using wordTrace_append hprefix tailTrace_96552
  have hstable : (prefixWord ++ tailWord_96552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96552).length < 2 ^ (prefixWord ++ tailWord_96552).sum := by decide
  have hdescent : baseEnd_96552 < baseStart_96552 := by decide
  rcases family_descends (prefixWord ++ tailWord_96552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_96567 : Nat := 118140960795 + 96567 * 2 ^ 59
def prefixEnd_96567 : Nat := 4983230072969 + 3 ^ 40 * 96567 * 2
def baseEnd_96567 : Nat := 44075810100292368771913

theorem tailTrace_96567 : CollatzResearch.WordTrace tailWord_96567 prefixEnd_96567 44075810100292368771913 := by
  unfold tailWord_96567
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522087841161726175687955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2348058560774484117125303 3522087841161726175687955)
  ·
    refine ⟨5283131761742589263531933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522087841161726175687955 5283131761742589263531933)
    ·
      refine ⟨1981174410653470973824475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5283131761742589263531933 1981174410653470973824475)
      ·
        refine ⟨2971761615980206460736713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981174410653470973824475 2971761615980206460736713)
        ·
          refine ⟨2228821211985154845552535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2971761615980206460736713 2228821211985154845552535)
          ·
            refine ⟨3343231817977732268328803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228821211985154845552535 3343231817977732268328803)
            ·
              refine ⟨5014847726966598402493205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343231817977732268328803 5014847726966598402493205)
              ·
                refine ⟨235070987201559300116869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5014847726966598402493205 235070987201559300116869)
                ·
                  refine ⟨44075810100292368771913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235070987201559300116869 44075810100292368771913)
                  ·
                    rfl

theorem cell20_96567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_96567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96567 prefixEnd_96567 := by exact prefixLift 96567
  have htrace : WordTrace (prefixWord ++ tailWord_96567) baseStart_96567 baseEnd_96567 := by
    simpa [prefixWord, tailWord_96567, baseEnd_96567] using wordTrace_append hprefix tailTrace_96567
  have hstable : (prefixWord ++ tailWord_96567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96567).length < 2 ^ (prefixWord ++ tailWord_96567).sum := by decide
  have hdescent : baseEnd_96567 < baseStart_96567 := by decide
  rcases family_descends (prefixWord ++ tailWord_96567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96597 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 2]
def baseStart_96597 : Nat := 118140960795 + 96597 * 2 ^ 59
def prefixEnd_96597 : Nat := 4983230072969 + 3 ^ 40 * 96597 * 2
def baseEnd_96597 : Nat := 44089502917745597771791

theorem tailTrace_96597 : CollatzResearch.WordTrace tailWord_96597 prefixEnd_96597 44089502917745597771791 := by
  unfold tailWord_96597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523182031053041299280045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2348788020702027532853363 3523182031053041299280045)
  ·
    refine ⟨1321193261644890487230017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3523182031053041299280045 1321193261644890487230017)
    ·
      refine ⟨990894946233667865422513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1321193261644890487230017 990894946233667865422513)
      ·
        refine ⟨743171209675250899066885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990894946233667865422513 743171209675250899066885)
        ·
          refine ⟨139344601814109543575041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 743171209675250899066885 139344601814109543575041)
          ·
            refine ⟨104508451360582157681281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139344601814109543575041 104508451360582157681281)
            ·
              refine ⟨78381338520436618260961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104508451360582157681281 78381338520436618260961)
              ·
                refine ⟨58786003890327463695721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78381338520436618260961 58786003890327463695721)
                ·
                  refine ⟨44089502917745597771791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58786003890327463695721 44089502917745597771791)
                  ·
                    rfl

theorem cell20_96597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_96597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96597 prefixEnd_96597 := by exact prefixLift 96597
  have htrace : WordTrace (prefixWord ++ tailWord_96597) baseStart_96597 baseEnd_96597 := by
    simpa [prefixWord, tailWord_96597, baseEnd_96597] using wordTrace_append hprefix tailTrace_96597
  have hstable : (prefixWord ++ tailWord_96597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96597).length < 2 ^ (prefixWord ++ tailWord_96597).sum := by decide
  have hdescent : baseEnd_96597 < baseStart_96597 := by decide
  rcases family_descends (prefixWord ++ tailWord_96597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96604 : List Nat := [2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_96604 : Nat := 118140960795 + 96604 * 2 ^ 59
def prefixEnd_96604 : Nat := 4983230072969 + 3 ^ 40 * 96604 * 2
def baseEnd_96604 : Nat := 14697565969494894846143

theorem tailTrace_96604 : CollatzResearch.WordTrace tailWord_96604 prefixEnd_96604 14697565969494894846143 := by
  unfold tailWord_96604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761718671013840747392433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2348958228018454329856577 1761718671013840747392433)
  ·
    refine ⟨1321289003260380560544325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1761718671013840747392433 1321289003260380560544325)
    ·
      refine ⟨247741688111321355102061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1321289003260380560544325 247741688111321355102061)
      ·
        refine ⟨92903133041745508163273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247741688111321355102061 92903133041745508163273)
        ·
          refine ⟨69677349781309131122455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92903133041745508163273 69677349781309131122455)
          ·
            refine ⟨104516024671963696683683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69677349781309131122455 104516024671963696683683)
            ·
              refine ⟨156774037007945545025525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104516024671963696683683 156774037007945545025525)
              ·
                refine ⟨14697565969494894846143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156774037007945545025525 14697565969494894846143)
                ·
                  rfl

theorem cell20_96604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_96604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96604 prefixEnd_96604 := by exact prefixLift 96604
  have htrace : WordTrace (prefixWord ++ tailWord_96604) baseStart_96604 baseEnd_96604 := by
    simpa [prefixWord, tailWord_96604, baseEnd_96604] using wordTrace_append hprefix tailTrace_96604
  have hstable : (prefixWord ++ tailWord_96604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96604).length < 2 ^ (prefixWord ++ tailWord_96604).sum := by decide
  have hdescent : baseEnd_96604 < baseStart_96604 := by decide
  rcases family_descends (prefixWord ++ tailWord_96604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96608 : List Nat := [2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_96608 : Nat := 118140960795 + 96608 * 2 ^ 59
def prefixEnd_96608 : Nat := 4983230072969 + 3 ^ 40 * 96608 * 2
def baseEnd_96608 : Nat := 14698174539159482801693

theorem tailTrace_96608 : CollatzResearch.WordTrace tailWord_96608 prefixEnd_96608 14698174539159482801693 := by
  unfold tailWord_96608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761791617006595088965239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2349055489342126785286985 1761791617006595088965239)
  ·
    refine ⟨2642687425509892633447859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1761791617006595088965239 2642687425509892633447859)
    ·
      refine ⟨3964031138264838950171789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642687425509892633447859 3964031138264838950171789)
      ·
        refine ⟨1486511676849314606314421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3964031138264838950171789 1486511676849314606314421)
        ·
          refine ⟨139360469704623244341977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1486511676849314606314421 139360469704623244341977)
          ·
            refine ⟨104520352278467433256483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139360469704623244341977 104520352278467433256483)
            ·
              refine ⟨156780528417701149884725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104520352278467433256483 156780528417701149884725)
              ·
                refine ⟨14698174539159482801693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156780528417701149884725 14698174539159482801693)
                ·
                  rfl

theorem cell20_96608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_96608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96608 prefixEnd_96608 := by exact prefixLift 96608
  have htrace : WordTrace (prefixWord ++ tailWord_96608) baseStart_96608 baseEnd_96608 := by
    simpa [prefixWord, tailWord_96608, baseEnd_96608] using wordTrace_append hprefix tailTrace_96608
  have hstable : (prefixWord ++ tailWord_96608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96608).length < 2 ^ (prefixWord ++ tailWord_96608).sum := by decide
  have hdescent : baseEnd_96608 < baseStart_96608 := by decide
  rcases family_descends (prefixWord ++ tailWord_96608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96615 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_96615 : Nat := 118140960795 + 96615 * 2 ^ 59
def prefixEnd_96615 : Nat := 4983230072969 + 3 ^ 40 * 96615 * 2
def baseEnd_96615 : Nat := 44097718608217535171717

theorem tailTrace_96615 : CollatzResearch.WordTrace tailWord_96615 prefixEnd_96615 44097718608217535171717 := by
  unfold tailWord_96615
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523838544987830373435299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2349225696658553582290199 3523838544987830373435299)
  ·
    refine ⟨5285757817481745560152949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523838544987830373435299 5285757817481745560152949)
    ·
      refine ⟨495539795388913646264339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5285757817481745560152949 495539795388913646264339)
      ·
        refine ⟨743309693083370469396509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495539795388913646264339 743309693083370469396509)
        ·
          refine ⟨278741134906263926023691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743309693083370469396509 278741134906263926023691)
          ·
            refine ⟨418111702359395889035537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278741134906263926023691 418111702359395889035537)
            ·
              refine ⟨313583776769546916776653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418111702359395889035537 313583776769546916776653)
              ·
                refine ⟨117593916288580093791245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313583776769546916776653 117593916288580093791245)
                ·
                  refine ⟨44097718608217535171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117593916288580093791245 44097718608217535171717)
                  ·
                    rfl

theorem cell20_96615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_96615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96615 prefixEnd_96615 := by exact prefixLift 96615
  have htrace : WordTrace (prefixWord ++ tailWord_96615) baseStart_96615 baseEnd_96615 := by
    simpa [prefixWord, tailWord_96615, baseEnd_96615] using wordTrace_append hprefix tailTrace_96615
  have hstable : (prefixWord ++ tailWord_96615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96615).length < 2 ^ (prefixWord ++ tailWord_96615).sum := by decide
  have hdescent : baseEnd_96615 < baseStart_96615 := by decide
  rcases family_descends (prefixWord ++ tailWord_96615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96712 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_96712 : Nat := 118140960795 + 96712 * 2 ^ 59
def prefixEnd_96712 : Nat := 4983230072969 + 3 ^ 40 * 96712 * 2
def baseEnd_96712 : Nat := 44141992051316308937987

theorem tailTrace_96712 : CollatzResearch.WordTrace tailWord_96712 prefixEnd_96712 44141992051316308937987 := by
  unfold tailWord_96712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763688212818207969858195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2351584283757610626477593 1763688212818207969858195)
  ·
    refine ⟨2645532319227311954787293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763688212818207969858195 2645532319227311954787293)
    ·
      refine ⟨992074619710241983045235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2645532319227311954787293 992074619710241983045235)
      ·
        refine ⟨1488111929565362974567853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992074619710241983045235 1488111929565362974567853)
        ·
          refine ⟨558041973587011115462945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1488111929565362974567853 558041973587011115462945)
          ·
            refine ⟨418531480190258336597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558041973587011115462945 418531480190258336597209)
            ·
              refine ⟨313898610142693752447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418531480190258336597209 313898610142693752447907)
              ·
                refine ⟨470847915214040628671861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313898610142693752447907 470847915214040628671861)
                ·
                  refine ⟨44141992051316308937987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470847915214040628671861 44141992051316308937987)
                  ·
                    rfl

theorem cell20_96712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_96712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96712 prefixEnd_96712 := by exact prefixLift 96712
  have htrace : WordTrace (prefixWord ++ tailWord_96712) baseStart_96712 baseEnd_96712 := by
    simpa [prefixWord, tailWord_96712, baseEnd_96712] using wordTrace_append hprefix tailTrace_96712
  have hstable : (prefixWord ++ tailWord_96712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96712).length < 2 ^ (prefixWord ++ tailWord_96712).sum := by decide
  have hdescent : baseEnd_96712 < baseStart_96712 := by decide
  rcases family_descends (prefixWord ++ tailWord_96712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96791 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_96791 : Nat := 118140960795 + 96791 * 2 ^ 59
def prefixEnd_96791 : Nat := 4983230072969 + 3 ^ 40 * 96791 * 2
def baseEnd_96791 : Nat := 44178049803943145304331

theorem tailTrace_96791 : CollatzResearch.WordTrace tailWord_96791 prefixEnd_96791 44178049803943145304331 := by
  unfold tailWord_96791
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530257792350212431842227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2353505194900141621228151 3530257792350212431842227)
  ·
    refine ⟨5295386688525318647763341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530257792350212431842227 5295386688525318647763341)
    ·
      refine ⟨1985770008196994492911253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5295386688525318647763341 1985770008196994492911253)
      ·
        refine ⟨93082969134234116855215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1985770008196994492911253 93082969134234116855215)
        ·
          refine ⟨139624453701351175282823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93082969134234116855215 139624453701351175282823)
          ·
            refine ⟨209436680552026762924235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139624453701351175282823 209436680552026762924235)
            ·
              refine ⟨314155020828040144386353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209436680552026762924235 314155020828040144386353)
              ·
                refine ⟨235616265621030108289765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314155020828040144386353 235616265621030108289765)
                ·
                  refine ⟨44178049803943145304331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235616265621030108289765 44178049803943145304331)
                  ·
                    rfl

theorem cell20_96791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_96791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96791 prefixEnd_96791 := by exact prefixLift 96791
  have htrace : WordTrace (prefixWord ++ tailWord_96791) baseStart_96791 baseEnd_96791 := by
    simpa [prefixWord, tailWord_96791, baseEnd_96791] using wordTrace_append hprefix tailTrace_96791
  have hstable : (prefixWord ++ tailWord_96791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96791).length < 2 ^ (prefixWord ++ tailWord_96791).sum := by decide
  have hdescent : baseEnd_96791 < baseStart_96791 := by decide
  rcases family_descends (prefixWord ++ tailWord_96791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96808 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_96808 : Nat := 118140960795 + 96808 * 2 ^ 59
def prefixEnd_96808 : Nat := 4983230072969 + 3 ^ 40 * 96808 * 2
def baseEnd_96808 : Nat := 44185809067166641737595

theorem tailTrace_96808 : CollatzResearch.WordTrace tailWord_96808 prefixEnd_96808 44185809067166641737595 := by
  unfold tailWord_96808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765438916644312167605539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2353918555525749556807385 1765438916644312167605539)
  ·
    refine ⟨2648158374966468251408309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765438916644312167605539 2648158374966468251408309)
    ·
      refine ⟨248264847653106398569529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2648158374966468251408309 248264847653106398569529)
      ·
        refine ⟨186198635739829798927147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248264847653106398569529 186198635739829798927147)
        ·
          refine ⟨279297953609744698390721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186198635739829798927147 279297953609744698390721)
          ·
            refine ⟨209473465207308523793041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279297953609744698390721 209473465207308523793041)
            ·
              refine ⟨157105098905481392844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209473465207308523793041 157105098905481392844781)
              ·
                refine ⟨58914412089555522316793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157105098905481392844781 58914412089555522316793)
                ·
                  refine ⟨44185809067166641737595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58914412089555522316793 44185809067166641737595)
                  ·
                    rfl

theorem cell20_96808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_96808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96808 prefixEnd_96808 := by exact prefixLift 96808
  have htrace : WordTrace (prefixWord ++ tailWord_96808) baseStart_96808 baseEnd_96808 := by
    simpa [prefixWord, tailWord_96808, baseEnd_96808] using wordTrace_append hprefix tailTrace_96808
  have hstable : (prefixWord ++ tailWord_96808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96808).length < 2 ^ (prefixWord ++ tailWord_96808).sum := by decide
  have hdescent : baseEnd_96808 < baseStart_96808 := by decide
  rcases family_descends (prefixWord ++ tailWord_96808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96822 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_96822 : Nat := 118140960795 + 96822 * 2 ^ 59
def prefixEnd_96822 : Nat := 4983230072969 + 3 ^ 40 * 96822 * 2
def baseEnd_96822 : Nat := 44192199048644815270871

theorem tailTrace_96822 : CollatzResearch.WordTrace tailWord_96822 prefixEnd_96822 44192199048644815270871 := by
  unfold tailWord_96822
  simp only [CollatzResearch.WordTrace]
  refine ⟨220711778452369045388795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2354258970158603150813813 220711778452369045388795)
  ·
    refine ⟨331067667678553568083193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220711778452369045388795 331067667678553568083193)
    ·
      refine ⟨248300750758915176062395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331067667678553568083193 248300750758915176062395)
      ·
        refine ⟨372451126138372764093593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248300750758915176062395 372451126138372764093593)
        ·
          refine ⟨279338344603779573070195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372451126138372764093593 279338344603779573070195)
          ·
            refine ⟨419007516905669359605293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279338344603779573070195 419007516905669359605293)
            ·
              refine ⟨157127818839626009851985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419007516905669359605293 157127818839626009851985)
              ·
                refine ⟨117845864129719507388989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157127818839626009851985 117845864129719507388989)
                ·
                  refine ⟨44192199048644815270871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117845864129719507388989 44192199048644815270871)
                  ·
                    rfl

theorem cell20_96822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_96822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96822 prefixEnd_96822 := by exact prefixLift 96822
  have htrace : WordTrace (prefixWord ++ tailWord_96822) baseStart_96822 baseEnd_96822 := by
    simpa [prefixWord, tailWord_96822, baseEnd_96822] using wordTrace_append hprefix tailTrace_96822
  have hstable : (prefixWord ++ tailWord_96822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96822).length < 2 ^ (prefixWord ++ tailWord_96822).sum := by decide
  have hdescent : baseEnd_96822 < baseStart_96822 := by decide
  rcases family_descends (prefixWord ++ tailWord_96822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96826 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_96826 : Nat := 118140960795 + 96826 * 2 ^ 59
def prefixEnd_96826 : Nat := 4983230072969 + 3 ^ 40 * 96826 * 2
def baseEnd_96826 : Nat := 44194024757638579137521

theorem tailTrace_96826 : CollatzResearch.WordTrace tailWord_96826 prefixEnd_96826 44194024757638579137521 := by
  unfold tailWord_96826
  simp only [CollatzResearch.WordTrace]
  refine ⟨882883586805853352341583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2354356231482275606244221 882883586805853352341583)
  ·
    refine ⟨1324325380208780028512375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882883586805853352341583 1324325380208780028512375)
    ·
      refine ⟨1986488070313170042768563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324325380208780028512375 1986488070313170042768563)
      ·
        refine ⟨2979732105469755064152845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986488070313170042768563 2979732105469755064152845)
        ·
          refine ⟨1117399539551158149057317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2979732105469755064152845 1117399539551158149057317)
          ·
            refine ⟨209512413665842152948247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1117399539551158149057317 209512413665842152948247)
            ·
              refine ⟨314268620498763229422371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209512413665842152948247 314268620498763229422371)
              ·
                refine ⟨471402930748144844133557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314268620498763229422371 471402930748144844133557)
                ·
                  refine ⟨44194024757638579137521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471402930748144844133557 44194024757638579137521)
                  ·
                    rfl

theorem cell20_96826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_96826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96826 prefixEnd_96826 := by exact prefixLift 96826
  have htrace : WordTrace (prefixWord ++ tailWord_96826) baseStart_96826 baseEnd_96826 := by
    simpa [prefixWord, tailWord_96826, baseEnd_96826] using wordTrace_append hprefix tailTrace_96826
  have hstable : (prefixWord ++ tailWord_96826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96826).length < 2 ^ (prefixWord ++ tailWord_96826).sum := by decide
  have hdescent : baseEnd_96826 < baseStart_96826 := by decide
  rcases family_descends (prefixWord ++ tailWord_96826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96829 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 2]
def baseStart_96829 : Nat := 118140960795 + 96829 * 2 ^ 59
def prefixEnd_96829 : Nat := 4983230072969 + 3 ^ 40 * 96829 * 2
def baseEnd_96829 : Nat := 44195394039383902037509

theorem tailTrace_96829 : CollatzResearch.WordTrace tailWord_96829 prefixEnd_96829 44195394039383902037509 := by
  unfold tailWord_96829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531643766212544921725541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2354429177475029947817027 3531643766212544921725541)
  ·
    refine ⟨662183206164852172823539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3531643766212544921725541 662183206164852172823539)
    ·
      refine ⟨993274809247278259235309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662183206164852172823539 993274809247278259235309)
      ·
        refine ⟨372478053467729347213241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 993274809247278259235309 372478053467729347213241)
        ·
          refine ⟨279358540100797010409931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372478053467729347213241 279358540100797010409931)
          ·
            refine ⟨419037810151195515614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279358540100797010409931 419037810151195515614897)
            ·
              refine ⟨314278357613396636711173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419037810151195515614897 314278357613396636711173)
              ·
                refine ⟨58927192052511869383345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314278357613396636711173 58927192052511869383345)
                ·
                  refine ⟨44195394039383902037509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58927192052511869383345 44195394039383902037509)
                  ·
                    rfl

theorem cell20_96829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_96829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96829 prefixEnd_96829 := by exact prefixLift 96829
  have htrace : WordTrace (prefixWord ++ tailWord_96829) baseStart_96829 baseEnd_96829 := by
    simpa [prefixWord, tailWord_96829, baseEnd_96829] using wordTrace_append hprefix tailTrace_96829
  have hstable : (prefixWord ++ tailWord_96829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96829).length < 2 ^ (prefixWord ++ tailWord_96829).sum := by decide
  have hdescent : baseEnd_96829 < baseStart_96829 := by decide
  rcases family_descends (prefixWord ++ tailWord_96829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96943 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 2]
def baseStart_96943 : Nat := 118140960795 + 96943 * 2 ^ 59
def prefixEnd_96943 : Nat := 4983230072969 + 3 ^ 40 * 96943 * 2
def baseEnd_96943 : Nat := 44247426745706172237043

theorem tailTrace_96943 : CollatzResearch.WordTrace tailWord_96943 prefixEnd_96943 44247426745706172237043 := by
  unfold tailWord_96943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535801687799542391375483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357201125199694927583655 3535801687799542391375483)
  ·
    refine ⟨5303702531699313587063225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535801687799542391375483 5303702531699313587063225)
    ·
      refine ⟨3977776898774485190297419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5303702531699313587063225 3977776898774485190297419)
      ·
        refine ⟨5966665348161727785446129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977776898774485190297419 5966665348161727785446129)
        ·
          refine ⟨4474999011121295839084597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5966665348161727785446129 4474999011121295839084597)
          ·
            refine ⟨419531157292621484914181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4474999011121295839084597 419531157292621484914181)
            ·
              refine ⟨78662091992366528421409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419531157292621484914181 78662091992366528421409)
              ·
                refine ⟨58996568994274896316057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78662091992366528421409 58996568994274896316057)
                ·
                  refine ⟨44247426745706172237043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58996568994274896316057 44247426745706172237043)
                  ·
                    rfl

theorem cell20_96943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2].length) (baseStart_96943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96943 prefixEnd_96943 := by exact prefixLift 96943
  have htrace : WordTrace (prefixWord ++ tailWord_96943) baseStart_96943 baseEnd_96943 := by
    simpa [prefixWord, tailWord_96943, baseEnd_96943] using wordTrace_append hprefix tailTrace_96943
  have hstable : (prefixWord ++ tailWord_96943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96943).length < 2 ^ (prefixWord ++ tailWord_96943).sum := by decide
  have hdescent : baseEnd_96943 < baseStart_96943 := by decide
  rcases family_descends (prefixWord ++ tailWord_96943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96964 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_96964 : Nat := 118140960795 + 96964 * 2 ^ 59
def prefixEnd_96964 : Nat := 4983230072969 + 3 ^ 40 * 96964 * 2
def baseEnd_96964 : Nat := 44257011717923432536957

theorem tailTrace_96964 : CollatzResearch.WordTrace tailWord_96964 prefixEnd_96964 44257011717923432536957 := by
  unfold tailWord_96964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768283810361731488944973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2357711747148975318593297 1768283810361731488944973)
  ·
    refine ⟨663106428885649308354365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1768283810361731488944973 663106428885649308354365)
    ·
      refine ⟨248664910832118490632887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 663106428885649308354365 248664910832118490632887)
      ·
        refine ⟨372997366248177735949331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248664910832118490632887 372997366248177735949331)
        ·
          refine ⟨559496049372266603923997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372997366248177735949331 559496049372266603923997)
          ·
            refine ⟨209811018514599976471499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559496049372266603923997 209811018514599976471499)
            ·
              refine ⟨314716527771899964707249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209811018514599976471499 314716527771899964707249)
              ·
                refine ⟨236037395828924973530437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314716527771899964707249 236037395828924973530437)
                ·
                  refine ⟨44257011717923432536957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236037395828924973530437 44257011717923432536957)
                  ·
                    rfl

theorem cell20_96964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_96964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96964 prefixEnd_96964 := by exact prefixLift 96964
  have htrace : WordTrace (prefixWord ++ tailWord_96964) baseStart_96964 baseEnd_96964 := by
    simpa [prefixWord, tailWord_96964, baseEnd_96964] using wordTrace_append hprefix tailTrace_96964
  have hstable : (prefixWord ++ tailWord_96964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96964).length < 2 ^ (prefixWord ++ tailWord_96964).sum := by decide
  have hdescent : baseEnd_96964 < baseStart_96964 := by decide
  rcases family_descends (prefixWord ++ tailWord_96964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96995 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_96995 : Nat := 118140960795 + 96995 * 2 ^ 59
def prefixEnd_96995 : Nat := 4983230072969 + 3 ^ 40 * 96995 * 2
def baseEnd_96995 : Nat := 44271160962625102503497

theorem tailTrace_96995 : CollatzResearch.WordTrace tailWord_96995 prefixEnd_96995 44271160962625102503497 := by
  unfold tailWord_96995
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537698283611155272268439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2358465522407436848178959 3537698283611155272268439)
  ·
    refine ⟨5306547425416732908402659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537698283611155272268439 5306547425416732908402659)
    ·
      refine ⟨7959821138125099362603989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306547425416732908402659 7959821138125099362603989)
      ·
        refine ⟨186558307924807016311031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7959821138125099362603989 186558307924807016311031)
        ·
          refine ⟨279837461887210524466547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186558307924807016311031 279837461887210524466547)
          ·
            refine ⟨419756192830815786699821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279837461887210524466547 419756192830815786699821)
            ·
              refine ⟨157408572311555920012433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419756192830815786699821 157408572311555920012433)
              ·
                refine ⟨118056429233666940009325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157408572311555920012433 118056429233666940009325)
                ·
                  refine ⟨44271160962625102503497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118056429233666940009325 44271160962625102503497)
                  ·
                    rfl

theorem cell20_96995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_96995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96995 prefixEnd_96995 := by exact prefixLift 96995
  have htrace : WordTrace (prefixWord ++ tailWord_96995) baseStart_96995 baseEnd_96995 := by
    simpa [prefixWord, tailWord_96995, baseEnd_96995] using wordTrace_append hprefix tailTrace_96995
  have hstable : (prefixWord ++ tailWord_96995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96995).length < 2 ^ (prefixWord ++ tailWord_96995).sum := by decide
  have hdescent : baseEnd_96995 < baseStart_96995 := by decide
  rcases family_descends (prefixWord ++ tailWord_96995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97026 : List Nat := [3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_97026 : Nat := 118140960795 + 97026 * 2 ^ 59
def prefixEnd_97026 : Nat := 4983230072969 + 3 ^ 40 * 97026 * 2
def baseEnd_97026 : Nat := 14761770069108924156679

theorem tailTrace_97026 : CollatzResearch.WordTrace tailWord_97026 prefixEnd_97026 14761770069108924156679 := by
  unfold tailWord_97026
  simp only [CollatzResearch.WordTrace]
  refine ⟨884707236624711891661733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2359219297665898377764621 884707236624711891661733)
  ·
    refine ⟨165882606867133479686575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 884707236624711891661733 165882606867133479686575)
    ·
      refine ⟨248823910300700219529863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165882606867133479686575 248823910300700219529863)
      ·
        refine ⟨373235865451050329294795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248823910300700219529863 373235865451050329294795)
        ·
          refine ⟨559853798176575493942193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373235865451050329294795 559853798176575493942193)
          ·
            refine ⟨419890348632431620456645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559853798176575493942193 419890348632431620456645)
            ·
              refine ⟨78729440368580928835621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419890348632431620456645 78729440368580928835621)
              ·
                refine ⟨14761770069108924156679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78729440368580928835621 14761770069108924156679)
                ·
                  rfl

theorem cell20_97026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_97026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97026 prefixEnd_97026 := by exact prefixLift 97026
  have htrace : WordTrace (prefixWord ++ tailWord_97026) baseStart_97026 baseEnd_97026 := by
    simpa [prefixWord, tailWord_97026, baseEnd_97026] using wordTrace_append hprefix tailTrace_97026
  have hstable : (prefixWord ++ tailWord_97026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97026).length < 2 ^ (prefixWord ++ tailWord_97026).sum := by decide
  have hdescent : baseEnd_97026 < baseStart_97026 := by decide
  rcases family_descends (prefixWord ++ tailWord_97026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97047 : List Nat := [1, 1, 3, 4, 3, 2, 6]
def baseStart_97047 : Nat := 118140960795 + 97047 * 2 ^ 59
def prefixEnd_97047 : Nat := 4983230072969 + 3 ^ 40 * 97047 * 2
def baseEnd_97047 : Nat := 4921655019949336974439

theorem tailTrace_97047 : CollatzResearch.WordTrace tailWord_97047 prefixEnd_97047 4921655019949336974439 := by
  unfold tailWord_97047
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539594879422768153161395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2359729919615178768774263 3539594879422768153161395)
  ·
    refine ⟨5309392319134152229742093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3539594879422768153161395 5309392319134152229742093)
    ·
      refine ⟨1991022119675307086153285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5309392319134152229742093 1991022119675307086153285)
      ·
        refine ⟨373316647439120078653741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1991022119675307086153285 373316647439120078653741)
        ·
          refine ⟨139993742789670029495153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373316647439120078653741 139993742789670029495153)
          ·
            refine ⟨104995307092252522121365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139993742789670029495153 104995307092252522121365)
            ·
              refine ⟨4921655019949336974439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104995307092252522121365 4921655019949336974439)
              ·
                rfl

theorem cell20_97047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_97047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97047 prefixEnd_97047 := by exact prefixLift 97047
  have htrace : WordTrace (prefixWord ++ tailWord_97047) baseStart_97047 baseEnd_97047 := by
    simpa [prefixWord, tailWord_97047, baseEnd_97047] using wordTrace_append hprefix tailTrace_97047
  have hstable : (prefixWord ++ tailWord_97047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97047).length < 2 ^ (prefixWord ++ tailWord_97047).sum := by decide
  have hdescent : baseEnd_97047 < baseStart_97047 := by decide
  rcases family_descends (prefixWord ++ tailWord_97047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97053 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 2]
def baseStart_97053 : Nat := 118140960795 + 97053 * 2 ^ 59
def prefixEnd_97053 : Nat := 4983230072969 + 3 ^ 40 * 97053 * 2
def baseEnd_97053 : Nat := 44297633743034678569927

theorem tailTrace_97053 : CollatzResearch.WordTrace tailWord_97053 prefixEnd_97053 44297633743034678569927 := by
  unfold tailWord_97053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539813717401031177879813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2359875811600687451919875 3539813717401031177879813)
  ·
    refine ⟨663715072012693345852465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3539813717401031177879813 663715072012693345852465)
    ·
      refine ⟨497786304009520009389349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 663715072012693345852465 497786304009520009389349)
      ·
        refine ⟨93334932001785001760503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 497786304009520009389349 93334932001785001760503)
        ·
          refine ⟨140002398002677502640755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93334932001785001760503 140002398002677502640755)
          ·
            refine ⟨210003597004016253961133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140002398002677502640755 210003597004016253961133)
            ·
              refine ⟨78751348876506095235425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210003597004016253961133 78751348876506095235425)
              ·
                refine ⟨59063511657379571426569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78751348876506095235425 59063511657379571426569)
                ·
                  refine ⟨44297633743034678569927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59063511657379571426569 44297633743034678569927)
                  ·
                    rfl

theorem cell20_97053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_97053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97053 prefixEnd_97053 := by exact prefixLift 97053
  have htrace : WordTrace (prefixWord ++ tailWord_97053) baseStart_97053 baseEnd_97053 := by
    simpa [prefixWord, tailWord_97053, baseEnd_97053] using wordTrace_append hprefix tailTrace_97053
  have hstable : (prefixWord ++ tailWord_97053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97053).length < 2 ^ (prefixWord ++ tailWord_97053).sum := by decide
  have hdescent : baseEnd_97053 < baseStart_97053 := by decide
  rcases family_descends (prefixWord ++ tailWord_97053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97057 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 2]
def baseStart_97057 : Nat := 118140960795 + 97057 * 2 ^ 59
def prefixEnd_97057 : Nat := 4983230072969 + 3 ^ 40 * 97057 * 2
def baseEnd_97057 : Nat := 44299459452028442436577

theorem tailTrace_97057 : CollatzResearch.WordTrace tailWord_97057 prefixEnd_97057 44299459452028442436577 := by
  unfold tailWord_97057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539959609386539861025425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2359973072924359907350283 3539959609386539861025425)
  ·
    refine ⟨2654969707039904895769069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3539959609386539861025425 2654969707039904895769069)
    ·
      refine ⟨995613640139964335913401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2654969707039904895769069 995613640139964335913401)
      ·
        refine ⟨746710230104973251935051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995613640139964335913401 746710230104973251935051)
        ·
          refine ⟨1120065345157459877902577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746710230104973251935051 1120065345157459877902577)
          ·
            refine ⟨840049008868094908426933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120065345157459877902577 840049008868094908426933)
            ·
              refine ⟨78754594581383897665025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 840049008868094908426933 78754594581383897665025)
              ·
                refine ⟨59065945936037923248769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78754594581383897665025 59065945936037923248769)
                ·
                  refine ⟨44299459452028442436577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59065945936037923248769 44299459452028442436577)
                  ·
                    rfl

theorem cell20_97057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_97057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97057 prefixEnd_97057 := by exact prefixLift 97057
  have htrace : WordTrace (prefixWord ++ tailWord_97057) baseStart_97057 baseEnd_97057 := by
    simpa [prefixWord, tailWord_97057, baseEnd_97057] using wordTrace_append hprefix tailTrace_97057
  have hstable : (prefixWord ++ tailWord_97057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97057).length < 2 ^ (prefixWord ++ tailWord_97057).sum := by decide
  have hdescent : baseEnd_97057 < baseStart_97057 := by decide
  rcases family_descends (prefixWord ++ tailWord_97057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97068 : List Nat := [2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_97068 : Nat := 118140960795 + 97068 * 2 ^ 59
def prefixEnd_97068 : Nat := 4983230072969 + 3 ^ 40 * 97068 * 2
def baseEnd_97068 : Nat := 14768160050587097689955

theorem tailTrace_97068 : CollatzResearch.WordTrace tailWord_97068 prefixEnd_97068 14768160050587097689955 := by
  unfold tailWord_97068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770180406173344369837929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2360240541564459159783905 1770180406173344369837929)
  ·
    refine ⟨1327635304630008277378447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1770180406173344369837929 1327635304630008277378447)
    ·
      refine ⟨1991452956945012416067671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327635304630008277378447 1991452956945012416067671)
      ·
        refine ⟨2987179435417518624101507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991452956945012416067671 2987179435417518624101507)
        ·
          refine ⟨4480769153126277936152261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987179435417518624101507 4480769153126277936152261)
          ·
            refine ⟨840144216211177113028549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4480769153126277936152261 840144216211177113028549)
            ·
              refine ⟨157527040539595708692853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840144216211177113028549 157527040539595708692853)
              ·
                refine ⟨14768160050587097689955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157527040539595708692853 14768160050587097689955)
                ·
                  rfl

theorem cell20_97068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_97068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97068 prefixEnd_97068 := by exact prefixLift 97068
  have htrace : WordTrace (prefixWord ++ tailWord_97068) baseStart_97068 baseEnd_97068 := by
    simpa [prefixWord, tailWord_97068, baseEnd_97068] using wordTrace_append hprefix tailTrace_97068
  have hstable : (prefixWord ++ tailWord_97068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97068).length < 2 ^ (prefixWord ++ tailWord_97068).sum := by decide
  have hdescent : baseEnd_97068 < baseStart_97068 := by decide
  rcases family_descends (prefixWord ++ tailWord_97068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97123 : List Nat := [1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_97123 : Nat := 118140960795 + 97123 * 2 ^ 59
def prefixEnd_97123 : Nat := 4983230072969 + 3 ^ 40 * 97123 * 2
def baseEnd_97123 : Nat := 14776527883475182078769

theorem tailTrace_97123 : CollatzResearch.WordTrace tailWord_97123 prefixEnd_97123 14776527883475182078769 := by
  unfold tailWord_97123
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542366827147433132928023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2361577884764955421952015 3542366827147433132928023)
  ·
    refine ⟨5313550240721149699392035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542366827147433132928023 5313550240721149699392035)
    ·
      refine ⟨7970325361081724549088053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313550240721149699392035 7970325361081724549088053)
      ·
        refine ⟨747218002601411676477005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7970325361081724549088053 747218002601411676477005)
        ·
          refine ⟨280206750975529378678877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747218002601411676477005 280206750975529378678877)
          ·
            refine ⟨105077531615823517004579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280206750975529378678877 105077531615823517004579)
            ·
              refine ⟨157616297423735275506869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105077531615823517004579 157616297423735275506869)
              ·
                refine ⟨14776527883475182078769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157616297423735275506869 14776527883475182078769)
                ·
                  rfl

theorem cell20_97123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_97123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97123 prefixEnd_97123 := by exact prefixLift 97123
  have htrace : WordTrace (prefixWord ++ tailWord_97123) baseStart_97123 baseEnd_97123 := by
    simpa [prefixWord, tailWord_97123, baseEnd_97123] using wordTrace_append hprefix tailTrace_97123
  have hstable : (prefixWord ++ tailWord_97123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97123).length < 2 ^ (prefixWord ++ tailWord_97123).sum := by decide
  have hdescent : baseEnd_97123 < baseStart_97123 := by decide
  rcases family_descends (prefixWord ++ tailWord_97123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97137 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_97137 : Nat := 118140960795 + 97137 * 2 ^ 59
def prefixEnd_97137 : Nat := 4983230072969 + 3 ^ 40 * 97137 * 2
def baseEnd_97137 : Nat := 44335973631903719769583

theorem tailTrace_97137 : CollatzResearch.WordTrace tailWord_97137 prefixEnd_97137 44335973631903719769583 := by
  unfold tailWord_97137
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542877449096713523937665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2361918299397809015958443 3542877449096713523937665)
  ·
    refine ⟨2657158086822535142953249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3542877449096713523937665 2657158086822535142953249)
    ·
      refine ⟨1992868565116901357214937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657158086822535142953249 1992868565116901357214937)
      ·
        refine ⟨1494651423837676017911203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1992868565116901357214937 1494651423837676017911203)
        ·
          refine ⟨2241977135756514026866805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494651423837676017911203 2241977135756514026866805)
          ·
            refine ⟨210185356477173190018763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2241977135756514026866805 210185356477173190018763)
            ·
              refine ⟨315278034715759785028145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210185356477173190018763 315278034715759785028145)
              ·
                refine ⟨236458526036819838771109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315278034715759785028145 236458526036819838771109)
                ·
                  refine ⟨44335973631903719769583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236458526036819838771109 44335973631903719769583)
                  ·
                    rfl

theorem cell20_97137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_97137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97137 prefixEnd_97137 := by exact prefixLift 97137
  have htrace : WordTrace (prefixWord ++ tailWord_97137) baseStart_97137 baseEnd_97137 := by
    simpa [prefixWord, tailWord_97137, baseEnd_97137] using wordTrace_append hprefix tailTrace_97137
  have hstable : (prefixWord ++ tailWord_97137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97137).length < 2 ^ (prefixWord ++ tailWord_97137).sum := by decide
  have hdescent : baseEnd_97137 < baseStart_97137 := by decide
  rcases family_descends (prefixWord ++ tailWord_97137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97175 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_97175 : Nat := 118140960795 + 97175 * 2 ^ 59
def prefixEnd_97175 : Nat := 4983230072969 + 3 ^ 40 * 97175 * 2
def baseEnd_97175 : Nat := 44353317867344476502761

theorem tailTrace_97175 : CollatzResearch.WordTrace tailWord_97175 prefixEnd_97175 44353317867344476502761 := by
  unfold tailWord_97175
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544263422959046013820979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2362842281972697342547319 3544263422959046013820979)
  ·
    refine ⟨5316395134438569020731469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3544263422959046013820979 5316395134438569020731469)
    ·
      refine ⟨1993648175414463382774301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5316395134438569020731469 1993648175414463382774301)
      ·
        refine ⟨747618065780423768540363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1993648175414463382774301 747618065780423768540363)
        ·
          refine ⟨1121427098670635652810545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747618065780423768540363 1121427098670635652810545)
          ·
            refine ⟨841070324002976739607909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121427098670635652810545 841070324002976739607909)
            ·
              refine ⟨157700685750558138676483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 841070324002976739607909 157700685750558138676483)
              ·
                refine ⟨236551028625837208014725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157700685750558138676483 236551028625837208014725)
                ·
                  refine ⟨44353317867344476502761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236551028625837208014725 44353317867344476502761)
                  ·
                    rfl

theorem cell20_97175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_97175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97175 prefixEnd_97175 := by exact prefixLift 97175
  have htrace : WordTrace (prefixWord ++ tailWord_97175) baseStart_97175 baseEnd_97175 := by
    simpa [prefixWord, tailWord_97175, baseEnd_97175] using wordTrace_append hprefix tailTrace_97175
  have hstable : (prefixWord ++ tailWord_97175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97175).length < 2 ^ (prefixWord ++ tailWord_97175).sum := by decide
  have hdescent : baseEnd_97175 < baseStart_97175 := by decide
  rcases family_descends (prefixWord ++ tailWord_97175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97209 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 2]
def baseStart_97209 : Nat := 118140960795 + 97209 * 2 ^ 59
def prefixEnd_97209 : Nat := 4983230072969 + 3 ^ 40 * 97209 * 2
def baseEnd_97209 : Nat := 44368836393791469369289

theorem tailTrace_97209 : CollatzResearch.WordTrace tailWord_97209 prefixEnd_97209 44368836393791469369289 := by
  unfold tailWord_97209
  simp only [CollatzResearch.WordTrace]
  refine ⟨3545503504835869820558681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2363669003223913213705787 3545503504835869820558681)
  ·
    refine ⟨2659127628626902365419011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3545503504835869820558681 2659127628626902365419011)
    ·
      refine ⟨3988691442940353548128517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659127628626902365419011 3988691442940353548128517)
      ·
        refine ⟨747879645551316290274097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3988691442940353548128517 747879645551316290274097)
        ·
          refine ⟨560909734163487217705573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747879645551316290274097 560909734163487217705573)
          ·
            refine ⟨105170575155653853319795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 560909734163487217705573 105170575155653853319795)
            ·
              refine ⟨157755862733480779979693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105170575155653853319795 157755862733480779979693)
              ·
                refine ⟨59158448525055292492385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157755862733480779979693 59158448525055292492385)
                ·
                  refine ⟨44368836393791469369289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59158448525055292492385 44368836393791469369289)
                  ·
                    rfl

theorem cell20_97209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_97209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97209 prefixEnd_97209 := by exact prefixLift 97209
  have htrace : WordTrace (prefixWord ++ tailWord_97209) baseStart_97209 baseEnd_97209 := by
    simpa [prefixWord, tailWord_97209, baseEnd_97209] using wordTrace_append hprefix tailTrace_97209
  have hstable : (prefixWord ++ tailWord_97209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97209).length < 2 ^ (prefixWord ++ tailWord_97209).sum := by decide
  have hdescent : baseEnd_97209 < baseStart_97209 := by decide
  rcases family_descends (prefixWord ++ tailWord_97209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97222 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_97222 : Nat := 118140960795 + 97222 * 2 ^ 59
def prefixEnd_97222 : Nat := 4983230072969 + 3 ^ 40 * 97222 * 2
def baseEnd_97222 : Nat := 44374769948021201935903

theorem tailTrace_97222 : CollatzResearch.WordTrace tailWord_97222 prefixEnd_97222 44374769948021201935903 := by
  unfold tailWord_97222
  simp only [CollatzResearch.WordTrace]
  refine ⟨110811801680899157524435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2363985102525848693854613 110811801680899157524435)
  ·
    refine ⟨166217702521348736286653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110811801680899157524435 166217702521348736286653)
    ·
      refine ⟨62331638445505776107495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166217702521348736286653 62331638445505776107495)
      ·
        refine ⟨93497457668258664161243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62331638445505776107495 93497457668258664161243)
        ·
          refine ⟨140246186502387996241865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93497457668258664161243 140246186502387996241865)
          ·
            refine ⟨105184639876790997181399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140246186502387996241865 105184639876790997181399)
            ·
              refine ⟨157776959815186495772099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105184639876790997181399 157776959815186495772099)
              ·
                refine ⟨236665439722779743658149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157776959815186495772099 236665439722779743658149)
                ·
                  refine ⟨44374769948021201935903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236665439722779743658149 44374769948021201935903)
                  ·
                    rfl

theorem cell20_97222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_97222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97222 prefixEnd_97222 := by exact prefixLift 97222
  have htrace : WordTrace (prefixWord ++ tailWord_97222) baseStart_97222 baseEnd_97222 := by
    simpa [prefixWord, tailWord_97222, baseEnd_97222] using wordTrace_append hprefix tailTrace_97222
  have hstable : (prefixWord ++ tailWord_97222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97222).length < 2 ^ (prefixWord ++ tailWord_97222).sum := by decide
  have hdescent : baseEnd_97222 < baseStart_97222 := by decide
  rcases family_descends (prefixWord ++ tailWord_97222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97227 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_97227 : Nat := 118140960795 + 97227 * 2 ^ 59
def prefixEnd_97227 : Nat := 4983230072969 + 3 ^ 40 * 97227 * 2
def baseEnd_97227 : Nat := 44377052084263406769215

theorem tailTrace_97227 : CollatzResearch.WordTrace tailWord_97227 prefixEnd_97227 44377052084263406769215 := by
  unfold tailWord_97227
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546160018770658894713935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2364106679180439263142623 3546160018770658894713935)
  ·
    refine ⟨5319240028155988342070903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546160018770658894713935 5319240028155988342070903)
    ·
      refine ⟨7978860042233982513106355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319240028155988342070903 7978860042233982513106355)
      ·
        refine ⟨11968290063350973769659533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978860042233982513106355 11968290063350973769659533)
        ·
          refine ⟨4488108773756615163622325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11968290063350973769659533 4488108773756615163622325)
          ·
            refine ⟨420760197539682671589593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4488108773756615163622325 420760197539682671589593)
            ·
              refine ⟨315570148154762003692195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420760197539682671589593 315570148154762003692195)
              ·
                refine ⟨473355222232143005538293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315570148154762003692195 473355222232143005538293)
                ·
                  refine ⟨44377052084263406769215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473355222232143005538293 44377052084263406769215)
                  ·
                    rfl

theorem cell20_97227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_97227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97227 prefixEnd_97227 := by exact prefixLift 97227
  have htrace : WordTrace (prefixWord ++ tailWord_97227) baseStart_97227 baseEnd_97227 := by
    simpa [prefixWord, tailWord_97227, baseEnd_97227] using wordTrace_append hprefix tailTrace_97227
  have hstable : (prefixWord ++ tailWord_97227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97227).length < 2 ^ (prefixWord ++ tailWord_97227).sum := by decide
  have hdescent : baseEnd_97227 < baseStart_97227 := by decide
  rcases family_descends (prefixWord ++ tailWord_97227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97230 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_97230 : Nat := 118140960795 + 97230 * 2 ^ 59
def prefixEnd_97230 : Nat := 4983230072969 + 3 ^ 40 * 97230 * 2
def baseEnd_97230 : Nat := 44378421366008729669203

theorem tailTrace_97230 : CollatzResearch.WordTrace tailWord_97230 prefixEnd_97230 44378421366008729669203 := by
  unfold tailWord_97230
  simp only [CollatzResearch.WordTrace]
  refine ⟨443283679719973800884143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2364179625173193604715429 443283679719973800884143)
  ·
    refine ⟨664925519579960701326215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 443283679719973800884143 664925519579960701326215)
    ·
      refine ⟨997388279369941051989323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664925519579960701326215 997388279369941051989323)
      ·
        refine ⟨1496082419054911577983985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997388279369941051989323 1496082419054911577983985)
        ·
          refine ⟨1122061814291183683487989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496082419054911577983985 1122061814291183683487989)
          ·
            refine ⟨105193295089798470326999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1122061814291183683487989 105193295089798470326999)
            ·
              refine ⟨157789942634697705490499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105193295089798470326999 157789942634697705490499)
              ·
                refine ⟨236684913952046558235749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157789942634697705490499 236684913952046558235749)
                ·
                  refine ⟨44378421366008729669203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236684913952046558235749 44378421366008729669203)
                  ·
                    rfl

theorem cell20_97230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_97230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97230 prefixEnd_97230 := by exact prefixLift 97230
  have htrace : WordTrace (prefixWord ++ tailWord_97230) baseStart_97230 baseEnd_97230 := by
    simpa [prefixWord, tailWord_97230, baseEnd_97230] using wordTrace_append hprefix tailTrace_97230
  have hstable : (prefixWord ++ tailWord_97230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97230).length < 2 ^ (prefixWord ++ tailWord_97230).sum := by decide
  have hdescent : baseEnd_97230 < baseStart_97230 := by decide
  rcases family_descends (prefixWord ++ tailWord_97230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97237 : List Nat := [1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_97237 : Nat := 118140960795 + 97237 * 2 ^ 59
def prefixEnd_97237 : Nat := 4983230072969 + 3 ^ 40 * 97237 * 2
def baseEnd_97237 : Nat := 14793872118915938811947

theorem tailTrace_97237 : CollatzResearch.WordTrace tailWord_97237 prefixEnd_97237 14793872118915938811947 := by
  unfold tailWord_97237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546524748734430602577965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2364349832489620401718643 3546524748734430602577965)
  ·
    refine ⟨1329946780775411475966737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3546524748734430602577965 1329946780775411475966737)
    ·
      refine ⟨997460085581558606975053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1329946780775411475966737 997460085581558606975053)
      ·
        refine ⟨374047532093084477615645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 997460085581558606975053 374047532093084477615645)
        ·
          refine ⟨140267824534906679105867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374047532093084477615645 140267824534906679105867)
          ·
            refine ⟨210401736802360018658801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140267824534906679105867 210401736802360018658801)
            ·
              refine ⟨157801302601770013994101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210401736802360018658801 157801302601770013994101)
              ·
                refine ⟨14793872118915938811947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157801302601770013994101 14793872118915938811947)
                ·
                  rfl

theorem cell20_97237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_97237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97237 prefixEnd_97237 := by exact prefixLift 97237
  have htrace : WordTrace (prefixWord ++ tailWord_97237) baseStart_97237 baseEnd_97237 := by
    simpa [prefixWord, tailWord_97237, baseEnd_97237] using wordTrace_append hprefix tailTrace_97237
  have hstable : (prefixWord ++ tailWord_97237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97237).length < 2 ^ (prefixWord ++ tailWord_97237).sum := by decide
  have hdescent : baseEnd_97237 < baseStart_97237 := by decide
  rcases family_descends (prefixWord ++ tailWord_97237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97258 : List Nat := [3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_97258 : Nat := 118140960795 + 97258 * 2 ^ 59
def prefixEnd_97258 : Nat := 4983230072969 + 3 ^ 40 * 97258 * 2
def baseEnd_97258 : Nat := 14797067109655025578585

theorem tailTrace_97258 : CollatzResearch.WordTrace tailWord_97258 prefixEnd_97258 14797067109655025578585 := by
  unfold tailWord_97258
  simp only [CollatzResearch.WordTrace]
  refine ⟨886822670414587797273107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2364860454438900792728285 886822670414587797273107)
  ·
    refine ⟨1330234005621881695909661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886822670414587797273107 1330234005621881695909661)
    ·
      refine ⟨498837752108205635966123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1330234005621881695909661 498837752108205635966123)
      ·
        refine ⟨748256628162308453949185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498837752108205635966123 748256628162308453949185)
        ·
          refine ⟨561192471121731340461889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748256628162308453949185 561192471121731340461889)
          ·
            refine ⟨420894353341298505346417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561192471121731340461889 420894353341298505346417)
            ·
              refine ⟨315670765005973879009813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420894353341298505346417 315670765005973879009813)
              ·
                refine ⟨14797067109655025578585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315670765005973879009813 14797067109655025578585)
                ·
                  rfl

theorem cell20_97258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_97258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97258 prefixEnd_97258 := by exact prefixLift 97258
  have htrace : WordTrace (prefixWord ++ tailWord_97258) baseStart_97258 baseEnd_97258 := by
    simpa [prefixWord, tailWord_97258, baseEnd_97258] using wordTrace_append hprefix tailTrace_97258
  have hstable : (prefixWord ++ tailWord_97258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97258).length < 2 ^ (prefixWord ++ tailWord_97258).sum := by decide
  have hdescent : baseEnd_97258 < baseStart_97258 := by decide
  rcases family_descends (prefixWord ++ tailWord_97258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97278 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_97278 : Nat := 118140960795 + 97278 * 2 ^ 59
def prefixEnd_97278 : Nat := 4983230072969 + 3 ^ 40 * 97278 * 2
def baseEnd_97278 : Nat := 44400329873933896069007

theorem tailTrace_97278 : CollatzResearch.WordTrace tailWord_97278 prefixEnd_97278 44400329873933896069007 := by
  unfold tailWord_97278
  simp only [CollatzResearch.WordTrace]
  refine ⟨443502517698236825602561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2365346761057263069880325 443502517698236825602561)
  ·
    refine ⟨332626888273677619201921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 443502517698236825602561 332626888273677619201921)
    ·
      refine ⟨249470166205258214401441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332626888273677619201921 249470166205258214401441)
      ·
        refine ⟨187102624653943660801081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249470166205258214401441 187102624653943660801081)
        ·
          refine ⟨140326968490457745600811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187102624653943660801081 140326968490457745600811)
          ·
            refine ⟨210490452735686618401217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140326968490457745600811 210490452735686618401217)
            ·
              refine ⟨157867839551764963800913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210490452735686618401217 157867839551764963800913)
              ·
                refine ⟨118400879663823722850685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157867839551764963800913 118400879663823722850685)
                ·
                  refine ⟨44400329873933896069007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118400879663823722850685 44400329873933896069007)
                  ·
                    rfl

theorem cell20_97278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_97278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97278 prefixEnd_97278 := by exact prefixLift 97278
  have htrace : WordTrace (prefixWord ++ tailWord_97278) baseStart_97278 baseEnd_97278 := by
    simpa [prefixWord, tailWord_97278, baseEnd_97278] using wordTrace_append hprefix tailTrace_97278
  have hstable : (prefixWord ++ tailWord_97278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97278).length < 2 ^ (prefixWord ++ tailWord_97278).sum := by decide
  have hdescent : baseEnd_97278 < baseStart_97278 := by decide
  rcases family_descends (prefixWord ++ tailWord_97278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97313 : List Nat := [1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_97313 : Nat := 118140960795 + 97313 * 2 ^ 59
def prefixEnd_97313 : Nat := 4983230072969 + 3 ^ 40 * 97313 * 2
def baseEnd_97313 : Nat := 14805434942543109967399

theorem tailTrace_97313 : CollatzResearch.WordTrace tailWord_97313 prefixEnd_97313 14805434942543109967399 := by
  unfold tailWord_97313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549296696459095582344593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2366197797639397054896395 3549296696459095582344593)
  ·
    refine ⟨2661972522344321686758445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3549296696459095582344593 2661972522344321686758445)
    ·
      refine ⟨998239695879120632534417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2661972522344321686758445 998239695879120632534417)
      ·
        refine ⟨748679771909340474400813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998239695879120632534417 748679771909340474400813)
        ·
          refine ⟨280754914466002677900305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 748679771909340474400813 280754914466002677900305)
          ·
            refine ⟨210566185849502008425229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280754914466002677900305 210566185849502008425229)
            ·
              refine ⟨78962319693563253159461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210566185849502008425229 78962319693563253159461)
              ·
                refine ⟨14805434942543109967399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78962319693563253159461 14805434942543109967399)
                ·
                  rfl

theorem cell20_97313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_97313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97313 prefixEnd_97313 := by exact prefixLift 97313
  have htrace : WordTrace (prefixWord ++ tailWord_97313) baseStart_97313 baseEnd_97313 := by
    simpa [prefixWord, tailWord_97313, baseEnd_97313] using wordTrace_append hprefix tailTrace_97313
  have hstable : (prefixWord ++ tailWord_97313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97313).length < 2 ^ (prefixWord ++ tailWord_97313).sum := by decide
  have hdescent : baseEnd_97313 < baseStart_97313 := by decide
  rcases family_descends (prefixWord ++ tailWord_97313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97337 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_97337 : Nat := 118140960795 + 97337 * 2 ^ 59
def prefixEnd_97337 : Nat := 4983230072969 + 3 ^ 40 * 97337 * 2
def baseEnd_97337 : Nat := 44427259081591913102099

theorem tailTrace_97337 : CollatzResearch.WordTrace tailWord_97337 prefixEnd_97337 44427259081591913102099 := by
  unfold tailWord_97337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3550172048372147681218265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2366781365581431787478843 3550172048372147681218265)
  ·
    refine ⟨2662629036279110760913699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3550172048372147681218265 2662629036279110760913699)
    ·
      refine ⟨3993943554418666141370549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662629036279110760913699 3993943554418666141370549)
      ·
        refine ⟨374432208226749950753489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3993943554418666141370549 374432208226749950753489)
        ·
          refine ⟨280824156170062463065117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374432208226749950753489 280824156170062463065117)
          ·
            refine ⟨105309058563773423649419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280824156170062463065117 105309058563773423649419)
            ·
              refine ⟨157963587845660135474129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105309058563773423649419 157963587845660135474129)
              ·
                refine ⟨118472690884245101605597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157963587845660135474129 118472690884245101605597)
                ·
                  refine ⟨44427259081591913102099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118472690884245101605597 44427259081591913102099)
                  ·
                    rfl

theorem cell20_97337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_97337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97337 prefixEnd_97337 := by exact prefixLift 97337
  have htrace : WordTrace (prefixWord ++ tailWord_97337) baseStart_97337 baseEnd_97337 := by
    simpa [prefixWord, tailWord_97337, baseEnd_97337] using wordTrace_append hprefix tailTrace_97337
  have hstable : (prefixWord ++ tailWord_97337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97337).length < 2 ^ (prefixWord ++ tailWord_97337).sum := by decide
  have hdescent : baseEnd_97337 < baseStart_97337 := by decide
  rcases family_descends (prefixWord ++ tailWord_97337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97372 : List Nat := [2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_97372 : Nat := 118140960795 + 97372 * 2 ^ 59
def prefixEnd_97372 : Nat := 4983230072969 + 3 ^ 40 * 97372 * 2
def baseEnd_97372 : Nat := 14814411345095782311763

theorem tailTrace_97372 : CollatzResearch.WordTrace tailWord_97372 prefixEnd_97372 14814411345095782311763 := by
  unfold tailWord_97372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775724301622674329371185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2367632402163565772494913 1775724301622674329371185)
  ·
    refine ⟨1331793226217005747028389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1775724301622674329371185 1331793226217005747028389)
    ·
      refine ⟨249711229915688577567823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1331793226217005747028389 249711229915688577567823)
      ·
        refine ⟨374566844873532866351735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249711229915688577567823 374566844873532866351735)
        ·
          refine ⟨561850267310299299527603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374566844873532866351735 561850267310299299527603)
          ·
            refine ⟨842775400965448949291405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561850267310299299527603 842775400965448949291405)
            ·
              refine ⟨316040775362043355984277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842775400965448949291405 316040775362043355984277)
              ·
                refine ⟨14814411345095782311763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316040775362043355984277 14814411345095782311763)
                ·
                  rfl

theorem cell20_97372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_97372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97372 prefixEnd_97372 := by exact prefixLift 97372
  have htrace : WordTrace (prefixWord ++ tailWord_97372) baseStart_97372 baseEnd_97372 := by
    simpa [prefixWord, tailWord_97372, baseEnd_97372] using wordTrace_append hprefix tailTrace_97372
  have hstable : (prefixWord ++ tailWord_97372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97372).length < 2 ^ (prefixWord ++ tailWord_97372).sum := by decide
  have hdescent : baseEnd_97372 < baseStart_97372 := by decide
  rcases family_descends (prefixWord ++ tailWord_97372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97378 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_97378 : Nat := 118140960795 + 97378 * 2 ^ 59
def prefixEnd_97378 : Nat := 4983230072969 + 3 ^ 40 * 97378 * 2
def baseEnd_97378 : Nat := 44445972598777992735265

theorem tailTrace_97378 : CollatzResearch.WordTrace tailWord_97378 prefixEnd_97378 44445972598777992735265 := by
  unfold tailWord_97378
  simp only [CollatzResearch.WordTrace]
  refine ⟨887916860305902920865197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2367778294149074455640525 887916860305902920865197)
  ·
    refine ⟨332968822614713595324449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 887916860305902920865197 332968822614713595324449)
    ·
      refine ⟨249726616961035196493337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332968822614713595324449 249726616961035196493337)
      ·
        refine ⟨187294962720776397370003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249726616961035196493337 187294962720776397370003)
        ·
          refine ⟨280942444081164596055005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187294962720776397370003 280942444081164596055005)
          ·
            refine ⟨105353416530436723520627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280942444081164596055005 105353416530436723520627)
            ·
              refine ⟨158030124795655085280941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105353416530436723520627 158030124795655085280941)
              ·
                refine ⟨59261296798370656980353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158030124795655085280941 59261296798370656980353)
                ·
                  refine ⟨44445972598777992735265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59261296798370656980353 44445972598777992735265)
                  ·
                    rfl

theorem cell20_97378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_97378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97378 prefixEnd_97378 := by exact prefixLift 97378
  have htrace : WordTrace (prefixWord ++ tailWord_97378) baseStart_97378 baseEnd_97378 := by
    simpa [prefixWord, tailWord_97378, baseEnd_97378] using wordTrace_append hprefix tailTrace_97378
  have hstable : (prefixWord ++ tailWord_97378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97378).length < 2 ^ (prefixWord ++ tailWord_97378).sum := by decide
  have hdescent : baseEnd_97378 < baseStart_97378 := by decide
  rcases family_descends (prefixWord ++ tailWord_97378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97403 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 2]
def baseStart_97403 : Nat := 118140960795 + 97403 * 2 ^ 59
def prefixEnd_97403 : Nat := 4983230072969 + 3 ^ 40 * 97403 * 2
def baseEnd_97403 : Nat := 44457383279989016901829

theorem tailTrace_97403 : CollatzResearch.WordTrace tailWord_97403 prefixEnd_97403 44457383279989016901829 := by
  unfold tailWord_97403
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552579266133040953120863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368386177422027302080575 3552579266133040953120863)
  ·
    refine ⟨5328868899199561429681295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552579266133040953120863 5328868899199561429681295)
    ·
      refine ⟨7993303348799342144521943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328868899199561429681295 7993303348799342144521943)
      ·
        refine ⟨11989955023199013216782915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993303348799342144521943 11989955023199013216782915)
        ·
          refine ⟨17984932534798519825174373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11989955023199013216782915 17984932534798519825174373)
          ·
            refine ⟨3372174850274722467220195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17984932534798519825174373 3372174850274722467220195)
            ·
              refine ⟨5058262275412083700830293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372174850274722467220195 5058262275412083700830293)
              ·
                refine ⟨59276511039985355869105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5058262275412083700830293 59276511039985355869105)
                ·
                  refine ⟨44457383279989016901829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59276511039985355869105 44457383279989016901829)
                  ·
                    rfl

theorem cell20_97403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2].length) (baseStart_97403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97403 prefixEnd_97403 := by exact prefixLift 97403
  have htrace : WordTrace (prefixWord ++ tailWord_97403) baseStart_97403 baseEnd_97403 := by
    simpa [prefixWord, tailWord_97403, baseEnd_97403] using wordTrace_append hprefix tailTrace_97403
  have hstable : (prefixWord ++ tailWord_97403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97403).length < 2 ^ (prefixWord ++ tailWord_97403).sum := by decide
  have hdescent : baseEnd_97403 < baseStart_97403 := by decide
  rcases family_descends (prefixWord ++ tailWord_97403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97455 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_97455 : Nat := 118140960795 + 97455 * 2 ^ 59
def prefixEnd_97455 : Nat := 4983230072969 + 3 ^ 40 * 97455 * 2
def baseEnd_97455 : Nat := 44481117496907947168283

theorem tailTrace_97455 : CollatzResearch.WordTrace tailWord_97455 prefixEnd_97455 44481117496907947168283 := by
  unfold tailWord_97455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554475861944653834013819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2369650574629769222675879 3554475861944653834013819)
  ·
    refine ⟨5331713792916980751020729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3554475861944653834013819 5331713792916980751020729)
    ·
      refine ⟨3998785344687735563265547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5331713792916980751020729 3998785344687735563265547)
      ·
        refine ⟨5998178017031603344898321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998785344687735563265547 5998178017031603344898321)
        ·
          refine ⟨4498633512773702508673741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5998178017031603344898321 4498633512773702508673741)
          ·
            refine ⟨1686987567290138440752653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4498633512773702508673741 1686987567290138440752653)
            ·
              refine ⟨632620337733801915282245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686987567290138440752653 632620337733801915282245)
              ·
                refine ⟨118616313325087859115421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632620337733801915282245 118616313325087859115421)
                ·
                  refine ⟨44481117496907947168283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118616313325087859115421 44481117496907947168283)
                  ·
                    rfl

theorem cell20_97455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_97455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97455 prefixEnd_97455 := by exact prefixLift 97455
  have htrace : WordTrace (prefixWord ++ tailWord_97455) baseStart_97455 baseEnd_97455 := by
    simpa [prefixWord, tailWord_97455, baseEnd_97455] using wordTrace_append hprefix tailTrace_97455
  have hstable : (prefixWord ++ tailWord_97455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97455).length < 2 ^ (prefixWord ++ tailWord_97455).sum := by decide
  have hdescent : baseEnd_97455 < baseStart_97455 := by decide
  rcases family_descends (prefixWord ++ tailWord_97455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97458 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_97458 : Nat := 118140960795 + 97458 * 2 ^ 59
def prefixEnd_97458 : Nat := 4983230072969 + 3 ^ 40 * 97458 * 2
def baseEnd_97458 : Nat := 44482486778653270068271

theorem tailTrace_97458 : CollatzResearch.WordTrace tailWord_97458 prefixEnd_97458 44482486778653270068271 := by
  unfold tailWord_97458
  simp only [CollatzResearch.WordTrace]
  refine ⟨888646320233446336593257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2369723520622523564248685 888646320233446336593257)
  ·
    refine ⟨666484740175084752444943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 888646320233446336593257 666484740175084752444943)
    ·
      refine ⟨999727110262627128667415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666484740175084752444943 999727110262627128667415)
      ·
        refine ⟨1499590665393940693001123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999727110262627128667415 1499590665393940693001123)
        ·
          refine ⟨2249385998090911039501685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499590665393940693001123 2249385998090911039501685)
          ·
            refine ⟨210879937321022909953283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2249385998090911039501685 210879937321022909953283)
            ·
              refine ⟨316319905981534364929925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210879937321022909953283 316319905981534364929925)
              ·
                refine ⟨59309982371537693424361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316319905981534364929925 59309982371537693424361)
                ·
                  refine ⟨44482486778653270068271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59309982371537693424361 44482486778653270068271)
                  ·
                    rfl

theorem cell20_97458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_97458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97458 prefixEnd_97458 := by exact prefixLift 97458
  have htrace : WordTrace (prefixWord ++ tailWord_97458) baseStart_97458 baseEnd_97458 := by
    simpa [prefixWord, tailWord_97458, baseEnd_97458] using wordTrace_append hprefix tailTrace_97458
  have hstable : (prefixWord ++ tailWord_97458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97458).length < 2 ^ (prefixWord ++ tailWord_97458).sum := by decide
  have hdescent : baseEnd_97458 < baseStart_97458 := by decide
  rcases family_descends (prefixWord ++ tailWord_97458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97478 : List Nat := [6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_97478 : Nat := 118140960795 + 97478 * 2 ^ 59
def prefixEnd_97478 : Nat := 4983230072969 + 3 ^ 40 * 97478 * 2
def baseEnd_97478 : Nat := 14830538441207363133841

theorem tailTrace_97478 : CollatzResearch.WordTrace tailWord_97478 prefixEnd_97478 14830538441207363133841 := by
  unfold tailWord_97478
  simp only [CollatzResearch.WordTrace]
  refine ⟨111103585651916523815659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2370209827240885841400725 111103585651916523815659)
  ·
    refine ⟨166655378477874785723489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111103585651916523815659 166655378477874785723489)
    ·
      refine ⟨124991533858406089292617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166655378477874785723489 124991533858406089292617)
      ·
        refine ⟨93743650393804566969463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124991533858406089292617 93743650393804566969463)
        ·
          refine ⟨140615475590706850454195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93743650393804566969463 140615475590706850454195)
          ·
            refine ⟨210923213386060275681293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140615475590706850454195 210923213386060275681293)
            ·
              refine ⟨79096205019772603380485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210923213386060275681293 79096205019772603380485)
              ·
                refine ⟨14830538441207363133841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79096205019772603380485 14830538441207363133841)
                ·
                  rfl

theorem cell20_97478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_97478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97478 prefixEnd_97478 := by exact prefixLift 97478
  have htrace : WordTrace (prefixWord ++ tailWord_97478) baseStart_97478 baseEnd_97478 := by
    simpa [prefixWord, tailWord_97478, baseEnd_97478] using wordTrace_append hprefix tailTrace_97478
  have hstable : (prefixWord ++ tailWord_97478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97478).length < 2 ^ (prefixWord ++ tailWord_97478).sum := by decide
  have hdescent : baseEnd_97478 < baseStart_97478 := by decide
  rcases family_descends (prefixWord ++ tailWord_97478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97492 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_97492 : Nat := 118140960795 + 97492 * 2 ^ 59
def prefixEnd_97492 : Nat := 4983230072969 + 3 ^ 40 * 97492 * 2
def baseEnd_97492 : Nat := 44498005305100262934799

theorem tailTrace_97492 : CollatzResearch.WordTrace tailWord_97492 prefixEnd_97492 44498005305100262934799 := by
  unfold tailWord_97492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777912681405304576555365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2370550241873739435407153 1777912681405304576555365)
  ·
    refine ⟨333358627763494608104131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1777912681405304576555365 333358627763494608104131)
    ·
      refine ⟨500037941645241912156197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333358627763494608104131 500037941645241912156197)
      ·
        refine ⟨93757114058482858529287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500037941645241912156197 93757114058482858529287)
        ·
          refine ⟨140635671087724287793931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93757114058482858529287 140635671087724287793931)
          ·
            refine ⟨210953506631586431690897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140635671087724287793931 210953506631586431690897)
            ·
              refine ⟨158215129973689823768173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210953506631586431690897 158215129973689823768173)
              ·
                refine ⟨59330673740133683913065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158215129973689823768173 59330673740133683913065)
                ·
                  refine ⟨44498005305100262934799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59330673740133683913065 44498005305100262934799)
                  ·
                    rfl

theorem cell20_97492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_97492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97492 prefixEnd_97492 := by exact prefixLift 97492
  have htrace : WordTrace (prefixWord ++ tailWord_97492) baseStart_97492 baseEnd_97492 := by
    simpa [prefixWord, tailWord_97492, baseEnd_97492] using wordTrace_append hprefix tailTrace_97492
  have hstable : (prefixWord ++ tailWord_97492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97492).length < 2 ^ (prefixWord ++ tailWord_97492).sum := by decide
  have hdescent : baseEnd_97492 < baseStart_97492 := by decide
  rcases family_descends (prefixWord ++ tailWord_97492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97517 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_97517 : Nat := 118140960795 + 97517 * 2 ^ 59
def prefixEnd_97517 : Nat := 4983230072969 + 3 ^ 40 * 97517 * 2
def baseEnd_97517 : Nat := 44509415986311287101363

theorem tailTrace_97517 : CollatzResearch.WordTrace tailWord_97517 prefixEnd_97517 44509415986311287101363 := by
  unfold tailWord_97517
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556737187720038422770805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2371158125146692281847203 3556737187720038422770805)
  ·
    refine ⟨333444111348753602134763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3556737187720038422770805 333444111348753602134763)
    ·
      refine ⟨500166167023130403202145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333444111348753602134763 500166167023130403202145)
      ·
        refine ⟨375124625267347802401609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500166167023130403202145 375124625267347802401609)
        ·
          refine ⟨281343468950510851801207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375124625267347802401609 281343468950510851801207)
          ·
            refine ⟨422015203425766277701811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281343468950510851801207 422015203425766277701811)
            ·
              refine ⟨633022805138649416552717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422015203425766277701811 633022805138649416552717)
              ·
                refine ⟨237383551926993531207269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633022805138649416552717 237383551926993531207269)
                ·
                  refine ⟨44509415986311287101363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237383551926993531207269 44509415986311287101363)
                  ·
                    rfl

theorem cell20_97517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_97517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97517 prefixEnd_97517 := by exact prefixLift 97517
  have htrace : WordTrace (prefixWord ++ tailWord_97517) baseStart_97517 baseEnd_97517 := by
    simpa [prefixWord, tailWord_97517, baseEnd_97517] using wordTrace_append hprefix tailTrace_97517
  have hstable : (prefixWord ++ tailWord_97517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97517).length < 2 ^ (prefixWord ++ tailWord_97517).sum := by decide
  have hdescent : baseEnd_97517 < baseStart_97517 := by decide
  rcases family_descends (prefixWord ++ tailWord_97517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97545 : List Nat := [1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_97545 : Nat := 118140960795 + 97545 * 2 ^ 59
def prefixEnd_97545 : Nat := 4983230072969 + 3 ^ 40 * 97545 * 2
def baseEnd_97545 : Nat := 14840731983089211389305

theorem tailTrace_97545 : CollatzResearch.WordTrace tailWord_97545 prefixEnd_97545 14840731983089211389305 := by
  unfold tailWord_97545
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557758431618599204790089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2371838954412399469860059 3557758431618599204790089)
  ·
    refine ⟨2668318823713949403592567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3557758431618599204790089 2668318823713949403592567)
    ·
      refine ⟨4002478235570924105388851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2668318823713949403592567 4002478235570924105388851)
      ·
        refine ⟨6003717353356386158083277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002478235570924105388851 6003717353356386158083277)
        ·
          refine ⟨2251394007508644809281229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6003717353356386158083277 2251394007508644809281229)
          ·
            refine ⟨844272752815741803480461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2251394007508644809281229 844272752815741803480461)
            ·
              refine ⟨316602282305903176305173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844272752815741803480461 316602282305903176305173)
              ·
                refine ⟨14840731983089211389305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316602282305903176305173 14840731983089211389305)
                ·
                  rfl

theorem cell20_97545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_97545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97545 prefixEnd_97545 := by exact prefixLift 97545
  have htrace : WordTrace (prefixWord ++ tailWord_97545) baseStart_97545 baseEnd_97545 := by
    simpa [prefixWord, tailWord_97545, baseEnd_97545] using wordTrace_append hprefix tailTrace_97545
  have hstable : (prefixWord ++ tailWord_97545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97545).length < 2 ^ (prefixWord ++ tailWord_97545).sum := by decide
  have hdescent : baseEnd_97545 < baseStart_97545 := by decide
  rcases family_descends (prefixWord ++ tailWord_97545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97562 : List Nat := [3, 1, 1, 3, 3, 3, 6]
def baseStart_97562 : Nat := 118140960795 + 97562 * 2 ^ 59
def prefixEnd_97562 : Nat := 4983230072969 + 3 ^ 40 * 97562 * 2
def baseEnd_97562 : Nat := 4947772801387903400131

theorem tailTrace_97562 : CollatzResearch.WordTrace tailWord_97562 prefixEnd_97562 4947772801387903400131 := by
  unfold tailWord_97562
  simp only [CollatzResearch.WordTrace]
  refine ⟨889594618139252777039735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2372252315038007405439293 889594618139252777039735)
  ·
    refine ⟨1334391927208879165559603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889594618139252777039735 1334391927208879165559603)
    ·
      refine ⟨2001587890813318748339405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334391927208879165559603 2001587890813318748339405)
      ·
        refine ⟨750595459054994530627277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2001587890813318748339405 750595459054994530627277)
        ·
          refine ⟨281473297145622948985229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750595459054994530627277 281473297145622948985229)
          ·
            refine ⟨105552486429608605869461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281473297145622948985229 105552486429608605869461)
            ·
              refine ⟨4947772801387903400131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105552486429608605869461 4947772801387903400131)
              ·
                rfl

theorem cell20_97562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_97562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97562 prefixEnd_97562 := by exact prefixLift 97562
  have htrace : WordTrace (prefixWord ++ tailWord_97562) baseStart_97562 baseEnd_97562 := by
    simpa [prefixWord, tailWord_97562, baseEnd_97562] using wordTrace_append hprefix tailTrace_97562
  have hstable : (prefixWord ++ tailWord_97562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97562).length < 2 ^ (prefixWord ++ tailWord_97562).sum := by decide
  have hdescent : baseEnd_97562 < baseStart_97562 := by decide
  rcases family_descends (prefixWord ++ tailWord_97562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_97569 : Nat := 118140960795 + 97569 * 2 ^ 59
def prefixEnd_97569 : Nat := 4983230072969 + 3 ^ 40 * 97569 * 2
def baseEnd_97569 : Nat := 44533150203230217367817

theorem tailTrace_97569 : CollatzResearch.WordTrace tailWord_97569 prefixEnd_97569 44533150203230217367817 := by
  unfold tailWord_97569
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558633783531651303663761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2372422522354434202442507 3558633783531651303663761)
  ·
    refine ⟨2668975337648738477747821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3558633783531651303663761 2668975337648738477747821)
    ·
      refine ⟨1000865751618276929155433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2668975337648738477747821 1000865751618276929155433)
      ·
        refine ⟨750649313713707696866575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000865751618276929155433 750649313713707696866575)
        ·
          refine ⟨1125973970570561545299863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750649313713707696866575 1125973970570561545299863)
          ·
            refine ⟨1688960955855842317949795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125973970570561545299863 1688960955855842317949795)
            ·
              refine ⟨2533441433783763476924693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688960955855842317949795 2533441433783763476924693)
              ·
                refine ⟨118755067208613912980845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2533441433783763476924693 118755067208613912980845)
                ·
                  refine ⟨44533150203230217367817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118755067208613912980845 44533150203230217367817)
                  ·
                    rfl

theorem cell20_97569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_97569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97569 prefixEnd_97569 := by exact prefixLift 97569
  have htrace : WordTrace (prefixWord ++ tailWord_97569) baseStart_97569 baseEnd_97569 := by
    simpa [prefixWord, tailWord_97569, baseEnd_97569] using wordTrace_append hprefix tailTrace_97569
  have hstable : (prefixWord ++ tailWord_97569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97569).length < 2 ^ (prefixWord ++ tailWord_97569).sum := by decide
  have hdescent : baseEnd_97569 < baseStart_97569 := by decide
  rcases family_descends (prefixWord ++ tailWord_97569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97586 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_97586 : Nat := 118140960795 + 97586 * 2 ^ 59
def prefixEnd_97586 : Nat := 4983230072969 + 3 ^ 40 * 97586 * 2
def baseEnd_97586 : Nat := 44540909466453713801081

theorem tailTrace_97586 : CollatzResearch.WordTrace tailWord_97586 prefixEnd_97586 44540909466453713801081 := by
  unfold tailWord_97586
  simp only [CollatzResearch.WordTrace]
  refine ⟨889813456117515801758153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2372835882980042138021741 889813456117515801758153)
  ·
    refine ⟨667360092088136851318615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 889813456117515801758153 667360092088136851318615)
    ·
      refine ⟨1001040138132205276977923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667360092088136851318615 1001040138132205276977923)
      ·
        refine ⟨1501560207198307915466885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001040138132205276977923 1501560207198307915466885)
        ·
          refine ⟨281542538849682734150041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1501560207198307915466885 281542538849682734150041)
          ·
            refine ⟨211156904137262050612531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281542538849682734150041 211156904137262050612531)
            ·
              refine ⟨316735356205893075918797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211156904137262050612531 316735356205893075918797)
              ·
                refine ⟨118775758577209903469549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316735356205893075918797 118775758577209903469549)
                ·
                  refine ⟨44540909466453713801081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118775758577209903469549 44540909466453713801081)
                  ·
                    rfl

theorem cell20_97586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_97586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97586 prefixEnd_97586 := by exact prefixLift 97586
  have htrace : WordTrace (prefixWord ++ tailWord_97586) baseStart_97586 baseEnd_97586 := by
    simpa [prefixWord, tailWord_97586, baseEnd_97586] using wordTrace_append hprefix tailTrace_97586
  have hstable : (prefixWord ++ tailWord_97586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97586).length < 2 ^ (prefixWord ++ tailWord_97586).sum := by decide
  have hdescent : baseEnd_97586 < baseStart_97586 := by decide
  rcases family_descends (prefixWord ++ tailWord_97586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97621 : List Nat := [1, 3, 2, 2, 3, 9]
def baseStart_97621 : Nat := 118140960795 + 97621 * 2 ^ 59
def prefixEnd_97621 : Nat := 4983230072969 + 3 ^ 40 * 97621 * 2
def baseEnd_97621 : Nat := 1650254978524042504973

theorem tailTrace_97621 : CollatzResearch.WordTrace tailWord_97621 prefixEnd_97621 1650254978524042504973 := by
  unfold tailWord_97621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560530379343264184556717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2373686919562176123037811 3560530379343264184556717)
  ·
    refine ⟨1335198892253724069208769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3560530379343264184556717 1335198892253724069208769)
    ·
      refine ⟨1001399169190293051906577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1335198892253724069208769 1001399169190293051906577)
      ·
        refine ⟨751049376892719788929933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001399169190293051906577 751049376892719788929933)
        ·
          refine ⟨281643516334769920848725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751049376892719788929933 281643516334769920848725)
          ·
            refine ⟨1650254978524042504973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 281643516334769920848725 1650254978524042504973)
            ·
              rfl

theorem cell20_97621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_97621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97621 prefixEnd_97621 := by exact prefixLift 97621
  have htrace : WordTrace (prefixWord ++ tailWord_97621) baseStart_97621 baseEnd_97621 := by
    simpa [prefixWord, tailWord_97621, baseEnd_97621] using wordTrace_append hprefix tailTrace_97621
  have hstable : (prefixWord ++ tailWord_97621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97621).length < 2 ^ (prefixWord ++ tailWord_97621).sum := by decide
  have hdescent : baseEnd_97621 < baseStart_97621 := by decide
  rcases family_descends (prefixWord ++ tailWord_97621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97665 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 2]
def baseStart_97665 : Nat := 118140960795 + 97665 * 2 ^ 59
def prefixEnd_97665 : Nat := 4983230072969 + 3 ^ 40 * 97665 * 2
def baseEnd_97665 : Nat := 44576967219080550167425

theorem tailTrace_97665 : CollatzResearch.WordTrace tailWord_97665 prefixEnd_97665 44576967219080550167425 := by
  unfold tailWord_97665
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562135191183859699158449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2374756794122573132772299 3562135191183859699158449)
  ·
    refine ⟨2671601393387894774368837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3562135191183859699158449 2671601393387894774368837)
    ·
      refine ⟨500925261260230270194157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2671601393387894774368837 500925261260230270194157)
      ·
        refine ⟨187846972972586351322809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500925261260230270194157 187846972972586351322809)
        ·
          refine ⟨140885229729439763492107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187846972972586351322809 140885229729439763492107)
          ·
            refine ⟨211327844594159645238161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140885229729439763492107 211327844594159645238161)
            ·
              refine ⟨158495883445619733928621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211327844594159645238161 158495883445619733928621)
              ·
                refine ⟨59435956292107400223233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158495883445619733928621 59435956292107400223233)
                ·
                  refine ⟨44576967219080550167425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59435956292107400223233 44576967219080550167425)
                  ·
                    rfl

theorem cell20_97665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_97665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97665 prefixEnd_97665 := by exact prefixLift 97665
  have htrace : WordTrace (prefixWord ++ tailWord_97665) baseStart_97665 baseEnd_97665 := by
    simpa [prefixWord, tailWord_97665, baseEnd_97665] using wordTrace_append hprefix tailTrace_97665
  have hstable : (prefixWord ++ tailWord_97665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97665).length < 2 ^ (prefixWord ++ tailWord_97665).sum := by decide
  have hdescent : baseEnd_97665 < baseStart_97665 := by decide
  rcases family_descends (prefixWord ++ tailWord_97665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97669 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 2]
def baseStart_97669 : Nat := 118140960795 + 97669 * 2 ^ 59
def prefixEnd_97669 : Nat := 4983230072969 + 3 ^ 40 * 97669 * 2
def baseEnd_97669 : Nat := 44578792928074314034075

theorem tailTrace_97669 : CollatzResearch.WordTrace tailWord_97669 prefixEnd_97669 44578792928074314034075 := by
  unfold tailWord_97669
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562281083169368382304061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2374854055446245588202707 3562281083169368382304061)
  ·
    refine ⟨1335855406188513143364023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3562281083169368382304061 1335855406188513143364023)
    ·
      refine ⟨2003783109282769715046035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335855406188513143364023 2003783109282769715046035)
      ·
        refine ⟨3005674663924154572569053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003783109282769715046035 3005674663924154572569053)
        ·
          refine ⟨1127127998971557964713395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3005674663924154572569053 1127127998971557964713395)
          ·
            refine ⟨1690691998457336947070093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127127998971557964713395 1690691998457336947070093)
            ·
              refine ⟨634009499421501355151285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690691998457336947070093 634009499421501355151285)
              ·
                refine ⟨59438390570765752045433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634009499421501355151285 59438390570765752045433)
                ·
                  refine ⟨44578792928074314034075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59438390570765752045433 44578792928074314034075)
                  ·
                    rfl

theorem cell20_97669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_97669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97669 prefixEnd_97669 := by exact prefixLift 97669
  have htrace : WordTrace (prefixWord ++ tailWord_97669) baseStart_97669 baseEnd_97669 := by
    simpa [prefixWord, tailWord_97669, baseEnd_97669] using wordTrace_append hprefix tailTrace_97669
  have hstable : (prefixWord ++ tailWord_97669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97669).length < 2 ^ (prefixWord ++ tailWord_97669).sum := by decide
  have hdescent : baseEnd_97669 < baseStart_97669 := by decide
  rcases family_descends (prefixWord ++ tailWord_97669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97759 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_97759 : Nat := 118140960795 + 97759 * 2 ^ 59
def prefixEnd_97759 : Nat := 4983230072969 + 3 ^ 40 * 97759 * 2
def baseEnd_97759 : Nat := 44619871380434001033707

theorem tailTrace_97759 : CollatzResearch.WordTrace tailWord_97759 prefixEnd_97759 44619871380434001033707 := by
  unfold tailWord_97759
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565563652843313753080331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2377042435228875835386887 3565563652843313753080331)
  ·
    refine ⟨5348345479264970629620497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565563652843313753080331 5348345479264970629620497)
    ·
      refine ⟨4011259109448727972215373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5348345479264970629620497 4011259109448727972215373)
      ·
        refine ⟨1504222166043272989580765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4011259109448727972215373 1504222166043272989580765)
        ·
          refine ⟨564083312266227371092787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1504222166043272989580765 564083312266227371092787)
          ·
            refine ⟨846124968399341056639181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564083312266227371092787 846124968399341056639181)
            ·
              refine ⟨317296863149752896239693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846124968399341056639181 317296863149752896239693)
              ·
                refine ⟨118986323681157336089885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317296863149752896239693 118986323681157336089885)
                ·
                  refine ⟨44619871380434001033707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118986323681157336089885 44619871380434001033707)
                  ·
                    rfl

theorem cell20_97759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_97759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97759 prefixEnd_97759 := by exact prefixLift 97759
  have htrace : WordTrace (prefixWord ++ tailWord_97759) baseStart_97759 baseEnd_97759 := by
    simpa [prefixWord, tailWord_97759, baseEnd_97759] using wordTrace_append hprefix tailTrace_97759
  have hstable : (prefixWord ++ tailWord_97759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97759).length < 2 ^ (prefixWord ++ tailWord_97759).sum := by decide
  have hdescent : baseEnd_97759 < baseStart_97759 := by decide
  rcases family_descends (prefixWord ++ tailWord_97759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97787 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_97787 : Nat := 118140960795 + 97787 * 2 ^ 59
def prefixEnd_97787 : Nat := 4983230072969 + 3 ^ 40 * 97787 * 2
def baseEnd_97787 : Nat := 44632651343390348100259

theorem tailTrace_97787 : CollatzResearch.WordTrace tailWord_97787 prefixEnd_97787 44632651343390348100259 := by
  unfold tailWord_97787
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566584896741874535099615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2377723264494583023399743 3566584896741874535099615)
  ·
    refine ⟨5349877345112811802649423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3566584896741874535099615 5349877345112811802649423)
    ·
      refine ⟨8024816017669217703974135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349877345112811802649423 8024816017669217703974135)
      ·
        refine ⟨12037224026503826555961203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8024816017669217703974135 12037224026503826555961203)
        ·
          refine ⟨18055836039755739833941805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12037224026503826555961203 18055836039755739833941805)
          ·
            refine ⟨6770938514908402437728177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18055836039755739833941805 6770938514908402437728177)
            ·
              refine ⟨5078203886181301828296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770938514908402437728177 5078203886181301828296133)
              ·
                refine ⟨952163228658994092805525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5078203886181301828296133 952163228658994092805525)
                ·
                  refine ⟨44632651343390348100259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 952163228658994092805525 44632651343390348100259)
                  ·
                    rfl

theorem cell20_97787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_97787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97787 prefixEnd_97787 := by exact prefixLift 97787
  have htrace : WordTrace (prefixWord ++ tailWord_97787) baseStart_97787 baseEnd_97787 := by
    simpa [prefixWord, tailWord_97787, baseEnd_97787] using wordTrace_append hprefix tailTrace_97787
  have hstable : (prefixWord ++ tailWord_97787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97787).length < 2 ^ (prefixWord ++ tailWord_97787).sum := by decide
  have hdescent : baseEnd_97787 < baseStart_97787 := by decide
  rcases family_descends (prefixWord ++ tailWord_97787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97790 : List Nat := [4, 2, 2, 3, 9]
def baseStart_97790 : Nat := 118140960795 + 97790 * 2 ^ 59
def prefixEnd_97790 : Nat := 4983230072969 + 3 ^ 40 * 97790 * 2
def baseEnd_97790 : Nat := 551037291668341617287

theorem tailTrace_97790 : CollatzResearch.WordTrace tailWord_97790 prefixEnd_97790 551037291668341617287 := by
  unfold tailWord_97790
  simp only [CollatzResearch.WordTrace]
  refine ⟨445836789466375755932353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2377796210487337364972549 445836789466375755932353)
  ·
    refine ⟨334377592099781816949265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 445836789466375755932353 334377592099781816949265)
    ·
      refine ⟨250783194074836362711949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334377592099781816949265 250783194074836362711949)
      ·
        refine ⟨94043697778063636016981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250783194074836362711949 94043697778063636016981)
        ·
          refine ⟨551037291668341617287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 94043697778063636016981 551037291668341617287)
          ·
            rfl

theorem cell20_97790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 9].length) (baseStart_97790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97790 prefixEnd_97790 := by exact prefixLift 97790
  have htrace : WordTrace (prefixWord ++ tailWord_97790) baseStart_97790 baseEnd_97790 := by
    simpa [prefixWord, tailWord_97790, baseEnd_97790] using wordTrace_append hprefix tailTrace_97790
  have hstable : (prefixWord ++ tailWord_97790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97790).length < 2 ^ (prefixWord ++ tailWord_97790).sum := by decide
  have hdescent : baseEnd_97790 < baseStart_97790 := by decide
  rcases family_descends (prefixWord ++ tailWord_97790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97796 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_97796 : Nat := 118140960795 + 97796 * 2 ^ 59
def prefixEnd_97796 : Nat := 4983230072969 + 3 ^ 40 * 97796 * 2
def baseEnd_97796 : Nat := 44636759188626316800223

theorem tailTrace_97796 : CollatzResearch.WordTrace tailWord_97796 prefixEnd_97796 44636759188626316800223 := by
  unfold tailWord_97796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783456576854634536088621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2377942102472846048118161 1783456576854634536088621)
  ·
    refine ⟨668796216320487951033233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1783456576854634536088621 668796216320487951033233)
    ·
      refine ⟨501597162240365963274925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 668796216320487951033233 501597162240365963274925)
      ·
        refine ⟨188098935840137236228097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501597162240365963274925 188098935840137236228097)
        ·
          refine ⟨141074201880102927171073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188098935840137236228097 141074201880102927171073)
          ·
            refine ⟨105805651410077195378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141074201880102927171073 105805651410077195378305)
            ·
              refine ⟨79354238557557896533729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105805651410077195378305 79354238557557896533729)
              ·
                refine ⟨59515678918168422400297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79354238557557896533729 59515678918168422400297)
                ·
                  refine ⟨44636759188626316800223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59515678918168422400297 44636759188626316800223)
                  ·
                    rfl

theorem cell20_97796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_97796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97796 prefixEnd_97796 := by exact prefixLift 97796
  have htrace : WordTrace (prefixWord ++ tailWord_97796) baseStart_97796 baseEnd_97796 := by
    simpa [prefixWord, tailWord_97796, baseEnd_97796] using wordTrace_append hprefix tailTrace_97796
  have hstable : (prefixWord ++ tailWord_97796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97796).length < 2 ^ (prefixWord ++ tailWord_97796).sum := by decide
  have hdescent : baseEnd_97796 < baseStart_97796 := by decide
  rcases family_descends (prefixWord ++ tailWord_97796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97800 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_97800 : Nat := 118140960795 + 97800 * 2 ^ 59
def prefixEnd_97800 : Nat := 4983230072969 + 3 ^ 40 * 97800 * 2
def baseEnd_97800 : Nat := 44638584897620080666873

theorem tailTrace_97800 : CollatzResearch.WordTrace tailWord_97800 prefixEnd_97800 44638584897620080666873 := by
  unfold tailWord_97800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783529522847388877661427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2378039363796518503548569 1783529522847388877661427)
  ·
    refine ⟨2675294284271083316492141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783529522847388877661427 2675294284271083316492141)
    ·
      refine ⟨1003235356601656243684553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2675294284271083316492141 1003235356601656243684553)
      ·
        refine ⟨752426517451242182763415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003235356601656243684553 752426517451242182763415)
        ·
          refine ⟨1128639776176863274145123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752426517451242182763415 1128639776176863274145123)
          ·
            refine ⟨1692959664265294911217685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128639776176863274145123 1692959664265294911217685)
            ·
              refine ⟨79357484262435698963329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1692959664265294911217685 79357484262435698963329)
              ·
                refine ⟨59518113196826774222497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79357484262435698963329 59518113196826774222497)
                ·
                  refine ⟨44638584897620080666873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59518113196826774222497 44638584897620080666873)
                  ·
                    rfl

theorem cell20_97800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_97800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97800 prefixEnd_97800 := by exact prefixLift 97800
  have htrace : WordTrace (prefixWord ++ tailWord_97800) baseStart_97800 baseEnd_97800 := by
    simpa [prefixWord, tailWord_97800, baseEnd_97800] using wordTrace_append hprefix tailTrace_97800
  have hstable : (prefixWord ++ tailWord_97800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97800).length < 2 ^ (prefixWord ++ tailWord_97800).sum := by decide
  have hdescent : baseEnd_97800 < baseStart_97800 := by decide
  rcases family_descends (prefixWord ++ tailWord_97800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97811 : List Nat := [1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_97811 : Nat := 118140960795 + 97811 * 2 ^ 59
def prefixEnd_97811 : Nat := 4983230072969 + 3 ^ 40 * 97811 * 2
def baseEnd_97811 : Nat := 14881201865784310433387

theorem tailTrace_97811 : CollatzResearch.WordTrace tailWord_97811 prefixEnd_97811 14881201865784310433387 := by
  unfold tailWord_97811
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567460248654926633973287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2378306832436617755982191 3567460248654926633973287)
  ·
    refine ⟨5351190372982389950959931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3567460248654926633973287 5351190372982389950959931)
    ·
      refine ⟨8026785559473584926439897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351190372982389950959931 8026785559473584926439897)
      ·
        refine ⟨6020089169605188694829923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8026785559473584926439897 6020089169605188694829923)
        ·
          refine ⟨9030133754407783042244885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020089169605188694829923 9030133754407783042244885)
          ·
            refine ⟨423287519737864830105229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9030133754407783042244885 423287519737864830105229)
            ·
              refine ⟨158732819901699311289461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423287519737864830105229 158732819901699311289461)
              ·
                refine ⟨14881201865784310433387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158732819901699311289461 14881201865784310433387)
                ·
                  rfl

theorem cell20_97811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_97811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97811 prefixEnd_97811 := by exact prefixLift 97811
  have htrace : WordTrace (prefixWord ++ tailWord_97811) baseStart_97811 baseEnd_97811 := by
    simpa [prefixWord, tailWord_97811, baseEnd_97811] using wordTrace_append hprefix tailTrace_97811
  have hstable : (prefixWord ++ tailWord_97811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97811).length < 2 ^ (prefixWord ++ tailWord_97811).sum := by decide
  have hdescent : baseEnd_97811 < baseStart_97811 := by decide
  rcases family_descends (prefixWord ++ tailWord_97811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97818 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_97818 : Nat := 118140960795 + 97818 * 2 ^ 59
def prefixEnd_97818 : Nat := 4983230072969 + 3 ^ 40 * 97818 * 2
def baseEnd_97818 : Nat := 44646800588092018066799

theorem tailTrace_97818 : CollatzResearch.WordTrace tailWord_97818 prefixEnd_97818 44646800588092018066799 := by
  unfold tailWord_97818
  simp only [CollatzResearch.WordTrace]
  refine ⟨891928889907391707369527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2378477039753044552985405 891928889907391707369527)
  ·
    refine ⟨1337893334861087561054291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891928889907391707369527 1337893334861087561054291)
    ·
      refine ⟨2006840002291631341581437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337893334861087561054291 2006840002291631341581437)
      ·
        refine ⟨752565000859361753093039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2006840002291631341581437 752565000859361753093039)
        ·
          refine ⟨1128847501289042629639559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752565000859361753093039 1128847501289042629639559)
          ·
            refine ⟨1693271251933563944459339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128847501289042629639559 1693271251933563944459339)
            ·
              refine ⟨2539906877900345916689009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693271251933563944459339 2539906877900345916689009)
              ·
                refine ⟨1904930158425259437516757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539906877900345916689009 1904930158425259437516757)
                ·
                  refine ⟨44646800588092018066799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1904930158425259437516757 44646800588092018066799)
                  ·
                    rfl

theorem cell20_97818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_97818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97818 prefixEnd_97818 := by exact prefixLift 97818
  have htrace : WordTrace (prefixWord ++ tailWord_97818) baseStart_97818 baseEnd_97818 := by
    simpa [prefixWord, tailWord_97818, baseEnd_97818] using wordTrace_append hprefix tailTrace_97818
  have hstable : (prefixWord ++ tailWord_97818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97818).length < 2 ^ (prefixWord ++ tailWord_97818).sum := by decide
  have hdescent : baseEnd_97818 < baseStart_97818 := by decide
  rcases family_descends (prefixWord ++ tailWord_97818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97838 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_97838 : Nat := 118140960795 + 97838 * 2 ^ 59
def prefixEnd_97838 : Nat := 4983230072969 + 3 ^ 40 * 97838 * 2
def baseEnd_97838 : Nat := 44655929133060837400051

theorem tailTrace_97838 : CollatzResearch.WordTrace tailWord_97838 prefixEnd_97838 44655929133060837400051 := by
  unfold tailWord_97838
  simp only [CollatzResearch.WordTrace]
  refine ⟨446055627444638780650771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2378963346371406830137445 446055627444638780650771)
  ·
    refine ⟨669083441166958170976157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446055627444638780650771 669083441166958170976157)
    ·
      refine ⟨250906290437609314116059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 669083441166958170976157 250906290437609314116059)
      ·
        refine ⟨376359435656413971174089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250906290437609314116059 376359435656413971174089)
        ·
          refine ⟨282269576742310478380567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376359435656413971174089 282269576742310478380567)
          ·
            refine ⟨423404365113465717570851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282269576742310478380567 423404365113465717570851)
            ·
              refine ⟨635106547670198576356277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423404365113465717570851 635106547670198576356277)
              ·
                refine ⟨59541238844081116533401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 635106547670198576356277 59541238844081116533401)
                ·
                  refine ⟨44655929133060837400051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59541238844081116533401 44655929133060837400051)
                  ·
                    rfl

theorem cell20_97838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_97838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97838 prefixEnd_97838 := by exact prefixLift 97838
  have htrace : WordTrace (prefixWord ++ tailWord_97838) baseStart_97838 baseEnd_97838 := by
    simpa [prefixWord, tailWord_97838, baseEnd_97838] using wordTrace_append hprefix tailTrace_97838
  have hstable : (prefixWord ++ tailWord_97838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97838).length < 2 ^ (prefixWord ++ tailWord_97838).sum := by decide
  have hdescent : baseEnd_97838 < baseStart_97838 := by decide
  rcases family_descends (prefixWord ++ tailWord_97838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97849 : List Nat := [1, 2, 1, 5, 1, 3, 7]
def baseStart_97849 : Nat := 118140960795 + 97849 * 2 ^ 59
def prefixEnd_97849 : Nat := 4983230072969 + 3 ^ 40 * 97849 * 2
def baseEnd_97849 : Nat := 4962327759199298670371

theorem tailTrace_97849 : CollatzResearch.WordTrace tailWord_97849 prefixEnd_97849 4962327759199298670371 := by
  unfold tailWord_97849
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568846222517259123856601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2379230815011506082571067 3568846222517259123856601)
  ·
    refine ⟨2676634666887944342892451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3568846222517259123856601 2676634666887944342892451)
    ·
      refine ⟨4014952000331916514338677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676634666887944342892451 4014952000331916514338677)
      ·
        refine ⟨376401750031117173219251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4014952000331916514338677 376401750031117173219251)
        ·
          refine ⟨564602625046675759828877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376401750031117173219251 564602625046675759828877)
          ·
            refine ⟨211725984392503409935829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564602625046675759828877 211725984392503409935829)
            ·
              refine ⟨4962327759199298670371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 211725984392503409935829 4962327759199298670371)
              ·
                rfl

theorem cell20_97849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_97849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97849 prefixEnd_97849 := by exact prefixLift 97849
  have htrace : WordTrace (prefixWord ++ tailWord_97849) baseStart_97849 baseEnd_97849 := by
    simpa [prefixWord, tailWord_97849, baseEnd_97849] using wordTrace_append hprefix tailTrace_97849
  have hstable : (prefixWord ++ tailWord_97849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97849).length < 2 ^ (prefixWord ++ tailWord_97849).sum := by decide
  have hdescent : baseEnd_97849 < baseStart_97849 := by decide
  rcases family_descends (prefixWord ++ tailWord_97849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97897 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 2]
def baseStart_97897 : Nat := 118140960795 + 97897 * 2 ^ 59
def prefixEnd_97897 : Nat := 4983230072969 + 3 ^ 40 * 97897 * 2
def baseEnd_97897 : Nat := 44682858340718854433143

theorem tailTrace_97897 : CollatzResearch.WordTrace tailWord_97897 prefixEnd_97897 44682858340718854433143 := by
  unfold tailWord_97897
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570596926343363321603945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2380397950895575547735963 3570596926343363321603945)
  ·
    refine ⟨2677947694757522491202959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3570596926343363321603945 2677947694757522491202959)
    ·
      refine ⟨4016921542136283736804439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677947694757522491202959 4016921542136283736804439)
      ·
        refine ⟨6025382313204425605206659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016921542136283736804439 6025382313204425605206659)
        ·
          refine ⟨9038073469806638407809989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025382313204425605206659 9038073469806638407809989)
          ·
            refine ⟨1694638775588744701464373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9038073469806638407809989 1694638775588744701464373)
            ·
              refine ⟨158872385211444815762285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1694638775588744701464373 158872385211444815762285)
              ·
                refine ⟨59577144454291805910857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158872385211444815762285 59577144454291805910857)
                ·
                  refine ⟨44682858340718854433143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59577144454291805910857 44682858340718854433143)
                  ·
                    rfl

theorem cell20_97897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_97897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97897 prefixEnd_97897 := by exact prefixLift 97897
  have htrace : WordTrace (prefixWord ++ tailWord_97897) baseStart_97897 baseEnd_97897 := by
    simpa [prefixWord, tailWord_97897, baseEnd_97897] using wordTrace_append hprefix tailTrace_97897
  have hstable : (prefixWord ++ tailWord_97897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97897).length < 2 ^ (prefixWord ++ tailWord_97897).sum := by decide
  have hdescent : baseEnd_97897 < baseStart_97897 := by decide
  rcases family_descends (prefixWord ++ tailWord_97897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97924 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_97924 : Nat := 118140960795 + 97924 * 2 ^ 59
def prefixEnd_97924 : Nat := 4983230072969 + 3 ^ 40 * 97924 * 2
def baseEnd_97924 : Nat := 44695181876426760533033

theorem tailTrace_97924 : CollatzResearch.WordTrace tailWord_97924 prefixEnd_97924 44695181876426760533033 := by
  unfold tailWord_97924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785790848622773466418413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2381054464830364621891217 1785790848622773466418413)
  ·
    refine ⟨669671568233540049906905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1785790848622773466418413 669671568233540049906905)
    ·
      refine ⟨502253676175155037430179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669671568233540049906905 502253676175155037430179)
      ·
        refine ⟨753380514262732556145269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502253676175155037430179 753380514262732556145269)
        ·
          refine ⟨70629423212131177138619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 753380514262732556145269 70629423212131177138619)
          ·
            refine ⟨105944134818196765707929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70629423212131177138619 105944134818196765707929)
            ·
              refine ⟨79458101113647574280947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105944134818196765707929 79458101113647574280947)
              ·
                refine ⟨119187151670471361421421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79458101113647574280947 119187151670471361421421)
                ·
                  refine ⟨44695181876426760533033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119187151670471361421421 44695181876426760533033)
                  ·
                    rfl

theorem cell20_97924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_97924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97924 prefixEnd_97924 := by exact prefixLift 97924
  have htrace : WordTrace (prefixWord ++ tailWord_97924) baseStart_97924 baseEnd_97924 := by
    simpa [prefixWord, tailWord_97924, baseEnd_97924] using wordTrace_append hprefix tailTrace_97924
  have hstable : (prefixWord ++ tailWord_97924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97924).length < 2 ^ (prefixWord ++ tailWord_97924).sum := by decide
  have hdescent : baseEnd_97924 < baseStart_97924 := by decide
  rcases family_descends (prefixWord ++ tailWord_97924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97925 : List Nat := [1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_97925 : Nat := 118140960795 + 97925 * 2 ^ 59
def prefixEnd_97925 : Nat := 4983230072969 + 3 ^ 40 * 97925 * 2
def baseEnd_97925 : Nat := 14898546101225067166565

theorem tailTrace_97925 : CollatzResearch.WordTrace tailWord_97925 prefixEnd_97925 14898546101225067166565 := by
  unfold tailWord_97925
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571618170241924103623229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2381078780161282735748819 3571618170241924103623229)
  ·
    refine ⟨1339356813840721538858711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3571618170241924103623229 1339356813840721538858711)
    ·
      refine ⟨2009035220761082308288067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339356813840721538858711 2009035220761082308288067)
      ·
        refine ⟨3013552831141623462432101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009035220761082308288067 3013552831141623462432101)
        ·
          refine ⟨565041155839054399206019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3013552831141623462432101 565041155839054399206019)
          ·
            refine ⟨847561733758581598809029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565041155839054399206019 847561733758581598809029)
            ·
              refine ⟨158917825079734049776693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 847561733758581598809029 158917825079734049776693)
              ·
                refine ⟨14898546101225067166565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158917825079734049776693 14898546101225067166565)
                ·
                  rfl

theorem cell20_97925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_97925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97925 prefixEnd_97925 := by exact prefixLift 97925
  have htrace : WordTrace (prefixWord ++ tailWord_97925) baseStart_97925 baseEnd_97925 := by
    simpa [prefixWord, tailWord_97925, baseEnd_97925] using wordTrace_append hprefix tailTrace_97925
  have hstable : (prefixWord ++ tailWord_97925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97925).length < 2 ^ (prefixWord ++ tailWord_97925).sum := by decide
  have hdescent : baseEnd_97925 < baseStart_97925 := by decide
  rcases family_descends (prefixWord ++ tailWord_97925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97970 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_97970 : Nat := 118140960795 + 97970 * 2 ^ 59
def prefixEnd_97970 : Nat := 4983230072969 + 3 ^ 40 * 97970 * 2
def baseEnd_97970 : Nat := 44716177529855044999511

theorem tailTrace_97970 : CollatzResearch.WordTrace tailWord_97970 prefixEnd_97970 44716177529855044999511 := by
  unfold tailWord_97970
  simp only [CollatzResearch.WordTrace]
  refine ⟨893314863769724197252841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2382172970052597859340909 893314863769724197252841)
  ·
    refine ⟨669986147827293147939631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 893314863769724197252841 669986147827293147939631)
    ·
      refine ⟨1004979221740939721909447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669986147827293147939631 1004979221740939721909447)
      ·
        refine ⟨1507468832611409582864171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004979221740939721909447 1507468832611409582864171)
        ·
          refine ⟨2261203248917114374296257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507468832611409582864171 2261203248917114374296257)
          ·
            refine ⟨1695902436687835780722193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261203248917114374296257 1695902436687835780722193)
            ·
              refine ⟨1271926827515876835541645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695902436687835780722193 1271926827515876835541645)
              ·
                refine ⟨476972560318453813328117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271926827515876835541645 476972560318453813328117)
                ·
                  refine ⟨44716177529855044999511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476972560318453813328117 44716177529855044999511)
                  ·
                    rfl

theorem cell20_97970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_97970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97970 prefixEnd_97970 := by exact prefixLift 97970
  have htrace : WordTrace (prefixWord ++ tailWord_97970) baseStart_97970 baseEnd_97970 := by
    simpa [prefixWord, tailWord_97970, baseEnd_97970] using wordTrace_append hprefix tailTrace_97970
  have hstable : (prefixWord ++ tailWord_97970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97970).length < 2 ^ (prefixWord ++ tailWord_97970).sum := by decide
  have hdescent : baseEnd_97970 < baseStart_97970 := by decide
  rcases family_descends (prefixWord ++ tailWord_97970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97980 : List Nat := [2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_97980 : Nat := 118140960795 + 97980 * 2 ^ 59
def prefixEnd_97980 : Nat := 4983230072969 + 3 ^ 40 * 97980 * 2
def baseEnd_97980 : Nat := 14906913934113151555379

theorem tailTrace_97980 : CollatzResearch.WordTrace tailWord_97980 prefixEnd_97980 14906913934113151555379 := by
  unfold tailWord_97980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786812092521334248437697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2382416123361778997916929 1786812092521334248437697)
  ·
    refine ⟨1340109069391000686328273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1786812092521334248437697 1340109069391000686328273)
    ·
      refine ⟨1005081802043250514746205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1340109069391000686328273 1005081802043250514746205)
      ·
        refine ⟨376905675766218943029827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1005081802043250514746205 376905675766218943029827)
        ·
          refine ⟨565358513649328414544741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376905675766218943029827 565358513649328414544741)
          ·
            refine ⟨106004721309249077727139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 565358513649328414544741 106004721309249077727139)
            ·
              refine ⟨159007081963873616590709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106004721309249077727139 159007081963873616590709)
              ·
                refine ⟨14906913934113151555379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159007081963873616590709 14906913934113151555379)
                ·
                  rfl

theorem cell20_97980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_97980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97980 prefixEnd_97980 := by exact prefixLift 97980
  have htrace : WordTrace (prefixWord ++ tailWord_97980) baseStart_97980 baseEnd_97980 := by
    simpa [prefixWord, tailWord_97980, baseEnd_97980] using wordTrace_append hprefix tailTrace_97980
  have hstable : (prefixWord ++ tailWord_97980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97980).length < 2 ^ (prefixWord ++ tailWord_97980).sum := by decide
  have hdescent : baseEnd_97980 < baseStart_97980 := by decide
  rcases family_descends (prefixWord ++ tailWord_97980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97990 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_97990 : Nat := 118140960795 + 97990 * 2 ^ 59
def prefixEnd_97990 : Nat := 4983230072969 + 3 ^ 40 * 97990 * 2
def baseEnd_97990 : Nat := 44725306074823864332763

theorem tailTrace_97990 : CollatzResearch.WordTrace tailWord_97990 prefixEnd_97990 44725306074823864332763 := by
  unfold tailWord_97990
  simp only [CollatzResearch.WordTrace]
  refine ⟨111687153593951256398107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2382659276670960136492949 111687153593951256398107)
  ·
    refine ⟨167530730390926884597161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111687153593951256398107 167530730390926884597161)
    ·
      refine ⟨125648047793195163447871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167530730390926884597161 125648047793195163447871)
      ·
        refine ⟨188472071689792745171807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125648047793195163447871 188472071689792745171807)
        ·
          refine ⟨282708107534689117757711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188472071689792745171807 282708107534689117757711)
          ·
            refine ⟨424062161302033676636567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282708107534689117757711 424062161302033676636567)
            ·
              refine ⟨636093241953050514954851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424062161302033676636567 636093241953050514954851)
              ·
                refine ⟨954139862929575772432277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636093241953050514954851 954139862929575772432277)
                ·
                  refine ⟨44725306074823864332763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 954139862929575772432277 44725306074823864332763)
                  ·
                    rfl

theorem cell20_97990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_97990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_97990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_97990 prefixEnd_97990 := by exact prefixLift 97990
  have htrace : WordTrace (prefixWord ++ tailWord_97990) baseStart_97990 baseEnd_97990 := by
    simpa [prefixWord, tailWord_97990, baseEnd_97990] using wordTrace_append hprefix tailTrace_97990
  have hstable : (prefixWord ++ tailWord_97990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97990).length < 2 ^ (prefixWord ++ tailWord_97990).sum := by decide
  have hdescent : baseEnd_97990 < baseStart_97990 := by decide
  rcases family_descends (prefixWord ++ tailWord_97990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98008 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_98008 : Nat := 118140960795 + 98008 * 2 ^ 59
def prefixEnd_98008 : Nat := 4983230072969 + 3 ^ 40 * 98008 * 2
def baseEnd_98008 : Nat := 44733521765295801732689

theorem tailTrace_98008 : CollatzResearch.WordTrace tailWord_98008 prefixEnd_98008 44733521765295801732689 := by
  unfold tailWord_98008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787322714470614639447339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2383096952627486185929785 1787322714470614639447339)
  ·
    refine ⟨2680984071705921959171009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787322714470614639447339 2680984071705921959171009)
    ·
      refine ⟨2010738053779441469378257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680984071705921959171009 2010738053779441469378257)
      ·
        refine ⟨1508053540334581102033693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010738053779441469378257 1508053540334581102033693)
        ·
          refine ⟨565520077625467913262635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1508053540334581102033693 565520077625467913262635)
          ·
            refine ⟨848280116438201869893953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565520077625467913262635 848280116438201869893953)
            ·
              refine ⟨636210087328651402420465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848280116438201869893953 636210087328651402420465)
              ·
                refine ⟨477157565496488551815349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636210087328651402420465 477157565496488551815349)
                ·
                  refine ⟨44733521765295801732689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 477157565496488551815349 44733521765295801732689)
                  ·
                    rfl

theorem cell20_98008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_98008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98008 prefixEnd_98008 := by exact prefixLift 98008
  have htrace : WordTrace (prefixWord ++ tailWord_98008) baseStart_98008 baseEnd_98008 := by
    simpa [prefixWord, tailWord_98008, baseEnd_98008] using wordTrace_append hprefix tailTrace_98008
  have hstable : (prefixWord ++ tailWord_98008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98008).length < 2 ^ (prefixWord ++ tailWord_98008).sum := by decide
  have hdescent : baseEnd_98008 < baseStart_98008 := by decide
  rcases family_descends (prefixWord ++ tailWord_98008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98015 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_98015 : Nat := 118140960795 + 98015 * 2 ^ 59
def prefixEnd_98015 : Nat := 4983230072969 + 3 ^ 40 * 98015 * 2
def baseEnd_98015 : Nat := 44736716756034888499327

theorem tailTrace_98015 : CollatzResearch.WordTrace tailWord_98015 prefixEnd_98015 44736716756034888499327 := by
  unfold tailWord_98015
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574900739915869474399499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2383267159943912982932999 3574900739915869474399499)
  ·
    refine ⟨5362351109873804211599249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574900739915869474399499 5362351109873804211599249)
    ·
      refine ⟨4021763332405353158699437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5362351109873804211599249 4021763332405353158699437)
      ·
        refine ⟨1508161249652007434512289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4021763332405353158699437 1508161249652007434512289)
        ·
          refine ⟨1131120937239005575884217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1508161249652007434512289 1131120937239005575884217)
          ·
            refine ⟨848340702929254181913163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131120937239005575884217 848340702929254181913163)
            ·
              refine ⟨1272511054393881272869745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848340702929254181913163 1272511054393881272869745)
              ·
                refine ⟨954383290795410954652309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272511054393881272869745 954383290795410954652309)
                ·
                  refine ⟨44736716756034888499327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 954383290795410954652309 44736716756034888499327)
                  ·
                    rfl

theorem cell20_98015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_98015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98015 prefixEnd_98015 := by exact prefixLift 98015
  have htrace : WordTrace (prefixWord ++ tailWord_98015) baseStart_98015 baseEnd_98015 := by
    simpa [prefixWord, tailWord_98015, baseEnd_98015] using wordTrace_append hprefix tailTrace_98015
  have hstable : (prefixWord ++ tailWord_98015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98015).length < 2 ^ (prefixWord ++ tailWord_98015).sum := by decide
  have hdescent : baseEnd_98015 < baseStart_98015 := by decide
  rcases family_descends (prefixWord ++ tailWord_98015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98190 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_98190 : Nat := 118140960795 + 98190 * 2 ^ 59
def prefixEnd_98190 : Nat := 4983230072969 + 3 ^ 40 * 98190 * 2
def baseEnd_98190 : Nat := 44816591524512057665279

theorem tailTrace_98190 : CollatzResearch.WordTrace tailWord_98190 prefixEnd_98190 44816591524512057665279 := by
  unfold tailWord_98190
  simp only [CollatzResearch.WordTrace]
  refine ⟨447660439285234295252503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2387522342854582908013349 447660439285234295252503)
  ·
    refine ⟨671490658927851442878755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447660439285234295252503 671490658927851442878755)
    ·
      refine ⟨1007235988391777164318133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671490658927851442878755 1007235988391777164318133)
      ·
        refine ⟨94428373911729109154825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1007235988391777164318133 94428373911729109154825)
        ·
          refine ⟨70821280433796831866119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94428373911729109154825 70821280433796831866119)
          ·
            refine ⟨106231920650695247799179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70821280433796831866119 106231920650695247799179)
            ·
              refine ⟨159347880976042871698769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106231920650695247799179 159347880976042871698769)
              ·
                refine ⟨119510910732032153774077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159347880976042871698769 119510910732032153774077)
                ·
                  refine ⟨44816591524512057665279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119510910732032153774077 44816591524512057665279)
                  ·
                    rfl

theorem cell20_98190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_98190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98190 prefixEnd_98190 := by exact prefixLift 98190
  have htrace : WordTrace (prefixWord ++ tailWord_98190) baseStart_98190 baseEnd_98190 := by
    simpa [prefixWord, tailWord_98190, baseEnd_98190] using wordTrace_append hprefix tailTrace_98190
  have hstable : (prefixWord ++ tailWord_98190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98190).length < 2 ^ (prefixWord ++ tailWord_98190).sum := by decide
  have hdescent : baseEnd_98190 < baseStart_98190 := by decide
  rcases family_descends (prefixWord ++ tailWord_98190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98194 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_98194 : Nat := 118140960795 + 98194 * 2 ^ 59
def prefixEnd_98194 : Nat := 4983230072969 + 3 ^ 40 * 98194 * 2
def baseEnd_98194 : Nat := 44818417233505821531929

theorem tailTrace_98194 : CollatzResearch.WordTrace tailWord_98194 prefixEnd_98194 44818417233505821531929 := by
  unfold tailWord_98194
  simp only [CollatzResearch.WordTrace]
  refine ⟨895357351566845761291409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2387619604178255363443757 895357351566845761291409)
  ·
    refine ⟨671518013675134320968557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 895357351566845761291409 671518013675134320968557)
    ·
      refine ⟨251819255128175370363209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 671518013675134320968557 251819255128175370363209)
      ·
        refine ⟨188864441346131527772407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251819255128175370363209 188864441346131527772407)
        ·
          refine ⟨283296662019197291658611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188864441346131527772407 283296662019197291658611)
          ·
            refine ⟨424944993028795937487917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283296662019197291658611 424944993028795937487917)
            ·
              refine ⟨159354372385798476557969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424944993028795937487917 159354372385798476557969)
              ·
                refine ⟨119515779289348857418477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159354372385798476557969 119515779289348857418477)
                ·
                  refine ⟨44818417233505821531929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119515779289348857418477 44818417233505821531929)
                  ·
                    rfl

theorem cell20_98194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_98194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98194 prefixEnd_98194 := by exact prefixLift 98194
  have htrace : WordTrace (prefixWord ++ tailWord_98194) baseStart_98194 baseEnd_98194 := by
    simpa [prefixWord, tailWord_98194, baseEnd_98194] using wordTrace_append hprefix tailTrace_98194
  have hstable : (prefixWord ++ tailWord_98194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98194).length < 2 ^ (prefixWord ++ tailWord_98194).sum := by decide
  have hdescent : baseEnd_98194 < baseStart_98194 := by decide
  rcases family_descends (prefixWord ++ tailWord_98194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_98219 : Nat := 118140960795 + 98219 * 2 ^ 59
def prefixEnd_98219 : Nat := 4983230072969 + 3 ^ 40 * 98219 * 2
def baseEnd_98219 : Nat := 44829827914716845698493

theorem tailTrace_98219 : CollatzResearch.WordTrace tailWord_98219 prefixEnd_98219 44829827914716845698493 := by
  unfold tailWord_98219
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582341231176812314825711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2388227487451208209883807 3582341231176812314825711)
  ·
    refine ⟨5373511846765218472238567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3582341231176812314825711 5373511846765218472238567)
    ·
      refine ⟨8060267770147827708357851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5373511846765218472238567 8060267770147827708357851)
      ·
        refine ⟨12090401655221741562536777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060267770147827708357851 12090401655221741562536777)
        ·
          refine ⟨9067801241416306171902583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12090401655221741562536777 9067801241416306171902583)
          ·
            refine ⟨13601701862124459257853875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067801241416306171902583 13601701862124459257853875)
            ·
              refine ⟨20402552793186688886780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13601701862124459257853875 20402552793186688886780813)
              ·
                refine ⟨7650957297445008332542805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20402552793186688886780813 7650957297445008332542805)
                ·
                  refine ⟨44829827914716845698493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7650957297445008332542805 44829827914716845698493)
                  ·
                    rfl

theorem cell20_98219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_98219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98219 prefixEnd_98219 := by exact prefixLift 98219
  have htrace : WordTrace (prefixWord ++ tailWord_98219) baseStart_98219 baseEnd_98219 := by
    simpa [prefixWord, tailWord_98219, baseEnd_98219] using wordTrace_append hprefix tailTrace_98219
  have hstable : (prefixWord ++ tailWord_98219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98219).length < 2 ^ (prefixWord ++ tailWord_98219).sum := by decide
  have hdescent : baseEnd_98219 < baseStart_98219 := by decide
  rcases family_descends (prefixWord ++ tailWord_98219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98229 : List Nat := [1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_98229 : Nat := 118140960795 + 98229 * 2 ^ 59
def prefixEnd_98229 : Nat := 4983230072969 + 3 ^ 40 * 98229 * 2
def baseEnd_98229 : Nat := 14944797395733751788373

theorem tailTrace_98229 : CollatzResearch.WordTrace tailWord_98229 prefixEnd_98229 14944797395733751788373 := by
  unfold tailWord_98229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582705961140584022689741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2388470640760389348459827 3582705961140584022689741)
  ·
    refine ⟨1343514735427719008508653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3582705961140584022689741 1343514735427719008508653)
    ·
      refine ⟨503818025785394628190745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1343514735427719008508653 503818025785394628190745)
      ·
        refine ⟨377863519339045971143059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503818025785394628190745 377863519339045971143059)
        ·
          refine ⟨566795279008568956714589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377863519339045971143059 566795279008568956714589)
          ·
            refine ⟨212548229628213358767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566795279008568956714589 212548229628213358767971)
            ·
              refine ⟨318822344442320038151957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212548229628213358767971 318822344442320038151957)
              ·
                refine ⟨14944797395733751788373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318822344442320038151957 14944797395733751788373)
                ·
                  rfl

theorem cell20_98229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_98229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98229 prefixEnd_98229 := by exact prefixLift 98229
  have htrace : WordTrace (prefixWord ++ tailWord_98229) baseStart_98229 baseEnd_98229 := by
    simpa [prefixWord, tailWord_98229, baseEnd_98229] using wordTrace_append hprefix tailTrace_98229
  have hstable : (prefixWord ++ tailWord_98229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98229).length < 2 ^ (prefixWord ++ tailWord_98229).sum := by decide
  have hdescent : baseEnd_98229 < baseStart_98229 := by decide
  rcases family_descends (prefixWord ++ tailWord_98229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98250 : List Nat := [3, 1, 2, 1, 2, 1, 10]
def baseStart_98250 : Nat := 118140960795 + 98250 * 2 ^ 59
def prefixEnd_98250 : Nat := 4983230072969 + 3 ^ 40 * 98250 * 2
def baseEnd_98250 : Nat := 4982664128824279518337

theorem tailTrace_98250 : CollatzResearch.WordTrace tailWord_98250 prefixEnd_98250 4982664128824279518337 := by
  unfold tailWord_98250
  simp only [CollatzResearch.WordTrace]
  refine ⟨895867973516126152301051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2388981262709669739469469 895867973516126152301051)
  ·
    refine ⟨1343801960274189228451577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 895867973516126152301051 1343801960274189228451577)
    ·
      refine ⟨1007851470205641921338683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343801960274189228451577 1007851470205641921338683)
      ·
        refine ⟨1511777205308462882008025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007851470205641921338683 1511777205308462882008025)
        ·
          refine ⟨1133832903981347161506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511777205308462882008025 1133832903981347161506019)
          ·
            refine ⟨1700749355972020742259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133832903981347161506019 1700749355972020742259029)
            ·
              refine ⟨4982664128824279518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1700749355972020742259029 4982664128824279518337)
              ·
                rfl

theorem cell20_98250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_98250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98250 prefixEnd_98250 := by exact prefixLift 98250
  have htrace : WordTrace (prefixWord ++ tailWord_98250) baseStart_98250 baseEnd_98250 := by
    simpa [prefixWord, tailWord_98250, baseEnd_98250] using wordTrace_append hprefix tailTrace_98250
  have hstable : (prefixWord ++ tailWord_98250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98250).length < 2 ^ (prefixWord ++ tailWord_98250).sum := by decide
  have hdescent : baseEnd_98250 < baseStart_98250 := by decide
  rcases family_descends (prefixWord ++ tailWord_98250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98288 : List Nat := [2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_98288 : Nat := 118140960795 + 98288 * 2 ^ 59
def prefixEnd_98288 : Nat := 4983230072969 + 3 ^ 40 * 98288 * 2
def baseEnd_98288 : Nat := 14953773798286424132737

theorem tailTrace_98288 : CollatzResearch.WordTrace tailWord_98288 prefixEnd_98288 14953773798286424132737 := by
  unfold tailWord_98288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792428933963418549543759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2389905245284558066058345 1792428933963418549543759)
  ·
    refine ⟨2688643400945127824315639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1792428933963418549543759 2688643400945127824315639)
    ·
      refine ⟨4032965101417691736473459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688643400945127824315639 4032965101417691736473459)
      ·
        refine ⟨6049447652126537604710189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032965101417691736473459 6049447652126537604710189)
        ·
          refine ⟨2268542869547451601766321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6049447652126537604710189 2268542869547451601766321)
          ·
            refine ⟨1701407152160588701324741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268542869547451601766321 1701407152160588701324741)
            ·
              refine ⟨319013841030110381498389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1701407152160588701324741 319013841030110381498389)
              ·
                refine ⟨14953773798286424132737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319013841030110381498389 14953773798286424132737)
                ·
                  rfl

theorem cell20_98288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_98288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98288 prefixEnd_98288 := by exact prefixLift 98288
  have htrace : WordTrace (prefixWord ++ tailWord_98288) baseStart_98288 baseEnd_98288 := by
    simpa [prefixWord, tailWord_98288, baseEnd_98288] using wordTrace_append hprefix tailTrace_98288
  have hstable : (prefixWord ++ tailWord_98288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98288).length < 2 ^ (prefixWord ++ tailWord_98288).sum := by decide
  have hdescent : baseEnd_98288 < baseStart_98288 := by decide
  rcases family_descends (prefixWord ++ tailWord_98288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98353 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 2]
def baseStart_98353 : Nat := 118140960795 + 98353 * 2 ^ 59
def prefixEnd_98353 : Nat := 4983230072969 + 3 ^ 40 * 98353 * 2
def baseEnd_98353 : Nat := 44890989166007935231279

theorem tailTrace_98353 : CollatzResearch.WordTrace tailWord_98353 prefixEnd_98353 44890989166007935231279 := by
  unfold tailWord_98353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587228612691353200203713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2391485741794235466802475 3587228612691353200203713)
  ·
    refine ⟨2690421459518514900152785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3587228612691353200203713 2690421459518514900152785)
    ·
      refine ⟨2017816094638886175114589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2690421459518514900152785 2017816094638886175114589)
      ·
        refine ⟨756681035489582315667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2017816094638886175114589 756681035489582315667971)
        ·
          refine ⟨1135021553234373473501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756681035489582315667971 1135021553234373473501957)
          ·
            refine ⟨212816541231445026281617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1135021553234373473501957 212816541231445026281617)
            ·
              refine ⟨159612405923583769711213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212816541231445026281617 159612405923583769711213)
              ·
                refine ⟨59854652221343913641705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159612405923583769711213 59854652221343913641705)
                ·
                  refine ⟨44890989166007935231279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59854652221343913641705 44890989166007935231279)
                  ·
                    rfl

theorem cell20_98353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_98353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98353 prefixEnd_98353 := by exact prefixLift 98353
  have htrace : WordTrace (prefixWord ++ tailWord_98353) baseStart_98353 baseEnd_98353 := by
    simpa [prefixWord, tailWord_98353, baseEnd_98353] using wordTrace_append hprefix tailTrace_98353
  have hstable : (prefixWord ++ tailWord_98353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98353).length < 2 ^ (prefixWord ++ tailWord_98353).sum := by decide
  have hdescent : baseEnd_98353 < baseStart_98353 := by decide
  rcases family_descends (prefixWord ++ tailWord_98353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98364 : List Nat := [2, 2, 2, 2, 2, 1, 9]
def baseStart_98364 : Nat := 118140960795 + 98364 * 2 ^ 59
def prefixEnd_98364 : Nat := 4983230072969 + 3 ^ 40 * 98364 * 2
def baseEnd_98364 : Nat := 4988445540637865096063

theorem tailTrace_98364 : CollatzResearch.WordTrace tailWord_98364 prefixEnd_98364 4988445540637865096063 := by
  unfold tailWord_98364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793814907825751039427073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2391753210434334719236097 1793814907825751039427073)
  ·
    refine ⟨1345361180869313279570305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1793814907825751039427073 1345361180869313279570305)
    ·
      refine ⟨1009020885651984959677729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345361180869313279570305 1009020885651984959677729)
      ·
        refine ⟨756765664238988719758297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1009020885651984959677729 756765664238988719758297)
        ·
          refine ⟨567574248179241539818723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756765664238988719758297 567574248179241539818723)
          ·
            refine ⟨851361372268862309728085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567574248179241539818723 851361372268862309728085)
            ·
              refine ⟨4988445540637865096063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 851361372268862309728085 4988445540637865096063)
              ·
                rfl

theorem cell20_98364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_98364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98364 prefixEnd_98364 := by exact prefixLift 98364
  have htrace : WordTrace (prefixWord ++ tailWord_98364) baseStart_98364 baseEnd_98364 := by
    simpa [prefixWord, tailWord_98364, baseEnd_98364] using wordTrace_append hprefix tailTrace_98364
  have hstable : (prefixWord ++ tailWord_98364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98364).length < 2 ^ (prefixWord ++ tailWord_98364).sum := by decide
  have hdescent : baseEnd_98364 < baseStart_98364 := by decide
  rcases family_descends (prefixWord ++ tailWord_98364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98381 : List Nat := [1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_98381 : Nat := 118140960795 + 98381 * 2 ^ 59
def prefixEnd_98381 : Nat := 4983230072969 + 3 ^ 40 * 98381 * 2
def baseEnd_98381 : Nat := 14967923042988094099277

theorem tailTrace_98381 : CollatzResearch.WordTrace tailWord_98381 prefixEnd_98381 14967923042988094099277 := by
  unfold tailWord_98381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3588249856589913982222997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2392166571059942654815331 3588249856589913982222997)
  ·
    refine ⟨168199212027652217916703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3588249856589913982222997 168199212027652217916703)
    ·
      refine ⟨252298818041478326875055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168199212027652217916703 252298818041478326875055)
      ·
        refine ⟨378448227062217490312583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252298818041478326875055 378448227062217490312583)
        ·
          refine ⟨567672340593326235468875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378448227062217490312583 567672340593326235468875)
          ·
            refine ⟨851508510889989353203313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567672340593326235468875 851508510889989353203313)
            ·
              refine ⟨638631383167492014902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851508510889989353203313 638631383167492014902485)
              ·
                refine ⟨14967923042988094099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 638631383167492014902485 14967923042988094099277)
                ·
                  rfl

theorem cell20_98381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_98381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98381 prefixEnd_98381 := by exact prefixLift 98381
  have htrace : WordTrace (prefixWord ++ tailWord_98381) baseStart_98381 baseEnd_98381 := by
    simpa [prefixWord, tailWord_98381, baseEnd_98381] using wordTrace_append hprefix tailTrace_98381
  have hstable : (prefixWord ++ tailWord_98381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98381).length < 2 ^ (prefixWord ++ tailWord_98381).sum := by decide
  have hdescent : baseEnd_98381 < baseStart_98381 := by decide
  rcases family_descends (prefixWord ++ tailWord_98381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98409 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_98409 : Nat := 118140960795 + 98409 * 2 ^ 59
def prefixEnd_98409 : Nat := 4983230072969 + 3 ^ 40 * 98409 * 2
def baseEnd_98409 : Nat := 44916549091920629364383

theorem tailTrace_98409 : CollatzResearch.WordTrace tailWord_98409 prefixEnd_98409 44916549091920629364383 := by
  unfold tailWord_98409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589271100488474764242281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2392847400325649842828187 3589271100488474764242281)
  ·
    refine ⟨2691953325366356073181711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3589271100488474764242281 2691953325366356073181711)
    ·
      refine ⟨4037929988049534109772567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691953325366356073181711 4037929988049534109772567)
      ·
        refine ⟨6056894982074301164658851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037929988049534109772567 6056894982074301164658851)
        ·
          refine ⟨9085342473111451746988277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056894982074301164658851 9085342473111451746988277)
          ·
            refine ⟨851750856854198601280151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9085342473111451746988277 851750856854198601280151)
            ·
              refine ⟨1277626285281297901920227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851750856854198601280151 1277626285281297901920227)
              ·
                refine ⟨1916439427921946852880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277626285281297901920227 1916439427921946852880341)
                ·
                  refine ⟨44916549091920629364383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1916439427921946852880341 44916549091920629364383)
                  ·
                    rfl

theorem cell20_98409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_98409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98409 prefixEnd_98409 := by exact prefixLift 98409
  have htrace : WordTrace (prefixWord ++ tailWord_98409) baseStart_98409 baseEnd_98409 := by
    simpa [prefixWord, tailWord_98409, baseEnd_98409] using wordTrace_append hprefix tailTrace_98409
  have hstable : (prefixWord ++ tailWord_98409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98409).length < 2 ^ (prefixWord ++ tailWord_98409).sum := by decide
  have hdescent : baseEnd_98409 < baseStart_98409 := by decide
  rcases family_descends (prefixWord ++ tailWord_98409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98474 : List Nat := [3, 1, 5, 1, 3, 7]
def baseStart_98474 : Nat := 118140960795 + 98474 * 2 ^ 59
def prefixEnd_98474 : Nat := 4983230072969 + 3 ^ 40 * 98474 * 2
def baseEnd_98474 : Nat := 1664674698632196007313

theorem tailTrace_98474 : CollatzResearch.WordTrace tailWord_98474 prefixEnd_98474 1664674698632196007313 := by
  unfold tailWord_98474
  simp only [CollatzResearch.WordTrace]
  refine ⟨897910461313247716339619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2394427896835327243572317 897910461313247716339619)
  ·
    refine ⟨1346865691969871574509429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897910461313247716339619 1346865691969871574509429)
    ·
      refine ⟨126268658622175460110259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1346865691969871574509429 126268658622175460110259)
      ·
        refine ⟨189402987933263190165389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126268658622175460110259 189402987933263190165389)
        ·
          refine ⟨71026120474973696312021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189402987933263190165389 71026120474973696312021)
          ·
            refine ⟨1664674698632196007313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71026120474973696312021 1664674698632196007313)
            ·
              rfl

theorem cell20_98474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 7].length) (baseStart_98474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98474 prefixEnd_98474 := by exact prefixLift 98474
  have htrace : WordTrace (prefixWord ++ tailWord_98474) baseStart_98474 baseEnd_98474 := by
    simpa [prefixWord, tailWord_98474, baseEnd_98474] using wordTrace_append hprefix tailTrace_98474
  have hstable : (prefixWord ++ tailWord_98474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98474).length < 2 ^ (prefixWord ++ tailWord_98474).sum := by decide
  have hdescent : baseEnd_98474 < baseStart_98474 := by decide
  rcases family_descends (prefixWord ++ tailWord_98474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98488 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_98488 : Nat := 118140960795 + 98488 * 2 ^ 59
def prefixEnd_98488 : Nat := 4983230072969 + 3 ^ 40 * 98488 * 2
def baseEnd_98488 : Nat := 44952606844547465730727

theorem tailTrace_98488 : CollatzResearch.WordTrace tailWord_98488 prefixEnd_98488 44952606844547465730727 := by
  unfold tailWord_98488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796076233601135628184059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2394768311468180837578745 1796076233601135628184059)
  ·
    refine ⟨2694114350401703442276089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796076233601135628184059 2694114350401703442276089)
    ·
      refine ⟨2020585762801277581707067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694114350401703442276089 2020585762801277581707067)
      ·
        refine ⟨3030878644201916372560601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020585762801277581707067 3030878644201916372560601)
        ·
          refine ⟨2273158983151437279420451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030878644201916372560601 2273158983151437279420451)
          ·
            refine ⟨3409738474727155919130677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273158983151437279420451 3409738474727155919130677)
            ·
              refine ⟨319662982005670867418501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3409738474727155919130677 319662982005670867418501)
              ·
                refine ⟨59936809126063287640969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319662982005670867418501 59936809126063287640969)
                ·
                  refine ⟨44952606844547465730727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59936809126063287640969 44952606844547465730727)
                  ·
                    rfl

theorem cell20_98488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_98488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98488 prefixEnd_98488 := by exact prefixLift 98488
  have htrace : WordTrace (prefixWord ++ tailWord_98488) baseStart_98488 baseEnd_98488 := by
    simpa [prefixWord, tailWord_98488, baseEnd_98488] using wordTrace_append hprefix tailTrace_98488
  have hstable : (prefixWord ++ tailWord_98488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98488).length < 2 ^ (prefixWord ++ tailWord_98488).sum := by decide
  have hdescent : baseEnd_98488 < baseStart_98488 := by decide
  rcases family_descends (prefixWord ++ tailWord_98488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98547 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_98547 : Nat := 118140960795 + 98547 * 2 ^ 59
def prefixEnd_98547 : Nat := 4983230072969 + 3 ^ 40 * 98547 * 2
def baseEnd_98547 : Nat := 44979536052205482763819

theorem tailTrace_98547 : CollatzResearch.WordTrace tailWord_98547 prefixEnd_98547 44979536052205482763819 := by
  unfold tailWord_98547
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594304373988524332765895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2396202915992349555177263 3594304373988524332765895)
  ·
    refine ⟨5391456560982786499148843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3594304373988524332765895 5391456560982786499148843)
    ·
      refine ⟨8087184841474179748723265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391456560982786499148843 8087184841474179748723265)
      ·
        refine ⟨6065388631105634811542449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8087184841474179748723265 6065388631105634811542449)
        ·
          refine ⟨4549041473329226108656837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065388631105634811542449 4549041473329226108656837)
          ·
            refine ⟨852945276249229895373157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4549041473329226108656837 852945276249229895373157)
            ·
              refine ⟨159927239296730605382467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 852945276249229895373157 159927239296730605382467)
              ·
                refine ⟨239890858945095908073701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159927239296730605382467 239890858945095908073701)
                ·
                  refine ⟨44979536052205482763819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239890858945095908073701 44979536052205482763819)
                  ·
                    rfl

theorem cell20_98547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_98547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98547 prefixEnd_98547 := by exact prefixLift 98547
  have htrace : WordTrace (prefixWord ++ tailWord_98547) baseStart_98547 baseEnd_98547 := by
    simpa [prefixWord, tailWord_98547, baseEnd_98547] using wordTrace_append hprefix tailTrace_98547
  have hstable : (prefixWord ++ tailWord_98547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98547).length < 2 ^ (prefixWord ++ tailWord_98547).sum := by decide
  have hdescent : baseEnd_98547 < baseStart_98547 := by decide
  rcases family_descends (prefixWord ++ tailWord_98547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98567 : List Nat := [1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_98567 : Nat := 118140960795 + 98567 * 2 ^ 59
def prefixEnd_98567 : Nat := 4983230072969 + 3 ^ 40 * 98567 * 2
def baseEnd_98567 : Nat := 14996221532391434032357

theorem tailTrace_98567 : CollatzResearch.WordTrace tailWord_98567 prefixEnd_98567 14996221532391434032357 := by
  unfold tailWord_98567
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595033833916067748493955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2396689222610711832329303 3595033833916067748493955)
  ·
    refine ⟨5392550750874101622740933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595033833916067748493955 5392550750874101622740933)
    ·
      refine ⟨1011103265788894054263925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5392550750874101622740933 1011103265788894054263925)
      ·
        refine ⟨94790931167708817587243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1011103265788894054263925 94790931167708817587243)
        ·
          refine ⟨142186396751563226380865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94790931167708817587243 142186396751563226380865)
          ·
            refine ⟨106639797563672419785649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142186396751563226380865 106639797563672419785649)
            ·
              refine ⟨79979848172754314839237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106639797563672419785649 79979848172754314839237)
              ·
                refine ⟨14996221532391434032357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79979848172754314839237 14996221532391434032357)
                ·
                  rfl

theorem cell20_98567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_98567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98567 prefixEnd_98567 := by exact prefixLift 98567
  have htrace : WordTrace (prefixWord ++ tailWord_98567) baseStart_98567 baseEnd_98567 := by
    simpa [prefixWord, tailWord_98567, baseEnd_98567] using wordTrace_append hprefix tailTrace_98567
  have hstable : (prefixWord ++ tailWord_98567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98567).length < 2 ^ (prefixWord ++ tailWord_98567).sum := by decide
  have hdescent : baseEnd_98567 < baseStart_98567 := by decide
  rcases family_descends (prefixWord ++ tailWord_98567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98592 : List Nat := [2, 1, 1, 5, 2, 1, 8]
def baseStart_98592 : Nat := 118140960795 + 98592 * 2 ^ 59
def prefixEnd_98592 : Nat := 4983230072969 + 3 ^ 40 * 98592 * 2
def baseEnd_98592 : Nat := 5000008364265036251515

theorem tailTrace_98592 : CollatzResearch.WordTrace tailWord_98592 prefixEnd_98592 5000008364265036251515 := by
  unfold tailWord_98592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797972829412748509077015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2397297105883664678769353 1797972829412748509077015)
  ·
    refine ⟨2696959244119122763615523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797972829412748509077015 2696959244119122763615523)
    ·
      refine ⟨4045438866178684145423285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696959244119122763615523 4045438866178684145423285)
      ·
        refine ⟨379259893704251638633433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4045438866178684145423285 379259893704251638633433)
        ·
          refine ⟨284444920278188728975075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379259893704251638633433 284444920278188728975075)
          ·
            refine ⟨426667380417283093462613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284444920278188728975075 426667380417283093462613)
            ·
              refine ⟨5000008364265036251515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 426667380417283093462613 5000008364265036251515)
              ·
                rfl

theorem cell20_98592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_98592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98592 prefixEnd_98592 := by exact prefixLift 98592
  have htrace : WordTrace (prefixWord ++ tailWord_98592) baseStart_98592 baseEnd_98592 := by
    simpa [prefixWord, tailWord_98592, baseEnd_98592] using wordTrace_append hprefix tailTrace_98592
  have hstable : (prefixWord ++ tailWord_98592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98592).length < 2 ^ (prefixWord ++ tailWord_98592).sum := by decide
  have hdescent : baseEnd_98592 < baseStart_98592 := by decide
  rcases family_descends (prefixWord ++ tailWord_98592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98609 : List Nat := [1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_98609 : Nat := 118140960795 + 98609 * 2 ^ 59
def prefixEnd_98609 : Nat := 4983230072969 + 3 ^ 40 * 98609 * 2
def baseEnd_98609 : Nat := 15002611513869607565633

theorem tailTrace_98609 : CollatzResearch.WordTrace tailWord_98609 prefixEnd_98609 15002611513869607565633 := by
  unfold tailWord_98609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596565699763908921522881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2397710466509272614348587 3596565699763908921522881)
  ·
    refine ⟨2697424274822931691142161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3596565699763908921522881 2697424274822931691142161)
    ·
      refine ⟨2023068206117198768356621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697424274822931691142161 2023068206117198768356621)
      ·
        refine ⟨758650577293949538133733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2023068206117198768356621 758650577293949538133733)
        ·
          refine ⟨142246983242615538400075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 758650577293949538133733 142246983242615538400075)
          ·
            refine ⟨213370474863923307600113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142246983242615538400075 213370474863923307600113)
            ·
              refine ⟨160027856147942480700085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213370474863923307600113 160027856147942480700085)
              ·
                refine ⟨15002611513869607565633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160027856147942480700085 15002611513869607565633)
                ·
                  rfl

theorem cell20_98609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_98609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98609 prefixEnd_98609 := by exact prefixLift 98609
  have htrace : WordTrace (prefixWord ++ tailWord_98609) baseStart_98609 baseEnd_98609 := by
    simpa [prefixWord, tailWord_98609, baseEnd_98609] using wordTrace_append hprefix tailTrace_98609
  have hstable : (prefixWord ++ tailWord_98609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98609).length < 2 ^ (prefixWord ++ tailWord_98609).sum := by decide
  have hdescent : baseEnd_98609 < baseStart_98609 := by decide
  rcases family_descends (prefixWord ++ tailWord_98609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98612 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_98612 : Nat := 118140960795 + 98612 * 2 ^ 59
def prefixEnd_98612 : Nat := 4983230072969 + 3 ^ 40 * 98612 * 2
def baseEnd_98612 : Nat := 45009203823354145596887

theorem tailTrace_98612 : CollatzResearch.WordTrace tailWord_98612 prefixEnd_98612 45009203823354145596887 := by
  unfold tailWord_98612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798337559376520216941045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2397783412502026955921393 1798337559376520216941045)
  ·
    refine ⟨168594146191548770338223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1798337559376520216941045 168594146191548770338223)
    ·
      refine ⟨252891219287323155507335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168594146191548770338223 252891219287323155507335)
      ·
        refine ⟨379336828930984733261003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252891219287323155507335 379336828930984733261003)
        ·
          refine ⟨569005243396477099891505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379336828930984733261003 569005243396477099891505)
          ·
            refine ⟨426753932547357824918629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569005243396477099891505 426753932547357824918629)
            ·
              refine ⟨80016362352629592172243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426753932547357824918629 80016362352629592172243)
              ·
                refine ⟨120024543528944388258365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80016362352629592172243 120024543528944388258365)
                ·
                  refine ⟨45009203823354145596887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120024543528944388258365 45009203823354145596887)
                  ·
                    rfl

theorem cell20_98612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_98612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98612 prefixEnd_98612 := by exact prefixLift 98612
  have htrace : WordTrace (prefixWord ++ tailWord_98612) baseStart_98612 baseEnd_98612 := by
    simpa [prefixWord, tailWord_98612, baseEnd_98612] using wordTrace_append hprefix tailTrace_98612
  have hstable : (prefixWord ++ tailWord_98612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98612).length < 2 ^ (prefixWord ++ tailWord_98612).sum := by decide
  have hdescent : baseEnd_98612 < baseStart_98612 := by decide
  rcases family_descends (prefixWord ++ tailWord_98612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98685 : List Nat := [1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_98685 : Nat := 118140960795 + 98685 * 2 ^ 59
def prefixEnd_98685 : Nat := 4983230072969 + 3 ^ 40 * 98685 * 2
def baseEnd_98685 : Nat := 15014174337496778721085

theorem tailTrace_98685 : CollatzResearch.WordTrace tailWord_98685 prefixEnd_98685 15014174337496778721085 := by
  unfold tailWord_98685
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599337647488573901289509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2399558431659049267526339 3599337647488573901289509)
  ·
    refine ⟨674875808904107606491783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3599337647488573901289509 674875808904107606491783)
    ·
      refine ⟨1012313713356161409737675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674875808904107606491783 1012313713356161409737675)
      ·
        refine ⟨1518470570034242114606513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012313713356161409737675 1518470570034242114606513)
        ·
          refine ⟨1138852927525681585954885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518470570034242114606513 1138852927525681585954885)
          ·
            refine ⟨213534923911065297366541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1138852927525681585954885 213534923911065297366541)
            ·
              refine ⟨80075596466649486512453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213534923911065297366541 80075596466649486512453)
              ·
                refine ⟨15014174337496778721085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80075596466649486512453 15014174337496778721085)
                ·
                  rfl

theorem cell20_98685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_98685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98685 prefixEnd_98685 := by exact prefixLift 98685
  have htrace : WordTrace (prefixWord ++ tailWord_98685) baseStart_98685 baseEnd_98685 := by
    simpa [prefixWord, tailWord_98685, baseEnd_98685] using wordTrace_append hprefix tailTrace_98685
  have hstable : (prefixWord ++ tailWord_98685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98685).length < 2 ^ (prefixWord ++ tailWord_98685).sum := by decide
  have hdescent : baseEnd_98685 < baseStart_98685 := by decide
  rcases family_descends (prefixWord ++ tailWord_98685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98713 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_98713 : Nat := 118140960795 + 98713 * 2 ^ 59
def prefixEnd_98713 : Nat := 4983230072969 + 3 ^ 40 * 98713 * 2
def baseEnd_98713 : Nat := 45055302975446683229807

theorem tailTrace_98713 : CollatzResearch.WordTrace tailWord_98713 prefixEnd_98713 45055302975446683229807 := by
  unfold tailWord_98713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600358891387134683308793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2400239260924756455539195 3600358891387134683308793)
  ·
    refine ⟨2700269168540351012481595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3600358891387134683308793 2700269168540351012481595)
    ·
      refine ⟨4050403752810526518722393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700269168540351012481595 4050403752810526518722393)
      ·
        refine ⟨3037802814607894889041795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050403752810526518722393 3037802814607894889041795)
        ·
          refine ⟨4556704221911842333562693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037802814607894889041795 4556704221911842333562693)
          ·
            refine ⟨854382041608470437543005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4556704221911842333562693 854382041608470437543005)
            ·
              refine ⟨320393265603176414078627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854382041608470437543005 320393265603176414078627)
              ·
                refine ⟨480589898404764621117941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320393265603176414078627 480589898404764621117941)
                ·
                  refine ⟨45055302975446683229807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480589898404764621117941 45055302975446683229807)
                  ·
                    rfl

theorem cell20_98713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_98713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98713 prefixEnd_98713 := by exact prefixLift 98713
  have htrace : WordTrace (prefixWord ++ tailWord_98713) baseStart_98713 baseEnd_98713 := by
    simpa [prefixWord, tailWord_98713, baseEnd_98713] using wordTrace_append hprefix tailTrace_98713
  have hstable : (prefixWord ++ tailWord_98713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98713).length < 2 ^ (prefixWord ++ tailWord_98713).sum := by decide
  have hdescent : baseEnd_98713 < baseStart_98713 := by decide
  rcases family_descends (prefixWord ++ tailWord_98713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98737 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_98737 : Nat := 118140960795 + 98737 * 2 ^ 59
def prefixEnd_98737 : Nat := 4983230072969 + 3 ^ 40 * 98737 * 2
def baseEnd_98737 : Nat := 45066257229409266429709

theorem tailTrace_98737 : CollatzResearch.WordTrace tailWord_98737 prefixEnd_98737 45066257229409266429709 := by
  unfold tailWord_98737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601234243300186782182465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2400822828866791188121643 3601234243300186782182465)
  ·
    refine ⟨2700925682475140086636849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601234243300186782182465 2700925682475140086636849)
    ·
      refine ⟨2025694261856355064977637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700925682475140086636849 2025694261856355064977637)
      ·
        refine ⟨379817674098066574683307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2025694261856355064977637 379817674098066574683307)
        ·
          refine ⟨569726511147099862024961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379817674098066574683307 569726511147099862024961)
          ·
            refine ⟨427294883360324896518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569726511147099862024961 427294883360324896518721)
            ·
              refine ⟨320471162520243672389041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427294883360324896518721 320471162520243672389041)
              ·
                refine ⟨240353371890182754291781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320471162520243672389041 240353371890182754291781)
                ·
                  refine ⟨45066257229409266429709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240353371890182754291781 45066257229409266429709)
                  ·
                    rfl

theorem cell20_98737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_98737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98737 prefixEnd_98737 := by exact prefixLift 98737
  have htrace : WordTrace (prefixWord ++ tailWord_98737) baseStart_98737 baseEnd_98737 := by
    simpa [prefixWord, tailWord_98737, baseEnd_98737] using wordTrace_append hprefix tailTrace_98737
  have hstable : (prefixWord ++ tailWord_98737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98737).length < 2 ^ (prefixWord ++ tailWord_98737).sum := by decide
  have hdescent : baseEnd_98737 < baseStart_98737 := by decide
  rcases family_descends (prefixWord ++ tailWord_98737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98796 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_98796 : Nat := 118140960795 + 98796 * 2 ^ 59
def prefixEnd_98796 : Nat := 4983230072969 + 3 ^ 40 * 98796 * 2
def baseEnd_98796 : Nat := 45093186437067283462801

theorem tailTrace_98796 : CollatzResearch.WordTrace tailWord_98796 prefixEnd_98796 45093186437067283462801 := by
  unfold tailWord_98796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801693075043219929290121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2402257433390959905720161 1801693075043219929290121)
  ·
    refine ⟨1351269806282414946967591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1801693075043219929290121 1351269806282414946967591)
    ·
      refine ⟨2026904709423622420451387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351269806282414946967591 2026904709423622420451387)
      ·
        refine ⟨3040357064135433630677081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026904709423622420451387 3040357064135433630677081)
        ·
          refine ⟨2280267798101575223007811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040357064135433630677081 2280267798101575223007811)
          ·
            refine ⟨3420401697152362834511717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280267798101575223007811 3420401697152362834511717)
            ·
              refine ⟨641325318216068031470947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3420401697152362834511717 641325318216068031470947)
              ·
                refine ⟨961987977324102047206421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641325318216068031470947 961987977324102047206421)
                ·
                  refine ⟨45093186437067283462801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 961987977324102047206421 45093186437067283462801)
                  ·
                    rfl

theorem cell20_98796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_98796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98796 prefixEnd_98796 := by exact prefixLift 98796
  have htrace : WordTrace (prefixWord ++ tailWord_98796) baseStart_98796 baseEnd_98796 := by
    simpa [prefixWord, tailWord_98796, baseEnd_98796] using wordTrace_append hprefix tailTrace_98796
  have hstable : (prefixWord ++ tailWord_98796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98796).length < 2 ^ (prefixWord ++ tailWord_98796).sum := by decide
  have hdescent : baseEnd_98796 < baseStart_98796 := by decide
  rcases family_descends (prefixWord ++ tailWord_98796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98803 : List Nat := [1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_98803 : Nat := 118140960795 + 98803 * 2 ^ 59
def prefixEnd_98803 : Nat := 4983230072969 + 3 ^ 40 * 98803 * 2
def baseEnd_98803 : Nat := 15032127142602123409813

theorem tailTrace_98803 : CollatzResearch.WordTrace tailWord_98803 prefixEnd_98803 15032127142602123409813 := by
  unfold tailWord_98803
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603641461061080054085063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2402427640707386702723375 3603641461061080054085063)
  ·
    refine ⟨5405462191591620081127595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603641461061080054085063 5405462191591620081127595)
    ·
      refine ⟨8108193287387430121691393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405462191591620081127595 8108193287387430121691393)
      ·
        refine ⟨6081144965540572591268545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108193287387430121691393 6081144965540572591268545)
        ·
          refine ⟨4560858724155429443451409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081144965540572591268545 4560858724155429443451409)
          ·
            refine ⟨3420644043116572082588557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560858724155429443451409 3420644043116572082588557)
            ·
              refine ⟨1282741516168714530970709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3420644043116572082588557 1282741516168714530970709)
              ·
                refine ⟨15032127142602123409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1282741516168714530970709 15032127142602123409813)
                ·
                  rfl

theorem cell20_98803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_98803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98803 prefixEnd_98803 := by exact prefixLift 98803
  have htrace : WordTrace (prefixWord ++ tailWord_98803) baseStart_98803 baseEnd_98803 := by
    simpa [prefixWord, tailWord_98803, baseEnd_98803] using wordTrace_append hprefix tailTrace_98803
  have hstable : (prefixWord ++ tailWord_98803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98803).length < 2 ^ (prefixWord ++ tailWord_98803).sum := by decide
  have hdescent : baseEnd_98803 < baseStart_98803 := by decide
  rcases family_descends (prefixWord ++ tailWord_98803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98820 : List Nat := [2, 3, 2, 3, 1, 9]
def baseStart_98820 : Nat := 118140960795 + 98820 * 2 ^ 59
def prefixEnd_98820 : Nat := 4983230072969 + 3 ^ 40 * 98820 * 2
def baseEnd_98820 : Nat := 1670523729297402468989

theorem tailTrace_98820 : CollatzResearch.WordTrace tailWord_98820 prefixEnd_98820 1670523729297402468989 := by
  unfold tailWord_98820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802130750999745978726957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2402841001332994638302609 1802130750999745978726957)
  ·
    refine ⟨675799031624904742022609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1802130750999745978726957 675799031624904742022609)
    ·
      refine ⟨506849273718678556516957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675799031624904742022609 506849273718678556516957)
      ·
        refine ⟨190068477644504458693859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506849273718678556516957 190068477644504458693859)
        ·
          refine ⟨285102716466756688040789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190068477644504458693859 285102716466756688040789)
          ·
            refine ⟨1670523729297402468989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 285102716466756688040789 1670523729297402468989)
            ·
              rfl

theorem cell20_98820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 9].length) (baseStart_98820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98820 prefixEnd_98820 := by exact prefixLift 98820
  have htrace : WordTrace (prefixWord ++ tailWord_98820) baseStart_98820 baseEnd_98820 := by
    simpa [prefixWord, tailWord_98820, baseEnd_98820] using wordTrace_append hprefix tailTrace_98820
  have hstable : (prefixWord ++ tailWord_98820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98820).length < 2 ^ (prefixWord ++ tailWord_98820).sum := by decide
  have hdescent : baseEnd_98820 < baseStart_98820 := by decide
  rcases family_descends (prefixWord ++ tailWord_98820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98822 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_98822 : Nat := 118140960795 + 98822 * 2 ^ 59
def prefixEnd_98822 : Nat := 4983230072969 + 3 ^ 40 * 98822 * 2
def baseEnd_98822 : Nat := 45105053545526748596029

theorem tailTrace_98822 : CollatzResearch.WordTrace tailWord_98822 prefixEnd_98822 45105053545526748596029 := by
  unfold tailWord_98822
  simp only [CollatzResearch.WordTrace]
  refine ⟨112635451499757696844585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2402889631994830866017813 112635451499757696844585)
  ·
    refine ⟨84476588624818272633439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112635451499757696844585 84476588624818272633439)
    ·
      refine ⟨126714882937227408950159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84476588624818272633439 126714882937227408950159)
      ·
        refine ⟨190072324405841113425239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126714882937227408950159 190072324405841113425239)
        ·
          refine ⟨285108486608761670137859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190072324405841113425239 285108486608761670137859)
          ·
            refine ⟨427662729913142505206789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285108486608761670137859 427662729913142505206789)
            ·
              refine ⟨80186761858714219726273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427662729913142505206789 80186761858714219726273)
              ·
                refine ⟨60140071394035664794705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80186761858714219726273 60140071394035664794705)
                ·
                  refine ⟨45105053545526748596029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60140071394035664794705 45105053545526748596029)
                  ·
                    rfl

theorem cell20_98822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_98822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98822 prefixEnd_98822 := by exact prefixLift 98822
  have htrace : WordTrace (prefixWord ++ tailWord_98822) baseStart_98822 baseEnd_98822 := by
    simpa [prefixWord, tailWord_98822, baseEnd_98822] using wordTrace_append hprefix tailTrace_98822
  have hstable : (prefixWord ++ tailWord_98822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98822).length < 2 ^ (prefixWord ++ tailWord_98822).sum := by decide
  have hdescent : baseEnd_98822 < baseStart_98822 := by decide
  rcases family_descends (prefixWord ++ tailWord_98822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98823 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_98823 : Nat := 118140960795 + 98823 * 2 ^ 59
def prefixEnd_98823 : Nat := 4983230072969 + 3 ^ 40 * 98823 * 2
def baseEnd_98823 : Nat := 45105509972775189562691

theorem tailTrace_98823 : CollatzResearch.WordTrace tailWord_98823 prefixEnd_98823 45105509972775189562691 := by
  unfold tailWord_98823
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604370920988623469813123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2402913947325748979875415 3604370920988623469813123)
  ·
    refine ⟨5406556381482935204719685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3604370920988623469813123 5406556381482935204719685)
    ·
      refine ⟨1013729321528050350884941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5406556381482935204719685 1013729321528050350884941)
      ·
        refine ⟨380148495573018881581853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1013729321528050350884941 380148495573018881581853)
        ·
          refine ⟨142555685839882080593195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380148495573018881581853 142555685839882080593195)
          ·
            refine ⟨213833528759823120889793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142555685839882080593195 213833528759823120889793)
            ·
              refine ⟨160375146569867340667345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213833528759823120889793 160375146569867340667345)
              ·
                refine ⟨120281359927400505500509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160375146569867340667345 120281359927400505500509)
                ·
                  refine ⟨45105509972775189562691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120281359927400505500509 45105509972775189562691)
                  ·
                    rfl

theorem cell20_98823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_98823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98823 prefixEnd_98823 := by exact prefixLift 98823
  have htrace : WordTrace (prefixWord ++ tailWord_98823) baseStart_98823 baseEnd_98823 := by
    simpa [prefixWord, tailWord_98823, baseEnd_98823] using wordTrace_append hprefix tailTrace_98823
  have hstable : (prefixWord ++ tailWord_98823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98823).length < 2 ^ (prefixWord ++ tailWord_98823).sum := by decide
  have hdescent : baseEnd_98823 < baseStart_98823 := by decide
  rcases family_descends (prefixWord ++ tailWord_98823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98844 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_98844 : Nat := 118140960795 + 98844 * 2 ^ 59
def prefixEnd_98844 : Nat := 4983230072969 + 3 ^ 40 * 98844 * 2
def baseEnd_98844 : Nat := 45115094944992449862605

theorem tailTrace_98844 : CollatzResearch.WordTrace tailWord_98844 prefixEnd_98844 45115094944992449862605 := by
  unfold tailWord_98844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802568426956272028163793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2403424569275029370885057 1802568426956272028163793)
  ·
    refine ⟨1351926320217204021122845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802568426956272028163793 1351926320217204021122845)
    ·
      refine ⟨506972370081451507921067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1351926320217204021122845 506972370081451507921067)
      ·
        refine ⟨760458555122177261881601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506972370081451507921067 760458555122177261881601)
        ·
          refine ⟨570343916341632946411201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760458555122177261881601 570343916341632946411201)
          ·
            refine ⟨427757937256224709808401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570343916341632946411201 427757937256224709808401)
            ·
              refine ⟨320818452942168532356301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427757937256224709808401 320818452942168532356301)
              ·
                refine ⟨120306919853313199633613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320818452942168532356301 120306919853313199633613)
                ·
                  refine ⟨45115094944992449862605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120306919853313199633613 45115094944992449862605)
                  ·
                    rfl

theorem cell20_98844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_98844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98844 prefixEnd_98844 := by exact prefixLift 98844
  have htrace : WordTrace (prefixWord ++ tailWord_98844) baseStart_98844 baseEnd_98844 := by
    simpa [prefixWord, tailWord_98844, baseEnd_98844] using wordTrace_append hprefix tailTrace_98844
  have hstable : (prefixWord ++ tailWord_98844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98844).length < 2 ^ (prefixWord ++ tailWord_98844).sum := by decide
  have hdescent : baseEnd_98844 < baseStart_98844 := by decide
  rcases family_descends (prefixWord ++ tailWord_98844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98851 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_98851 : Nat := 118140960795 + 98851 * 2 ^ 59
def prefixEnd_98851 : Nat := 4983230072969 + 3 ^ 40 * 98851 * 2
def baseEnd_98851 : Nat := 45118289935731536629243

theorem tailTrace_98851 : CollatzResearch.WordTrace tailWord_98851 prefixEnd_98851 45118289935731536629243 := by
  unfold tailWord_98851
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605392164887184251832407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2403594776591456167888271 3605392164887184251832407)
  ·
    refine ⟨5408088247330776377748611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605392164887184251832407 5408088247330776377748611)
    ·
      refine ⟨8112132370996164566622917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408088247330776377748611 8112132370996164566622917)
      ·
        refine ⟨1521024819561780856241797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8112132370996164566622917 1521024819561780856241797)
        ·
          refine ⟨285192153667833910545337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1521024819561780856241797 285192153667833910545337)
          ·
            refine ⟨213894115250875432909003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285192153667833910545337 213894115250875432909003)
            ·
              refine ⟨320841172876313149363505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213894115250875432909003 320841172876313149363505)
              ·
                refine ⟨240630879657234862022629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320841172876313149363505 240630879657234862022629)
                ·
                  refine ⟨45118289935731536629243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240630879657234862022629 45118289935731536629243)
                  ·
                    rfl

theorem cell20_98851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_98851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98851 prefixEnd_98851 := by exact prefixLift 98851
  have htrace : WordTrace (prefixWord ++ tailWord_98851) baseStart_98851 baseEnd_98851 := by
    simpa [prefixWord, tailWord_98851, baseEnd_98851] using wordTrace_append hprefix tailTrace_98851
  have hstable : (prefixWord ++ tailWord_98851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98851).length < 2 ^ (prefixWord ++ tailWord_98851).sum := by decide
  have hdescent : baseEnd_98851 < baseStart_98851 := by decide
  rcases family_descends (prefixWord ++ tailWord_98851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98872 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_98872 : Nat := 118140960795 + 98872 * 2 ^ 59
def prefixEnd_98872 : Nat := 4983230072969 + 3 ^ 40 * 98872 * 2
def baseEnd_98872 : Nat := 45127874907948796929157

theorem tailTrace_98872 : CollatzResearch.WordTrace tailWord_98872 prefixEnd_98872 45127874907948796929157 := by
  unfold tailWord_98872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803079048905552419173435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2404105398540736558897913 1803079048905552419173435)
  ·
    refine ⟨2704618573358328628760153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1803079048905552419173435 2704618573358328628760153)
    ·
      refine ⟨2028463930018746471570115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2704618573358328628760153 2028463930018746471570115)
      ·
        refine ⟨3042695895028119707355173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028463930018746471570115 3042695895028119707355173)
        ·
          refine ⟨570505480317772445129095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3042695895028119707355173 570505480317772445129095)
          ·
            refine ⟨855758220476658667693643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570505480317772445129095 855758220476658667693643)
            ·
              refine ⟨1283637330714988001540465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855758220476658667693643 1283637330714988001540465)
              ·
                refine ⟨962727998036241001155349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283637330714988001540465 962727998036241001155349)
                ·
                  refine ⟨45127874907948796929157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 962727998036241001155349 45127874907948796929157)
                  ·
                    rfl

theorem cell20_98872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_98872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98872 prefixEnd_98872 := by exact prefixLift 98872
  have htrace : WordTrace (prefixWord ++ tailWord_98872) baseStart_98872 baseEnd_98872 := by
    simpa [prefixWord, tailWord_98872, baseEnd_98872] using wordTrace_append hprefix tailTrace_98872
  have hstable : (prefixWord ++ tailWord_98872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98872).length < 2 ^ (prefixWord ++ tailWord_98872).sum := by decide
  have hdescent : baseEnd_98872 < baseStart_98872 := by decide
  rcases family_descends (prefixWord ++ tailWord_98872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98879 : List Nat := [1, 1, 2, 2, 3, 2, 9]
def baseStart_98879 : Nat := 118140960795 + 98879 * 2 ^ 59
def prefixEnd_98879 : Nat := 4983230072969 + 3 ^ 40 * 98879 * 2
def baseEnd_98879 : Nat := 5014563322076431521755

theorem tailTrace_98879 : CollatzResearch.WordTrace tailWord_98879 prefixEnd_98879 5014563322076431521755 := by
  unfold tailWord_98879
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606413408785745033851691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2404275605857163355901127 3606413408785745033851691)
  ·
    refine ⟨5409620113178617550777537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606413408785745033851691 5409620113178617550777537)
    ·
      refine ⟨4057215084883963163083153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409620113178617550777537 4057215084883963163083153)
      ·
        refine ⟨3042911313662972372312365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057215084883963163083153 3042911313662972372312365)
        ·
          refine ⟨1141091742623614639617137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3042911313662972372312365 1141091742623614639617137)
          ·
            refine ⟨855818806967710979712853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141091742623614639617137 855818806967710979712853)
            ·
              refine ⟨5014563322076431521755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 855818806967710979712853 5014563322076431521755)
              ·
                rfl

theorem cell20_98879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_98879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98879 prefixEnd_98879 := by exact prefixLift 98879
  have htrace : WordTrace (prefixWord ++ tailWord_98879) baseStart_98879 baseEnd_98879 := by
    simpa [prefixWord, tailWord_98879, baseEnd_98879] using wordTrace_append hprefix tailTrace_98879
  have hstable : (prefixWord ++ tailWord_98879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98879).length < 2 ^ (prefixWord ++ tailWord_98879).sum := by decide
  have hdescent : baseEnd_98879 < baseStart_98879 := by decide
  rcases family_descends (prefixWord ++ tailWord_98879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98913 : List Nat := [1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_98913 : Nat := 118140960795 + 98913 * 2 ^ 59
def prefixEnd_98913 : Nat := 4983230072969 + 3 ^ 40 * 98913 * 2
def baseEnd_98913 : Nat := 15048862808378292187441

theorem tailTrace_98913 : CollatzResearch.WordTrace tailWord_98913 prefixEnd_98913 15048862808378292187441 := by
  unfold tailWord_98913
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607653490662568840589393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2405102327108379227059595 3607653490662568840589393)
  ·
    refine ⟨2705740117996926630442045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3607653490662568840589393 2705740117996926630442045)
    ·
      refine ⟨1014652544248847486415767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2705740117996926630442045 1014652544248847486415767)
      ·
        refine ⟨1521978816373271229623651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014652544248847486415767 1521978816373271229623651)
        ·
          refine ⟨2282968224559906844435477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521978816373271229623651 2282968224559906844435477)
          ·
            refine ⟨107014135526245633332913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2282968224559906844435477 107014135526245633332913)
            ·
              refine ⟨80260601644684224999685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107014135526245633332913 80260601644684224999685)
              ·
                refine ⟨15048862808378292187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80260601644684224999685 15048862808378292187441)
                ·
                  rfl

theorem cell20_98913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_98913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98913 prefixEnd_98913 := by exact prefixLift 98913
  have htrace : WordTrace (prefixWord ++ tailWord_98913) baseStart_98913 baseEnd_98913 := by
    simpa [prefixWord, tailWord_98913, baseEnd_98913] using wordTrace_append hprefix tailTrace_98913
  have hstable : (prefixWord ++ tailWord_98913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98913).length < 2 ^ (prefixWord ++ tailWord_98913).sum := by decide
  have hdescent : baseEnd_98913 < baseStart_98913 := by decide
  rcases family_descends (prefixWord ++ tailWord_98913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98954 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_98954 : Nat := 118140960795 + 98954 * 2 ^ 59
def prefixEnd_98954 : Nat := 4983230072969 + 3 ^ 40 * 98954 * 2
def baseEnd_98954 : Nat := 45165301942320956195489

theorem tailTrace_98954 : CollatzResearch.WordTrace tailWord_98954 prefixEnd_98954 45165301942320956195489 := by
  unfold tailWord_98954
  simp only [CollatzResearch.WordTrace]
  refine ⟨902287220878508210707979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2406099255676021895221277 902287220878508210707979)
  ·
    refine ⟨1353430831317762316061969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 902287220878508210707979 1353430831317762316061969)
    ·
      refine ⟨1015073123488321737046477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1353430831317762316061969 1015073123488321737046477)
      ·
        refine ⟨380652421308120651392429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015073123488321737046477 380652421308120651392429)
        ·
          refine ⟨142744657990545244272161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380652421308120651392429 142744657990545244272161)
          ·
            refine ⟨107058493492908933204121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142744657990545244272161 107058493492908933204121)
            ·
              refine ⟨80293870119681699903091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107058493492908933204121 80293870119681699903091)
              ·
                refine ⟨120440805179522549854637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80293870119681699903091 120440805179522549854637)
                ·
                  refine ⟨45165301942320956195489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120440805179522549854637 45165301942320956195489)
                  ·
                    rfl

theorem cell20_98954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_98954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98954 prefixEnd_98954 := by exact prefixLift 98954
  have htrace : WordTrace (prefixWord ++ tailWord_98954) baseStart_98954 baseEnd_98954 := by
    simpa [prefixWord, tailWord_98954, baseEnd_98954] using wordTrace_append hprefix tailTrace_98954
  have hstable : (prefixWord ++ tailWord_98954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98954).length < 2 ^ (prefixWord ++ tailWord_98954).sum := by decide
  have hdescent : baseEnd_98954 < baseStart_98954 := by decide
  rcases family_descends (prefixWord ++ tailWord_98954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98958 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_98958 : Nat := 118140960795 + 98958 * 2 ^ 59
def prefixEnd_98958 : Nat := 4983230072969 + 3 ^ 40 * 98958 * 2
def baseEnd_98958 : Nat := 45167127651314720062139

theorem tailTrace_98958 : CollatzResearch.WordTrace tailWord_98958 prefixEnd_98958 45167127651314720062139 := by
  unfold tailWord_98958
  simp only [CollatzResearch.WordTrace]
  refine ⟨451161846937442690747191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2406196516999694350651685 451161846937442690747191)
  ·
    refine ⟨676742770406164036120787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451161846937442690747191 676742770406164036120787)
    ·
      refine ⟨1015114155609246054181181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676742770406164036120787 1015114155609246054181181)
      ·
        refine ⟨380667808353467270317943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015114155609246054181181 380667808353467270317943)
        ·
          refine ⟨571001712530200905476915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380667808353467270317943 571001712530200905476915)
          ·
            refine ⟨856502568795301358215373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571001712530200905476915 856502568795301358215373)
            ·
              refine ⟨321188463298238009330765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856502568795301358215373 321188463298238009330765)
              ·
                refine ⟨120445673736839253499037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321188463298238009330765 120445673736839253499037)
                ·
                  refine ⟨45167127651314720062139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120445673736839253499037 45167127651314720062139)
                  ·
                    rfl

theorem cell20_98958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_98958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98958 prefixEnd_98958 := by exact prefixLift 98958
  have htrace : WordTrace (prefixWord ++ tailWord_98958) baseStart_98958 baseEnd_98958 := by
    simpa [prefixWord, tailWord_98958, baseEnd_98958] using wordTrace_append hprefix tailTrace_98958
  have hstable : (prefixWord ++ tailWord_98958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98958).length < 2 ^ (prefixWord ++ tailWord_98958).sum := by decide
  have hdescent : baseEnd_98958 < baseStart_98958 := by decide
  rcases family_descends (prefixWord ++ tailWord_98958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98972 : List Nat := [2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_98972 : Nat := 118140960795 + 98972 * 2 ^ 59
def prefixEnd_98972 : Nat := 4983230072969 + 3 ^ 40 * 98972 * 2
def baseEnd_98972 : Nat := 15057839210930964531805

theorem tailTrace_98972 : CollatzResearch.WordTrace tailWord_98972 prefixEnd_98972 15057839210930964531805 := by
  unfold tailWord_98972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804902698724410958493585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2406536931632547944658113 1804902698724410958493585)
  ·
    refine ⟨1353677024043308218870189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1804902698724410958493585 1353677024043308218870189)
    ·
      refine ⟨507628884016240582076321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1353677024043308218870189 507628884016240582076321)
      ·
        refine ⟨380721663012180436557241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507628884016240582076321 380721663012180436557241)
        ·
          refine ⟨285541247259135327417931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380721663012180436557241 285541247259135327417931)
          ·
            refine ⟨428311870888702991126897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285541247259135327417931 428311870888702991126897)
            ·
              refine ⟨321233903166527243345173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428311870888702991126897 321233903166527243345173)
              ·
                refine ⟨15057839210930964531805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321233903166527243345173 15057839210930964531805)
                ·
                  rfl

theorem cell20_98972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_98972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_98972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_98972 prefixEnd_98972 := by exact prefixLift 98972
  have htrace : WordTrace (prefixWord ++ tailWord_98972) baseStart_98972 baseEnd_98972 := by
    simpa [prefixWord, tailWord_98972, baseEnd_98972] using wordTrace_append hprefix tailTrace_98972
  have hstable : (prefixWord ++ tailWord_98972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98972).length < 2 ^ (prefixWord ++ tailWord_98972).sum := by decide
  have hdescent : baseEnd_98972 < baseStart_98972 := by decide
  rcases family_descends (prefixWord ++ tailWord_98972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99048 : List Nat := [2, 1, 4, 1, 4, 1, 7]
def baseStart_99048 : Nat := 118140960795 + 99048 * 2 ^ 59
def prefixEnd_99048 : Nat := 4983230072969 + 3 ^ 40 * 99048 * 2
def baseEnd_99048 : Nat := 5023134011519378562419

theorem tailTrace_99048 : CollatzResearch.WordTrace tailWord_99048 prefixEnd_99048 5023134011519378562419 := by
  unfold tailWord_99048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806288672586743448376899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2408384896782324597835865 1806288672586743448376899)
  ·
    refine ⟨2709433008880115172565349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806288672586743448376899 2709433008880115172565349)
    ·
      refine ⟨508018689165021594856003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2709433008880115172565349 508018689165021594856003)
      ·
        refine ⟨762028033747532392284005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508018689165021594856003 762028033747532392284005)
        ·
          refine ⟨142880256327662323553251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 762028033747532392284005 142880256327662323553251)
          ·
            refine ⟨214320384491493485329877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142880256327662323553251 214320384491493485329877)
            ·
              refine ⟨5023134011519378562419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 214320384491493485329877 5023134011519378562419)
              ·
                rfl

theorem cell20_99048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_99048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99048 prefixEnd_99048 := by exact prefixLift 99048
  have htrace : WordTrace (prefixWord ++ tailWord_99048) baseStart_99048 baseEnd_99048 := by
    simpa [prefixWord, tailWord_99048, baseEnd_99048] using wordTrace_append hprefix tailTrace_99048
  have hstable : (prefixWord ++ tailWord_99048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99048).length < 2 ^ (prefixWord ++ tailWord_99048).sum := by decide
  have hdescent : baseEnd_99048 < baseStart_99048 := by decide
  rcases family_descends (prefixWord ++ tailWord_99048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99055 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_99055 : Nat := 118140960795 + 99055 * 2 ^ 59
def prefixEnd_99055 : Nat := 4983230072969 + 3 ^ 40 * 99055 * 2
def baseEnd_99055 : Nat := 45211401094413493828409

theorem tailTrace_99055 : CollatzResearch.WordTrace tailWord_99055 prefixEnd_99055 45211401094413493828409 := by
  unfold tailWord_99055
  simp only [CollatzResearch.WordTrace]
  refine ⟨3612832656148127092258619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2408555104098751394839079 3612832656148127092258619)
  ·
    refine ⟨5419248984222190638387929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3612832656148127092258619 5419248984222190638387929)
    ·
      refine ⟨4064436738166642978790947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5419248984222190638387929 4064436738166642978790947)
      ·
        refine ⟨6096655107249964468186421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064436738166642978790947 6096655107249964468186421)
        ·
          refine ⟨571561416304684168892477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6096655107249964468186421 571561416304684168892477)
          ·
            refine ⟨214335531114256563334679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571561416304684168892477 214335531114256563334679)
            ·
              refine ⟨321503296671384845002019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214335531114256563334679 321503296671384845002019)
              ·
                refine ⟨482254945007077267503029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321503296671384845002019 482254945007077267503029)
                ·
                  refine ⟨45211401094413493828409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482254945007077267503029 45211401094413493828409)
                  ·
                    rfl

theorem cell20_99055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_99055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99055 prefixEnd_99055 := by exact prefixLift 99055
  have htrace : WordTrace (prefixWord ++ tailWord_99055) baseStart_99055 baseEnd_99055 := by
    simpa [prefixWord, tailWord_99055, baseEnd_99055] using wordTrace_append hprefix tailTrace_99055
  have hstable : (prefixWord ++ tailWord_99055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99055).length < 2 ^ (prefixWord ++ tailWord_99055).sum := by decide
  have hdescent : baseEnd_99055 < baseStart_99055 := by decide
  rcases family_descends (prefixWord ++ tailWord_99055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99058 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_99058 : Nat := 118140960795 + 99058 * 2 ^ 59
def prefixEnd_99058 : Nat := 4983230072969 + 3 ^ 40 * 99058 * 2
def baseEnd_99058 : Nat := 45212770376158816728397

theorem tailTrace_99058 : CollatzResearch.WordTrace tailWord_99058 prefixEnd_99058 45212770376158816728397 := by
  unfold tailWord_99058
  simp only [CollatzResearch.WordTrace]
  refine ⟨903235518784314651154457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2408628050091505736411885 903235518784314651154457)
  ·
    refine ⟨677426639088235988365843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 903235518784314651154457 677426639088235988365843)
    ·
      refine ⟨1016139958632353982548765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677426639088235988365843 1016139958632353982548765)
      ·
        refine ⟨381052484487132743455787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1016139958632353982548765 381052484487132743455787)
        ·
          refine ⟨571578726730699115183681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381052484487132743455787 571578726730699115183681)
          ·
            refine ⟨428684045048024336387761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571578726730699115183681 428684045048024336387761)
            ·
              refine ⟨321513033786018252290821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428684045048024336387761 321513033786018252290821)
              ·
                refine ⟨60283693834878422304529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321513033786018252290821 60283693834878422304529)
                ·
                  refine ⟨45212770376158816728397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60283693834878422304529 45212770376158816728397)
                  ·
                    rfl

theorem cell20_99058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_99058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99058 prefixEnd_99058 := by exact prefixLift 99058
  have htrace : WordTrace (prefixWord ++ tailWord_99058) baseStart_99058 baseEnd_99058 := by
    simpa [prefixWord, tailWord_99058, baseEnd_99058] using wordTrace_append hprefix tailTrace_99058
  have hstable : (prefixWord ++ tailWord_99058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99058).length < 2 ^ (prefixWord ++ tailWord_99058).sum := by decide
  have hdescent : baseEnd_99058 < baseStart_99058 := by decide
  rcases family_descends (prefixWord ++ tailWord_99058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99069 : List Nat := [1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_99069 : Nat := 118140960795 + 99069 * 2 ^ 59
def prefixEnd_99069 : Nat := 4983230072969 + 3 ^ 40 * 99069 * 2
def baseEnd_99069 : Nat := 15072597025297222453895

theorem tailTrace_99069 : CollatzResearch.WordTrace tailWord_99069 prefixEnd_99069 15072597025297222453895 := by
  unfold tailWord_99069
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613343278097407483268261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2408895518731604988845507 3613343278097407483268261)
  ·
    refine ⟨677501864643263903112799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3613343278097407483268261 677501864643263903112799)
    ·
      refine ⟨1016252796964895854669199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677501864643263903112799 1016252796964895854669199)
      ·
        refine ⟨1524379195447343782003799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016252796964895854669199 1524379195447343782003799)
        ·
          refine ⟨2286568793171015673005699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524379195447343782003799 2286568793171015673005699)
          ·
            refine ⟨3429853189756523509508549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286568793171015673005699 3429853189756523509508549)
            ·
              refine ⟨643097473079348158032853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3429853189756523509508549 643097473079348158032853)
              ·
                refine ⟨15072597025297222453895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 643097473079348158032853 15072597025297222453895)
                ·
                  rfl

theorem cell20_99069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_99069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99069 prefixEnd_99069 := by exact prefixLift 99069
  have htrace : WordTrace (prefixWord ++ tailWord_99069) baseStart_99069 baseEnd_99069 := by
    simpa [prefixWord, tailWord_99069, baseEnd_99069] using wordTrace_append hprefix tailTrace_99069
  have hstable : (prefixWord ++ tailWord_99069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99069).length < 2 ^ (prefixWord ++ tailWord_99069).sum := by decide
  have hdescent : baseEnd_99069 < baseStart_99069 := by decide
  rcases family_descends (prefixWord ++ tailWord_99069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99079 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_99079 : Nat := 118140960795 + 99079 * 2 ^ 59
def prefixEnd_99079 : Nat := 4983230072969 + 3 ^ 40 * 99079 * 2
def baseEnd_99079 : Nat := 45222355348376077028311

theorem tailTrace_99079 : CollatzResearch.WordTrace tailWord_99079 prefixEnd_99079 45222355348376077028311 := by
  unfold tailWord_99079
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613708008061179191132291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2409138672040786127421527 3613708008061179191132291)
  ·
    refine ⟨5420562012091768786698437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613708008061179191132291 5420562012091768786698437)
    ·
      refine ⟨1016355377267206647505957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5420562012091768786698437 1016355377267206647505957)
      ·
        refine ⟨190566633237601246407367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1016355377267206647505957 190566633237601246407367)
        ·
          refine ⟨285849949856401869611051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190566633237601246407367 285849949856401869611051)
          ·
            refine ⟨428774924784602804416577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285849949856401869611051 428774924784602804416577)
            ·
              refine ⟨321581193588452103312433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428774924784602804416577 321581193588452103312433)
              ·
                refine ⟨241185895191339077484325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321581193588452103312433 241185895191339077484325)
                ·
                  refine ⟨45222355348376077028311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241185895191339077484325 45222355348376077028311)
                  ·
                    rfl

theorem cell20_99079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_99079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99079 prefixEnd_99079 := by exact prefixLift 99079
  have htrace : WordTrace (prefixWord ++ tailWord_99079) baseStart_99079 baseEnd_99079 := by
    simpa [prefixWord, tailWord_99079, baseEnd_99079] using wordTrace_append hprefix tailTrace_99079
  have hstable : (prefixWord ++ tailWord_99079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99079).length < 2 ^ (prefixWord ++ tailWord_99079).sum := by decide
  have hdescent : baseEnd_99079 < baseStart_99079 := by decide
  rcases family_descends (prefixWord ++ tailWord_99079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99145 : List Nat := [1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_99145 : Nat := 118140960795 + 99145 * 2 ^ 59
def prefixEnd_99145 : Nat := 4983230072969 + 3 ^ 40 * 99145 * 2
def baseEnd_99145 : Nat := 15084159848924393609347

theorem tailTrace_99145 : CollatzResearch.WordTrace tailWord_99145 prefixEnd_99145 15084159848924393609347 := by
  unfold tailWord_99145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616115225822072463034889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2410743483881381642023259 3616115225822072463034889)
  ·
    refine ⟨2712086419366554347276167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3616115225822072463034889 2712086419366554347276167)
    ·
      refine ⟨4068129629049831520914251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712086419366554347276167 4068129629049831520914251)
      ·
        refine ⟨6102194443574747281371377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068129629049831520914251 6102194443574747281371377)
        ·
          refine ⟨4576645832681060461028533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6102194443574747281371377 4576645832681060461028533)
          ·
            refine ⟨429060546813849418221425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4576645832681060461028533 429060546813849418221425)
            ·
              refine ⟨321795410110387063666069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429060546813849418221425 321795410110387063666069)
              ·
                refine ⟨15084159848924393609347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321795410110387063666069 15084159848924393609347)
                ·
                  rfl

theorem cell20_99145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_99145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99145 prefixEnd_99145 := by exact prefixLift 99145
  have htrace : WordTrace (prefixWord ++ tailWord_99145) baseStart_99145 baseEnd_99145 := by
    simpa [prefixWord, tailWord_99145, baseEnd_99145] using wordTrace_append hprefix tailTrace_99145
  have hstable : (prefixWord ++ tailWord_99145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99145).length < 2 ^ (prefixWord ++ tailWord_99145).sum := by decide
  have hdescent : baseEnd_99145 < baseStart_99145 := by decide
  rcases family_descends (prefixWord ++ tailWord_99145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99152 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_99152 : Nat := 118140960795 + 99152 * 2 ^ 59
def prefixEnd_99152 : Nat := 4983230072969 + 3 ^ 40 * 99152 * 2
def baseEnd_99152 : Nat := 45255674537512267594679

theorem tailTrace_99152 : CollatzResearch.WordTrace tailWord_99152 prefixEnd_99152 45255674537512267594679 := by
  unfold tailWord_99152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808185268398356329269855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2410913691197808439026473 1808185268398356329269855)
  ·
    refine ⟨2712277902597534493904783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808185268398356329269855 2712277902597534493904783)
    ·
      refine ⟨4068416853896301740857175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712277902597534493904783 4068416853896301740857175)
      ·
        refine ⟨6102625280844452611285763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068416853896301740857175 6102625280844452611285763)
        ·
          refine ⟨9153937921266678916928645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102625280844452611285763 9153937921266678916928645)
          ·
            refine ⟨1716363360237502296924121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9153937921266678916928645 1716363360237502296924121)
            ·
              refine ⟨1287272520178126722693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716363360237502296924121 1287272520178126722693091)
              ·
                refine ⟨1930908780267190084039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287272520178126722693091 1930908780267190084039637)
                ·
                  refine ⟨45255674537512267594679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1930908780267190084039637 45255674537512267594679)
                  ·
                    rfl

theorem cell20_99152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_99152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99152 prefixEnd_99152 := by exact prefixLift 99152
  have htrace : WordTrace (prefixWord ++ tailWord_99152) baseStart_99152 baseEnd_99152 := by
    simpa [prefixWord, tailWord_99152, baseEnd_99152] using wordTrace_append hprefix tailTrace_99152
  have hstable : (prefixWord ++ tailWord_99152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99152).length < 2 ^ (prefixWord ++ tailWord_99152).sum := by decide
  have hdescent : baseEnd_99152 < baseStart_99152 := by decide
  rcases family_descends (prefixWord ++ tailWord_99152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99172 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_99172 : Nat := 118140960795 + 99172 * 2 ^ 59
def prefixEnd_99172 : Nat := 4983230072969 + 3 ^ 40 * 99172 * 2
def baseEnd_99172 : Nat := 45264803082481086927931

theorem tailTrace_99172 : CollatzResearch.WordTrace tailWord_99172 prefixEnd_99172 45264803082481086927931 := by
  unfold tailWord_99172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808549998362128037133885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2411399997816170716178513 1808549998362128037133885)
  ·
    refine ⟨678206249385798013925207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1808549998362128037133885 678206249385798013925207)
    ·
      refine ⟨1017309374078697020887811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678206249385798013925207 1017309374078697020887811)
      ·
        refine ⟨1525964061118045531331717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017309374078697020887811 1525964061118045531331717)
        ·
          refine ⟨286118261459633537124697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1525964061118045531331717 286118261459633537124697)
          ·
            refine ⟨214588696094725152843523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286118261459633537124697 214588696094725152843523)
            ·
              refine ⟨321883044142087729265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214588696094725152843523 321883044142087729265285)
              ·
                refine ⟨60353070776641449237241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321883044142087729265285 60353070776641449237241)
                ·
                  refine ⟨45264803082481086927931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60353070776641449237241 45264803082481086927931)
                  ·
                    rfl

theorem cell20_99172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_99172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99172 prefixEnd_99172 := by exact prefixLift 99172
  have htrace : WordTrace (prefixWord ++ tailWord_99172) baseStart_99172 baseEnd_99172 := by
    simpa [prefixWord, tailWord_99172, baseEnd_99172] using wordTrace_append hprefix tailTrace_99172
  have hstable : (prefixWord ++ tailWord_99172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99172).length < 2 ^ (prefixWord ++ tailWord_99172).sum := by decide
  have hdescent : baseEnd_99172 < baseStart_99172 := by decide
  rcases family_descends (prefixWord ++ tailWord_99172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99210 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_99210 : Nat := 118140960795 + 99210 * 2 ^ 59
def prefixEnd_99210 : Nat := 4983230072969 + 3 ^ 40 * 99210 * 2
def baseEnd_99210 : Nat := 45282147317921843661109

theorem tailTrace_99210 : CollatzResearch.WordTrace tailWord_99210 prefixEnd_99210 45282147317921843661109 := by
  unfold tailWord_99210
  simp only [CollatzResearch.WordTrace]
  refine ⟨904621492646647141037771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2412323980391059042767389 904621492646647141037771)
  ·
    refine ⟨1356932238969970711556657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904621492646647141037771 1356932238969970711556657)
    ·
      refine ⟨1017699179227478033667493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1356932238969970711556657 1017699179227478033667493)
      ·
        refine ⟨190818596105152131312655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1017699179227478033667493 190818596105152131312655)
        ·
          refine ⟨286227894157728196968983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190818596105152131312655 286227894157728196968983)
          ·
            refine ⟨429341841236592295453475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286227894157728196968983 429341841236592295453475)
            ·
              refine ⟨644012761854888443180213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429341841236592295453475 644012761854888443180213)
              ·
                refine ⟨60376196423895791548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644012761854888443180213 60376196423895791548145)
                ·
                  refine ⟨45282147317921843661109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60376196423895791548145 45282147317921843661109)
                  ·
                    rfl

theorem cell20_99210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_99210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99210 prefixEnd_99210 := by exact prefixLift 99210
  have htrace : WordTrace (prefixWord ++ tailWord_99210) baseStart_99210 baseEnd_99210 := by
    simpa [prefixWord, tailWord_99210, baseEnd_99210] using wordTrace_append hprefix tailTrace_99210
  have hstable : (prefixWord ++ tailWord_99210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99210).length < 2 ^ (prefixWord ++ tailWord_99210).sum := by decide
  have hdescent : baseEnd_99210 < baseStart_99210 := by decide
  rcases family_descends (prefixWord ++ tailWord_99210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99221 : List Nat := [1, 3, 2, 1, 1, 5, 7]
def baseStart_99221 : Nat := 118140960795 + 99221 * 2 ^ 59
def prefixEnd_99221 : Nat := 4983230072969 + 3 ^ 40 * 99221 * 2
def baseEnd_99221 : Nat := 5031907557517188254933

theorem tailTrace_99221 : CollatzResearch.WordTrace tailWord_99221 prefixEnd_99221 5031907557517188254933 := by
  unfold tailWord_99221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618887173546737442801517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2412591449031158295201011 3618887173546737442801517)
  ·
    refine ⟨1357082690080026541050569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3618887173546737442801517 1357082690080026541050569)
    ·
      refine ⟨1017812017560019905787927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1357082690080026541050569 1017812017560019905787927)
      ·
        refine ⟨1526718026340029858681891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017812017560019905787927 1526718026340029858681891)
        ·
          refine ⟨2290077039510044788022837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526718026340029858681891 2290077039510044788022837)
          ·
            refine ⟨214694722454066698877141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2290077039510044788022837 214694722454066698877141)
            ·
              refine ⟨5031907557517188254933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 214694722454066698877141 5031907557517188254933)
              ·
                rfl

theorem cell20_99221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_99221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99221 prefixEnd_99221 := by exact prefixLift 99221
  have htrace : WordTrace (prefixWord ++ tailWord_99221) baseStart_99221 baseEnd_99221 := by
    simpa [prefixWord, tailWord_99221, baseEnd_99221] using wordTrace_append hprefix tailTrace_99221
  have hstable : (prefixWord ++ tailWord_99221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99221).length < 2 ^ (prefixWord ++ tailWord_99221).sum := by decide
  have hdescent : baseEnd_99221 < baseStart_99221 := by decide
  rcases family_descends (prefixWord ++ tailWord_99221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99231 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_99231 : Nat := 118140960795 + 99231 * 2 ^ 59
def prefixEnd_99231 : Nat := 4983230072969 + 3 ^ 40 * 99231 * 2
def baseEnd_99231 : Nat := 45291732290139103961023

theorem tailTrace_99231 : CollatzResearch.WordTrace tailWord_99231 prefixEnd_99231 45291732290139103961023 := by
  unfold tailWord_99231
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619251903510509150665547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2412834602340339433777031 3619251903510509150665547)
  ·
    refine ⟨5428877855265763725998321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3619251903510509150665547 5428877855265763725998321)
    ·
      refine ⟨4071658391449322794498741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428877855265763725998321 4071658391449322794498741)
      ·
        refine ⟨381717974198374011984257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4071658391449322794498741 381717974198374011984257)
        ·
          refine ⟨286288480648780508988193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381717974198374011984257 286288480648780508988193)
          ·
            refine ⟨214716360486585381741145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286288480648780508988193 214716360486585381741145)
            ·
              refine ⟨161037270364939036305859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214716360486585381741145 161037270364939036305859)
              ·
                refine ⟨241555905547408554458789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161037270364939036305859 241555905547408554458789)
                ·
                  refine ⟨45291732290139103961023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241555905547408554458789 45291732290139103961023)
                  ·
                    rfl

theorem cell20_99231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_99231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99231 prefixEnd_99231 := by exact prefixLift 99231
  have htrace : WordTrace (prefixWord ++ tailWord_99231) baseStart_99231 baseEnd_99231 := by
    simpa [prefixWord, tailWord_99231, baseEnd_99231] using wordTrace_append hprefix tailTrace_99231
  have hstable : (prefixWord ++ tailWord_99231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99231).length < 2 ^ (prefixWord ++ tailWord_99231).sum := by decide
  have hdescent : baseEnd_99231 < baseStart_99231 := by decide
  rcases family_descends (prefixWord ++ tailWord_99231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99286 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_99286 : Nat := 118140960795 + 99286 * 2 ^ 59
def prefixEnd_99286 : Nat := 4983230072969 + 3 ^ 40 * 99286 * 2
def baseEnd_99286 : Nat := 45316835788803357127465

theorem tailTrace_99286 : CollatzResearch.WordTrace tailWord_99286 prefixEnd_99286 45316835788803357127465 := by
  unfold tailWord_99286
  simp only [CollatzResearch.WordTrace]
  refine ⟨226328619894453346494857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2414171945540835695945141 226328619894453346494857)
  ·
    refine ⟨169746464920840009871143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226328619894453346494857 169746464920840009871143)
    ·
      refine ⟨254619697381260014806715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169746464920840009871143 254619697381260014806715)
      ·
        refine ⟨381929546071890022210073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254619697381260014806715 381929546071890022210073)
        ·
          refine ⟨286447159553917516657555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381929546071890022210073 286447159553917516657555)
          ·
            refine ⟨429670739330876274986333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286447159553917516657555 429670739330876274986333)
            ·
              refine ⟨161126527249078603119875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429670739330876274986333 161126527249078603119875)
              ·
                refine ⟨241689790873617904679813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161126527249078603119875 241689790873617904679813)
                ·
                  refine ⟨45316835788803357127465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241689790873617904679813 45316835788803357127465)
                  ·
                    rfl

theorem cell20_99286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_99286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99286 prefixEnd_99286 := by exact prefixLift 99286
  have htrace : WordTrace (prefixWord ++ tailWord_99286) baseStart_99286 baseEnd_99286 := by
    simpa [prefixWord, tailWord_99286, baseEnd_99286] using wordTrace_append hprefix tailTrace_99286
  have hstable : (prefixWord ++ tailWord_99286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99286).length < 2 ^ (prefixWord ++ tailWord_99286).sum := by decide
  have hdescent : baseEnd_99286 < baseStart_99286 := by decide
  rcases family_descends (prefixWord ++ tailWord_99286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99338 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_99338 : Nat := 118140960795 + 99338 * 2 ^ 59
def prefixEnd_99338 : Nat := 4983230072969 + 3 ^ 40 * 99338 * 2
def baseEnd_99338 : Nat := 45340570005722287393919

theorem tailTrace_99338 : CollatzResearch.WordTrace tailWord_99338 prefixEnd_99338 45340570005722287393919 := by
  unfold tailWord_99338
  simp only [CollatzResearch.WordTrace]
  refine ⟨905788628530716606202667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2415436342748577616540445 905788628530716606202667)
  ·
    refine ⟨1358682942796074909304001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905788628530716606202667 1358682942796074909304001)
    ·
      refine ⟨1019012207097056181978001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358682942796074909304001 1019012207097056181978001)
      ·
        refine ⟨764259155322792136483501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019012207097056181978001 764259155322792136483501)
        ·
          refine ⟨286597183246047051181313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764259155322792136483501 286597183246047051181313)
          ·
            refine ⟨214947887434535288385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286597183246047051181313 214947887434535288385985)
            ·
              refine ⟨161210915575901466289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214947887434535288385985 161210915575901466289489)
              ·
                refine ⟨120908186681926099717117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161210915575901466289489 120908186681926099717117)
                ·
                  refine ⟨45340570005722287393919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120908186681926099717117 45340570005722287393919)
                  ·
                    rfl

theorem cell20_99338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_99338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99338 prefixEnd_99338 := by exact prefixLift 99338
  have htrace : WordTrace (prefixWord ++ tailWord_99338) baseStart_99338 baseEnd_99338 := by
    simpa [prefixWord, tailWord_99338, baseEnd_99338] using wordTrace_append hprefix tailTrace_99338
  have hstable : (prefixWord ++ tailWord_99338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99338).length < 2 ^ (prefixWord ++ tailWord_99338).sum := by decide
  have hdescent : baseEnd_99338 < baseStart_99338 := by decide
  rcases family_descends (prefixWord ++ tailWord_99338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99352 : List Nat := [2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_99352 : Nat := 118140960795 + 99352 * 2 ^ 59
def prefixEnd_99352 : Nat := 4983230072969 + 3 ^ 40 * 99352 * 2
def baseEnd_99352 : Nat := 15115653329066820309065

theorem tailTrace_99352 : CollatzResearch.WordTrace tailWord_99352 prefixEnd_99352 15115653329066820309065 := by
  unfold tailWord_99352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811832568036073407910155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2415776757381431210546873 1811832568036073407910155)
  ·
    refine ⟨2717748852054110111865233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811832568036073407910155 2717748852054110111865233)
    ·
      refine ⟨2038311639040582583898925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2717748852054110111865233 2038311639040582583898925)
      ·
        refine ⟨764366864640218468962097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2038311639040582583898925 764366864640218468962097)
        ·
          refine ⟨573275148480163851721573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764366864640218468962097 573275148480163851721573)
          ·
            refine ⟨107489090340030722197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 573275148480163851721573 107489090340030722197795)
            ·
              refine ⟨161233635510046083296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107489090340030722197795 161233635510046083296693)
              ·
                refine ⟨15115653329066820309065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161233635510046083296693 15115653329066820309065)
                ·
                  rfl

theorem cell20_99352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_99352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99352 prefixEnd_99352 := by exact prefixLift 99352
  have htrace : WordTrace (prefixWord ++ tailWord_99352) baseStart_99352 baseEnd_99352 := by
    simpa [prefixWord, tailWord_99352, baseEnd_99352] using wordTrace_append hprefix tailTrace_99352
  have hstable : (prefixWord ++ tailWord_99352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99352).length < 2 ^ (prefixWord ++ tailWord_99352).sum := by decide
  have hdescent : baseEnd_99352 < baseStart_99352 := by decide
  rcases family_descends (prefixWord ++ tailWord_99352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99359 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_99359 : Nat := 118140960795 + 99359 * 2 ^ 59
def prefixEnd_99359 : Nat := 4983230072969 + 3 ^ 40 * 99359 * 2
def baseEnd_99359 : Nat := 45350154977939547693833

theorem tailTrace_99359 : CollatzResearch.WordTrace tailWord_99359 prefixEnd_99359 45350154977939547693833 := by
  unfold tailWord_99359
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623920447046787011325131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2415946964697858007550087 3623920447046787011325131)
  ·
    refine ⟨5435880670570180516987697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3623920447046787011325131 5435880670570180516987697)
    ·
      refine ⟨4076910502927635387740773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5435880670570180516987697 4076910502927635387740773)
      ·
        refine ⟨764420719298931635201395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4076910502927635387740773 764420719298931635201395)
        ·
          refine ⟨1146631078948397452802093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764420719298931635201395 1146631078948397452802093)
          ·
            refine ⟨429986654605649044800785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1146631078948397452802093 429986654605649044800785)
            ·
              refine ⟨322489990954236783600589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429986654605649044800785 322489990954236783600589)
              ·
                refine ⟨120933746607838793850221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322489990954236783600589 120933746607838793850221)
                ·
                  refine ⟨45350154977939547693833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120933746607838793850221 45350154977939547693833)
                  ·
                    rfl

theorem cell20_99359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_99359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99359 prefixEnd_99359 := by exact prefixLift 99359
  have htrace : WordTrace (prefixWord ++ tailWord_99359) baseStart_99359 baseEnd_99359 := by
    simpa [prefixWord, tailWord_99359, baseEnd_99359] using wordTrace_append hprefix tailTrace_99359
  have hstable : (prefixWord ++ tailWord_99359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99359).length < 2 ^ (prefixWord ++ tailWord_99359).sum := by decide
  have hdescent : baseEnd_99359 < baseStart_99359 := by decide
  rcases family_descends (prefixWord ++ tailWord_99359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99390 : List Nat := [4, 2, 1, 3, 1, 2, 7]
def baseStart_99390 : Nat := 118140960795 + 99390 * 2 ^ 59
def prefixEnd_99390 : Nat := 4983230072969 + 3 ^ 40 * 99390 * 2
def baseEnd_99390 : Nat := 5040478246960135295597

theorem tailTrace_99390 : CollatzResearch.WordTrace tailWord_99390 prefixEnd_99390 5040478246960135295597 := by
  unfold tailWord_99390
  simp only [CollatzResearch.WordTrace]
  refine ⟨453131388741809913212953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2416700739956319537135749 453131388741809913212953)
  ·
    refine ⟨339848541556357434909715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 453131388741809913212953 339848541556357434909715)
    ·
      refine ⟨509772812334536152364573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339848541556357434909715 509772812334536152364573)
      ·
        refine ⟨191164804625451057136715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509772812334536152364573 191164804625451057136715)
        ·
          refine ⟨286747206938176585705073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191164804625451057136715 286747206938176585705073)
          ·
            refine ⟨215060405203632439278805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286747206938176585705073 215060405203632439278805)
            ·
              refine ⟨5040478246960135295597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215060405203632439278805 5040478246960135295597)
              ·
                rfl

theorem cell20_99390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_99390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99390 prefixEnd_99390 := by exact prefixLift 99390
  have htrace : WordTrace (prefixWord ++ tailWord_99390) baseStart_99390 baseEnd_99390 := by
    simpa [prefixWord, tailWord_99390, baseEnd_99390] using wordTrace_append hprefix tailTrace_99390
  have hstable : (prefixWord ++ tailWord_99390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99390).length < 2 ^ (prefixWord ++ tailWord_99390).sum := by decide
  have hdescent : baseEnd_99390 < baseStart_99390 := by decide
  rcases family_descends (prefixWord ++ tailWord_99390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99393 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_99393 : Nat := 118140960795 + 99393 * 2 ^ 59
def prefixEnd_99393 : Nat := 4983230072969 + 3 ^ 40 * 99393 * 2
def baseEnd_99393 : Nat := 45365673504386540560361

theorem tailTrace_99393 : CollatzResearch.WordTrace tailWord_99393 prefixEnd_99393 45365673504386540560361 := by
  unfold tailWord_99393
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625160528923610818062833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2416773685949073878708555 3625160528923610818062833)
  ·
    refine ⟨2718870396692708113547125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3625160528923610818062833 2718870396692708113547125)
    ·
      refine ⟨254894099689941385645043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2718870396692708113547125 254894099689941385645043)
      ·
        refine ⟨382341149534912078467565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254894099689941385645043 382341149534912078467565)
        ·
          refine ⟨143377931075592029425337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382341149534912078467565 143377931075592029425337)
          ·
            refine ⟨107533448306694022069003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143377931075592029425337 107533448306694022069003)
            ·
              refine ⟨161300172460041033103505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107533448306694022069003 161300172460041033103505)
              ·
                refine ⟨120975129345030774827629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161300172460041033103505 120975129345030774827629)
                ·
                  refine ⟨45365673504386540560361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120975129345030774827629 45365673504386540560361)
                  ·
                    rfl

theorem cell20_99393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_99393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99393 prefixEnd_99393 := by exact prefixLift 99393
  have htrace : WordTrace (prefixWord ++ tailWord_99393) baseStart_99393 baseEnd_99393 := by
    simpa [prefixWord, tailWord_99393, baseEnd_99393] using wordTrace_append hprefix tailTrace_99393
  have hstable : (prefixWord ++ tailWord_99393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99393).length < 2 ^ (prefixWord ++ tailWord_99393).sum := by decide
  have hdescent : baseEnd_99393 < baseStart_99393 := by decide
  rcases family_descends (prefixWord ++ tailWord_99393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99397 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_99397 : Nat := 118140960795 + 99397 * 2 ^ 59
def prefixEnd_99397 : Nat := 4983230072969 + 3 ^ 40 * 99397 * 2
def baseEnd_99397 : Nat := 45367499213380304427011

theorem tailTrace_99397 : CollatzResearch.WordTrace tailWord_99397 prefixEnd_99397 45367499213380304427011 := by
  unfold tailWord_99397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625306420909119501208445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2416870947272746334138963 3625306420909119501208445)
  ·
    refine ⟨1359489907840919812953167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3625306420909119501208445 1359489907840919812953167)
    ·
      refine ⟨2039234861761379719429751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359489907840919812953167 2039234861761379719429751)
      ·
        refine ⟨3058852292642069579144627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039234861761379719429751 3058852292642069579144627)
        ·
          refine ⟨4588278438963104368716941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058852292642069579144627 4588278438963104368716941)
          ·
            refine ⟨1720604414611164138268853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4588278438963104368716941 1720604414611164138268853)
            ·
              refine ⟨161306663869796637962705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1720604414611164138268853 161306663869796637962705)
              ·
                refine ⟨120979997902347478472029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161306663869796637962705 120979997902347478472029)
                ·
                  refine ⟨45367499213380304427011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120979997902347478472029 45367499213380304427011)
                  ·
                    rfl

theorem cell20_99397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_99397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99397 prefixEnd_99397 := by exact prefixLift 99397
  have htrace : WordTrace (prefixWord ++ tailWord_99397) baseStart_99397 baseEnd_99397 := by
    simpa [prefixWord, tailWord_99397, baseEnd_99397] using wordTrace_append hprefix tailTrace_99397
  have hstable : (prefixWord ++ tailWord_99397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99397).length < 2 ^ (prefixWord ++ tailWord_99397).sum := by decide
  have hdescent : baseEnd_99397 < baseStart_99397 := by decide
  rcases family_descends (prefixWord ++ tailWord_99397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99438 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_99438 : Nat := 118140960795 + 99438 * 2 ^ 59
def prefixEnd_99438 : Nat := 4983230072969 + 3 ^ 40 * 99438 * 2
def baseEnd_99438 : Nat := 45386212730566384060177

theorem tailTrace_99438 : CollatzResearch.WordTrace tailWord_99438 prefixEnd_99438 45386212730566384060177 := by
  unfold tailWord_99438
  simp only [CollatzResearch.WordTrace]
  refine ⟨453350226720072937931371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2417867875840389002300645 453350226720072937931371)
  ·
    refine ⟨680025340080109406897057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453350226720072937931371 680025340080109406897057)
    ·
      refine ⟨510019005060082055172793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680025340080109406897057 510019005060082055172793)
      ·
        refine ⟨382514253795061541379595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510019005060082055172793 382514253795061541379595)
        ·
          refine ⟨573771380692592312069393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382514253795061541379595 573771380692592312069393)
          ·
            refine ⟨430328535519444234052045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573771380692592312069393 430328535519444234052045)
            ·
              refine ⟨161373200819791587769517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430328535519444234052045 161373200819791587769517)
              ·
                refine ⟨60514950307421845413569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161373200819791587769517 60514950307421845413569)
                ·
                  refine ⟨45386212730566384060177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60514950307421845413569 45386212730566384060177)
                  ·
                    rfl

theorem cell20_99438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_99438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99438 prefixEnd_99438 := by exact prefixLift 99438
  have htrace : WordTrace (prefixWord ++ tailWord_99438) baseStart_99438 baseEnd_99438 := by
    simpa [prefixWord, tailWord_99438, baseEnd_99438] using wordTrace_append hprefix tailTrace_99438
  have hstable : (prefixWord ++ tailWord_99438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99438).length < 2 ^ (prefixWord ++ tailWord_99438).sum := by decide
  have hdescent : baseEnd_99438 < baseStart_99438 := by decide
  rcases family_descends (prefixWord ++ tailWord_99438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99445 : List Nat := [1, 3, 4, 3, 1, 2, 6]
def baseStart_99445 : Nat := 118140960795 + 99445 * 2 ^ 59
def prefixEnd_99445 : Nat := 4983230072969 + 3 ^ 40 * 99445 * 2
def baseEnd_99445 : Nat := 5043267524589496758535

theorem tailTrace_99445 : CollatzResearch.WordTrace tailWord_99445 prefixEnd_99445 5043267524589496758535 := by
  unfold tailWord_99445
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627057124735223698955789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2418038083156815799303859 3627057124735223698955789)
  ·
    refine ⟨1360146421775708887108421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3627057124735223698955789 1360146421775708887108421)
    ·
      refine ⟨255027454082945416332829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1360146421775708887108421 255027454082945416332829)
      ·
        refine ⟨95635295281104531124811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255027454082945416332829 95635295281104531124811)
        ·
          refine ⟨143452942921656796687217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95635295281104531124811 143452942921656796687217)
          ·
            refine ⟨107589707191242597515413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143452942921656796687217 107589707191242597515413)
            ·
              refine ⟨5043267524589496758535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107589707191242597515413 5043267524589496758535)
              ·
                rfl

theorem cell20_99445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_99445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99445 prefixEnd_99445 := by exact prefixLift 99445
  have htrace : WordTrace (prefixWord ++ tailWord_99445) baseStart_99445 baseEnd_99445 := by
    simpa [prefixWord, tailWord_99445, baseEnd_99445] using wordTrace_append hprefix tailTrace_99445
  have hstable : (prefixWord ++ tailWord_99445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99445).length < 2 ^ (prefixWord ++ tailWord_99445).sum := by decide
  have hdescent : baseEnd_99445 < baseStart_99445 := by decide
  rcases family_descends (prefixWord ++ tailWord_99445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99456 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_99456 : Nat := 118140960795 + 99456 * 2 ^ 59
def prefixEnd_99456 : Nat := 4983230072969 + 3 ^ 40 * 99456 * 2
def baseEnd_99456 : Nat := 45394428421038321460103

theorem tailTrace_99456 : CollatzResearch.WordTrace tailWord_99456 prefixEnd_99456 45394428421038321460103 := by
  unfold tailWord_99456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813729163847686288803111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2418305551796915051737481 1813729163847686288803111)
  ·
    refine ⟨2720593745771529433204667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813729163847686288803111 2720593745771529433204667)
    ·
      refine ⟨4080890618657294149807001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720593745771529433204667 4080890618657294149807001)
      ·
        refine ⟨3060667963992970612355251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4080890618657294149807001 3060667963992970612355251)
        ·
          refine ⟨4591001945989455918532877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060667963992970612355251 4591001945989455918532877)
          ·
            refine ⟨1721625729746045969449829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4591001945989455918532877 1721625729746045969449829)
            ·
              refine ⟨322804824327383619271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1721625729746045969449829 322804824327383619271843)
              ·
                refine ⟨484207236491075428907765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322804824327383619271843 484207236491075428907765)
                ·
                  refine ⟨45394428421038321460103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484207236491075428907765 45394428421038321460103)
                  ·
                    rfl

theorem cell20_99456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_99456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99456 prefixEnd_99456 := by exact prefixLift 99456
  have htrace : WordTrace (prefixWord ++ tailWord_99456) baseStart_99456 baseEnd_99456 := by
    simpa [prefixWord, tailWord_99456, baseEnd_99456] using wordTrace_append hprefix tailTrace_99456
  have hstable : (prefixWord ++ tailWord_99456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99456).length < 2 ^ (prefixWord ++ tailWord_99456).sum := by decide
  have hdescent : baseEnd_99456 < baseStart_99456 := by decide
  rcases family_descends (prefixWord ++ tailWord_99456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99510 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_99510 : Nat := 118140960795 + 99510 * 2 ^ 59
def prefixEnd_99510 : Nat := 4983230072969 + 3 ^ 40 * 99510 * 2
def baseEnd_99510 : Nat := 45419075492454133659883

theorem tailTrace_99510 : CollatzResearch.WordTrace tailWord_99510 prefixEnd_99510 45419075492454133659883 := by
  unfold tailWord_99510
  simp only [CollatzResearch.WordTrace]
  refine ⟨226839241843733737504499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2419618579666493200047989 226839241843733737504499)
  ·
    refine ⟨340258862765600606256749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226839241843733737504499 340258862765600606256749)
    ·
      refine ⟨127597073537100227346281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340258862765600606256749 127597073537100227346281)
      ·
        refine ⟨95697805152825170509711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127597073537100227346281 95697805152825170509711)
        ·
          refine ⟨143546707729237755764567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95697805152825170509711 143546707729237755764567)
          ·
            refine ⟨215320061593856633646851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143546707729237755764567 215320061593856633646851)
            ·
              refine ⟨322980092390784950470277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215320061593856633646851 322980092390784950470277)
              ·
                refine ⟨60558767323272178213177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322980092390784950470277 60558767323272178213177)
                ·
                  refine ⟨45419075492454133659883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60558767323272178213177 45419075492454133659883)
                  ·
                    rfl

theorem cell20_99510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_99510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99510 prefixEnd_99510 := by exact prefixLift 99510
  have htrace : WordTrace (prefixWord ++ tailWord_99510) baseStart_99510 baseEnd_99510 := by
    simpa [prefixWord, tailWord_99510, baseEnd_99510] using wordTrace_append hprefix tailTrace_99510
  have hstable : (prefixWord ++ tailWord_99510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99510).length < 2 ^ (prefixWord ++ tailWord_99510).sum := by decide
  have hdescent : baseEnd_99510 < baseStart_99510 := by decide
  rcases family_descends (prefixWord ++ tailWord_99510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99511 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_99511 : Nat := 118140960795 + 99511 * 2 ^ 59
def prefixEnd_99511 : Nat := 4983230072969 + 3 ^ 40 * 99511 * 2
def baseEnd_99511 : Nat := 45419531919702574626545

theorem tailTrace_99511 : CollatzResearch.WordTrace tailWord_99511 prefixEnd_99511 45419531919702574626545 := by
  unfold tailWord_99511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629464342496116970858387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2419642894997411313905591 3629464342496116970858387)
  ·
    refine ⟨5444196513744175456287581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629464342496116970858387 5444196513744175456287581)
    ·
      refine ⟨2041573692654065796107843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5444196513744175456287581 2041573692654065796107843)
      ·
        refine ⟨3062360538981098694161765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041573692654065796107843 3062360538981098694161765)
        ·
          refine ⟨574192601058956005155331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3062360538981098694161765 574192601058956005155331)
          ·
            refine ⟨861288901588434007732997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574192601058956005155331 861288901588434007732997)
            ·
              refine ⟨161491669047831376449937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 861288901588434007732997 161491669047831376449937)
              ·
                refine ⟨121118751785873532337453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161491669047831376449937 121118751785873532337453)
                ·
                  refine ⟨45419531919702574626545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121118751785873532337453 45419531919702574626545)
                  ·
                    rfl

theorem cell20_99511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_99511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99511 prefixEnd_99511 := by exact prefixLift 99511
  have htrace : WordTrace (prefixWord ++ tailWord_99511) baseStart_99511 baseEnd_99511 := by
    simpa [prefixWord, tailWord_99511, baseEnd_99511] using wordTrace_append hprefix tailTrace_99511
  have hstable : (prefixWord ++ tailWord_99511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99511).length < 2 ^ (prefixWord ++ tailWord_99511).sum := by decide
  have hdescent : baseEnd_99511 < baseStart_99511 := by decide
  rcases family_descends (prefixWord ++ tailWord_99511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99521 : List Nat := [1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_99521 : Nat := 118140960795 + 99521 * 2 ^ 59
def prefixEnd_99521 : Nat := 4983230072969 + 3 ^ 40 * 99521 * 2
def baseEnd_99521 : Nat := 15141365397395661431057

theorem tailTrace_99521 : CollatzResearch.WordTrace tailWord_99521 prefixEnd_99521 15141365397395661431057 := by
  unfold tailWord_99521
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629829072459888678722417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2419886048306592452481611 3629829072459888678722417)
  ·
    refine ⟨2722371804344916509041813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3629829072459888678722417 2722371804344916509041813)
    ·
      refine ⟨127611178328667961361335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2722371804344916509041813 127611178328667961361335)
      ·
        refine ⟨191416767493001942042003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127611178328667961361335 191416767493001942042003)
        ·
          refine ⟨287125151239502913063005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191416767493001942042003 287125151239502913063005)
          ·
            refine ⟨107671931714813592398627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287125151239502913063005 107671931714813592398627)
            ·
              refine ⟨161507897572220388597941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107671931714813592398627 161507897572220388597941)
              ·
                refine ⟨15141365397395661431057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161507897572220388597941 15141365397395661431057)
                ·
                  rfl

theorem cell20_99521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_99521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99521 prefixEnd_99521 := by exact prefixLift 99521
  have htrace : WordTrace (prefixWord ++ tailWord_99521) baseStart_99521 baseEnd_99521 := by
    simpa [prefixWord, tailWord_99521, baseEnd_99521] using wordTrace_append hprefix tailTrace_99521
  have hstable : (prefixWord ++ tailWord_99521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99521).length < 2 ^ (prefixWord ++ tailWord_99521).sum := by decide
  have hdescent : baseEnd_99521 < baseStart_99521 := by decide
  rcases family_descends (prefixWord ++ tailWord_99521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_99539 : Nat := 118140960795 + 99539 * 2 ^ 59
def prefixEnd_99539 : Nat := 4983230072969 + 3 ^ 40 * 99539 * 2
def baseEnd_99539 : Nat := 45432311882658921693097

theorem tailTrace_99539 : CollatzResearch.WordTrace tailWord_99539 prefixEnd_99539 45432311882658921693097 := by
  unfold tailWord_99539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630485586394677752877671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2420323724263118501918447 3630485586394677752877671)
  ·
    refine ⟨5445728379592016629316507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3630485586394677752877671 5445728379592016629316507)
    ·
      refine ⟨8168592569388024943974761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445728379592016629316507 8168592569388024943974761)
      ·
        refine ⟨6126444427041018707981071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168592569388024943974761 6126444427041018707981071)
        ·
          refine ⟨9189666640561528061971607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126444427041018707981071 9189666640561528061971607)
          ·
            refine ⟨13784499960842292092957411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189666640561528061971607 13784499960842292092957411)
            ·
              refine ⟨20676749941263438139436117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13784499960842292092957411 20676749941263438139436117)
              ·
                refine ⟨242305663374180915696517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20676749941263438139436117 242305663374180915696517)
                ·
                  refine ⟨45432311882658921693097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242305663374180915696517 45432311882658921693097)
                  ·
                    rfl

theorem cell20_99539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_99539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99539 prefixEnd_99539 := by exact prefixLift 99539
  have htrace : WordTrace (prefixWord ++ tailWord_99539) baseStart_99539 baseEnd_99539 := by
    simpa [prefixWord, tailWord_99539, baseEnd_99539] using wordTrace_append hprefix tailTrace_99539
  have hstable : (prefixWord ++ tailWord_99539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99539).length < 2 ^ (prefixWord ++ tailWord_99539).sum := by decide
  have hdescent : baseEnd_99539 < baseStart_99539 := by decide
  rcases family_descends (prefixWord ++ tailWord_99539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99584 : List Nat := [2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_99584 : Nat := 118140960795 + 99584 * 2 ^ 59
def prefixEnd_99584 : Nat := 4983230072969 + 3 ^ 40 * 99584 * 2
def baseEnd_99584 : Nat := 15150950369612921730971

theorem tailTrace_99584 : CollatzResearch.WordTrace tailWord_99584 prefixEnd_99584 15150950369612921730971 := by
  unfold tailWord_99584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816063435615825219132903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2421417914154433625510537 1816063435615825219132903)
  ·
    refine ⟨2724095153423737828699355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816063435615825219132903 2724095153423737828699355)
    ·
      refine ⟨4086142730135606743049033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724095153423737828699355 4086142730135606743049033)
      ·
        refine ⟨3064607047601705057286775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086142730135606743049033 3064607047601705057286775)
        ·
          refine ⟨4596910571402557585930163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064607047601705057286775 4596910571402557585930163)
          ·
            refine ⟨6895365857103836378895245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596910571402557585930163 6895365857103836378895245)
            ·
              refine ⟨2585762196413938642085717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6895365857103836378895245 2585762196413938642085717)
              ·
                refine ⟨15150950369612921730971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2585762196413938642085717 15150950369612921730971)
                ·
                  rfl

theorem cell20_99584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_99584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99584 prefixEnd_99584 := by exact prefixLift 99584
  have htrace : WordTrace (prefixWord ++ tailWord_99584) baseStart_99584 baseEnd_99584 := by
    simpa [prefixWord, tailWord_99584, baseEnd_99584] using wordTrace_append hprefix tailTrace_99584
  have hstable : (prefixWord ++ tailWord_99584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99584).length < 2 ^ (prefixWord ++ tailWord_99584).sum := by decide
  have hdescent : baseEnd_99584 < baseStart_99584 := by decide
  rcases family_descends (prefixWord ++ tailWord_99584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99608 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_99608 : Nat := 118140960795 + 99608 * 2 ^ 59
def prefixEnd_99608 : Nat := 4983230072969 + 3 ^ 40 * 99608 * 2
def baseEnd_99608 : Nat := 45463805362801348392815

theorem tailTrace_99608 : CollatzResearch.WordTrace tailWord_99608 prefixEnd_99608 45463805362801348392815 := by
  unfold tailWord_99608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816501111572351268569739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2422001482096468358092985 1816501111572351268569739)
  ·
    refine ⟨2724751667358526902854609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816501111572351268569739 2724751667358526902854609)
    ·
      refine ⟨2043563750518895177140957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2724751667358526902854609 2043563750518895177140957)
      ·
        refine ⟨766336406444585691427859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2043563750518895177140957 766336406444585691427859)
        ·
          refine ⟨1149504609666878537141789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766336406444585691427859 1149504609666878537141789)
          ·
            refine ⟨431064228625079451428171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1149504609666878537141789 431064228625079451428171)
            ·
              refine ⟨646596342937619177142257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431064228625079451428171 646596342937619177142257)
              ·
                refine ⟨484947257203214382856693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646596342937619177142257 484947257203214382856693)
                ·
                  refine ⟨45463805362801348392815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484947257203214382856693 45463805362801348392815)
                  ·
                    rfl

theorem cell20_99608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_99608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99608 prefixEnd_99608 := by exact prefixLift 99608
  have htrace : WordTrace (prefixWord ++ tailWord_99608) baseStart_99608 baseEnd_99608 := by
    simpa [prefixWord, tailWord_99608, baseEnd_99608] using wordTrace_append hprefix tailTrace_99608
  have hstable : (prefixWord ++ tailWord_99608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99608).length < 2 ^ (prefixWord ++ tailWord_99608).sum := by decide
  have hdescent : baseEnd_99608 < baseStart_99608 := by decide
  rcases family_descends (prefixWord ++ tailWord_99608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99614 : List Nat := [4, 3, 2, 1, 3, 1, 6]
def baseStart_99614 : Nat := 118140960795 + 99614 * 2 ^ 59
def prefixEnd_99614 : Nat := 4983230072969 + 3 ^ 40 * 99614 * 2
def baseEnd_99614 : Nat := 5051838214032443799199

theorem tailTrace_99614 : CollatzResearch.WordTrace tailWord_99614 prefixEnd_99614 5051838214032443799199 := by
  unfold tailWord_99614
  simp only [CollatzResearch.WordTrace]
  refine ⟨454152632640370695232237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2422147374081977041238597 454152632640370695232237)
  ·
    refine ⟨170307237240139010712089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 454152632640370695232237 170307237240139010712089)
    ·
      refine ⟨127730427930104258034067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170307237240139010712089 127730427930104258034067)
      ·
        refine ⟨191595641895156387051101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127730427930104258034067 191595641895156387051101)
        ·
          refine ⟨71848365710683645144163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191595641895156387051101 71848365710683645144163)
          ·
            refine ⟨107772548566025467716245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71848365710683645144163 107772548566025467716245)
            ·
              refine ⟨5051838214032443799199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107772548566025467716245 5051838214032443799199)
              ·
                rfl

theorem cell20_99614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_99614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99614 prefixEnd_99614 := by exact prefixLift 99614
  have htrace : WordTrace (prefixWord ++ tailWord_99614) baseStart_99614 baseEnd_99614 := by
    simpa [prefixWord, tailWord_99614, baseEnd_99614] using wordTrace_append hprefix tailTrace_99614
  have hstable : (prefixWord ++ tailWord_99614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99614).length < 2 ^ (prefixWord ++ tailWord_99614).sum := by decide
  have hdescent : baseEnd_99614 < baseStart_99614 := by decide
  rcases family_descends (prefixWord ++ tailWord_99614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99618 : List Nat := [3, 3, 1, 1, 4, 2, 6]
def baseStart_99618 : Nat := 118140960795 + 99618 * 2 ^ 59
def prefixEnd_99618 : Nat := 4983230072969 + 3 ^ 40 * 99618 * 2
def baseEnd_99618 : Nat := 5052041070587306451049

theorem tailTrace_99618 : CollatzResearch.WordTrace tailWord_99618 prefixEnd_99618 5052041070587306451049 := by
  unfold tailWord_99618
  simp only [CollatzResearch.WordTrace]
  refine ⟨908341738277118561250877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2422244635405649496669005 908341738277118561250877)
  ·
    refine ⟨340628151853919460469079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 908341738277118561250877 340628151853919460469079)
    ·
      refine ⟨510942227780879190703619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340628151853919460469079 510942227780879190703619)
      ·
        refine ⟨766413341671318786055429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510942227780879190703619 766413341671318786055429)
        ·
          refine ⟨143702501563372272385393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 766413341671318786055429 143702501563372272385393)
          ·
            refine ⟨107776876172529204289045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143702501563372272385393 107776876172529204289045)
            ·
              refine ⟨5052041070587306451049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107776876172529204289045 5052041070587306451049)
              ·
                rfl

theorem cell20_99618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_99618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99618 prefixEnd_99618 := by exact prefixLift 99618
  have htrace : WordTrace (prefixWord ++ tailWord_99618) baseStart_99618 baseEnd_99618 := by
    simpa [prefixWord, tailWord_99618, baseEnd_99618] using wordTrace_append hprefix tailTrace_99618
  have hstable : (prefixWord ++ tailWord_99618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99618).length < 2 ^ (prefixWord ++ tailWord_99618).sum := by decide
  have hdescent : baseEnd_99618 < baseStart_99618 := by decide
  rcases family_descends (prefixWord ++ tailWord_99618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99653 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_99653 : Nat := 118140960795 + 99653 * 2 ^ 59
def prefixEnd_99653 : Nat := 4983230072969 + 3 ^ 40 * 99653 * 2
def baseEnd_99653 : Nat := 45484344588981191892631

theorem tailTrace_99653 : CollatzResearch.WordTrace tailWord_99653 prefixEnd_99653 45484344588981191892631 := by
  unfold tailWord_99653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634643507981675222527613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2423095671987783481685075 3634643507981675222527613)
  ·
    refine ⟨1362991315493128208447855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3634643507981675222527613 1362991315493128208447855)
    ·
      refine ⟨2044486973239692312671783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362991315493128208447855 2044486973239692312671783)
      ·
        refine ⟨3066730459859538469007675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044486973239692312671783 3066730459859538469007675)
        ·
          refine ⟨4600095689789307703511513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066730459859538469007675 4600095689789307703511513)
          ·
            refine ⟨3450071767341980777633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600095689789307703511513 3450071767341980777633635)
            ·
              refine ⟨5175107651012971166450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450071767341980777633635 5175107651012971166450453)
              ·
                refine ⟨242583171141233023427365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5175107651012971166450453 242583171141233023427365)
                ·
                  refine ⟨45484344588981191892631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242583171141233023427365 45484344588981191892631)
                  ·
                    rfl

theorem cell20_99653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_99653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99653 prefixEnd_99653 := by exact prefixLift 99653
  have htrace : WordTrace (prefixWord ++ tailWord_99653) baseStart_99653 baseEnd_99653 := by
    simpa [prefixWord, tailWord_99653, baseEnd_99653] using wordTrace_append hprefix tailTrace_99653
  have hstable : (prefixWord ++ tailWord_99653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99653).length < 2 ^ (prefixWord ++ tailWord_99653).sum := by decide
  have hdescent : baseEnd_99653 < baseStart_99653 := by decide
  rcases family_descends (prefixWord ++ tailWord_99653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99742 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_99742 : Nat := 118140960795 + 99742 * 2 ^ 59
def prefixEnd_99742 : Nat := 4983230072969 + 3 ^ 40 * 99742 * 2
def baseEnd_99742 : Nat := 45524966614092437925601

theorem tailTrace_99742 : CollatzResearch.WordTrace tailWord_99742 prefixEnd_99742 45524966614092437925601 := by
  unfold tailWord_99742
  simp only [CollatzResearch.WordTrace]
  refine ⟨454736200582405427814685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2425259736439495615011653 454736200582405427814685)
  ·
    refine ⟨170526075218402035430507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 454736200582405427814685 170526075218402035430507)
    ·
      refine ⟨255789112827603053145761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170526075218402035430507 255789112827603053145761)
      ·
        refine ⟨191841834620702289859321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255789112827603053145761 191841834620702289859321)
        ·
          refine ⟨143881375965526717394491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191841834620702289859321 143881375965526717394491)
          ·
            refine ⟨215822063948290076091737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143881375965526717394491 215822063948290076091737)
            ·
              refine ⟨161866547961217557068803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215822063948290076091737 161866547961217557068803)
              ·
                refine ⟨242799821941826335603205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161866547961217557068803 242799821941826335603205)
                ·
                  refine ⟨45524966614092437925601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242799821941826335603205 45524966614092437925601)
                  ·
                    rfl

theorem cell20_99742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_99742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99742 prefixEnd_99742 := by exact prefixLift 99742
  have htrace : WordTrace (prefixWord ++ tailWord_99742) baseStart_99742 baseEnd_99742 := by
    simpa [prefixWord, tailWord_99742, baseEnd_99742] using wordTrace_append hprefix tailTrace_99742
  have hstable : (prefixWord ++ tailWord_99742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99742).length < 2 ^ (prefixWord ++ tailWord_99742).sum := by decide
  have hdescent : baseEnd_99742 < baseStart_99742 := by decide
  rcases family_descends (prefixWord ++ tailWord_99742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99746 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_99746 : Nat := 118140960795 + 99746 * 2 ^ 59
def prefixEnd_99746 : Nat := 4983230072969 + 3 ^ 40 * 99746 * 2
def baseEnd_99746 : Nat := 45526792323086201792251

theorem tailTrace_99746 : CollatzResearch.WordTrace tailWord_99746 prefixEnd_99746 45526792323086201792251 := by
  unfold tailWord_99746
  simp only [CollatzResearch.WordTrace]
  refine ⟨909508874161188026415773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2425356997763168070442061 909508874161188026415773)
  ·
    refine ⟨341065827810445509905915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 909508874161188026415773 341065827810445509905915)
    ·
      refine ⟨511598741715668264858873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341065827810445509905915 511598741715668264858873)
      ·
        refine ⟨383699056286751198644155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511598741715668264858873 383699056286751198644155)
        ·
          refine ⟨575548584430126797966233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383699056286751198644155 575548584430126797966233)
          ·
            refine ⟨431661438322595098474675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575548584430126797966233 431661438322595098474675)
            ·
              refine ⟨647492157483892647712013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431661438322595098474675 647492157483892647712013)
              ·
                refine ⟨242809559056459742892005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647492157483892647712013 242809559056459742892005)
                ·
                  refine ⟨45526792323086201792251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242809559056459742892005 45526792323086201792251)
                  ·
                    rfl

theorem cell20_99746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_99746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99746 prefixEnd_99746 := by exact prefixLift 99746
  have htrace : WordTrace (prefixWord ++ tailWord_99746) baseStart_99746 baseEnd_99746 := by
    simpa [prefixWord, tailWord_99746, baseEnd_99746] using wordTrace_append hprefix tailTrace_99746
  have hstable : (prefixWord ++ tailWord_99746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99746).length < 2 ^ (prefixWord ++ tailWord_99746).sum := by decide
  have hdescent : baseEnd_99746 < baseStart_99746 := by decide
  rcases family_descends (prefixWord ++ tailWord_99746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99767 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_99767 : Nat := 118140960795 + 99767 * 2 ^ 59
def prefixEnd_99767 : Nat := 4983230072969 + 3 ^ 40 * 99767 * 2
def baseEnd_99767 : Nat := 45536377295303462092165

theorem tailTrace_99767 : CollatzResearch.WordTrace tailWord_99767 prefixEnd_99767 45536377295303462092165 := by
  unfold tailWord_99767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638801429568672692177555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2425867619712448461451703 3638801429568672692177555)
  ·
    refine ⟨5458202144353009038266333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3638801429568672692177555 5458202144353009038266333)
    ·
      refine ⟨2046825804132378389349875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5458202144353009038266333 2046825804132378389349875)
      ·
        refine ⟨3070238706198567584024813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046825804132378389349875 3070238706198567584024813)
        ·
          refine ⟨1151339514824462844009305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3070238706198567584024813 1151339514824462844009305)
          ·
            refine ⟨863504636118347133006979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151339514824462844009305 863504636118347133006979)
            ·
              refine ⟨1295256954177520699510469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863504636118347133006979 1295256954177520699510469)
              ·
                refine ⟨242860678908285131158213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1295256954177520699510469 242860678908285131158213)
                ·
                  refine ⟨45536377295303462092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242860678908285131158213 45536377295303462092165)
                  ·
                    rfl

theorem cell20_99767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_99767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99767 prefixEnd_99767 := by exact prefixLift 99767
  have htrace : WordTrace (prefixWord ++ tailWord_99767) baseStart_99767 baseEnd_99767 := by
    simpa [prefixWord, tailWord_99767, baseEnd_99767] using wordTrace_append hprefix tailTrace_99767
  have hstable : (prefixWord ++ tailWord_99767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99767).length < 2 ^ (prefixWord ++ tailWord_99767).sum := by decide
  have hdescent : baseEnd_99767 < baseStart_99767 := by decide
  rcases family_descends (prefixWord ++ tailWord_99767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99780 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_99780 : Nat := 118140960795 + 99780 * 2 ^ 59
def prefixEnd_99780 : Nat := 4983230072969 + 3 ^ 40 * 99780 * 2
def baseEnd_99780 : Nat := 45542310849533194658779

theorem tailTrace_99780 : CollatzResearch.WordTrace tailWord_99780 prefixEnd_99780 45542310849533194658779 := by
  unfold tailWord_99780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819637789260787956200397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2426183719014383941600529 1819637789260787956200397)
  ·
    refine ⟨682364170972795483575149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1819637789260787956200397 682364170972795483575149)
    ·
      refine ⟨255886564114798306340681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 682364170972795483575149 255886564114798306340681)
      ·
        refine ⟨191914923086098729755511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255886564114798306340681 191914923086098729755511)
        ·
          refine ⟨287872384629148094633267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191914923086098729755511 287872384629148094633267)
          ·
            refine ⟨431808576943722141949901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287872384629148094633267 431808576943722141949901)
            ·
              refine ⟨161928216353895803231213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431808576943722141949901 161928216353895803231213)
              ·
                refine ⟨60723081132710926211705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161928216353895803231213 60723081132710926211705)
                ·
                  refine ⟨45542310849533194658779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60723081132710926211705 45542310849533194658779)
                  ·
                    rfl

theorem cell20_99780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_99780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99780 prefixEnd_99780 := by exact prefixLift 99780
  have htrace : WordTrace (prefixWord ++ tailWord_99780) baseStart_99780 baseEnd_99780 := by
    simpa [prefixWord, tailWord_99780, baseEnd_99780] using wordTrace_append hprefix tailTrace_99780
  have hstable : (prefixWord ++ tailWord_99780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99780).length < 2 ^ (prefixWord ++ tailWord_99780).sum := by decide
  have hdescent : baseEnd_99780 < baseStart_99780 := by decide
  rcases family_descends (prefixWord ++ tailWord_99780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99815 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_99815 : Nat := 118140960795 + 99815 * 2 ^ 59
def prefixEnd_99815 : Nat := 4983230072969 + 3 ^ 40 * 99815 * 2
def baseEnd_99815 : Nat := 45558285803228628491969

theorem tailTrace_99815 : CollatzResearch.WordTrace tailWord_99815 prefixEnd_99815 45558285803228628491969 := by
  unfold tailWord_99815
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640552133394776889924899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2427034755596517926616599 3640552133394776889924899)
  ·
    refine ⟨5460828200092165334887349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640552133394776889924899 5460828200092165334887349)
    ·
      refine ⟨511952643758640500145689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5460828200092165334887349 511952643758640500145689)
      ·
        refine ⟨383964482818980375109267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511952643758640500145689 383964482818980375109267)
        ·
          refine ⟨575946724228470562663901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383964482818980375109267 575946724228470562663901)
          ·
            refine ⟨215980021585676460998963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575946724228470562663901 215980021585676460998963)
            ·
              refine ⟨323970032378514691498445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215980021585676460998963 323970032378514691498445)
              ·
                refine ⟨121488762141943009311917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323970032378514691498445 121488762141943009311917)
                ·
                  refine ⟨45558285803228628491969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121488762141943009311917 45558285803228628491969)
                  ·
                    rfl

theorem cell20_99815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_99815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99815 prefixEnd_99815 := by exact prefixLift 99815
  have htrace : WordTrace (prefixWord ++ tailWord_99815) baseStart_99815 baseEnd_99815 := by
    simpa [prefixWord, tailWord_99815, baseEnd_99815] using wordTrace_append hprefix tailTrace_99815
  have hstable : (prefixWord ++ tailWord_99815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99815).length < 2 ^ (prefixWord ++ tailWord_99815).sum := by decide
  have hdescent : baseEnd_99815 < baseStart_99815 := by decide
  rcases family_descends (prefixWord ++ tailWord_99815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99819 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_99819 : Nat := 118140960795 + 99819 * 2 ^ 59
def prefixEnd_99819 : Nat := 4983230072969 + 3 ^ 40 * 99819 * 2
def baseEnd_99819 : Nat := 45560111512222392358619

theorem tailTrace_99819 : CollatzResearch.WordTrace tailWord_99819 prefixEnd_99819 45560111512222392358619 := by
  unfold tailWord_99819
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640698025380285573070511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2427132016920190382047007 3640698025380285573070511)
  ·
    refine ⟨5461047038070428359605767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640698025380285573070511 5461047038070428359605767)
    ·
      refine ⟨8191570557105642539408651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5461047038070428359605767 8191570557105642539408651)
      ·
        refine ⟨12287355835658463809112977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8191570557105642539408651 12287355835658463809112977)
        ·
          refine ⟨9215516876743847856834733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12287355835658463809112977 9215516876743847856834733)
          ·
            refine ⟨3455818828778942946313025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9215516876743847856834733 3455818828778942946313025)
            ·
              refine ⟨2591864121584207209734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455818828778942946313025 2591864121584207209734769)
              ·
                refine ⟨1943898091188155407301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591864121584207209734769 1943898091188155407301077)
                ·
                  refine ⟨45560111512222392358619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1943898091188155407301077 45560111512222392358619)
                  ·
                    rfl

theorem cell20_99819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_99819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99819 prefixEnd_99819 := by exact prefixLift 99819
  have htrace : WordTrace (prefixWord ++ tailWord_99819) baseStart_99819 baseEnd_99819 := by
    simpa [prefixWord, tailWord_99819, baseEnd_99819] using wordTrace_append hprefix tailTrace_99819
  have hstable : (prefixWord ++ tailWord_99819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99819).length < 2 ^ (prefixWord ++ tailWord_99819).sum := by decide
  have hdescent : baseEnd_99819 < baseStart_99819 := by decide
  rcases family_descends (prefixWord ++ tailWord_99819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99850 : List Nat := [3, 1, 2, 2, 2, 10]
def baseStart_99850 : Nat := 118140960795 + 99850 * 2 ^ 59
def prefixEnd_99850 : Nat := 4983230072969 + 3 ^ 40 * 99850 * 2
def baseEnd_99850 : Nat := 1687935583589780086117

theorem tailTrace_99850 : CollatzResearch.WordTrace tailWord_99850 prefixEnd_99850 1687935583589780086117 := by
  unfold tailWord_99850
  simp only [CollatzResearch.WordTrace]
  refine ⟨910457172066994466862251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2427885792178651911632669 910457172066994466862251)
  ·
    refine ⟨1365685758100491700293377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910457172066994466862251 1365685758100491700293377)
    ·
      refine ⟨1024264318575368775220033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365685758100491700293377 1024264318575368775220033)
      ·
        refine ⟨768198238931526581415025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024264318575368775220033 768198238931526581415025)
        ·
          refine ⟨576148679198644936061269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768198238931526581415025 576148679198644936061269)
          ·
            refine ⟨1687935583589780086117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 576148679198644936061269 1687935583589780086117)
            ·
              rfl

theorem cell20_99850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 10].length) (baseStart_99850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99850 prefixEnd_99850 := by exact prefixLift 99850
  have htrace : WordTrace (prefixWord ++ tailWord_99850) baseStart_99850 baseEnd_99850 := by
    simpa [prefixWord, tailWord_99850, baseEnd_99850] using wordTrace_append hprefix tailTrace_99850
  have hstable : (prefixWord ++ tailWord_99850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99850).length < 2 ^ (prefixWord ++ tailWord_99850).sum := by decide
  have hdescent : baseEnd_99850 < baseStart_99850 := by decide
  rcases family_descends (prefixWord ++ tailWord_99850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99943 : List Nat := [1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_99943 : Nat := 118140960795 + 99943 * 2 ^ 59
def prefixEnd_99943 : Nat := 4983230072969 + 3 ^ 40 * 99943 * 2
def baseEnd_99943 : Nat := 15205569497009690741593

theorem tailTrace_99943 : CollatzResearch.WordTrace tailWord_99943 prefixEnd_99943 15205569497009690741593 := by
  unfold tailWord_99943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645220676931054750584483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2430147117954036500389655 3645220676931054750584483)
  ·
    refine ⟨5467831015396582125876725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3645220676931054750584483 5467831015396582125876725)
    ·
      refine ⟨512609157693429574300943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5467831015396582125876725 512609157693429574300943)
      ·
        refine ⟨768913736540144361451415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512609157693429574300943 768913736540144361451415)
        ·
          refine ⟨1153370604810216542177123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768913736540144361451415 1153370604810216542177123)
          ·
            refine ⟨1730055907215324813265685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153370604810216542177123 1730055907215324813265685)
            ·
              refine ⟨81096370650718350621829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1730055907215324813265685 81096370650718350621829)
              ·
                refine ⟨15205569497009690741593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81096370650718350621829 15205569497009690741593)
                ·
                  rfl

theorem cell20_99943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_99943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99943 prefixEnd_99943 := by exact prefixLift 99943
  have htrace : WordTrace (prefixWord ++ tailWord_99943) baseStart_99943 baseEnd_99943 := by
    simpa [prefixWord, tailWord_99943, baseEnd_99943] using wordTrace_append hprefix tailTrace_99943
  have hstable : (prefixWord ++ tailWord_99943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99943).length < 2 ^ (prefixWord ++ tailWord_99943).sum := by decide
  have hdescent : baseEnd_99943 < baseStart_99943 := by decide
  rcases family_descends (prefixWord ++ tailWord_99943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99949 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 2]
def baseStart_99949 : Nat := 118140960795 + 99949 * 2 ^ 59
def prefixEnd_99949 : Nat := 4983230072969 + 3 ^ 40 * 99949 * 2
def baseEnd_99949 : Nat := 45619447054519718024755

theorem tailTrace_99949 : CollatzResearch.WordTrace tailWord_99949 prefixEnd_99949 45619447054519718024755 := by
  unfold tailWord_99949
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645439514909317775302901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2430293009939545183535267 3645439514909317775302901)
  ·
    refine ⟨341759954522748541434647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3645439514909317775302901 341759954522748541434647)
    ·
      refine ⟨512639931784122812151971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341759954522748541434647 512639931784122812151971)
      ·
        refine ⟨768959897676184218227957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512639931784122812151971 768959897676184218227957)
        ·
          refine ⟨72089990407142270458871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 768959897676184218227957 72089990407142270458871)
          ·
            refine ⟨108134985610713405688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72089990407142270458871 108134985610713405688307)
            ·
              refine ⟨162202478416070108532461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108134985610713405688307 162202478416070108532461)
              ·
                refine ⟨60825929406026290699673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162202478416070108532461 60825929406026290699673)
                ·
                  refine ⟨45619447054519718024755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60825929406026290699673 45619447054519718024755)
                  ·
                    rfl

theorem cell20_99949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_99949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_99949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_99949 prefixEnd_99949 := by exact prefixLift 99949
  have htrace : WordTrace (prefixWord ++ tailWord_99949) baseStart_99949 baseEnd_99949 := by
    simpa [prefixWord, tailWord_99949, baseEnd_99949] using wordTrace_append hprefix tailTrace_99949
  have hstable : (prefixWord ++ tailWord_99949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99949).length < 2 ^ (prefixWord ++ tailWord_99949).sum := by decide
  have hdescent : baseEnd_99949 < baseStart_99949 := by decide
  rcases family_descends (prefixWord ++ tailWord_99949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100022 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_100022 : Nat := 118140960795 + 100022 * 2 ^ 59
def prefixEnd_100022 : Nat := 4983230072969 + 3 ^ 40 * 100022 * 2
def baseEnd_100022 : Nat := 45652766243655908591123

theorem tailTrace_100022 : CollatzResearch.WordTrace tailWord_100022 prefixEnd_100022 45652766243655908591123 := by
  unfold tailWord_100022
  simp only [CollatzResearch.WordTrace]
  refine ⟨228006377727803202669395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2432068029096567495140213 228006377727803202669395)
  ·
    refine ⟨342009566591704804004093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228006377727803202669395 342009566591704804004093)
    ·
      refine ⟨128253587471889301501535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342009566591704804004093 128253587471889301501535)
      ·
        refine ⟨192380381207833952252303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128253587471889301501535 192380381207833952252303)
        ·
          refine ⟨288570571811750928378455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192380381207833952252303 288570571811750928378455)
          ·
            refine ⟨432855857717626392567683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288570571811750928378455 432855857717626392567683)
            ·
              refine ⟨649283786576439588851525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432855857717626392567683 649283786576439588851525)
              ·
                refine ⟨121740709983082422909661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649283786576439588851525 121740709983082422909661)
                ·
                  refine ⟨45652766243655908591123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121740709983082422909661 45652766243655908591123)
                  ·
                    rfl

theorem cell20_100022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_100022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100022 prefixEnd_100022 := by exact prefixLift 100022
  have htrace : WordTrace (prefixWord ++ tailWord_100022) baseStart_100022 baseEnd_100022 := by
    simpa [prefixWord, tailWord_100022, baseEnd_100022] using wordTrace_append hprefix tailTrace_100022
  have hstable : (prefixWord ++ tailWord_100022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100022).length < 2 ^ (prefixWord ++ tailWord_100022).sum := by decide
  have hdescent : baseEnd_100022 < baseStart_100022 := by decide
  rcases family_descends (prefixWord ++ tailWord_100022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100026 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_100026 : Nat := 118140960795 + 100026 * 2 ^ 59
def prefixEnd_100026 : Nat := 4983230072969 + 3 ^ 40 * 100026 * 2
def baseEnd_100026 : Nat := 45654591952649672457773

theorem tailTrace_100026 : CollatzResearch.WordTrace tailWord_100026 prefixEnd_100026 45654591952649672457773 := by
  unfold tailWord_100026
  simp only [CollatzResearch.WordTrace]
  refine ⟨912061983907589981463983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2432165290420239950570621 912061983907589981463983)
  ·
    refine ⟨1368092975861384972195975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912061983907589981463983 1368092975861384972195975)
    ·
      refine ⟨2052139463792077458293963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368092975861384972195975 2052139463792077458293963)
      ·
        refine ⟨3078209195688116187440945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052139463792077458293963 3078209195688116187440945)
        ·
          refine ⟨2308656896766087140580709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078209195688116187440945 2308656896766087140580709)
          ·
            refine ⟨432873168143641338858883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2308656896766087140580709 432873168143641338858883)
            ·
              refine ⟨649309752215462008288325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432873168143641338858883 649309752215462008288325)
              ·
                refine ⟨121745578540399126554061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649309752215462008288325 121745578540399126554061)
                ·
                  refine ⟨45654591952649672457773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121745578540399126554061 45654591952649672457773)
                  ·
                    rfl

theorem cell20_100026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_100026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100026 prefixEnd_100026 := by exact prefixLift 100026
  have htrace : WordTrace (prefixWord ++ tailWord_100026) baseStart_100026 baseEnd_100026 := by
    simpa [prefixWord, tailWord_100026, baseEnd_100026] using wordTrace_append hprefix tailTrace_100026
  have hstable : (prefixWord ++ tailWord_100026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100026).length < 2 ^ (prefixWord ++ tailWord_100026).sum := by decide
  have hdescent : baseEnd_100026 < baseStart_100026 := by decide
  rcases family_descends (prefixWord ++ tailWord_100026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100050 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_100050 : Nat := 118140960795 + 100050 * 2 ^ 59
def prefixEnd_100050 : Nat := 4983230072969 + 3 ^ 40 * 100050 * 2
def baseEnd_100050 : Nat := 45665546206612255657675

theorem tailTrace_100050 : CollatzResearch.WordTrace tailWord_100050 prefixEnd_100050 45665546206612255657675 := by
  unfold tailWord_100050
  simp only [CollatzResearch.WordTrace]
  refine ⟨912280821885853006182401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2432748858362274683153069 912280821885853006182401)
  ·
    refine ⟨684210616414389754636801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 912280821885853006182401 684210616414389754636801)
    ·
      refine ⟨513157962310792315977601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 684210616414389754636801 513157962310792315977601)
      ·
        refine ⟨384868471733094236983201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513157962310792315977601 384868471733094236983201)
        ·
          refine ⟨288651353799820677737401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384868471733094236983201 288651353799820677737401)
          ·
            refine ⟨216488515349865508303051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288651353799820677737401 216488515349865508303051)
            ·
              refine ⟨324732773024798262454577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216488515349865508303051 324732773024798262454577)
              ·
                refine ⟨243549579768598696840933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324732773024798262454577 243549579768598696840933)
                ·
                  refine ⟨45665546206612255657675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243549579768598696840933 45665546206612255657675)
                  ·
                    rfl

theorem cell20_100050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_100050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100050 prefixEnd_100050 := by exact prefixLift 100050
  have htrace : WordTrace (prefixWord ++ tailWord_100050) baseStart_100050 baseEnd_100050 := by
    simpa [prefixWord, tailWord_100050, baseEnd_100050] using wordTrace_append hprefix tailTrace_100050
  have hstable : (prefixWord ++ tailWord_100050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100050).length < 2 ^ (prefixWord ++ tailWord_100050).sum := by decide
  have hdescent : baseEnd_100050 < baseStart_100050 := by decide
  rcases family_descends (prefixWord ++ tailWord_100050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100057 : List Nat := [1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_100057 : Nat := 118140960795 + 100057 * 2 ^ 59
def prefixEnd_100057 : Nat := 4983230072969 + 3 ^ 40 * 100057 * 2
def baseEnd_100057 : Nat := 15222913732450447474771

theorem tailTrace_100057 : CollatzResearch.WordTrace tailWord_100057 prefixEnd_100057 15222913732450447474771 := by
  unfold tailWord_100057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649378598518052220234425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432919065678701480156283 3649378598518052220234425)
  ·
    refine ⟨2737033948888539165175819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3649378598518052220234425 2737033948888539165175819)
    ·
      refine ⟨4105550923332808747763729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737033948888539165175819 4105550923332808747763729)
      ·
        refine ⟨3079163192499606560822797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4105550923332808747763729 3079163192499606560822797)
        ·
          refine ⟨1154686197187352460308549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079163192499606560822797 1154686197187352460308549)
          ·
            refine ⟨216503661972628586307853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1154686197187352460308549 216503661972628586307853)
            ·
              refine ⟨81188873239735719865445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216503661972628586307853 81188873239735719865445)
              ·
                refine ⟨15222913732450447474771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81188873239735719865445 15222913732450447474771)
                ·
                  rfl

theorem cell20_100057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_100057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100057 prefixEnd_100057 := by exact prefixLift 100057
  have htrace : WordTrace (prefixWord ++ tailWord_100057) baseStart_100057 baseEnd_100057 := by
    simpa [prefixWord, tailWord_100057, baseEnd_100057] using wordTrace_append hprefix tailTrace_100057
  have hstable : (prefixWord ++ tailWord_100057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100057).length < 2 ^ (prefixWord ++ tailWord_100057).sum := by decide
  have hdescent : baseEnd_100057 < baseStart_100057 := by decide
  rcases family_descends (prefixWord ++ tailWord_100057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100078 : List Nat := [4, 1, 2, 1, 1, 2, 9]
def baseStart_100078 : Nat := 118140960795 + 100078 * 2 ^ 59
def prefixEnd_100078 : Nat := 4983230072969 + 3 ^ 40 * 100078 * 2
def baseEnd_100078 : Nat := 5075369574396511413803

theorem tailTrace_100078 : CollatzResearch.WordTrace tailWord_100078 prefixEnd_100078 5075369574396511413803 := by
  unfold tailWord_100078
  simp only [CollatzResearch.WordTrace]
  refine ⟨456268066430246600843611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2433429687627981871165925 456268066430246600843611)
  ·
    refine ⟨684402099645369901265417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456268066430246600843611 684402099645369901265417)
    ·
      refine ⟨513301574734027425949063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 684402099645369901265417 513301574734027425949063)
      ·
        refine ⟨769952362101041138923595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513301574734027425949063 769952362101041138923595)
        ·
          refine ⟨1154928543151561708385393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769952362101041138923595 1154928543151561708385393)
          ·
            refine ⟨866196407363671281289045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154928543151561708385393 866196407363671281289045)
            ·
              refine ⟨5075369574396511413803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 866196407363671281289045 5075369574396511413803)
              ·
                rfl

theorem cell20_100078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_100078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100078 prefixEnd_100078 := by exact prefixLift 100078
  have htrace : WordTrace (prefixWord ++ tailWord_100078) baseStart_100078 baseEnd_100078 := by
    simpa [prefixWord, tailWord_100078, baseEnd_100078] using wordTrace_append hprefix tailTrace_100078
  have hstable : (prefixWord ++ tailWord_100078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100078).length < 2 ^ (prefixWord ++ tailWord_100078).sum := by decide
  have hdescent : baseEnd_100078 < baseStart_100078 := by decide
  rcases family_descends (prefixWord ++ tailWord_100078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100081 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_100081 : Nat := 118140960795 + 100081 * 2 ^ 59
def prefixEnd_100081 : Nat := 4983230072969 + 3 ^ 40 * 100081 * 2
def baseEnd_100081 : Nat := 45679695451313925624215

theorem tailTrace_100081 : CollatzResearch.WordTrace tailWord_100081 prefixEnd_100081 45679695451313925624215 := by
  unfold tailWord_100081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650253950431104319108097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433502633620736212738731 3650253950431104319108097)
  ·
    refine ⟨2737690462823328239331073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3650253950431104319108097 2737690462823328239331073)
    ·
      refine ⟨2053267847117496179498305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2737690462823328239331073 2053267847117496179498305)
      ·
        refine ⟨1539950885338122134623729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053267847117496179498305 1539950885338122134623729)
        ·
          refine ⟨1154963164003591600967797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539950885338122134623729 1154963164003591600967797)
          ·
            refine ⟨108277796625336712590731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1154963164003591600967797 108277796625336712590731)
            ·
              refine ⟨162416694938005068886097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108277796625336712590731 162416694938005068886097)
              ·
                refine ⟨121812521203503801664573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162416694938005068886097 121812521203503801664573)
                ·
                  refine ⟨45679695451313925624215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121812521203503801664573 45679695451313925624215)
                  ·
                    rfl

theorem cell20_100081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_100081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100081 prefixEnd_100081 := by exact prefixLift 100081
  have htrace : WordTrace (prefixWord ++ tailWord_100081) baseStart_100081 baseEnd_100081 := by
    simpa [prefixWord, tailWord_100081, baseEnd_100081] using wordTrace_append hprefix tailTrace_100081
  have hstable : (prefixWord ++ tailWord_100081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100081).length < 2 ^ (prefixWord ++ tailWord_100081).sum := by decide
  have hdescent : baseEnd_100081 < baseStart_100081 := by decide
  rcases family_descends (prefixWord ++ tailWord_100081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100084 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_100084 : Nat := 118140960795 + 100084 * 2 ^ 59
def prefixEnd_100084 : Nat := 4983230072969 + 3 ^ 40 * 100084 * 2
def baseEnd_100084 : Nat := 45681064733059248524203

theorem tailTrace_100084 : CollatzResearch.WordTrace tailWord_100084 prefixEnd_100084 45681064733059248524203 := by
  unfold tailWord_100084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825181684710117915733653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2433575579613490554311537 1825181684710117915733653)
  ·
    refine ⟨85555391470786777300015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1825181684710117915733653 85555391470786777300015)
    ·
      refine ⟨128333087206180165950023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85555391470786777300015 128333087206180165950023)
      ·
        refine ⟨192499630809270248925035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128333087206180165950023 192499630809270248925035)
        ·
          refine ⟨288749446213905373387553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192499630809270248925035 288749446213905373387553)
          ·
            refine ⟨216562084660429030040665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288749446213905373387553 216562084660429030040665)
            ·
              refine ⟨162421563495321772530499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216562084660429030040665 162421563495321772530499)
              ·
                refine ⟨243632345242982658795749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162421563495321772530499 243632345242982658795749)
                ·
                  refine ⟨45681064733059248524203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243632345242982658795749 45681064733059248524203)
                  ·
                    rfl

theorem cell20_100084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_100084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100084 prefixEnd_100084 := by exact prefixLift 100084
  have htrace : WordTrace (prefixWord ++ tailWord_100084) baseStart_100084 baseEnd_100084 := by
    simpa [prefixWord, tailWord_100084, baseEnd_100084] using wordTrace_append hprefix tailTrace_100084
  have hstable : (prefixWord ++ tailWord_100084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100084).length < 2 ^ (prefixWord ++ tailWord_100084).sum := by decide
  have hdescent : baseEnd_100084 < baseStart_100084 := by decide
  rcases family_descends (prefixWord ++ tailWord_100084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100098 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_100098 : Nat := 118140960795 + 100098 * 2 ^ 59
def prefixEnd_100098 : Nat := 4983230072969 + 3 ^ 40 * 100098 * 2
def baseEnd_100098 : Nat := 45687454714537422057479

theorem tailTrace_100098 : CollatzResearch.WordTrace tailWord_100098 prefixEnd_100098 45687454714537422057479 := by
  unfold tailWord_100098
  simp only [CollatzResearch.WordTrace]
  refine ⟨912718497842379055619237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2433915994246344148317965 912718497842379055619237)
  ·
    refine ⟨171134718345446072928607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 912718497842379055619237 171134718345446072928607)
    ·
      refine ⟨256702077518169109392911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171134718345446072928607 256702077518169109392911)
      ·
        refine ⟨385053116277253664089367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256702077518169109392911 385053116277253664089367)
        ·
          refine ⟨577579674415880496134051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385053116277253664089367 577579674415880496134051)
          ·
            refine ⟨866369511623820744201077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577579674415880496134051 866369511623820744201077)
            ·
              refine ⟨81222141714733194768851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 866369511623820744201077 81222141714733194768851)
              ·
                refine ⟨121833212572099792153277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81222141714733194768851 121833212572099792153277)
                ·
                  refine ⟨45687454714537422057479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121833212572099792153277 45687454714537422057479)
                  ·
                    rfl

theorem cell20_100098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_100098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100098 prefixEnd_100098 := by exact prefixLift 100098
  have htrace : WordTrace (prefixWord ++ tailWord_100098) baseStart_100098 baseEnd_100098 := by
    simpa [prefixWord, tailWord_100098, baseEnd_100098] using wordTrace_append hprefix tailTrace_100098
  have hstable : (prefixWord ++ tailWord_100098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100098).length < 2 ^ (prefixWord ++ tailWord_100098).sum := by decide
  have hdescent : baseEnd_100098 < baseStart_100098 := by decide
  rcases family_descends (prefixWord ++ tailWord_100098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100150 : List Nat := [5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_100150 : Nat := 118140960795 + 100150 * 2 ^ 59
def prefixEnd_100150 : Nat := 4983230072969 + 3 ^ 40 * 100150 * 2
def baseEnd_100150 : Nat := 15237062977152117441311

theorem tailTrace_100150 : CollatzResearch.WordTrace tailWord_100150 prefixEnd_100150 15237062977152117441311 := by
  unfold tailWord_100150
  simp only [CollatzResearch.WordTrace]
  refine ⟨228298161698820568960619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2435180391454086068913269 228298161698820568960619)
  ·
    refine ⟨342447242548230853440929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228298161698820568960619 342447242548230853440929)
    ·
      refine ⟨256835431911173140080697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342447242548230853440929 256835431911173140080697)
      ·
        refine ⟨192626573933379855060523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256835431911173140080697 192626573933379855060523)
        ·
          refine ⟨288939860900069782590785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192626573933379855060523 288939860900069782590785)
          ·
            refine ⟨216704895675052336943089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288939860900069782590785 216704895675052336943089)
            ·
              refine ⟨162528671756289252707317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216704895675052336943089 162528671756289252707317)
              ·
                refine ⟨15237062977152117441311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162528671756289252707317 15237062977152117441311)
                ·
                  rfl

theorem cell20_100150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_100150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100150 prefixEnd_100150 := by exact prefixLift 100150
  have htrace : WordTrace (prefixWord ++ tailWord_100150) baseStart_100150 baseEnd_100150 := by
    simpa [prefixWord, tailWord_100150, baseEnd_100150] using wordTrace_append hprefix tailTrace_100150
  have hstable : (prefixWord ++ tailWord_100150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100150).length < 2 ^ (prefixWord ++ tailWord_100150).sum := by decide
  have hdescent : baseEnd_100150 < baseStart_100150 := by decide
  rcases family_descends (prefixWord ++ tailWord_100150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100153 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_100153 : Nat := 118140960795 + 100153 * 2 ^ 59
def prefixEnd_100153 : Nat := 4983230072969 + 3 ^ 40 * 100153 * 2
def baseEnd_100153 : Nat := 45712558213201675223921

theorem tailTrace_100153 : CollatzResearch.WordTrace tailWord_100153 prefixEnd_100153 45712558213201675223921 := by
  unfold tailWord_100153
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652880006170260615729113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2435253337446840410486075 3652880006170260615729113)
  ·
    refine ⟨2739660004627695461796835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3652880006170260615729113 2739660004627695461796835)
    ·
      refine ⟨4109490006941543192695253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2739660004627695461796835 4109490006941543192695253)
      ·
        refine ⟨96316172037692418578795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4109490006941543192695253 96316172037692418578795)
        ·
          refine ⟨144474258056538627868193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96316172037692418578795 144474258056538627868193)
          ·
            refine ⟨108355693542403970901145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144474258056538627868193 108355693542403970901145)
            ·
              refine ⟨81266770156802978175859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108355693542403970901145 81266770156802978175859)
              ·
                refine ⟨121900155235204467263789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81266770156802978175859 121900155235204467263789)
                ·
                  refine ⟨45712558213201675223921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121900155235204467263789 45712558213201675223921)
                  ·
                    rfl

theorem cell20_100153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_100153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100153 prefixEnd_100153 := by exact prefixLift 100153
  have htrace : WordTrace (prefixWord ++ tailWord_100153) baseStart_100153 baseEnd_100153 := by
    simpa [prefixWord, tailWord_100153, baseEnd_100153] using wordTrace_append hprefix tailTrace_100153
  have hstable : (prefixWord ++ tailWord_100153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100153).length < 2 ^ (prefixWord ++ tailWord_100153).sum := by decide
  have hdescent : baseEnd_100153 < baseStart_100153 := by decide
  rcases family_descends (prefixWord ++ tailWord_100153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100154 : List Nat := [3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_100154 : Nat := 118140960795 + 100154 * 2 ^ 59
def prefixEnd_100154 : Nat := 4983230072969 + 3 ^ 40 * 100154 * 2
def baseEnd_100154 : Nat := 15237671546816705396861

theorem tailTrace_100154 : CollatzResearch.WordTrace tailWord_100154 prefixEnd_100154 15237671546816705396861 := by
  unfold tailWord_100154
  simp only [CollatzResearch.WordTrace]
  refine ⟨913229119791659446628879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2435277652777758524343677 913229119791659446628879)
  ·
    refine ⟨1369843679687489169943319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913229119791659446628879 1369843679687489169943319)
    ·
      refine ⟨2054765519531233754914979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369843679687489169943319 2054765519531233754914979)
      ·
        refine ⟨3082148279296850632372469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054765519531233754914979 3082148279296850632372469)
        ·
          refine ⟨288951401184079746784919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3082148279296850632372469 288951401184079746784919)
          ·
            refine ⟨433427101776119620177379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288951401184079746784919 433427101776119620177379)
            ·
              refine ⟨650140652664179430266069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433427101776119620177379 650140652664179430266069)
              ·
                refine ⟨15237671546816705396861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 650140652664179430266069 15237671546816705396861)
                ·
                  rfl

theorem cell20_100154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_100154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100154 prefixEnd_100154 := by exact prefixLift 100154
  have htrace : WordTrace (prefixWord ++ tailWord_100154) baseStart_100154 baseEnd_100154 := by
    simpa [prefixWord, tailWord_100154, baseEnd_100154] using wordTrace_append hprefix tailTrace_100154
  have hstable : (prefixWord ++ tailWord_100154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100154).length < 2 ^ (prefixWord ++ tailWord_100154).sum := by decide
  have hdescent : baseEnd_100154 < baseStart_100154 := by decide
  rcases family_descends (prefixWord ++ tailWord_100154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100157 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_100157 : Nat := 118140960795 + 100157 * 2 ^ 59
def prefixEnd_100157 : Nat := 4983230072969 + 3 ^ 40 * 100157 * 2
def baseEnd_100157 : Nat := 45714383922195439090571

theorem tailTrace_100157 : CollatzResearch.WordTrace tailWord_100157 prefixEnd_100157 45714383922195439090571 := by
  unfold tailWord_100157
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653025898155769298874725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2435350598770512865916483 3653025898155769298874725)
  ·
    refine ⟨684942355904206743539011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3653025898155769298874725 684942355904206743539011)
    ·
      refine ⟨1027413533856310115308517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684942355904206743539011 1027413533856310115308517)
      ·
        refine ⟨192640037598058146620347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1027413533856310115308517 192640037598058146620347)
        ·
          refine ⟨288960056397087219930521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192640037598058146620347 288960056397087219930521)
          ·
            refine ⟨216720042297815414947891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288960056397087219930521 216720042297815414947891)
            ·
              refine ⟨325080063446723122421837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216720042297815414947891 325080063446723122421837)
              ·
                refine ⟨121905023792521170908189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325080063446723122421837 121905023792521170908189)
                ·
                  refine ⟨45714383922195439090571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121905023792521170908189 45714383922195439090571)
                  ·
                    rfl

theorem cell20_100157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_100157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100157 prefixEnd_100157 := by exact prefixLift 100157
  have htrace : WordTrace (prefixWord ++ tailWord_100157) baseStart_100157 baseEnd_100157 := by
    simpa [prefixWord, tailWord_100157, baseEnd_100157] using wordTrace_append hprefix tailTrace_100157
  have hstable : (prefixWord ++ tailWord_100157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100157).length < 2 ^ (prefixWord ++ tailWord_100157).sum := by decide
  have hdescent : baseEnd_100157 < baseStart_100157 := by decide
  rcases family_descends (prefixWord ++ tailWord_100157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100195 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_100195 : Nat := 118140960795 + 100195 * 2 ^ 59
def prefixEnd_100195 : Nat := 4983230072969 + 3 ^ 40 * 100195 * 2
def baseEnd_100195 : Nat := 45731728157636195823749

theorem tailTrace_100195 : CollatzResearch.WordTrace tailWord_100195 prefixEnd_100195 45731728157636195823749 := by
  unfold tailWord_100195
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654411872018101788758039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2436274581345401192505359 3654411872018101788758039)
  ·
    refine ⟨5481617808027152683137059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3654411872018101788758039 5481617808027152683137059)
    ·
      refine ⟨8222426712040729024705589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5481617808027152683137059 8222426712040729024705589)
      ·
        refine ⟨770852504253818346066149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8222426712040729024705589 770852504253818346066149)
        ·
          refine ⟨144534844547590939887403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 770852504253818346066149 144534844547590939887403)
          ·
            refine ⟨216802266821386409831105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144534844547590939887403 216802266821386409831105)
            ·
              refine ⟨162601700116039807373329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216802266821386409831105 162601700116039807373329)
              ·
                refine ⟨121951275087029855529997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162601700116039807373329 121951275087029855529997)
                ·
                  refine ⟨45731728157636195823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121951275087029855529997 45731728157636195823749)
                  ·
                    rfl

theorem cell20_100195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_100195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100195 prefixEnd_100195 := by exact prefixLift 100195
  have htrace : WordTrace (prefixWord ++ tailWord_100195) baseStart_100195 baseEnd_100195 := by
    simpa [prefixWord, tailWord_100195, baseEnd_100195] using wordTrace_append hprefix tailTrace_100195
  have hstable : (prefixWord ++ tailWord_100195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100195).length < 2 ^ (prefixWord ++ tailWord_100195).sum := by decide
  have hdescent : baseEnd_100195 < baseStart_100195 := by decide
  rcases family_descends (prefixWord ++ tailWord_100195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100246 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_100246 : Nat := 118140960795 + 100246 * 2 ^ 59
def prefixEnd_100246 : Nat := 4983230072969 + 3 ^ 40 * 100246 * 2
def baseEnd_100246 : Nat := 45755005947306685123541

theorem tailTrace_100246 : CollatzResearch.WordTrace tailWord_100246 prefixEnd_100246 45755005947306685123541 := by
  unfold tailWord_100246
  simp only [CollatzResearch.WordTrace]
  refine ⟨228516999677083593679037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2437514663222224999243061 228516999677083593679037)
  ·
    refine ⟨85693874878906347629639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228516999677083593679037 85693874878906347629639)
    ·
      refine ⟨128540812318359521444459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85693874878906347629639 128540812318359521444459)
      ·
        refine ⟨192811218477539282166689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128540812318359521444459 192811218477539282166689)
        ·
          refine ⟨144608413858154461625017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192811218477539282166689 144608413858154461625017)
          ·
            refine ⟨108456310393615846218763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144608413858154461625017 108456310393615846218763)
            ·
              refine ⟨162684465590423769328145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108456310393615846218763 162684465590423769328145)
              ·
                refine ⟨122013349192817826996109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162684465590423769328145 122013349192817826996109)
                ·
                  refine ⟨45755005947306685123541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122013349192817826996109 45755005947306685123541)
                  ·
                    rfl

theorem cell20_100246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_100246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100246 prefixEnd_100246 := by exact prefixLift 100246
  have htrace : WordTrace (prefixWord ++ tailWord_100246) baseStart_100246 baseEnd_100246 := by
    simpa [prefixWord, tailWord_100246, baseEnd_100246] using wordTrace_append hprefix tailTrace_100246
  have hstable : (prefixWord ++ tailWord_100246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100246).length < 2 ^ (prefixWord ++ tailWord_100246).sum := by decide
  have hdescent : baseEnd_100246 < baseStart_100246 := by decide
  rcases family_descends (prefixWord ++ tailWord_100246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100282 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_100282 : Nat := 118140960795 + 100282 * 2 ^ 59
def prefixEnd_100282 : Nat := 4983230072969 + 3 ^ 40 * 100282 * 2
def baseEnd_100282 : Nat := 45771437328250559923393

theorem tailTrace_100282 : CollatzResearch.WordTrace tailWord_100282 prefixEnd_100282 45771437328250559923393 := by
  unfold tailWord_100282
  simp only [CollatzResearch.WordTrace]
  refine ⟨914396255675728911793775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2438390015135277098116733 914396255675728911793775)
  ·
    refine ⟨1371594383513593367690663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914396255675728911793775 1371594383513593367690663)
    ·
      refine ⟨2057391575270390051535995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371594383513593367690663 2057391575270390051535995)
      ·
        refine ⟨3086087362905585077303993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057391575270390051535995 3086087362905585077303993)
        ·
          refine ⟨2314565522179188807977995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086087362905585077303993 2314565522179188807977995)
          ·
            refine ⟨3471848283268783211966993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314565522179188807977995 3471848283268783211966993)
            ·
              refine ⟨2603886212451587408975245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471848283268783211966993 2603886212451587408975245)
              ·
                refine ⟨976457329669345278365717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2603886212451587408975245 976457329669345278365717)
                ·
                  refine ⟨45771437328250559923393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 976457329669345278365717 45771437328250559923393)
                  ·
                    rfl

theorem cell20_100282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_100282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100282 prefixEnd_100282 := by exact prefixLift 100282
  have htrace : WordTrace (prefixWord ++ tailWord_100282) baseStart_100282 baseEnd_100282 := by
    simpa [prefixWord, tailWord_100282, baseEnd_100282] using wordTrace_append hprefix tailTrace_100282
  have hstable : (prefixWord ++ tailWord_100282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100282).length < 2 ^ (prefixWord ++ tailWord_100282).sum := by decide
  have hdescent : baseEnd_100282 < baseStart_100282 := by decide
  rcases family_descends (prefixWord ++ tailWord_100282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100285 : List Nat := [1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_100285 : Nat := 118140960795 + 100285 * 2 ^ 59
def prefixEnd_100285 : Nat := 4983230072969 + 3 ^ 40 * 100285 * 2
def baseEnd_100285 : Nat := 15257602203331960941127

theorem tailTrace_100285 : CollatzResearch.WordTrace tailWord_100285 prefixEnd_100285 15257602203331960941127 := by
  unfold tailWord_100285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657694441692047159534309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2438462961128031439689539 3657694441692047159534309)
  ·
    refine ⟨685817707817258842412683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3657694441692047159534309 685817707817258842412683)
    ·
      refine ⟨1028726561725888263619025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685817707817258842412683 1028726561725888263619025)
      ·
        refine ⟨771544921294416197714269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028726561725888263619025 771544921294416197714269)
        ·
          refine ⟨289329345485406074142851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 771544921294416197714269 289329345485406074142851)
          ·
            refine ⟨433994018228109111214277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289329345485406074142851 433994018228109111214277)
            ·
              refine ⟨81373878417770458352677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433994018228109111214277 81373878417770458352677)
              ·
                refine ⟨15257602203331960941127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81373878417770458352677 15257602203331960941127)
                ·
                  rfl

theorem cell20_100285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_100285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100285 prefixEnd_100285 := by exact prefixLift 100285
  have htrace : WordTrace (prefixWord ++ tailWord_100285) baseStart_100285 baseEnd_100285 := by
    simpa [prefixWord, tailWord_100285, baseEnd_100285] using wordTrace_append hprefix tailTrace_100285
  have hstable : (prefixWord ++ tailWord_100285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100285).length < 2 ^ (prefixWord ++ tailWord_100285).sum := by decide
  have hdescent : baseEnd_100285 < baseStart_100285 := by decide
  rcases family_descends (prefixWord ++ tailWord_100285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100322 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_100322 : Nat := 118140960795 + 100322 * 2 ^ 59
def prefixEnd_100322 : Nat := 4983230072969 + 3 ^ 40 * 100322 * 2
def baseEnd_100322 : Nat := 45789694418188198589897

theorem tailTrace_100322 : CollatzResearch.WordTrace tailWord_100322 prefixEnd_100322 45789694418188198589897 := by
  unfold tailWord_100322
  simp only [CollatzResearch.WordTrace]
  refine ⟨914760985639500619657805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2439362628372001652420813 914760985639500619657805)
  ·
    refine ⟨343035369614812732371677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 914760985639500619657805 343035369614812732371677)
    ·
      refine ⟨128638263605554774639379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343035369614812732371677 128638263605554774639379)
      ·
        refine ⟨192957395408332161959069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128638263605554774639379 192957395408332161959069)
        ·
          refine ⟨72359023278124560734651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192957395408332161959069 72359023278124560734651)
          ·
            refine ⟨108538534917186841101977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72359023278124560734651 108538534917186841101977)
            ·
              refine ⟨81403901187890130826483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108538534917186841101977 81403901187890130826483)
              ·
                refine ⟨122105851781835196239725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81403901187890130826483 122105851781835196239725)
                ·
                  refine ⟨45789694418188198589897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122105851781835196239725 45789694418188198589897)
                  ·
                    rfl

theorem cell20_100322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_100322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100322 prefixEnd_100322 := by exact prefixLift 100322
  have htrace : WordTrace (prefixWord ++ tailWord_100322) baseStart_100322 baseEnd_100322 := by
    simpa [prefixWord, tailWord_100322, baseEnd_100322] using wordTrace_append hprefix tailTrace_100322
  have hstable : (prefixWord ++ tailWord_100322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100322).length < 2 ^ (prefixWord ++ tailWord_100322).sum := by decide
  have hdescent : baseEnd_100322 < baseStart_100322 := by decide
  rcases family_descends (prefixWord ++ tailWord_100322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100330 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_100330 : Nat := 118140960795 + 100330 * 2 ^ 59
def prefixEnd_100330 : Nat := 4983230072969 + 3 ^ 40 * 100330 * 2
def baseEnd_100330 : Nat := 45793345836175726323197

theorem tailTrace_100330 : CollatzResearch.WordTrace tailWord_100330 prefixEnd_100330 45793345836175726323197 := by
  unfold tailWord_100330
  simp only [CollatzResearch.WordTrace]
  refine ⟨914833931632254961230611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2439557151019346563281629 914833931632254961230611)
  ·
    refine ⟨1372250897448382441845917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914833931632254961230611 1372250897448382441845917)
    ·
      refine ⟨514594086543143415692219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1372250897448382441845917 514594086543143415692219)
      ·
        refine ⟨771891129814715123538329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514594086543143415692219 771891129814715123538329)
        ·
          refine ⟨578918347361036342653747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771891129814715123538329 578918347361036342653747)
          ·
            refine ⟨868377521041554513980621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578918347361036342653747 868377521041554513980621)
            ·
              refine ⟨325641570390582942742733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868377521041554513980621 325641570390582942742733)
              ·
                refine ⟨122115588896468603528525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325641570390582942742733 122115588896468603528525)
                ·
                  refine ⟨45793345836175726323197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122115588896468603528525 45793345836175726323197)
                  ·
                    rfl

theorem cell20_100330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_100330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100330 prefixEnd_100330 := by exact prefixLift 100330
  have htrace : WordTrace (prefixWord ++ tailWord_100330) baseStart_100330 baseEnd_100330 := by
    simpa [prefixWord, tailWord_100330, baseEnd_100330] using wordTrace_append hprefix tailTrace_100330
  have hstable : (prefixWord ++ tailWord_100330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100330).length < 2 ^ (prefixWord ++ tailWord_100330).sum := by decide
  have hdescent : baseEnd_100330 < baseStart_100330 := by decide
  rcases family_descends (prefixWord ++ tailWord_100330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100403 : List Nat := [1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_100403 : Nat := 118140960795 + 100403 * 2 ^ 59
def prefixEnd_100403 : Nat := 4983230072969 + 3 ^ 40 * 100403 * 2
def baseEnd_100403 : Nat := 15275555008437305629855

theorem tailTrace_100403 : CollatzResearch.WordTrace tailWord_100403 prefixEnd_100403 15275555008437305629855 := by
  unfold tailWord_100403
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661998255264553312329863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2441332170176368874886575 3661998255264553312329863)
  ·
    refine ⟨5492997382896829968494795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661998255264553312329863 5492997382896829968494795)
    ·
      refine ⟨8239496074345244952742193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492997382896829968494795 8239496074345244952742193)
      ·
        refine ⟨6179622055758933714556645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8239496074345244952742193 6179622055758933714556645)
        ·
          refine ⟨1158679135454800071479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6179622055758933714556645 1158679135454800071479371)
          ·
            refine ⟨1738018703182200107219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158679135454800071479371 1738018703182200107219057)
            ·
              refine ⟨1303514027386650080414293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738018703182200107219057 1303514027386650080414293)
              ·
                refine ⟨15275555008437305629855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1303514027386650080414293 15275555008437305629855)
                ·
                  rfl

theorem cell20_100403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_100403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100403 prefixEnd_100403 := by exact prefixLift 100403
  have htrace : WordTrace (prefixWord ++ tailWord_100403) baseStart_100403 baseEnd_100403 := by
    simpa [prefixWord, tailWord_100403, baseEnd_100403] using wordTrace_append hprefix tailTrace_100403
  have hstable : (prefixWord ++ tailWord_100403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100403).length < 2 ^ (prefixWord ++ tailWord_100403).sum := by decide
  have hdescent : baseEnd_100403 < baseStart_100403 := by decide
  rcases family_descends (prefixWord ++ tailWord_100403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100406 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_100406 : Nat := 118140960795 + 100406 * 2 ^ 59
def prefixEnd_100406 : Nat := 4983230072969 + 3 ^ 40 * 100406 * 2
def baseEnd_100406 : Nat := 45828034307057239789553

theorem tailTrace_100406 : CollatzResearch.WordTrace tailWord_100406 prefixEnd_100406 45828034307057239789553 := by
  unfold tailWord_100406
  simp only [CollatzResearch.WordTrace]
  refine ⟨228881729640855301543067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2441405116169123216459381 228881729640855301543067)
  ·
    refine ⟨343322594461282952314601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228881729640855301543067 343322594461282952314601)
    ·
      refine ⟨257491945845962214235951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343322594461282952314601 257491945845962214235951)
      ·
        refine ⟨386237918768943321353927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257491945845962214235951 386237918768943321353927)
        ·
          refine ⟨579356878153414982030891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386237918768943321353927 579356878153414982030891)
          ·
            refine ⟨869035317230122473046337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579356878153414982030891 869035317230122473046337)
            ·
              refine ⟨651776487922591854784753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869035317230122473046337 651776487922591854784753)
              ·
                refine ⟨488832365941943891088565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651776487922591854784753 488832365941943891088565)
                ·
                  refine ⟨45828034307057239789553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 488832365941943891088565 45828034307057239789553)
                  ·
                    rfl

theorem cell20_100406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_100406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100406 prefixEnd_100406 := by exact prefixLift 100406
  have htrace : WordTrace (prefixWord ++ tailWord_100406) baseStart_100406 baseEnd_100406 := by
    simpa [prefixWord, tailWord_100406, baseEnd_100406] using wordTrace_append hprefix tailTrace_100406
  have hstable : (prefixWord ++ tailWord_100406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100406).length < 2 ^ (prefixWord ++ tailWord_100406).sum := by decide
  have hdescent : baseEnd_100406 < baseStart_100406 := by decide
  rcases family_descends (prefixWord ++ tailWord_100406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100409 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 2]
def baseStart_100409 : Nat := 118140960795 + 100409 * 2 ^ 59
def prefixEnd_100409 : Nat := 4983230072969 + 3 ^ 40 * 100409 * 2
def baseEnd_100409 : Nat := 45829403588802562689541

theorem tailTrace_100409 : CollatzResearch.WordTrace tailWord_100409 prefixEnd_100409 45829403588802562689541 := by
  unfold tailWord_100409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662217093242816337048281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2441478062161877558032187 3662217093242816337048281)
  ·
    refine ⟨2746662819932112252786211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3662217093242816337048281 2746662819932112252786211)
    ·
      refine ⟨4119994229898168379179317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746662819932112252786211 4119994229898168379179317)
      ·
        refine ⟨386249459052953285548061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4119994229898168379179317 386249459052953285548061)
        ·
          refine ⟨144843547144857482080523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386249459052953285548061 144843547144857482080523)
          ·
            refine ⟨217265320717286223120785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144843547144857482080523 217265320717286223120785)
            ·
              refine ⟨162948990537964667340589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217265320717286223120785 162948990537964667340589)
              ·
                refine ⟨61105871451736750252721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162948990537964667340589 61105871451736750252721)
                ·
                  refine ⟨45829403588802562689541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61105871451736750252721 45829403588802562689541)
                  ·
                    rfl

theorem cell20_100409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_100409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100409 prefixEnd_100409 := by exact prefixLift 100409
  have htrace : WordTrace (prefixWord ++ tailWord_100409) baseStart_100409 baseEnd_100409 := by
    simpa [prefixWord, tailWord_100409, baseEnd_100409] using wordTrace_append hprefix tailTrace_100409
  have hstable : (prefixWord ++ tailWord_100409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100409).length < 2 ^ (prefixWord ++ tailWord_100409).sum := by decide
  have hdescent : baseEnd_100409 < baseStart_100409 := by decide
  rcases family_descends (prefixWord ++ tailWord_100409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100430 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_100430 : Nat := 118140960795 + 100430 * 2 ^ 59
def prefixEnd_100430 : Nat := 4983230072969 + 3 ^ 40 * 100430 * 2
def baseEnd_100430 : Nat := 45838988561019822989455

theorem tailTrace_100430 : CollatzResearch.WordTrace tailWord_100430 prefixEnd_100430 45838988561019822989455 := by
  unfold tailWord_100430
  simp only [CollatzResearch.WordTrace]
  refine ⟨457872878270842115445343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2441988684111157949041829 457872878270842115445343)
  ·
    refine ⟨686809317406263173168015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457872878270842115445343 686809317406263173168015)
    ·
      refine ⟨1030213976109394759752023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686809317406263173168015 1030213976109394759752023)
      ·
        refine ⟨1545320964164092139628035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030213976109394759752023 1545320964164092139628035)
        ·
          refine ⟨2317981446246138209442053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545320964164092139628035 2317981446246138209442053)
          ·
            refine ⟨434621521171150914270385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2317981446246138209442053 434621521171150914270385)
            ·
              refine ⟨325966140878363185702789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434621521171150914270385 325966140878363185702789)
              ·
                refine ⟨61118651414693097319273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325966140878363185702789 61118651414693097319273)
                ·
                  refine ⟨45838988561019822989455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61118651414693097319273 45838988561019822989455)
                  ·
                    rfl

theorem cell20_100430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_100430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100430 prefixEnd_100430 := by exact prefixLift 100430
  have htrace : WordTrace (prefixWord ++ tailWord_100430) baseStart_100430 baseEnd_100430 := by
    simpa [prefixWord, tailWord_100430, baseEnd_100430] using wordTrace_append hprefix tailTrace_100430
  have hstable : (prefixWord ++ tailWord_100430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100430).length < 2 ^ (prefixWord ++ tailWord_100430).sum := by decide
  have hdescent : baseEnd_100430 < baseStart_100430 := by decide
  rcases family_descends (prefixWord ++ tailWord_100430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100441 : List Nat := [1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_100441 : Nat := 118140960795 + 100441 * 2 ^ 59
def prefixEnd_100441 : Nat := 4983230072969 + 3 ^ 40 * 100441 * 2
def baseEnd_100441 : Nat := 15281336420250891207581

theorem tailTrace_100441 : CollatzResearch.WordTrace tailWord_100441 prefixEnd_100441 15281336420250891207581 := by
  unfold tailWord_100441
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663384229126885802213177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2442256152751257201475451 3663384229126885802213177)
  ·
    refine ⟨2747538171845164351659883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3663384229126885802213177 2747538171845164351659883)
    ·
      refine ⟨4121307257767746527489825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747538171845164351659883 4121307257767746527489825)
      ·
        refine ⟨3090980443325809895617369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121307257767746527489825 3090980443325809895617369)
        ·
          refine ⟨2318235332494357421713027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090980443325809895617369 2318235332494357421713027)
          ·
            refine ⟨3477352998741536132569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318235332494357421713027 3477352998741536132569541)
            ·
              refine ⟨652003687264038024856789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3477352998741536132569541 652003687264038024856789)
              ·
                refine ⟨15281336420250891207581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 652003687264038024856789 15281336420250891207581)
                ·
                  rfl

theorem cell20_100441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_100441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100441 prefixEnd_100441 := by exact prefixLift 100441
  have htrace : WordTrace (prefixWord ++ tailWord_100441) baseStart_100441 baseEnd_100441 := by
    simpa [prefixWord, tailWord_100441, baseEnd_100441] using wordTrace_append hprefix tailTrace_100441
  have hstable : (prefixWord ++ tailWord_100441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100441).length < 2 ^ (prefixWord ++ tailWord_100441).sum := by decide
  have hdescent : baseEnd_100441 < baseStart_100441 := by decide
  rcases family_descends (prefixWord ++ tailWord_100441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100485 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 2]
def baseStart_100485 : Nat := 118140960795 + 100485 * 2 ^ 59
def prefixEnd_100485 : Nat := 4983230072969 + 3 ^ 40 * 100485 * 2
def baseEnd_100485 : Nat := 45864092059684076155897

theorem tailTrace_100485 : CollatzResearch.WordTrace tailWord_100485 prefixEnd_100485 45864092059684076155897 := by
  unfold tailWord_100485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664989040967481316814909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2443326027311654211209939 3664989040967481316814909)
  ·
    refine ⟨1374370890362805493805591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3664989040967481316814909 1374370890362805493805591)
    ·
      refine ⟨2061556335544208240708387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374370890362805493805591 2061556335544208240708387)
      ·
        refine ⟨3092334503316312361062581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061556335544208240708387 3092334503316312361062581)
        ·
          refine ⟨289906359685904283849617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3092334503316312361062581 289906359685904283849617)
          ·
            refine ⟨217429769764428212887213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289906359685904283849617 217429769764428212887213)
            ·
              refine ⟨81536163661660579832705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217429769764428212887213 81536163661660579832705)
              ·
                refine ⟨61152122746245434874529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81536163661660579832705 61152122746245434874529)
                ·
                  refine ⟨45864092059684076155897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61152122746245434874529 45864092059684076155897)
                  ·
                    rfl

theorem cell20_100485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_100485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100485 prefixEnd_100485 := by exact prefixLift 100485
  have htrace : WordTrace (prefixWord ++ tailWord_100485) baseStart_100485 baseEnd_100485 := by
    simpa [prefixWord, tailWord_100485, baseEnd_100485] using wordTrace_append hprefix tailTrace_100485
  have hstable : (prefixWord ++ tailWord_100485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100485).length < 2 ^ (prefixWord ++ tailWord_100485).sum := by decide
  have hdescent : baseEnd_100485 < baseStart_100485 := by decide
  rcases family_descends (prefixWord ++ tailWord_100485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100517 : List Nat := [1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_100517 : Nat := 118140960795 + 100517 * 2 ^ 59
def prefixEnd_100517 : Nat := 4983230072969 + 3 ^ 40 * 100517 * 2
def baseEnd_100517 : Nat := 15292899243878062363033

theorem tailTrace_100517 : CollatzResearch.WordTrace tailWord_100517 prefixEnd_100517 15292899243878062363033 := by
  unfold tailWord_100517
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666156176851550781979805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2444104117901033854653203 3666156176851550781979805)
  ·
    refine ⟨1374808566319331543242427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3666156176851550781979805 1374808566319331543242427)
    ·
      refine ⟨2062212849478997314863641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374808566319331543242427 2062212849478997314863641)
      ·
        refine ⟨1546659637109247986147731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062212849478997314863641 1546659637109247986147731)
        ·
          refine ⟨2319989455663871979221597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546659637109247986147731 2319989455663871979221597)
          ·
            refine ⟨869996045873951992208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2319989455663871979221597 869996045873951992208099)
            ·
              refine ⟨1304994068810927988312149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869996045873951992208099 1304994068810927988312149)
              ·
                refine ⟨15292899243878062363033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1304994068810927988312149 15292899243878062363033)
                ·
                  rfl

theorem cell20_100517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_100517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100517 prefixEnd_100517 := by exact prefixLift 100517
  have htrace : WordTrace (prefixWord ++ tailWord_100517) baseStart_100517 baseEnd_100517 := by
    simpa [prefixWord, tailWord_100517, baseEnd_100517] using wordTrace_append hprefix tailTrace_100517
  have hstable : (prefixWord ++ tailWord_100517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100517).length < 2 ^ (prefixWord ++ tailWord_100517).sum := by decide
  have hdescent : baseEnd_100517 < baseStart_100517 := by decide
  rcases family_descends (prefixWord ++ tailWord_100517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100527 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 2]
def baseStart_100527 : Nat := 118140960795 + 100527 * 2 ^ 59
def prefixEnd_100527 : Nat := 4983230072969 + 3 ^ 40 * 100527 * 2
def baseEnd_100527 : Nat := 45883262004118596755725

theorem tailTrace_100527 : CollatzResearch.WordTrace tailWord_100527 prefixEnd_100527 45883262004118596755725 := by
  unfold tailWord_100527
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666520906815322489843835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2444347271210214993229223 3666520906815322489843835)
  ·
    refine ⟨5499781360222983734765753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666520906815322489843835 5499781360222983734765753)
    ·
      refine ⟨4124836020167237801074315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5499781360222983734765753 4124836020167237801074315)
      ·
        refine ⟨6187254030250856701611473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124836020167237801074315 6187254030250856701611473)
        ·
          refine ⟨4640440522688142526208605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187254030250856701611473 4640440522688142526208605)
          ·
            refine ⟨1740165196008053447328227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4640440522688142526208605 1740165196008053447328227)
            ·
              refine ⟨2610247794012080170992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740165196008053447328227 2610247794012080170992341)
              ·
                refine ⟨61177682672158129007633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2610247794012080170992341 61177682672158129007633)
                ·
                  refine ⟨45883262004118596755725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61177682672158129007633 45883262004118596755725)
                  ·
                    rfl

theorem cell20_100527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2].length) (baseStart_100527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100527 prefixEnd_100527 := by exact prefixLift 100527
  have htrace : WordTrace (prefixWord ++ tailWord_100527) baseStart_100527 baseEnd_100527 := by
    simpa [prefixWord, tailWord_100527, baseEnd_100527] using wordTrace_append hprefix tailTrace_100527
  have hstable : (prefixWord ++ tailWord_100527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100527).length < 2 ^ (prefixWord ++ tailWord_100527).sum := by decide
  have hdescent : baseEnd_100527 < baseStart_100527 := by decide
  rcases family_descends (prefixWord ++ tailWord_100527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100534 : List Nat := [5, 1, 3, 11]
def baseStart_100534 : Nat := 118140960795 + 100534 * 2 ^ 59
def prefixEnd_100534 : Nat := 4983230072969 + 3 ^ 40 * 100534 * 2
def baseEnd_100534 : Nat := 188833156357439026841

theorem tailTrace_100534 : CollatzResearch.WordTrace tailWord_100534 prefixEnd_100534 188833156357439026841 := by
  unfold tailWord_100534
  simp only [CollatzResearch.WordTrace]
  refine ⟨229173513611872667834291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2444517478526641790232437 229173513611872667834291)
  ·
    refine ⟨343760270417809001751437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229173513611872667834291 343760270417809001751437)
    ·
      refine ⟨128910101406678375656789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343760270417809001751437 128910101406678375656789)
      ·
        refine ⟨188833156357439026841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 128910101406678375656789 188833156357439026841)
        ·
          rfl

theorem cell20_100534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 11].length) (baseStart_100534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100534 prefixEnd_100534 := by exact prefixLift 100534
  have htrace : WordTrace (prefixWord ++ tailWord_100534) baseStart_100534 baseEnd_100534 := by
    simpa [prefixWord, tailWord_100534, baseEnd_100534] using wordTrace_append hprefix tailTrace_100534
  have hstable : (prefixWord ++ tailWord_100534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100534).length < 2 ^ (prefixWord ++ tailWord_100534).sum := by decide
  have hdescent : baseEnd_100534 < baseStart_100534 := by decide
  rcases family_descends (prefixWord ++ tailWord_100534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100540 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_100540 : Nat := 118140960795 + 100540 * 2 ^ 59
def prefixEnd_100540 : Nat := 4983230072969 + 3 ^ 40 * 100540 * 2
def baseEnd_100540 : Nat := 45889195558348329322339

theorem tailTrace_100540 : CollatzResearch.WordTrace tailWord_100540 prefixEnd_100540 45889195558348329322339 := by
  unfold tailWord_100540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833497527884112855033537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2444663370512150473378049 1833497527884112855033537)
  ·
    refine ⟨1375123145913084641275153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1833497527884112855033537 1375123145913084641275153)
    ·
      refine ⟨1031342359434813480956365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1375123145913084641275153 1031342359434813480956365)
      ·
        refine ⟨386753384788055055358637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1031342359434813480956365 386753384788055055358637)
        ·
          refine ⟨145032519295520645759489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386753384788055055358637 145032519295520645759489)
          ·
            refine ⟨108774389471640484319617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145032519295520645759489 108774389471640484319617)
            ·
              refine ⟨81580792103730363239713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108774389471640484319617 81580792103730363239713)
              ·
                refine ⟨61185594077797772429785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81580792103730363239713 61185594077797772429785)
                ·
                  refine ⟨45889195558348329322339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61185594077797772429785 45889195558348329322339)
                  ·
                    rfl

theorem cell20_100540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_100540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100540 prefixEnd_100540 := by exact prefixLift 100540
  have htrace : WordTrace (prefixWord ++ tailWord_100540) baseStart_100540 baseEnd_100540 := by
    simpa [prefixWord, tailWord_100540, baseEnd_100540] using wordTrace_append hprefix tailTrace_100540
  have hstable : (prefixWord ++ tailWord_100540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100540).length < 2 ^ (prefixWord ++ tailWord_100540).sum := by decide
  have hdescent : baseEnd_100540 < baseStart_100540 := by decide
  rcases family_descends (prefixWord ++ tailWord_100540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100544 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_100544 : Nat := 118140960795 + 100544 * 2 ^ 59
def prefixEnd_100544 : Nat := 4983230072969 + 3 ^ 40 * 100544 * 2
def baseEnd_100544 : Nat := 45891021267342093188989

theorem tailTrace_100544 : CollatzResearch.WordTrace tailWord_100544 prefixEnd_100544 45891021267342093188989 := by
  unfold tailWord_100544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833570473876867196606343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2444760631835822928808457 1833570473876867196606343)
  ·
    refine ⟨2750355710815300794909515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833570473876867196606343 2750355710815300794909515)
    ·
      refine ⟨4125533566222951192364273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750355710815300794909515 4125533566222951192364273)
      ·
        refine ⟨3094150174667213394273205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125533566222951192364273 3094150174667213394273205)
        ·
          refine ⟨290076578875051255713113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3094150174667213394273205 290076578875051255713113)
          ·
            refine ⟨217557434156288441784835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290076578875051255713113 217557434156288441784835)
            ·
              refine ⟨326336151234432662677253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217557434156288441784835 326336151234432662677253)
              ·
                refine ⟨61188028356456124251985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326336151234432662677253 61188028356456124251985)
                ·
                  refine ⟨45891021267342093188989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61188028356456124251985 45891021267342093188989)
                  ·
                    rfl

theorem cell20_100544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_100544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100544 prefixEnd_100544 := by exact prefixLift 100544
  have htrace : WordTrace (prefixWord ++ tailWord_100544) baseStart_100544 baseEnd_100544 := by
    simpa [prefixWord, tailWord_100544, baseEnd_100544] using wordTrace_append hprefix tailTrace_100544
  have hstable : (prefixWord ++ tailWord_100544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100544).length < 2 ^ (prefixWord ++ tailWord_100544).sum := by decide
  have hdescent : baseEnd_100544 < baseStart_100544 := by decide
  rcases family_descends (prefixWord ++ tailWord_100544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100558 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_100558 : Nat := 118140960795 + 100558 * 2 ^ 59
def prefixEnd_100558 : Nat := 4983230072969 + 3 ^ 40 * 100558 * 2
def baseEnd_100558 : Nat := 45897411248820266722265

theorem tailTrace_100558 : CollatzResearch.WordTrace tailWord_100558 prefixEnd_100558 45897411248820266722265 := by
  unfold tailWord_100558
  simp only [CollatzResearch.WordTrace]
  refine ⟨458456446212876848027791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2445101046468676522814885 458456446212876848027791)
  ·
    refine ⟨687684669319315272041687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458456446212876848027791 687684669319315272041687)
    ·
      refine ⟨1031527003978972908062531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687684669319315272041687 1031527003978972908062531)
      ·
        refine ⟨1547290505968459362093797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031527003978972908062531 1547290505968459362093797)
        ·
          refine ⟨290116969869086130392587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1547290505968459362093797 290116969869086130392587)
          ·
            refine ⟨435175454803629195588881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290116969869086130392587 435175454803629195588881)
            ·
              refine ⟨326381591102721896691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435175454803629195588881 326381591102721896691661)
              ·
                refine ⟨122393096663520711259373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326381591102721896691661 122393096663520711259373)
                ·
                  refine ⟨45897411248820266722265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122393096663520711259373 45897411248820266722265)
                  ·
                    rfl

theorem cell20_100558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_100558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100558 prefixEnd_100558 := by exact prefixLift 100558
  have htrace : WordTrace (prefixWord ++ tailWord_100558) baseStart_100558 baseEnd_100558 := by
    simpa [prefixWord, tailWord_100558, baseEnd_100558] using wordTrace_append hprefix tailTrace_100558
  have hstable : (prefixWord ++ tailWord_100558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100558).length < 2 ^ (prefixWord ++ tailWord_100558).sum := by decide
  have hdescent : baseEnd_100558 < baseStart_100558 := by decide
  rcases family_descends (prefixWord ++ tailWord_100558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100586 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_100586 : Nat := 118140960795 + 100586 * 2 ^ 59
def prefixEnd_100586 : Nat := 4983230072969 + 3 ^ 40 * 100586 * 2
def baseEnd_100586 : Nat := 45910191211776613788817

theorem tailTrace_100586 : CollatzResearch.WordTrace tailWord_100586 prefixEnd_100586 45910191211776613788817 := by
  unfold tailWord_100586
  simp only [CollatzResearch.WordTrace]
  refine ⟨917168203400393891560403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2445781875734383710827741 917168203400393891560403)
  ·
    refine ⟨1375752305100590837340605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 917168203400393891560403 1375752305100590837340605)
    ·
      refine ⟨515907114412721564002727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1375752305100590837340605 515907114412721564002727)
      ·
        refine ⟨773860671619082346004091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515907114412721564002727 773860671619082346004091)
        ·
          refine ⟨1160791007428623519006137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773860671619082346004091 1160791007428623519006137)
          ·
            refine ⟨870593255571467639254603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160791007428623519006137 870593255571467639254603)
            ·
              refine ⟨1305889883357201458881905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870593255571467639254603 1305889883357201458881905)
              ·
                refine ⟨979417412517901094161429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305889883357201458881905 979417412517901094161429)
                ·
                  refine ⟨45910191211776613788817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 979417412517901094161429 45910191211776613788817)
                  ·
                    rfl

theorem cell20_100586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_100586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100586 prefixEnd_100586 := by exact prefixLift 100586
  have htrace : WordTrace (prefixWord ++ tailWord_100586) baseStart_100586 baseEnd_100586 := by
    simpa [prefixWord, tailWord_100586, baseEnd_100586] using wordTrace_append hprefix tailTrace_100586
  have hstable : (prefixWord ++ tailWord_100586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100586).length < 2 ^ (prefixWord ++ tailWord_100586).sum := by decide
  have hdescent : baseEnd_100586 < baseStart_100586 := by decide
  rcases family_descends (prefixWord ++ tailWord_100586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100654 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_100654 : Nat := 118140960795 + 100654 * 2 ^ 59
def prefixEnd_100654 : Nat := 4983230072969 + 3 ^ 40 * 100654 * 2
def baseEnd_100654 : Nat := 45941228264670599521873

theorem tailTrace_100654 : CollatzResearch.WordTrace tailWord_100654 prefixEnd_100654 45941228264670599521873 := by
  unfold tailWord_100654
  simp only [CollatzResearch.WordTrace]
  refine ⟨458894122169402897464627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2447435318236815453144677 458894122169402897464627)
  ·
    refine ⟨688341183254104346196941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458894122169402897464627 688341183254104346196941)
    ·
      refine ⟨258127943720289129823853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 688341183254104346196941 258127943720289129823853)
      ·
        refine ⟨96797978895108423683945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258127943720289129823853 96797978895108423683945)
        ·
          refine ⟨72598484171331317762959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96797978895108423683945 72598484171331317762959)
          ·
            refine ⟨108897726256996976644439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72598484171331317762959 108897726256996976644439)
            ·
              refine ⟨163346589385495464966659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108897726256996976644439 163346589385495464966659)
              ·
                refine ⟨245019884078243197449989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163346589385495464966659 245019884078243197449989)
                ·
                  refine ⟨45941228264670599521873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245019884078243197449989 45941228264670599521873)
                  ·
                    rfl

theorem cell20_100654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_100654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100654 prefixEnd_100654 := by exact prefixLift 100654
  have htrace : WordTrace (prefixWord ++ tailWord_100654) baseStart_100654 baseEnd_100654 := by
    simpa [prefixWord, tailWord_100654, baseEnd_100654] using wordTrace_append hprefix tailTrace_100654
  have hstable : (prefixWord ++ tailWord_100654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100654).length < 2 ^ (prefixWord ++ tailWord_100654).sum := by decide
  have hdescent : baseEnd_100654 < baseStart_100654 := by decide
  rcases family_descends (prefixWord ++ tailWord_100654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100658 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_100658 : Nat := 118140960795 + 100658 * 2 ^ 59
def prefixEnd_100658 : Nat := 4983230072969 + 3 ^ 40 * 100658 * 2
def baseEnd_100658 : Nat := 45943053973664363388523

theorem tailTrace_100658 : CollatzResearch.WordTrace tailWord_100658 prefixEnd_100658 45943053973664363388523 := by
  unfold tailWord_100658
  simp only [CollatzResearch.WordTrace]
  refine ⟨917824717335182965715657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2447532579560487908575085 917824717335182965715657)
  ·
    refine ⟨688368538001387224286743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917824717335182965715657 688368538001387224286743)
    ·
      refine ⟨1032552807002080836430115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688368538001387224286743 1032552807002080836430115)
      ·
        refine ⟨1548829210503121254645173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032552807002080836430115 1548829210503121254645173)
        ·
          refine ⟨145202738484667617622985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1548829210503121254645173 145202738484667617622985)
          ·
            refine ⟨108902053863500713217239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145202738484667617622985 108902053863500713217239)
            ·
              refine ⟨163353080795251069825859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108902053863500713217239 163353080795251069825859)
              ·
                refine ⟨245029621192876604738789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163353080795251069825859 245029621192876604738789)
                ·
                  refine ⟨45943053973664363388523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245029621192876604738789 45943053973664363388523)
                  ·
                    rfl

theorem cell20_100658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_100658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100658 prefixEnd_100658 := by exact prefixLift 100658
  have htrace : WordTrace (prefixWord ++ tailWord_100658) baseStart_100658 baseEnd_100658 := by
    simpa [prefixWord, tailWord_100658, baseEnd_100658] using wordTrace_append hprefix tailTrace_100658
  have hstable : (prefixWord ++ tailWord_100658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100658).length < 2 ^ (prefixWord ++ tailWord_100658).sum := by decide
  have hdescent : baseEnd_100658 < baseStart_100658 := by decide
  rcases family_descends (prefixWord ++ tailWord_100658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100702 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_100702 : Nat := 118140960795 + 100702 * 2 ^ 59
def prefixEnd_100702 : Nat := 4983230072969 + 3 ^ 40 * 100702 * 2
def baseEnd_100702 : Nat := 45963136772595765921677

theorem tailTrace_100702 : CollatzResearch.WordTrace tailWord_100702 prefixEnd_100702 45963136772595765921677 := by
  unfold tailWord_100702
  simp only [CollatzResearch.WordTrace]
  refine ⟨459112960147665922183045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2448602454120884918309573 459112960147665922183045)
  ·
    refine ⟨86083680027687360409321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 459112960147665922183045 86083680027687360409321)
    ·
      refine ⟨64562760020765520306991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86083680027687360409321 64562760020765520306991)
      ·
        refine ⟨96844140031148280460487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64562760020765520306991 96844140031148280460487)
        ·
          refine ⟨145266210046722420690731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96844140031148280460487 145266210046722420690731)
          ·
            refine ⟨217899315070083631036097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145266210046722420690731 217899315070083631036097)
            ·
              refine ⟨163424486302562723277073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217899315070083631036097 163424486302562723277073)
              ·
                refine ⟨122568364726922042457805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163424486302562723277073 122568364726922042457805)
                ·
                  refine ⟨45963136772595765921677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122568364726922042457805 45963136772595765921677)
                  ·
                    rfl

theorem cell20_100702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_100702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100702 prefixEnd_100702 := by exact prefixLift 100702
  have htrace : WordTrace (prefixWord ++ tailWord_100702) baseStart_100702 baseEnd_100702 := by
    simpa [prefixWord, tailWord_100702, baseEnd_100702] using wordTrace_append hprefix tailTrace_100702
  have hstable : (prefixWord ++ tailWord_100702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100702).length < 2 ^ (prefixWord ++ tailWord_100702).sum := by decide
  have hdescent : baseEnd_100702 < baseStart_100702 := by decide
  rcases family_descends (prefixWord ++ tailWord_100702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100731 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_100731 : Nat := 118140960795 + 100731 * 2 ^ 59
def prefixEnd_100731 : Nat := 4983230072969 + 3 ^ 40 * 100731 * 2
def baseEnd_100731 : Nat := 45976373162800553954891

theorem tailTrace_100731 : CollatzResearch.WordTrace tailWord_100731 prefixEnd_100731 45976373162800553954891 := by
  unfold tailWord_100731
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673961398076265330270047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449307598717510220180031 3673961398076265330270047)
  ·
    refine ⟨5510942097114397995405071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673961398076265330270047 5510942097114397995405071)
    ·
      refine ⟨8266413145671596993107607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510942097114397995405071 8266413145671596993107607)
      ·
        refine ⟨12399619718507395489661411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266413145671596993107607 12399619718507395489661411)
        ·
          refine ⟨18599429577761093234492117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12399619718507395489661411 18599429577761093234492117)
          ·
            refine ⟨435924130728775622683409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18599429577761093234492117 435924130728775622683409)
            ·
              refine ⟨326943098046581717012557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435924130728775622683409 326943098046581717012557)
              ·
                refine ⟨122603661767468143879709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326943098046581717012557 122603661767468143879709)
                ·
                  refine ⟨45976373162800553954891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122603661767468143879709 45976373162800553954891)
                  ·
                    rfl

theorem cell20_100731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_100731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100731 prefixEnd_100731 := by exact prefixLift 100731
  have htrace : WordTrace (prefixWord ++ tailWord_100731) baseStart_100731 baseEnd_100731 := by
    simpa [prefixWord, tailWord_100731, baseEnd_100731] using wordTrace_append hprefix tailTrace_100731
  have hstable : (prefixWord ++ tailWord_100731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100731).length < 2 ^ (prefixWord ++ tailWord_100731).sum := by decide
  have hdescent : baseEnd_100731 < baseStart_100731 := by decide
  rcases family_descends (prefixWord ++ tailWord_100731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100765 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_100765 : Nat := 118140960795 + 100765 * 2 ^ 59
def prefixEnd_100765 : Nat := 4983230072969 + 3 ^ 40 * 100765 * 2
def baseEnd_100765 : Nat := 45991891689247546821419

theorem tailTrace_100765 : CollatzResearch.WordTrace tailWord_100765 prefixEnd_100765 45991891689247546821419 := by
  unfold tailWord_100765
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675201479953089137007749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2450134319968726091338499 3675201479953089137007749)
  ·
    refine ⟨689100277491204213188953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3675201479953089137007749 689100277491204213188953)
    ·
      refine ⟨516825208118403159891715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689100277491204213188953 516825208118403159891715)
      ·
        refine ⟨775237812177604739837573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516825208118403159891715 775237812177604739837573)
        ·
          refine ⟨145357089783300888719545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 775237812177604739837573 145357089783300888719545)
          ·
            refine ⟨109017817337475666539659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145357089783300888719545 109017817337475666539659)
            ·
              refine ⟨163526726006213499809489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109017817337475666539659 163526726006213499809489)
              ·
                refine ⟨122645044504660124857117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163526726006213499809489 122645044504660124857117)
                ·
                  refine ⟨45991891689247546821419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122645044504660124857117 45991891689247546821419)
                  ·
                    rfl

theorem cell20_100765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_100765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100765 prefixEnd_100765 := by exact prefixLift 100765
  have htrace : WordTrace (prefixWord ++ tailWord_100765) baseStart_100765 baseEnd_100765 := by
    simpa [prefixWord, tailWord_100765, baseEnd_100765] using wordTrace_append hprefix tailTrace_100765
  have hstable : (prefixWord ++ tailWord_100765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100765).length < 2 ^ (prefixWord ++ tailWord_100765).sum := by decide
  have hdescent : baseEnd_100765 < baseStart_100765 := by decide
  rcases family_descends (prefixWord ++ tailWord_100765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100786 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_100786 : Nat := 118140960795 + 100786 * 2 ^ 59
def prefixEnd_100786 : Nat := 4983230072969 + 3 ^ 40 * 100786 * 2
def baseEnd_100786 : Nat := 46001476661464807121333

theorem tailTrace_100786 : CollatzResearch.WordTrace tailWord_100786 prefixEnd_100786 46001476661464807121333 := by
  unfold tailWord_100786
  simp only [CollatzResearch.WordTrace]
  refine ⟨918991853219252430880553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2450644941918006482348141 918991853219252430880553)
  ·
    refine ⟨689243889914439323160415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 918991853219252430880553 689243889914439323160415)
    ·
      refine ⟨1033865834871658984740623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689243889914439323160415 1033865834871658984740623)
      ·
        refine ⟨1550798752307488477110935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033865834871658984740623 1550798752307488477110935)
        ·
          refine ⟨2326198128461232715666403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550798752307488477110935 2326198128461232715666403)
          ·
            refine ⟨3489297192691849073499605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326198128461232715666403 3489297192691849073499605)
            ·
              refine ⟨81780402953715212660147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3489297192691849073499605 81780402953715212660147)
              ·
                refine ⟨122670604430572818990221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81780402953715212660147 122670604430572818990221)
                ·
                  refine ⟨46001476661464807121333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122670604430572818990221 46001476661464807121333)
                  ·
                    rfl

theorem cell20_100786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_100786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100786 prefixEnd_100786 := by exact prefixLift 100786
  have htrace : WordTrace (prefixWord ++ tailWord_100786) baseStart_100786 baseEnd_100786 := by
    simpa [prefixWord, tailWord_100786, baseEnd_100786] using wordTrace_append hprefix tailTrace_100786
  have hstable : (prefixWord ++ tailWord_100786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100786).length < 2 ^ (prefixWord ++ tailWord_100786).sum := by decide
  have hdescent : baseEnd_100786 < baseStart_100786 := by decide
  rcases family_descends (prefixWord ++ tailWord_100786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100821 : List Nat := [1, 3, 2, 3, 1, 2, 8]
def baseStart_100821 : Nat := 118140960795 + 100821 * 2 ^ 59
def prefixEnd_100821 : Nat := 4983230072969 + 3 ^ 40 * 100821 * 2
def baseEnd_100821 : Nat := 5113050179462248994947

theorem tailTrace_100821 : CollatzResearch.WordTrace tailWord_100821 prefixEnd_100821 5113050179462248994947 := by
  unfold tailWord_100821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677243967750210701046317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2451495978500140467364211 3677243967750210701046317)
  ·
    refine ⟨1378966487906329012892369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3677243967750210701046317 1378966487906329012892369)
    ·
      refine ⟨1034224865929746759669277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1378966487906329012892369 1034224865929746759669277)
      ·
        refine ⟨387834324723655034875979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1034224865929746759669277 387834324723655034875979)
        ·
          refine ⟨581751487085482552313969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387834324723655034875979 581751487085482552313969)
          ·
            refine ⟨436313615314111914235477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581751487085482552313969 436313615314111914235477)
            ·
              refine ⟨5113050179462248994947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 436313615314111914235477 5113050179462248994947)
              ·
                rfl

theorem cell20_100821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_100821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100821 prefixEnd_100821 := by exact prefixLift 100821
  have htrace : WordTrace (prefixWord ++ tailWord_100821) baseStart_100821 baseEnd_100821 := by
    simpa [prefixWord, tailWord_100821, baseEnd_100821] using wordTrace_append hprefix tailTrace_100821
  have hstable : (prefixWord ++ tailWord_100821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100821).length < 2 ^ (prefixWord ++ tailWord_100821).sum := by decide
  have hdescent : baseEnd_100821 < baseStart_100821 := by decide
  rcases family_descends (prefixWord ++ tailWord_100821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100831 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_100831 : Nat := 118140960795 + 100831 * 2 ^ 59
def prefixEnd_100831 : Nat := 4983230072969 + 3 ^ 40 * 100831 * 2
def baseEnd_100831 : Nat := 46022015887644650621149

theorem tailTrace_100831 : CollatzResearch.WordTrace tailWord_100831 prefixEnd_100831 46022015887644650621149 := by
  unfold tailWord_100831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677608697713982408910347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2451739131809321605940231 3677608697713982408910347)
  ·
    refine ⟨5516413046570973613365521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677608697713982408910347 5516413046570973613365521)
    ·
      refine ⟨4137309784928230210024141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516413046570973613365521 4137309784928230210024141)
      ·
        refine ⟨1551491169348086328759053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4137309784928230210024141 1551491169348086328759053)
        ·
          refine ⟨581809188505532373284645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1551491169348086328759053 581809188505532373284645)
          ·
            refine ⟨109089222844787319990871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 581809188505532373284645 109089222844787319990871)
            ·
              refine ⟨163633834267180979986307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109089222844787319990871 163633834267180979986307)
              ·
                refine ⟨245450751400771469979461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163633834267180979986307 245450751400771469979461)
                ·
                  refine ⟨46022015887644650621149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245450751400771469979461 46022015887644650621149)
                  ·
                    rfl

theorem cell20_100831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_100831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100831 prefixEnd_100831 := by exact prefixLift 100831
  have htrace : WordTrace (prefixWord ++ tailWord_100831) baseStart_100831 baseEnd_100831 := by
    simpa [prefixWord, tailWord_100831, baseEnd_100831] using wordTrace_append hprefix tailTrace_100831
  have hstable : (prefixWord ++ tailWord_100831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100831).length < 2 ^ (prefixWord ++ tailWord_100831).sum := by decide
  have hdescent : baseEnd_100831 < baseStart_100831 := by decide
  rcases family_descends (prefixWord ++ tailWord_100831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100834 : List Nat := [3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_100834 : Nat := 118140960795 + 100834 * 2 ^ 59
def prefixEnd_100834 : Nat := 4983230072969 + 3 ^ 40 * 100834 * 2
def baseEnd_100834 : Nat := 15341128389796657840379

theorem tailTrace_100834 : CollatzResearch.WordTrace tailWord_100834 prefixEnd_100834 15341128389796657840379 := by
  unfold tailWord_100834
  simp only [CollatzResearch.WordTrace]
  refine ⟨919429529175778480317389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2451812077802075947513037 919429529175778480317389)
  ·
    refine ⟨344786073440916930119021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 919429529175778480317389 344786073440916930119021)
    ·
      refine ⟨129294777540343848794633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344786073440916930119021 129294777540343848794633)
      ·
        refine ⟨96971083155257886595975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129294777540343848794633 96971083155257886595975)
        ·
          refine ⟨145456624732886829893963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96971083155257886595975 145456624732886829893963)
          ·
            refine ⟨218184937099330244840945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145456624732886829893963 218184937099330244840945)
            ·
              refine ⟨163638702824497683630709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218184937099330244840945 163638702824497683630709)
              ·
                refine ⟨15341128389796657840379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163638702824497683630709 15341128389796657840379)
                ·
                  rfl

theorem cell20_100834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_100834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100834 prefixEnd_100834 := by exact prefixLift 100834
  have htrace : WordTrace (prefixWord ++ tailWord_100834) baseStart_100834 baseEnd_100834 := by
    simpa [prefixWord, tailWord_100834, baseEnd_100834] using wordTrace_append hprefix tailTrace_100834
  have hstable : (prefixWord ++ tailWord_100834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100834).length < 2 ^ (prefixWord ++ tailWord_100834).sum := by decide
  have hdescent : baseEnd_100834 < baseStart_100834 := by decide
  rcases family_descends (prefixWord ++ tailWord_100834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100873 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_100873 : Nat := 118140960795 + 100873 * 2 ^ 59
def prefixEnd_100873 : Nat := 4983230072969 + 3 ^ 40 * 100873 * 2
def baseEnd_100873 : Nat := 46041185832079171220977

theorem tailTrace_100873 : CollatzResearch.WordTrace tailWord_100873 prefixEnd_100873 46041185832079171220977 := by
  unfold tailWord_100873
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679140563561823581939273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2452760375707882387959515 3679140563561823581939273)
  ·
    refine ⟨2759355422671367686454455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3679140563561823581939273 2759355422671367686454455)
    ·
      refine ⟨4139033134007051529681683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759355422671367686454455 4139033134007051529681683)
      ·
        refine ⟨6208549701010577294522525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139033134007051529681683 6208549701010577294522525)
        ·
          refine ⟨2328206137878966485445947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6208549701010577294522525 2328206137878966485445947)
          ·
            refine ⟨3492309206818449728168921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328206137878966485445947 3492309206818449728168921)
            ·
              refine ⟨2619231905113837296126691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492309206818449728168921 2619231905113837296126691)
              ·
                refine ⟨3928847857670755944190037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619231905113837296126691 3928847857670755944190037)
                ·
                  refine ⟨46041185832079171220977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3928847857670755944190037 46041185832079171220977)
                  ·
                    rfl

theorem cell20_100873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_100873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100873 prefixEnd_100873 := by exact prefixLift 100873
  have htrace : WordTrace (prefixWord ++ tailWord_100873) baseStart_100873 baseEnd_100873 := by
    simpa [prefixWord, tailWord_100873, baseEnd_100873] using wordTrace_append hprefix tailTrace_100873
  have hstable : (prefixWord ++ tailWord_100873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100873).length < 2 ^ (prefixWord ++ tailWord_100873).sum := by decide
  have hdescent : baseEnd_100873 < baseStart_100873 := by decide
  rcases family_descends (prefixWord ++ tailWord_100873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100883 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_100883 : Nat := 118140960795 + 100883 * 2 ^ 59
def prefixEnd_100883 : Nat := 4983230072969 + 3 ^ 40 * 100883 * 2
def baseEnd_100883 : Nat := 46045750104563580887603

theorem tailTrace_100883 : CollatzResearch.WordTrace tailWord_100883 prefixEnd_100883 46045750104563580887603 := by
  unfold tailWord_100883
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679505293525595289803303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2453003529017063526535535 3679505293525595289803303)
  ·
    refine ⟨5519257940288392934704955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679505293525595289803303 5519257940288392934704955)
    ·
      refine ⟨8278886910432589402057433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5519257940288392934704955 8278886910432589402057433)
      ·
        refine ⟨6209165182824442051543075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8278886910432589402057433 6209165182824442051543075)
        ·
          refine ⟨9313747774236663077314613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209165182824442051543075 9313747774236663077314613)
          ·
            refine ⟨873163853834687163498245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9313747774236663077314613 873163853834687163498245)
            ·
              refine ⟨163718222594003843155921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 873163853834687163498245 163718222594003843155921)
              ·
                refine ⟨122788666945502882366941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163718222594003843155921 122788666945502882366941)
                ·
                  refine ⟨46045750104563580887603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122788666945502882366941 46045750104563580887603)
                  ·
                    rfl

theorem cell20_100883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_100883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100883 prefixEnd_100883 := by exact prefixLift 100883
  have htrace : WordTrace (prefixWord ++ tailWord_100883) baseStart_100883 baseEnd_100883 := by
    simpa [prefixWord, tailWord_100883, baseEnd_100883] using wordTrace_append hprefix tailTrace_100883
  have hstable : (prefixWord ++ tailWord_100883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100883).length < 2 ^ (prefixWord ++ tailWord_100883).sum := by decide
  have hdescent : baseEnd_100883 < baseStart_100883 := by decide
  rcases family_descends (prefixWord ++ tailWord_100883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100924 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_100924 : Nat := 118140960795 + 100924 * 2 ^ 59
def prefixEnd_100924 : Nat := 4983230072969 + 3 ^ 40 * 100924 * 2
def baseEnd_100924 : Nat := 46064463621749660520769

theorem tailTrace_100924 : CollatzResearch.WordTrace tailWord_100924 prefixEnd_100924 46064463621749660520769 := by
  unfold tailWord_100924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840500343188529646022913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2454000457584706194697217 1840500343188529646022913)
  ·
    refine ⟨1380375257391397234517185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1840500343188529646022913 1380375257391397234517185)
    ·
      refine ⟨1035281443043547925887889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380375257391397234517185 1035281443043547925887889)
      ·
        refine ⟨776461082282660944415917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035281443043547925887889 776461082282660944415917)
        ·
          refine ⟨291172905855997854155969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776461082282660944415917 291172905855997854155969)
          ·
            refine ⟨218379679391998390616977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291172905855997854155969 218379679391998390616977)
            ·
              refine ⟨163784759543998792962733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218379679391998390616977 163784759543998792962733)
              ·
                refine ⟨61419284828999547361025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163784759543998792962733 61419284828999547361025)
                ·
                  refine ⟨46064463621749660520769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61419284828999547361025 46064463621749660520769)
                  ·
                    rfl

theorem cell20_100924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_100924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100924 prefixEnd_100924 := by exact prefixLift 100924
  have htrace : WordTrace (prefixWord ++ tailWord_100924) baseStart_100924 baseEnd_100924 := by
    simpa [prefixWord, tailWord_100924, baseEnd_100924] using wordTrace_append hprefix tailTrace_100924
  have hstable : (prefixWord ++ tailWord_100924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100924).length < 2 ^ (prefixWord ++ tailWord_100924).sum := by decide
  have hdescent : baseEnd_100924 < baseStart_100924 := by decide
  rcases family_descends (prefixWord ++ tailWord_100924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100934 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_100934 : Nat := 118140960795 + 100934 * 2 ^ 59
def prefixEnd_100934 : Nat := 4983230072969 + 3 ^ 40 * 100934 * 2
def baseEnd_100934 : Nat := 46069027894234070187395

theorem tailTrace_100934 : CollatzResearch.WordTrace tailWord_100934 prefixEnd_100934 46069027894234070187395 := by
  unfold tailWord_100934
  simp only [CollatzResearch.WordTrace]
  refine ⟨115042669260650968747183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2454243610893887333273237 115042669260650968747183)
  ·
    refine ⟨172564003890976453120775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115042669260650968747183 172564003890976453120775)
    ·
      refine ⟨258846005836464679681163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172564003890976453120775 258846005836464679681163)
      ·
        refine ⟨388269008754697019521745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258846005836464679681163 388269008754697019521745)
        ·
          refine ⟨291201756566022764641309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388269008754697019521745 291201756566022764641309)
          ·
            refine ⟨109200658712258536740491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291201756566022764641309 109200658712258536740491)
            ·
              refine ⟨163800988068387805110737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109200658712258536740491 163800988068387805110737)
              ·
                refine ⟨122850741051290853833053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163800988068387805110737 122850741051290853833053)
                ·
                  refine ⟨46069027894234070187395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122850741051290853833053 46069027894234070187395)
                  ·
                    rfl

theorem cell20_100934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_100934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100934 prefixEnd_100934 := by exact prefixLift 100934
  have htrace : WordTrace (prefixWord ++ tailWord_100934) baseStart_100934 baseEnd_100934 := by
    simpa [prefixWord, tailWord_100934, baseEnd_100934] using wordTrace_append hprefix tailTrace_100934
  have hstable : (prefixWord ++ tailWord_100934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100934).length < 2 ^ (prefixWord ++ tailWord_100934).sum := by decide
  have hdescent : baseEnd_100934 < baseStart_100934 := by decide
  rcases family_descends (prefixWord ++ tailWord_100934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100935 : List Nat := [1, 1, 4, 1, 4, 2, 7]
def baseStart_100935 : Nat := 118140960795 + 100935 * 2 ^ 59
def prefixEnd_100935 : Nat := 4983230072969 + 3 ^ 40 * 100935 * 2
def baseEnd_100935 : Nat := 5118831591275834572673

theorem tailTrace_100935 : CollatzResearch.WordTrace tailWord_100935 prefixEnd_100935 5118831591275834572673 := by
  unfold tailWord_100935
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681401889337208170696259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2454267926224805447130839 3681401889337208170696259)
  ·
    refine ⟨5522102834005812256044389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3681401889337208170696259 5522102834005812256044389)
    ·
      refine ⟨1035394281376089798008323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5522102834005812256044389 1035394281376089798008323)
      ·
        refine ⟨1553091422064134697012485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035394281376089798008323 1553091422064134697012485)
        ·
          refine ⟨291204641637025255689841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1553091422064134697012485 291204641637025255689841)
          ·
            refine ⟨218403481227768941767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291204641637025255689841 218403481227768941767381)
            ·
              refine ⟨5118831591275834572673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 218403481227768941767381 5118831591275834572673)
              ·
                rfl

theorem cell20_100935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_100935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100935 prefixEnd_100935 := by exact prefixLift 100935
  have htrace : WordTrace (prefixWord ++ tailWord_100935) baseStart_100935 baseEnd_100935 := by
    simpa [prefixWord, tailWord_100935, baseEnd_100935] using wordTrace_append hprefix tailTrace_100935
  have hstable : (prefixWord ++ tailWord_100935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100935).length < 2 ^ (prefixWord ++ tailWord_100935).sum := by decide
  have hdescent : baseEnd_100935 < baseStart_100935 := by decide
  rcases family_descends (prefixWord ++ tailWord_100935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100938 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_100938 : Nat := 118140960795 + 100938 * 2 ^ 59
def prefixEnd_100938 : Nat := 4983230072969 + 3 ^ 40 * 100938 * 2
def baseEnd_100938 : Nat := 46070853603227834054045

theorem tailTrace_100938 : CollatzResearch.WordTrace tailWord_100938 prefixEnd_100938 46070853603227834054045 := by
  unfold tailWord_100938
  simp only [CollatzResearch.WordTrace]
  refine ⟨920377827081584920763867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2454340872217559788703645 920377827081584920763867)
  ·
    refine ⟨1380566740622377381145801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920377827081584920763867 1380566740622377381145801)
    ·
      refine ⟨1035425055466783035859351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380566740622377381145801 1035425055466783035859351)
      ·
        refine ⟨1553137583200174553789027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035425055466783035859351 1553137583200174553789027)
        ·
          refine ⟨2329706374800261830683541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553137583200174553789027 2329706374800261830683541)
          ·
            refine ⟨109204986318762273313291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2329706374800261830683541 109204986318762273313291)
            ·
              refine ⟨163807479478143409969937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109204986318762273313291 163807479478143409969937)
              ·
                refine ⟨122855609608607557477453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163807479478143409969937 122855609608607557477453)
                ·
                  refine ⟨46070853603227834054045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122855609608607557477453 46070853603227834054045)
                  ·
                    rfl

theorem cell20_100938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_100938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100938 prefixEnd_100938 := by exact prefixLift 100938
  have htrace : WordTrace (prefixWord ++ tailWord_100938) baseStart_100938 baseEnd_100938 := by
    simpa [prefixWord, tailWord_100938, baseEnd_100938] using wordTrace_append hprefix tailTrace_100938
  have hstable : (prefixWord ++ tailWord_100938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100938).length < 2 ^ (prefixWord ++ tailWord_100938).sum := by decide
  have hdescent : baseEnd_100938 < baseStart_100938 := by decide
  rcases family_descends (prefixWord ++ tailWord_100938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100945 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 2]
def baseStart_100945 : Nat := 118140960795 + 100945 * 2 ^ 59
def prefixEnd_100945 : Nat := 4983230072969 + 3 ^ 40 * 100945 * 2
def baseEnd_100945 : Nat := 46074048593966920820683

theorem tailTrace_100945 : CollatzResearch.WordTrace tailWord_100945 prefixEnd_100945 46074048593966920820683 := by
  unfold tailWord_100945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681766619300979878560289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2454511079533986585706859 3681766619300979878560289)
  ·
    refine ⟨2761324964475734908920217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3681766619300979878560289 2761324964475734908920217)
    ·
      refine ⟨2070993723356801181690163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2761324964475734908920217 2070993723356801181690163)
      ·
        refine ⟨3106490585035201772535245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070993723356801181690163 3106490585035201772535245)
        ·
          refine ⟨1164933969388200664700717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3106490585035201772535245 1164933969388200664700717)
          ·
            refine ⟨436850238520575249262769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164933969388200664700717 436850238520575249262769)
            ·
              refine ⟨327637678890431436947077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436850238520575249262769 327637678890431436947077)
              ·
                refine ⟨61432064791955894427577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327637678890431436947077 61432064791955894427577)
                ·
                  refine ⟨46074048593966920820683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61432064791955894427577 46074048593966920820683)
                  ·
                    rfl

theorem cell20_100945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_100945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100945 prefixEnd_100945 := by exact prefixLift 100945
  have htrace : WordTrace (prefixWord ++ tailWord_100945) baseStart_100945 baseEnd_100945 := by
    simpa [prefixWord, tailWord_100945, baseEnd_100945] using wordTrace_append hprefix tailTrace_100945
  have hstable : (prefixWord ++ tailWord_100945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100945).length < 2 ^ (prefixWord ++ tailWord_100945).sum := by decide
  have hdescent : baseEnd_100945 < baseStart_100945 := by decide
  rcases family_descends (prefixWord ++ tailWord_100945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100983 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 2]
def baseStart_100983 : Nat := 118140960795 + 100983 * 2 ^ 59
def prefixEnd_100983 : Nat := 4983230072969 + 3 ^ 40 * 100983 * 2
def baseEnd_100983 : Nat := 46091392829407677553861

theorem tailTrace_100983 : CollatzResearch.WordTrace tailWord_100983 prefixEnd_100983 46091392829407677553861 := by
  unfold tailWord_100983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683152593163312368443603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2455435062108874912295735 3683152593163312368443603)
  ·
    refine ⟨5524728889744968552665405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3683152593163312368443603 5524728889744968552665405)
    ·
      refine ⟨2071773333654363207249527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5524728889744968552665405 2071773333654363207249527)
      ·
        refine ⟨3107660000481544810874291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071773333654363207249527 3107660000481544810874291)
        ·
          refine ⟨4661490000722317216311437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107660000481544810874291 4661490000722317216311437)
          ·
            refine ⟨1748058750270868956116789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4661490000722317216311437 1748058750270868956116789)
            ·
              refine ⟨163880507837893964635949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1748058750270868956116789 163880507837893964635949)
              ·
                refine ⟨61455190439210236738481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163880507837893964635949 61455190439210236738481)
                ·
                  refine ⟨46091392829407677553861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61455190439210236738481 46091392829407677553861)
                  ·
                    rfl

theorem cell20_100983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2].length) (baseStart_100983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_100983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_100983 prefixEnd_100983 := by exact prefixLift 100983
  have htrace : WordTrace (prefixWord ++ tailWord_100983) baseStart_100983 baseEnd_100983 := by
    simpa [prefixWord, tailWord_100983, baseEnd_100983] using wordTrace_append hprefix tailTrace_100983
  have hstable : (prefixWord ++ tailWord_100983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100983).length < 2 ^ (prefixWord ++ tailWord_100983).sum := by decide
  have hdescent : baseEnd_100983 < baseStart_100983 := by decide
  rcases family_descends (prefixWord ++ tailWord_100983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101066 : List Nat := [3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_101066 : Nat := 118140960795 + 101066 * 2 ^ 59
def prefixEnd_101066 : Nat := 4983230072969 + 3 ^ 40 * 101066 * 2
def baseEnd_101066 : Nat := 15376425430342759262285

theorem tailTrace_101066 : CollatzResearch.WordTrace tailWord_101066 prefixEnd_101066 15376425430342759262285 := by
  unfold tailWord_101066
  simp only [CollatzResearch.WordTrace]
  refine ⟨921544962965654385928763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2457453234575078362476701 921544962965654385928763)
  ·
    refine ⟨1382317444448481578893145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921544962965654385928763 1382317444448481578893145)
    ·
      refine ⟨1036738083336361184169859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382317444448481578893145 1036738083336361184169859)
      ·
        refine ⟨1555107125004541776254789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036738083336361184169859 1555107125004541776254789)
        ·
          refine ⟨291582585938351583047773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1555107125004541776254789 291582585938351583047773)
          ·
            refine ⟨109343469726881843642915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291582585938351583047773 109343469726881843642915)
            ·
              refine ⟨164015204590322765464373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109343469726881843642915 164015204590322765464373)
              ·
                refine ⟨15376425430342759262285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164015204590322765464373 15376425430342759262285)
                ·
                  rfl

theorem cell20_101066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_101066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101066 prefixEnd_101066 := by exact prefixLift 101066
  have htrace : WordTrace (prefixWord ++ tailWord_101066) baseStart_101066 baseEnd_101066 := by
    simpa [prefixWord, tailWord_101066, baseEnd_101066] using wordTrace_append hprefix tailTrace_101066
  have hstable : (prefixWord ++ tailWord_101066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101066).length < 2 ^ (prefixWord ++ tailWord_101066).sum := by decide
  have hdescent : baseEnd_101066 < baseStart_101066 := by decide
  rcases family_descends (prefixWord ++ tailWord_101066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101080 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_101080 : Nat := 118140960795 + 101080 * 2 ^ 59
def prefixEnd_101080 : Nat := 4983230072969 + 3 ^ 40 * 101080 * 2
def baseEnd_101080 : Nat := 46135666272506451320131

theorem tailTrace_101080 : CollatzResearch.WordTrace tailWord_101080 prefixEnd_101080 46135666272506451320131 := by
  unfold tailWord_101080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843345236905948967362347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2457793649207931956483129 1843345236905948967362347)
  ·
    refine ⟨2765017855358923451043521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843345236905948967362347 2765017855358923451043521)
    ·
      refine ⟨2073763391519192588282641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765017855358923451043521 2073763391519192588282641)
      ·
        refine ⟨1555322543639394441211981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2073763391519192588282641 1555322543639394441211981)
        ·
          refine ⟨583245953864772915454493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1555322543639394441211981 583245953864772915454493)
          ·
            refine ⟨218717232699289843295435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583245953864772915454493 218717232699289843295435)
            ·
              refine ⟨328075849048934764943153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218717232699289843295435 328075849048934764943153)
              ·
                refine ⟨246056886786701073707365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328075849048934764943153 246056886786701073707365)
                ·
                  refine ⟨46135666272506451320131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246056886786701073707365 46135666272506451320131)
                  ·
                    rfl

theorem cell20_101080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_101080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101080 prefixEnd_101080 := by exact prefixLift 101080
  have htrace : WordTrace (prefixWord ++ tailWord_101080) baseStart_101080 baseEnd_101080 := by
    simpa [prefixWord, tailWord_101080, baseEnd_101080] using wordTrace_append hprefix tailTrace_101080
  have hstable : (prefixWord ++ tailWord_101080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101080).length < 2 ^ (prefixWord ++ tailWord_101080).sum := by decide
  have hdescent : baseEnd_101080 < baseStart_101080 := by decide
  rcases family_descends (prefixWord ++ tailWord_101080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101128 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_101128 : Nat := 118140960795 + 101128 * 2 ^ 59
def prefixEnd_101128 : Nat := 4983230072969 + 3 ^ 40 * 101128 * 2
def baseEnd_101128 : Nat := 46157574780431617719935

theorem tailTrace_101128 : CollatzResearch.WordTrace tailWord_101128 prefixEnd_101128 46157574780431617719935 := by
  unfold tailWord_101128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844220588819001066236019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2458960785092001421648025 1844220588819001066236019)
  ·
    refine ⟨2766330883228501599354029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844220588819001066236019 2766330883228501599354029)
    ·
      refine ⟨1037374081210688099757761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2766330883228501599354029 1037374081210688099757761)
      ·
        refine ⟨778030560908016074818321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1037374081210688099757761 778030560908016074818321)
        ·
          refine ⟨583522920681012056113741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778030560908016074818321 583522920681012056113741)
          ·
            refine ⟨218821095255379521042653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583522920681012056113741 218821095255379521042653)
            ·
              refine ⟨82057910720767320390995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218821095255379521042653 82057910720767320390995)
              ·
                refine ⟨123086866081150980586493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82057910720767320390995 123086866081150980586493)
                ·
                  refine ⟨46157574780431617719935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123086866081150980586493 46157574780431617719935)
                  ·
                    rfl

theorem cell20_101128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_101128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101128 prefixEnd_101128 := by exact prefixLift 101128
  have htrace : WordTrace (prefixWord ++ tailWord_101128) baseStart_101128 baseEnd_101128 := by
    simpa [prefixWord, tailWord_101128, baseEnd_101128] using wordTrace_append hprefix tailTrace_101128
  have hstable : (prefixWord ++ tailWord_101128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101128).length < 2 ^ (prefixWord ++ tailWord_101128).sum := by decide
  have hdescent : baseEnd_101128 < baseStart_101128 := by decide
  rcases family_descends (prefixWord ++ tailWord_101128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101138 : List Nat := [3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_101138 : Nat := 118140960795 + 101138 * 2 ^ 59
def prefixEnd_101138 : Nat := 4983230072969 + 3 ^ 40 * 101138 * 2
def baseEnd_101138 : Nat := 15387379684305342462187

theorem tailTrace_101138 : CollatzResearch.WordTrace tailWord_101138 prefixEnd_101138 15387379684305342462187 := by
  unfold tailWord_101138
  simp only [CollatzResearch.WordTrace]
  refine ⟨922201476900443460084017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2459203938401182560224045 922201476900443460084017)
  ·
    refine ⟨691651107675332595063013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 922201476900443460084017 691651107675332595063013)
    ·
      refine ⟨129684582689124861574315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 691651107675332595063013 129684582689124861574315)
      ·
        refine ⟨194526874033687292361473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129684582689124861574315 194526874033687292361473)
        ·
          refine ⟨145895155525265469271105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194526874033687292361473 145895155525265469271105)
          ·
            refine ⟨109421366643949101953329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145895155525265469271105 109421366643949101953329)
            ·
              refine ⟨82066024982961826464997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109421366643949101953329 82066024982961826464997)
              ·
                refine ⟨15387379684305342462187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82066024982961826464997 15387379684305342462187)
                ·
                  rfl

theorem cell20_101138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_101138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101138 prefixEnd_101138 := by exact prefixLift 101138
  have htrace : WordTrace (prefixWord ++ tailWord_101138) baseStart_101138 baseEnd_101138 := by
    simpa [prefixWord, tailWord_101138, baseEnd_101138] using wordTrace_append hprefix tailTrace_101138
  have hstable : (prefixWord ++ tailWord_101138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101138).length < 2 ^ (prefixWord ++ tailWord_101138).sum := by decide
  have hdescent : baseEnd_101138 < baseStart_101138 := by decide
  rcases family_descends (prefixWord ++ tailWord_101138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101139 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_101139 : Nat := 118140960795 + 101139 * 2 ^ 59
def prefixEnd_101139 : Nat := 4983230072969 + 3 ^ 40 * 101139 * 2
def baseEnd_101139 : Nat := 46162595480164468353223

theorem tailTrace_101139 : CollatzResearch.WordTrace tailWord_101139 prefixEnd_101139 46162595480164468353223 := by
  unfold tailWord_101139
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688842380598151011122471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2459228253732100674081647 3688842380598151011122471)
  ·
    refine ⟨5533263570897226516683707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688842380598151011122471 5533263570897226516683707)
    ·
      refine ⟨8299895356345839775025561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533263570897226516683707 8299895356345839775025561)
      ·
        refine ⟨6224921517259379831269171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8299895356345839775025561 6224921517259379831269171)
        ·
          refine ⟨9337382275889069746903757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224921517259379831269171 9337382275889069746903757)
          ·
            refine ⟨3501518353458401155088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9337382275889069746903757 3501518353458401155088909)
            ·
              refine ⟨1313069382546900433158341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3501518353458401155088909 1313069382546900433158341)
              ·
                refine ⟨246200509227543831217189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1313069382546900433158341 246200509227543831217189)
                ·
                  refine ⟨46162595480164468353223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246200509227543831217189 46162595480164468353223)
                  ·
                    rfl

theorem cell20_101139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_101139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101139 prefixEnd_101139 := by exact prefixLift 101139
  have htrace : WordTrace (prefixWord ++ tailWord_101139) baseStart_101139 baseEnd_101139 := by
    simpa [prefixWord, tailWord_101139, baseEnd_101139] using wordTrace_append hprefix tailTrace_101139
  have hstable : (prefixWord ++ tailWord_101139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101139).length < 2 ^ (prefixWord ++ tailWord_101139).sum := by decide
  have hdescent : baseEnd_101139 < baseStart_101139 := by decide
  rcases family_descends (prefixWord ++ tailWord_101139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101152 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_101152 : Nat := 118140960795 + 101152 * 2 ^ 59
def prefixEnd_101152 : Nat := 4983230072969 + 3 ^ 40 * 101152 * 2
def baseEnd_101152 : Nat := 46168529034394200919837

theorem tailTrace_101152 : CollatzResearch.WordTrace tailWord_101152 prefixEnd_101152 46168529034394200919837 := by
  unfold tailWord_101152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844658264775527115672855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2459544353034036154230473 1844658264775527115672855)
  ·
    refine ⟨2766987397163290673509283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844658264775527115672855 2766987397163290673509283)
    ·
      refine ⟨4150481095744936010263925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766987397163290673509283 4150481095744936010263925)
      ·
        refine ⟨389107602726087750962243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4150481095744936010263925 389107602726087750962243)
        ·
          refine ⟨583661404089131626443365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389107602726087750962243 583661404089131626443365)
          ·
            refine ⟨109436513266712179958131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583661404089131626443365 109436513266712179958131)
            ·
              refine ⟨164154769900068269937197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109436513266712179958131 164154769900068269937197)
              ·
                refine ⟨61558038712525601226449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164154769900068269937197 61558038712525601226449)
                ·
                  refine ⟨46168529034394200919837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61558038712525601226449 46168529034394200919837)
                  ·
                    rfl

theorem cell20_101152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_101152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101152 prefixEnd_101152 := by exact prefixLift 101152
  have htrace : WordTrace (prefixWord ++ tailWord_101152) baseStart_101152 baseEnd_101152 := by
    simpa [prefixWord, tailWord_101152, baseEnd_101152] using wordTrace_append hprefix tailTrace_101152
  have hstable : (prefixWord ++ tailWord_101152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101152).length < 2 ^ (prefixWord ++ tailWord_101152).sum := by decide
  have hdescent : baseEnd_101152 < baseStart_101152 := by decide
  rcases family_descends (prefixWord ++ tailWord_101152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101170 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_101170 : Nat := 118140960795 + 101170 * 2 ^ 59
def prefixEnd_101170 : Nat := 4983230072969 + 3 ^ 40 * 101170 * 2
def baseEnd_101170 : Nat := 46176744724866138319763

theorem tailTrace_101170 : CollatzResearch.WordTrace tailWord_101170 prefixEnd_101170 46176744724866138319763 := by
  unfold tailWord_101170
  simp only [CollatzResearch.WordTrace]
  refine ⟨922493260871460826375241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2459982028990562203667309 922493260871460826375241)
  ·
    refine ⟨691869945653595619781431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 922493260871460826375241 691869945653595619781431)
    ·
      refine ⟨1037804918480393429672147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691869945653595619781431 1037804918480393429672147)
      ·
        refine ⟨1556707377720590144508221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037804918480393429672147 1556707377720590144508221)
        ·
          refine ⟨583765266645221304190583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1556707377720590144508221 583765266645221304190583)
          ·
            refine ⟨875647899967831956285875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583765266645221304190583 875647899967831956285875)
            ·
              refine ⟨1313471849951747934428813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875647899967831956285875 1313471849951747934428813)
              ·
                refine ⟨492551943731905475410805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313471849951747934428813 492551943731905475410805)
                ·
                  refine ⟨46176744724866138319763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492551943731905475410805 46176744724866138319763)
                  ·
                    rfl

theorem cell20_101170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_101170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101170 prefixEnd_101170 := by exact prefixLift 101170
  have htrace : WordTrace (prefixWord ++ tailWord_101170) baseStart_101170 baseEnd_101170 := by
    simpa [prefixWord, tailWord_101170, baseEnd_101170] using wordTrace_append hprefix tailTrace_101170
  have hstable : (prefixWord ++ tailWord_101170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101170).length < 2 ^ (prefixWord ++ tailWord_101170).sum := by decide
  have hdescent : baseEnd_101170 < baseStart_101170 := by decide
  rcases family_descends (prefixWord ++ tailWord_101170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101173 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_101173 : Nat := 118140960795 + 101173 * 2 ^ 59
def prefixEnd_101173 : Nat := 4983230072969 + 3 ^ 40 * 101173 * 2
def baseEnd_101173 : Nat := 46178114006611461219751

theorem tailTrace_101173 : CollatzResearch.WordTrace tailWord_101173 prefixEnd_101173 46178114006611461219751 := by
  unfold tailWord_101173
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690082462474974817860173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2460054974983316545240115 3690082462474974817860173)
  ·
    refine ⟨1383780923428115556697565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3690082462474974817860173 1383780923428115556697565)
    ·
      refine ⟨518917846285543333761587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1383780923428115556697565 518917846285543333761587)
      ·
        refine ⟨778376769428315000642381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518917846285543333761587 778376769428315000642381)
        ·
          refine ⟨291891288535618125240893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 778376769428315000642381 291891288535618125240893)
          ·
            refine ⟨109459233200856796965335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291891288535618125240893 109459233200856796965335)
            ·
              refine ⟨164188849801285195448003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109459233200856796965335 164188849801285195448003)
              ·
                refine ⟨246283274701927793172005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164188849801285195448003 246283274701927793172005)
                ·
                  refine ⟨46178114006611461219751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246283274701927793172005 46178114006611461219751)
                  ·
                    rfl

theorem cell20_101173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_101173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101173 prefixEnd_101173 := by exact prefixLift 101173
  have htrace : WordTrace (prefixWord ++ tailWord_101173) baseStart_101173 baseEnd_101173 := by
    simpa [prefixWord, tailWord_101173, baseEnd_101173] using wordTrace_append hprefix tailTrace_101173
  have hstable : (prefixWord ++ tailWord_101173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101173).length < 2 ^ (prefixWord ++ tailWord_101173).sum := by decide
  have hdescent : baseEnd_101173 < baseStart_101173 := by decide
  rcases family_descends (prefixWord ++ tailWord_101173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101218 : List Nat := [3, 3, 2, 1, 4, 7]
def baseStart_101218 : Nat := 118140960795 + 101218 * 2 ^ 59
def prefixEnd_101218 : Nat := 4983230072969 + 3 ^ 40 * 101218 * 2
def baseEnd_101218 : Nat := 1711061230844122397021

theorem tailTrace_101218 : CollatzResearch.WordTrace tailWord_101218 prefixEnd_101218 1711061230844122397021 := by
  unfold tailWord_101218
  simp only [CollatzResearch.WordTrace]
  refine ⟨922930936827986875812077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2461149164874631668832205 922930936827986875812077)
  ·
    refine ⟨346099101310495078429529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 922930936827986875812077 346099101310495078429529)
    ·
      refine ⟨259574325982871308822147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346099101310495078429529 259574325982871308822147)
      ·
        refine ⟨389361488974306963233221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259574325982871308822147 389361488974306963233221)
        ·
          refine ⟨73005279182682555606229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389361488974306963233221 73005279182682555606229)
          ·
            refine ⟨1711061230844122397021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73005279182682555606229 1711061230844122397021)
            ·
              rfl

theorem cell20_101218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 7].length) (baseStart_101218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101218 prefixEnd_101218 := by exact prefixLift 101218
  have htrace : WordTrace (prefixWord ++ tailWord_101218) baseStart_101218 baseEnd_101218 := by
    simpa [prefixWord, tailWord_101218, baseEnd_101218] using wordTrace_append hprefix tailTrace_101218
  have hstable : (prefixWord ++ tailWord_101218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101218).length < 2 ^ (prefixWord ++ tailWord_101218).sum := by decide
  have hdescent : baseEnd_101218 < baseStart_101218 := by decide
  rcases family_descends (prefixWord ++ tailWord_101218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101253 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_101253 : Nat := 118140960795 + 101253 * 2 ^ 59
def prefixEnd_101253 : Nat := 4983230072969 + 3 ^ 40 * 101253 * 2
def baseEnd_101253 : Nat := 46214628186486738552757

theorem tailTrace_101253 : CollatzResearch.WordTrace tailWord_101253 prefixEnd_101253 46214628186486738552757 := by
  unfold tailWord_101253
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693000302185148480772413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2462000201456765653848275 3693000302185148480772413)
  ·
    refine ⟨1384875113319430680289655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3693000302185148480772413 1384875113319430680289655)
    ·
      refine ⟨2077312669979146020434483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384875113319430680289655 2077312669979146020434483)
      ·
        refine ⟨3115969004968719030651725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077312669979146020434483 3115969004968719030651725)
        ·
          refine ⟨1168488376863269636494397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3115969004968719030651725 1168488376863269636494397)
          ·
            refine ⟨438183141323726113685399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1168488376863269636494397 438183141323726113685399)
            ·
              refine ⟨657274711985589170528099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438183141323726113685399 657274711985589170528099)
              ·
                refine ⟨985912067978383755792149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657274711985589170528099 985912067978383755792149)
                ·
                  refine ⟨46214628186486738552757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 985912067978383755792149 46214628186486738552757)
                  ·
                    rfl

theorem cell20_101253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_101253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101253 prefixEnd_101253 := by exact prefixLift 101253
  have htrace : WordTrace (prefixWord ++ tailWord_101253) baseStart_101253 baseEnd_101253 := by
    simpa [prefixWord, tailWord_101253, baseEnd_101253] using wordTrace_append hprefix tailTrace_101253
  have hstable : (prefixWord ++ tailWord_101253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101253).length < 2 ^ (prefixWord ++ tailWord_101253).sum := by decide
  have hdescent : baseEnd_101253 < baseStart_101253 := by decide
  rcases family_descends (prefixWord ++ tailWord_101253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101256 : List Nat := [2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_101256 : Nat := 118140960795 + 101256 * 2 ^ 59
def prefixEnd_101256 : Nat := 4983230072969 + 3 ^ 40 * 101256 * 2
def baseEnd_101256 : Nat := 15405332489410687150915

theorem tailTrace_101256 : CollatzResearch.WordTrace tailWord_101256 prefixEnd_101256 15405332489410687150915 := by
  unfold tailWord_101256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846554860587139996565811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2462073147449519995421081 1846554860587139996565811)
  ·
    refine ⟨2769832290880709994848717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846554860587139996565811 2769832290880709994848717)
    ·
      refine ⟨1038687109080266248068269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2769832290880709994848717 1038687109080266248068269)
      ·
        refine ⟨389507665905099843025601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1038687109080266248068269 389507665905099843025601)
        ·
          refine ⟨292130749428824882269201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389507665905099843025601 292130749428824882269201)
          ·
            refine ⟨219098062071618661701901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292130749428824882269201 219098062071618661701901)
            ·
              refine ⟨82161773276856998138213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219098062071618661701901 82161773276856998138213)
              ·
                refine ⟨15405332489410687150915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82161773276856998138213 15405332489410687150915)
                ·
                  rfl

theorem cell20_101256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_101256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101256 prefixEnd_101256 := by exact prefixLift 101256
  have htrace : WordTrace (prefixWord ++ tailWord_101256) baseStart_101256 baseEnd_101256 := by
    simpa [prefixWord, tailWord_101256, baseEnd_101256] using wordTrace_append hprefix tailTrace_101256
  have hstable : (prefixWord ++ tailWord_101256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101256).length < 2 ^ (prefixWord ++ tailWord_101256).sum := by decide
  have hdescent : baseEnd_101256 < baseStart_101256 := by decide
  rcases family_descends (prefixWord ++ tailWord_101256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101260 : List Nat := [2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_101260 : Nat := 118140960795 + 101260 * 2 ^ 59
def prefixEnd_101260 : Nat := 4983230072969 + 3 ^ 40 * 101260 * 2
def baseEnd_101260 : Nat := 15405941059075275106465

theorem tailTrace_101260 : CollatzResearch.WordTrace tailWord_101260 prefixEnd_101260 15405941059075275106465 := by
  unfold tailWord_101260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846627806579894338138617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2462170408773192450851489 1846627806579894338138617)
  ·
    refine ⟨1384970854934920753603963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1846627806579894338138617 1384970854934920753603963)
    ·
      refine ⟨2077456282402381130405945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384970854934920753603963 2077456282402381130405945)
      ·
        refine ⟨1558092211801785847804459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2077456282402381130405945 1558092211801785847804459)
        ·
          refine ⟨2337138317702678771706689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558092211801785847804459 2337138317702678771706689)
          ·
            refine ⟨1752853738277009078780017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337138317702678771706689 1752853738277009078780017)
            ·
              refine ⟨1314640303707756809085013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752853738277009078780017 1314640303707756809085013)
              ·
                refine ⟨15405941059075275106465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1314640303707756809085013 15405941059075275106465)
                ·
                  rfl

theorem cell20_101260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_101260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101260 prefixEnd_101260 := by exact prefixLift 101260
  have htrace : WordTrace (prefixWord ++ tailWord_101260) baseStart_101260 baseEnd_101260 := by
    simpa [prefixWord, tailWord_101260, baseEnd_101260] using wordTrace_append hprefix tailTrace_101260
  have hstable : (prefixWord ++ tailWord_101260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101260).length < 2 ^ (prefixWord ++ tailWord_101260).sum := by decide
  have hdescent : baseEnd_101260 < baseStart_101260 := by decide
  rcases family_descends (prefixWord ++ tailWord_101260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101284 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_101284 : Nat := 118140960795 + 101284 * 2 ^ 59
def prefixEnd_101284 : Nat := 4983230072969 + 3 ^ 40 * 101284 * 2
def baseEnd_101284 : Nat := 46228777431188408519297

theorem tailTrace_101284 : CollatzResearch.WordTrace tailWord_101284 prefixEnd_101284 46228777431188408519297 := by
  unfold tailWord_101284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847065482536420387575453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2462753976715227183433937 1847065482536420387575453)
  ·
    refine ⟨692649555951157645340795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1847065482536420387575453 692649555951157645340795)
    ·
      refine ⟨1038974333926736468011193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692649555951157645340795 1038974333926736468011193)
      ·
        refine ⟨779230750445052351008395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038974333926736468011193 779230750445052351008395)
        ·
          refine ⟨1168846125667578526512593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779230750445052351008395 1168846125667578526512593)
          ·
            refine ⟨876634594250683894884445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168846125667578526512593 876634594250683894884445)
            ·
              refine ⟨328737972844006460581667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876634594250683894884445 328737972844006460581667)
              ·
                refine ⟨493106959266009690872501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328737972844006460581667 493106959266009690872501)
                ·
                  refine ⟨46228777431188408519297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493106959266009690872501 46228777431188408519297)
                  ·
                    rfl

theorem cell20_101284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_101284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101284 prefixEnd_101284 := by exact prefixLift 101284
  have htrace : WordTrace (prefixWord ++ tailWord_101284) baseStart_101284 baseEnd_101284 := by
    simpa [prefixWord, tailWord_101284, baseEnd_101284] using wordTrace_append hprefix tailTrace_101284
  have hstable : (prefixWord ++ tailWord_101284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101284).length < 2 ^ (prefixWord ++ tailWord_101284).sum := by decide
  have hdescent : baseEnd_101284 < baseStart_101284 := by decide
  rcases family_descends (prefixWord ++ tailWord_101284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101287 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_101287 : Nat := 118140960795 + 101287 * 2 ^ 59
def prefixEnd_101287 : Nat := 4983230072969 + 3 ^ 40 * 101287 * 2
def baseEnd_101287 : Nat := 46230146712933731419285

theorem tailTrace_101287 : CollatzResearch.WordTrace tailWord_101287 prefixEnd_101287 46230146712933731419285 := by
  unfold tailWord_101287
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694240384061972287510115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2462826922707981525006743 3694240384061972287510115)
  ·
    refine ⟨5541360576092958431265173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3694240384061972287510115 5541360576092958431265173)
    ·
      refine ⟨259751277004357426465555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5541360576092958431265173 259751277004357426465555)
      ·
        refine ⟨389626915506536139698333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259751277004357426465555 389626915506536139698333)
        ·
          refine ⟨146110093314951052386875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389626915506536139698333 146110093314951052386875)
          ·
            refine ⟨219165139972426578580313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146110093314951052386875 219165139972426578580313)
            ·
              refine ⟨164373854979319933935235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219165139972426578580313 164373854979319933935235)
              ·
                refine ⟨246560782468979900902853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164373854979319933935235 246560782468979900902853)
                ·
                  refine ⟨46230146712933731419285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246560782468979900902853 46230146712933731419285)
                  ·
                    rfl

theorem cell20_101287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_101287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101287 prefixEnd_101287 := by exact prefixLift 101287
  have htrace : WordTrace (prefixWord ++ tailWord_101287) baseStart_101287 baseEnd_101287 := by
    simpa [prefixWord, tailWord_101287, baseEnd_101287] using wordTrace_append hprefix tailTrace_101287
  have hstable : (prefixWord ++ tailWord_101287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101287).length < 2 ^ (prefixWord ++ tailWord_101287).sum := by decide
  have hdescent : baseEnd_101287 < baseStart_101287 := by decide
  rcases family_descends (prefixWord ++ tailWord_101287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101336 : List Nat := [2, 1, 2, 2, 2, 3, 8]
def baseStart_101336 : Nat := 118140960795 + 101336 * 2 ^ 59
def prefixEnd_101336 : Nat := 4983230072969 + 3 ^ 40 * 101336 * 2
def baseEnd_101336 : Nat := 5139167960900815420639

theorem tailTrace_101336 : CollatzResearch.WordTrace tailWord_101336 prefixEnd_101336 5139167960900815420639 := by
  unfold tailWord_101336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848013780442226828021931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2464018373922969104029241 1848013780442226828021931)
  ·
    refine ⟨2772020670663340242032897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848013780442226828021931 2772020670663340242032897)
    ·
      refine ⟨2079015502997505181524673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772020670663340242032897 2079015502997505181524673)
      ·
        refine ⟨1559261627248128886143505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2079015502997505181524673 1559261627248128886143505)
        ·
          refine ⟨1169446220436096664607629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559261627248128886143505 1169446220436096664607629)
          ·
            refine ⟨438542332663536249227861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169446220436096664607629 438542332663536249227861)
            ·
              refine ⟨5139167960900815420639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 438542332663536249227861 5139167960900815420639)
              ·
                rfl

theorem cell20_101336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_101336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101336 prefixEnd_101336 := by exact prefixLift 101336
  have htrace : WordTrace (prefixWord ++ tailWord_101336) baseStart_101336 baseEnd_101336 := by
    simpa [prefixWord, tailWord_101336, baseEnd_101336] using wordTrace_append hprefix tailTrace_101336
  have hstable : (prefixWord ++ tailWord_101336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101336).length < 2 ^ (prefixWord ++ tailWord_101336).sum := by decide
  have hdescent : baseEnd_101336 < baseStart_101336 := by decide
  rcases family_descends (prefixWord ++ tailWord_101336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101401 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 2]
def baseStart_101401 : Nat := 118140960795 + 101401 * 2 ^ 59
def prefixEnd_101401 : Nat := 4983230072969 + 3 ^ 40 * 101401 * 2
def baseEnd_101401 : Nat := 46282179419256001618819

theorem tailTrace_101401 : CollatzResearch.WordTrace tailWord_101401 prefixEnd_101401 46282179419256001618819 := by
  unfold tailWord_101401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698398305648969757160057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2465598870432646504773371 3698398305648969757160057)
  ·
    refine ⟨2773798729236727317870043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3698398305648969757160057 2773798729236727317870043)
    ·
      refine ⟨4160698093855090976805065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773798729236727317870043 4160698093855090976805065)
      ·
        refine ⟨3120523570391318232603799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4160698093855090976805065 3120523570391318232603799)
        ·
          refine ⟨4680785355586977348905699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120523570391318232603799 4680785355586977348905699)
          ·
            refine ⟨7021178033380466023358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680785355586977348905699 7021178033380466023358549)
            ·
              refine ⟨82279430078677336211233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 7021178033380466023358549 82279430078677336211233)
              ·
                refine ⟨61709572559008002158425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82279430078677336211233 61709572559008002158425)
                ·
                  refine ⟨46282179419256001618819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61709572559008002158425 46282179419256001618819)
                  ·
                    rfl

theorem cell20_101401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_101401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101401 prefixEnd_101401 := by exact prefixLift 101401
  have htrace : WordTrace (prefixWord ++ tailWord_101401) baseStart_101401 baseEnd_101401 := by
    simpa [prefixWord, tailWord_101401, baseEnd_101401] using wordTrace_append hprefix tailTrace_101401
  have hstable : (prefixWord ++ tailWord_101401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101401).length < 2 ^ (prefixWord ++ tailWord_101401).sum := by decide
  have hdescent : baseEnd_101401 < baseStart_101401 := by decide
  rcases family_descends (prefixWord ++ tailWord_101401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101422 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_101422 : Nat := 118140960795 + 101422 * 2 ^ 59
def prefixEnd_101422 : Nat := 4983230072969 + 3 ^ 40 * 101422 * 2
def baseEnd_101422 : Nat := 46291764391473261918733

theorem tailTrace_101422 : CollatzResearch.WordTrace tailWord_101422 prefixEnd_101422 46291764391473261918733 := by
  unfold tailWord_101422
  simp only [CollatzResearch.WordTrace]
  refine ⟨462395529821611292959315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2466109492381926895783013 462395529821611292959315)
  ·
    refine ⟨693593294732416939438973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 462395529821611292959315 693593294732416939438973)
    ·
      refine ⟨260097485524656352289615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 693593294732416939438973 260097485524656352289615)
      ·
        refine ⟨390146228286984528434423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260097485524656352289615 390146228286984528434423)
        ·
          refine ⟨585219342430476792651635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390146228286984528434423 585219342430476792651635)
          ·
            refine ⟨877829013645715188977453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585219342430476792651635 877829013645715188977453)
            ·
              refine ⟨329185880117143195866545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877829013645715188977453 329185880117143195866545)
              ·
                refine ⟨246889410087857396899909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329185880117143195866545 246889410087857396899909)
                ·
                  refine ⟨46291764391473261918733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246889410087857396899909 46291764391473261918733)
                  ·
                    rfl

theorem cell20_101422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_101422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101422 prefixEnd_101422 := by exact prefixLift 101422
  have htrace : WordTrace (prefixWord ++ tailWord_101422) baseStart_101422 baseEnd_101422 := by
    simpa [prefixWord, tailWord_101422, baseEnd_101422] using wordTrace_append hprefix tailTrace_101422
  have hstable : (prefixWord ++ tailWord_101422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101422).length < 2 ^ (prefixWord ++ tailWord_101422).sum := by decide
  have hdescent : baseEnd_101422 < baseStart_101422 := by decide
  rcases family_descends (prefixWord ++ tailWord_101422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101446 : List Nat := [6, 1, 1, 1, 1, 3, 7]
def baseStart_101446 : Nat := 118140960795 + 101446 * 2 ^ 59
def prefixEnd_101446 : Nat := 4983230072969 + 3 ^ 40 * 101446 * 2
def baseEnd_101446 : Nat := 5144746516159538346515

theorem tailTrace_101446 : CollatzResearch.WordTrace tailWord_101446 prefixEnd_101446 5144746516159538346515 := by
  unfold tailWord_101446
  simp only [CollatzResearch.WordTrace]
  refine ⟨115626237202685701329631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2466693060323961628365461 115626237202685701329631)
  ·
    refine ⟨173439355804028551994447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115626237202685701329631 173439355804028551994447)
    ·
      refine ⟨260159033706042827991671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173439355804028551994447 260159033706042827991671)
      ·
        refine ⟨390238550559064241987507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260159033706042827991671 390238550559064241987507)
        ·
          refine ⟨585357825838596362981261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390238550559064241987507 585357825838596362981261)
          ·
            refine ⟨219509184689473636117973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585357825838596362981261 219509184689473636117973)
            ·
              refine ⟨5144746516159538346515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219509184689473636117973 5144746516159538346515)
              ·
                rfl

theorem cell20_101446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_101446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101446 prefixEnd_101446 := by exact prefixLift 101446
  have htrace : WordTrace (prefixWord ++ tailWord_101446) baseStart_101446 baseEnd_101446 := by
    simpa [prefixWord, tailWord_101446, baseEnd_101446] using wordTrace_append hprefix tailTrace_101446
  have hstable : (prefixWord ++ tailWord_101446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101446).length < 2 ^ (prefixWord ++ tailWord_101446).sum := by decide
  have hdescent : baseEnd_101446 < baseStart_101446 := by decide
  rcases family_descends (prefixWord ++ tailWord_101446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101453 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_101453 : Nat := 118140960795 + 101453 * 2 ^ 59
def prefixEnd_101453 : Nat := 4983230072969 + 3 ^ 40 * 101453 * 2
def baseEnd_101453 : Nat := 46305913636174931885273

theorem tailTrace_101453 : CollatzResearch.WordTrace tailWord_101453 prefixEnd_101453 46305913636174931885273 := by
  unfold tailWord_101453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700294901460582638053013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2466863267640388425368675 3700294901460582638053013)
  ·
    refine ⟨173451323505964811158735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3700294901460582638053013 173451323505964811158735)
    ·
      refine ⟨260176985258947216738103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173451323505964811158735 260176985258947216738103)
      ·
        refine ⟨390265477888420825107155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260176985258947216738103 390265477888420825107155)
        ·
          refine ⟨585398216832631237660733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390265477888420825107155 585398216832631237660733)
          ·
            refine ⟨219524331312236714122775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585398216832631237660733 219524331312236714122775)
            ·
              refine ⟨329286496968355071184163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219524331312236714122775 329286496968355071184163)
              ·
                refine ⟨493929745452532606776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329286496968355071184163 493929745452532606776245)
                ·
                  refine ⟨46305913636174931885273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493929745452532606776245 46305913636174931885273)
                  ·
                    rfl

theorem cell20_101453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_101453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101453 prefixEnd_101453 := by exact prefixLift 101453
  have htrace : WordTrace (prefixWord ++ tailWord_101453) baseStart_101453 baseEnd_101453 := by
    simpa [prefixWord, tailWord_101453, baseEnd_101453] using wordTrace_append hprefix tailTrace_101453
  have hstable : (prefixWord ++ tailWord_101453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101453).length < 2 ^ (prefixWord ++ tailWord_101453).sum := by decide
  have hdescent : baseEnd_101453 < baseStart_101453 := by decide
  rcases family_descends (prefixWord ++ tailWord_101453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101480 : List Nat := [2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_101480 : Nat := 118140960795 + 101480 * 2 ^ 59
def prefixEnd_101480 : Nat := 4983230072969 + 3 ^ 40 * 101480 * 2
def baseEnd_101480 : Nat := 15439412390627612661721

theorem tailTrace_101480 : CollatzResearch.WordTrace tailWord_101480 prefixEnd_101480 15439412390627612661721 := by
  unfold tailWord_101480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850639836181383124642947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2467519781575177499523929 1850639836181383124642947)
  ·
    refine ⟨2775959754272074686964421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850639836181383124642947 2775959754272074686964421)
    ·
      refine ⟨520492453926014003805829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2775959754272074686964421 520492453926014003805829)
      ·
        refine ⟨97592335111127625713593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 520492453926014003805829 97592335111127625713593)
        ·
          refine ⟨73194251333345719285195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97592335111127625713593 73194251333345719285195)
          ·
            refine ⟨109791377000018578927793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73194251333345719285195 109791377000018578927793)
            ·
              refine ⟨82343532750013934195845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109791377000018578927793 82343532750013934195845)
              ·
                refine ⟨15439412390627612661721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82343532750013934195845 15439412390627612661721)
                ·
                  rfl

theorem cell20_101480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_101480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101480 prefixEnd_101480 := by exact prefixLift 101480
  have htrace : WordTrace (prefixWord ++ tailWord_101480) baseStart_101480 baseEnd_101480 := by
    simpa [prefixWord, tailWord_101480, baseEnd_101480] using wordTrace_append hprefix tailTrace_101480
  have hstable : (prefixWord ++ tailWord_101480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101480).length < 2 ^ (prefixWord ++ tailWord_101480).sum := by decide
  have hdescent : baseEnd_101480 < baseStart_101480 := by decide
  rcases family_descends (prefixWord ++ tailWord_101480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101481 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_101481 : Nat := 118140960795 + 101481 * 2 ^ 59
def prefixEnd_101481 : Nat := 4983230072969 + 3 ^ 40 * 101481 * 2
def baseEnd_101481 : Nat := 46318693599131278951825

theorem tailTrace_101481 : CollatzResearch.WordTrace tailWord_101481 prefixEnd_101481 46318693599131278951825 := by
  unfold tailWord_101481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701316145359143420072297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2467544096906095613381531 3701316145359143420072297)
  ·
    refine ⟨2775987109019357565054223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3701316145359143420072297 2775987109019357565054223)
    ·
      refine ⟨4163980663529036347581335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775987109019357565054223 4163980663529036347581335)
      ·
        refine ⟨6245970995293554521372003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163980663529036347581335 6245970995293554521372003)
        ·
          refine ⟨9368956492940331782058005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245970995293554521372003 9368956492940331782058005)
          ·
            refine ⟨439169835606578052283969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9368956492940331782058005 439169835606578052283969)
            ·
              refine ⟨329377376704933539212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439169835606578052283969 329377376704933539212977)
              ·
                refine ⟨247033032528700154409733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329377376704933539212977 247033032528700154409733)
                ·
                  refine ⟨46318693599131278951825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247033032528700154409733 46318693599131278951825)
                  ·
                    rfl

theorem cell20_101481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_101481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101481 prefixEnd_101481 := by exact prefixLift 101481
  have htrace : WordTrace (prefixWord ++ tailWord_101481) baseStart_101481 baseEnd_101481 := by
    simpa [prefixWord, tailWord_101481, baseEnd_101481] using wordTrace_append hprefix tailTrace_101481
  have hstable : (prefixWord ++ tailWord_101481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101481).length < 2 ^ (prefixWord ++ tailWord_101481).sum := by decide
  have hdescent : baseEnd_101481 < baseStart_101481 := by decide
  rcases family_descends (prefixWord ++ tailWord_101481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101488 : List Nat := [2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_101488 : Nat := 118140960795 + 101488 * 2 ^ 59
def prefixEnd_101488 : Nat := 4983230072969 + 3 ^ 40 * 101488 * 2
def baseEnd_101488 : Nat := 15440629529956788572821

theorem tailTrace_101488 : CollatzResearch.WordTrace tailWord_101488 prefixEnd_101488 15440629529956788572821 := by
  unfold tailWord_101488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850785728166891807788559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2467714304222522410384745 1850785728166891807788559)
  ·
    refine ⟨2776178592250337711682839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850785728166891807788559 2776178592250337711682839)
    ·
      refine ⟨4164267888375506567524259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776178592250337711682839 4164267888375506567524259)
      ·
        refine ⟨6246401832563259851286389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164267888375506567524259 6246401832563259851286389)
        ·
          refine ⟨585600171802805611058099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6246401832563259851286389 585600171802805611058099)
          ·
            refine ⟨878400257704208416587149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585600171802805611058099 878400257704208416587149)
            ·
              refine ⟨329400096639078156220181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878400257704208416587149 329400096639078156220181)
              ·
                refine ⟨15440629529956788572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 329400096639078156220181 15440629529956788572821)
                ·
                  rfl

theorem cell20_101488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_101488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101488 prefixEnd_101488 := by exact prefixLift 101488
  have htrace : WordTrace (prefixWord ++ tailWord_101488) baseStart_101488 baseEnd_101488 := by
    simpa [prefixWord, tailWord_101488, baseEnd_101488] using wordTrace_append hprefix tailTrace_101488
  have hstable : (prefixWord ++ tailWord_101488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101488).length < 2 ^ (prefixWord ++ tailWord_101488).sum := by decide
  have hdescent : baseEnd_101488 < baseStart_101488 := by decide
  rcases family_descends (prefixWord ++ tailWord_101488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101495 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_101495 : Nat := 118140960795 + 101495 * 2 ^ 59
def prefixEnd_101495 : Nat := 4983230072969 + 3 ^ 40 * 101495 * 2
def baseEnd_101495 : Nat := 46325083580609452485101

theorem tailTrace_101495 : CollatzResearch.WordTrace tailWord_101495 prefixEnd_101495 46325083580609452485101 := by
  unfold tailWord_101495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701826767308423811081939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2467884511538949207387959 3701826767308423811081939)
  ·
    refine ⟨5552740150962635716622909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701826767308423811081939 5552740150962635716622909)
    ·
      refine ⟨2082277556610988393733591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5552740150962635716622909 2082277556610988393733591)
      ·
        refine ⟨3123416334916482590600387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082277556610988393733591 3123416334916482590600387)
        ·
          refine ⟨4685124502374723885900581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123416334916482590600387 4685124502374723885900581)
          ·
            refine ⟨878460844195260728606359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4685124502374723885900581 878460844195260728606359)
            ·
              refine ⟨1317691266292891092909539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878460844195260728606359 1317691266292891092909539)
              ·
                refine ⟨1976536899439336639364309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317691266292891092909539 1976536899439336639364309)
                ·
                  refine ⟨46325083580609452485101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1976536899439336639364309 46325083580609452485101)
                  ·
                    rfl

theorem cell20_101495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_101495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101495 prefixEnd_101495 := by exact prefixLift 101495
  have htrace : WordTrace (prefixWord ++ tailWord_101495) baseStart_101495 baseEnd_101495 := by
    simpa [prefixWord, tailWord_101495, baseEnd_101495] using wordTrace_append hprefix tailTrace_101495
  have hstable : (prefixWord ++ tailWord_101495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101495).length < 2 ^ (prefixWord ++ tailWord_101495).sum := by decide
  have hdescent : baseEnd_101495 < baseStart_101495 := by decide
  rcases family_descends (prefixWord ++ tailWord_101495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101505 : List Nat := [1, 2, 4, 2, 2, 3, 6]
def baseStart_101505 : Nat := 118140960795 + 101505 * 2 ^ 59
def prefixEnd_101505 : Nat := 4983230072969 + 3 ^ 40 * 101505 * 2
def baseEnd_101505 : Nat := 5147738650343762461303

theorem tailTrace_101505 : CollatzResearch.WordTrace tailWord_101505 prefixEnd_101505 5147738650343762461303 := by
  unfold tailWord_101505
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702191497272195518945969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2468127664848130345963979 3702191497272195518945969)
  ·
    refine ⟨2776643622954146639209477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3702191497272195518945969 2776643622954146639209477)
    ·
      refine ⟨520620679303902494851777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2776643622954146639209477 520620679303902494851777)
      ·
        refine ⟨390465509477926871138833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520620679303902494851777 390465509477926871138833)
        ·
          refine ⟨292849132108445153354125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390465509477926871138833 292849132108445153354125)
          ·
            refine ⟨109818424540666932507797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292849132108445153354125 109818424540666932507797)
            ·
              refine ⟨5147738650343762461303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109818424540666932507797 5147738650343762461303)
              ·
                rfl

theorem cell20_101505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_101505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101505 prefixEnd_101505 := by exact prefixLift 101505
  have htrace : WordTrace (prefixWord ++ tailWord_101505) baseStart_101505 baseEnd_101505 := by
    simpa [prefixWord, tailWord_101505, baseEnd_101505] using wordTrace_append hprefix tailTrace_101505
  have hstable : (prefixWord ++ tailWord_101505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101505).length < 2 ^ (prefixWord ++ tailWord_101505).sum := by decide
  have hdescent : baseEnd_101505 < baseStart_101505 := by decide
  rcases family_descends (prefixWord ++ tailWord_101505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101543 : List Nat := [1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_101543 : Nat := 118140960795 + 101543 * 2 ^ 59
def prefixEnd_101543 : Nat := 4983230072969 + 3 ^ 40 * 101543 * 2
def baseEnd_101543 : Nat := 15448997362844872961635

theorem tailTrace_101543 : CollatzResearch.WordTrace tailWord_101543 prefixEnd_101543 15448997362844872961635 := by
  unfold tailWord_101543
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703577471134528008829283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2469051647423018672552855 3703577471134528008829283)
  ·
    refine ⟨5555366206701792013243925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703577471134528008829283 5555366206701792013243925)
    ·
      refine ⟨260407790939146500620809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5555366206701792013243925 260407790939146500620809)
      ·
        refine ⟨195305843204359875465607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260407790939146500620809 195305843204359875465607)
        ·
          refine ⟨292958764806539813198411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195305843204359875465607 292958764806539813198411)
          ·
            refine ⟨439438147209809719797617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292958764806539813198411 439438147209809719797617)
            ·
              refine ⟨329578610407357289848213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439438147209809719797617 329578610407357289848213)
              ·
                refine ⟨15448997362844872961635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 329578610407357289848213 15448997362844872961635)
                ·
                  rfl

theorem cell20_101543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_101543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101543 prefixEnd_101543 := by exact prefixLift 101543
  have htrace : WordTrace (prefixWord ++ tailWord_101543) baseStart_101543 baseEnd_101543 := by
    simpa [prefixWord, tailWord_101543, baseEnd_101543] using wordTrace_append hprefix tailTrace_101543
  have hstable : (prefixWord ++ tailWord_101543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101543).length < 2 ^ (prefixWord ++ tailWord_101543).sum := by decide
  have hdescent : baseEnd_101543 < baseStart_101543 := by decide
  rcases family_descends (prefixWord ++ tailWord_101543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101564 : List Nat := [2, 2, 2, 3, 2, 9]
def baseStart_101564 : Nat := 118140960795 + 101564 * 2 ^ 59
def prefixEnd_101564 : Nat := 4983230072969 + 3 ^ 40 * 101564 * 2
def baseEnd_101564 : Nat := 1716910261509328858697

theorem tailTrace_101564 : CollatzResearch.WordTrace tailWord_101564 prefixEnd_101564 1716910261509328858697 := by
  unfold tailWord_101564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852171702029224297671873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2469562269372299063562497 1852171702029224297671873)
  ·
    refine ⟨1389128776521918223253905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1852171702029224297671873 1389128776521918223253905)
    ·
      refine ⟨1041846582391438667440429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1389128776521918223253905 1041846582391438667440429)
      ·
        refine ⟨390692468396789500290161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041846582391438667440429 390692468396789500290161)
        ·
          refine ⟨293019351297592125217621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390692468396789500290161 293019351297592125217621)
          ·
            refine ⟨1716910261509328858697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 293019351297592125217621 1716910261509328858697)
            ·
              rfl

theorem cell20_101564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 9].length) (baseStart_101564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101564 prefixEnd_101564 := by exact prefixLift 101564
  have htrace : WordTrace (prefixWord ++ tailWord_101564) baseStart_101564 baseEnd_101564 := by
    simpa [prefixWord, tailWord_101564, baseEnd_101564] using wordTrace_append hprefix tailTrace_101564
  have hstable : (prefixWord ++ tailWord_101564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101564).length < 2 ^ (prefixWord ++ tailWord_101564).sum := by decide
  have hdescent : baseEnd_101564 < baseStart_101564 := by decide
  rcases family_descends (prefixWord ++ tailWord_101564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101612 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_101612 : Nat := 118140960795 + 101612 * 2 ^ 59
def prefixEnd_101612 : Nat := 4983230072969 + 3 ^ 40 * 101612 * 2
def baseEnd_101612 : Nat := 46378485568677045584623

theorem tailTrace_101612 : CollatzResearch.WordTrace tailWord_101612 prefixEnd_101612 46378485568677045584623 := by
  unfold tailWord_101612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853047053942276396545545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2470729405256368528727393 1853047053942276396545545)
  ·
    refine ⟨1389785290456707297409159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853047053942276396545545 1389785290456707297409159)
    ·
      refine ⟨2084677935685060946113739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389785290456707297409159 2084677935685060946113739)
      ·
        refine ⟨3127016903527591419170609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084677935685060946113739 3127016903527591419170609)
        ·
          refine ⟨2345262677645693564377957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3127016903527591419170609 2345262677645693564377957)
          ·
            refine ⟨439736752058567543320867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2345262677645693564377957 439736752058567543320867)
            ·
              refine ⟨659605128087851314981301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439736752058567543320867 659605128087851314981301)
              ·
                refine ⟨61837980758236060779497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659605128087851314981301 61837980758236060779497)
                ·
                  refine ⟨46378485568677045584623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61837980758236060779497 46378485568677045584623)
                  ·
                    rfl

theorem cell20_101612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_101612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101612 prefixEnd_101612 := by exact prefixLift 101612
  have htrace : WordTrace (prefixWord ++ tailWord_101612) baseStart_101612 baseEnd_101612 := by
    simpa [prefixWord, tailWord_101612, baseEnd_101612] using wordTrace_append hprefix tailTrace_101612
  have hstable : (prefixWord ++ tailWord_101612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101612).length < 2 ^ (prefixWord ++ tailWord_101612).sum := by decide
  have hdescent : baseEnd_101612 < baseStart_101612 := by decide
  rcases family_descends (prefixWord ++ tailWord_101612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101633 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_101633 : Nat := 118140960795 + 101633 * 2 ^ 59
def prefixEnd_101633 : Nat := 4983230072969 + 3 ^ 40 * 101633 * 2
def baseEnd_101633 : Nat := 46388070540894305884537

theorem tailTrace_101633 : CollatzResearch.WordTrace tailWord_101633 prefixEnd_101633 46388070540894305884537 := by
  unfold tailWord_101633
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706860040808473379605553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471240027205648919737035 3706860040808473379605553)
  ·
    refine ⟨2780145030606355034704165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3706860040808473379605553 2780145030606355034704165)
    ·
      refine ⟨521277193238691569007031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2780145030606355034704165 521277193238691569007031)
      ·
        refine ⟨781915789858037353510547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521277193238691569007031 781915789858037353510547)
        ·
          refine ⟨1172873684787056030265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781915789858037353510547 1172873684787056030265821)
          ·
            refine ⟨439827631795146011349683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1172873684787056030265821 439827631795146011349683)
            ·
              refine ⟨659741447692719017024525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439827631795146011349683 659741447692719017024525)
              ·
                refine ⟨247403042884769631384197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659741447692719017024525 247403042884769631384197)
                ·
                  refine ⟨46388070540894305884537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247403042884769631384197 46388070540894305884537)
                  ·
                    rfl

theorem cell20_101633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_101633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101633 prefixEnd_101633 := by exact prefixLift 101633
  have htrace : WordTrace (prefixWord ++ tailWord_101633) baseStart_101633 baseEnd_101633 := by
    simpa [prefixWord, tailWord_101633, baseEnd_101633] using wordTrace_append hprefix tailTrace_101633
  have hstable : (prefixWord ++ tailWord_101633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101633).length < 2 ^ (prefixWord ++ tailWord_101633).sum := by decide
  have hdescent : baseEnd_101633 < baseStart_101633 := by decide
  rcases family_descends (prefixWord ++ tailWord_101633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101643 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_101643 : Nat := 118140960795 + 101643 * 2 ^ 59
def prefixEnd_101643 : Nat := 4983230072969 + 3 ^ 40 * 101643 * 2
def baseEnd_101643 : Nat := 46392634813378715551163

theorem tailTrace_101643 : CollatzResearch.WordTrace tailWord_101643 prefixEnd_101643 46392634813378715551163 := by
  unfold tailWord_101643
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707224770772245087469583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471483180514830058313055 3707224770772245087469583)
  ·
    refine ⟨5560837156158367631204375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707224770772245087469583 5560837156158367631204375)
    ·
      refine ⟨8341255734237551446806563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560837156158367631204375 8341255734237551446806563)
      ·
        refine ⟨12511883601356327170209845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341255734237551446806563 12511883601356327170209845)
        ·
          refine ⟨1172989087627155672207173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12511883601356327170209845 1172989087627155672207173)
          ·
            refine ⟨219935453930091688538845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1172989087627155672207173 219935453930091688538845)
            ·
              refine ⟨82475795223784383202067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219935453930091688538845 82475795223784383202067)
              ·
                refine ⟨123713692835676574803101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82475795223784383202067 123713692835676574803101)
                ·
                  refine ⟨46392634813378715551163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123713692835676574803101 46392634813378715551163)
                  ·
                    rfl

theorem cell20_101643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_101643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101643 prefixEnd_101643 := by exact prefixLift 101643
  have htrace : WordTrace (prefixWord ++ tailWord_101643) baseStart_101643 baseEnd_101643 := by
    simpa [prefixWord, tailWord_101643, baseEnd_101643] using wordTrace_append hprefix tailTrace_101643
  have hstable : (prefixWord ++ tailWord_101643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101643).length < 2 ^ (prefixWord ++ tailWord_101643).sum := by decide
  have hdescent : baseEnd_101643 < baseStart_101643 := by decide
  rcases family_descends (prefixWord ++ tailWord_101643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101667 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 2]
def baseStart_101667 : Nat := 118140960795 + 101667 * 2 ^ 59
def prefixEnd_101667 : Nat := 4983230072969 + 3 ^ 40 * 101667 * 2
def baseEnd_101667 : Nat := 46403589067341298751065

theorem tailTrace_101667 : CollatzResearch.WordTrace tailWord_101667 prefixEnd_101667 46403589067341298751065 := by
  unfold tailWord_101667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708100122685297186343255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2472066748456864790895503 3708100122685297186343255)
  ·
    refine ⟨5562150184027945779514883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708100122685297186343255 5562150184027945779514883)
    ·
      refine ⟨8343225276041918669272325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562150184027945779514883 8343225276041918669272325)
      ·
        refine ⟨1564354739257859750488561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8343225276041918669272325 1564354739257859750488561)
        ·
          refine ⟨1173266054443394812866421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564354739257859750488561 1173266054443394812866421)
          ·
            refine ⟨109993692604068263706227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1173266054443394812866421 109993692604068263706227)
            ·
              refine ⟨164990538906102395559341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109993692604068263706227 164990538906102395559341)
              ·
                refine ⟨61871452089788398334753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164990538906102395559341 61871452089788398334753)
                ·
                  refine ⟨46403589067341298751065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61871452089788398334753 46403589067341298751065)
                  ·
                    rfl

theorem cell20_101667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2].length) (baseStart_101667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101667 prefixEnd_101667 := by exact prefixLift 101667
  have htrace : WordTrace (prefixWord ++ tailWord_101667) baseStart_101667 baseEnd_101667 := by
    simpa [prefixWord, tailWord_101667, baseEnd_101667] using wordTrace_append hprefix tailTrace_101667
  have hstable : (prefixWord ++ tailWord_101667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101667).length < 2 ^ (prefixWord ++ tailWord_101667).sum := by decide
  have hdescent : baseEnd_101667 < baseStart_101667 := by decide
  rcases family_descends (prefixWord ++ tailWord_101667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101684 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_101684 : Nat := 118140960795 + 101684 * 2 ^ 59
def prefixEnd_101684 : Nat := 4983230072969 + 3 ^ 40 * 101684 * 2
def baseEnd_101684 : Nat := 46411348330564795184329

theorem tailTrace_101684 : CollatzResearch.WordTrace tailWord_101684 prefixEnd_101684 46411348330564795184329 := by
  unfold tailWord_101684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854360081811854544856053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2472480109082472726474737 1854360081811854544856053)
  ·
    refine ⟨173846257669861363580255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1854360081811854544856053 173846257669861363580255)
    ·
      refine ⟨260769386504792045370383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173846257669861363580255 260769386504792045370383)
      ·
        refine ⟨391154079757188068055575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260769386504792045370383 391154079757188068055575)
        ·
          refine ⟨586731119635782102083363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391154079757188068055575 586731119635782102083363)
          ·
            refine ⟨880096679453673153125045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586731119635782102083363 880096679453673153125045)
            ·
              refine ⟨82509063698781858105473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 880096679453673153125045 82509063698781858105473)
              ·
                refine ⟨61881797774086393579105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82509063698781858105473 61881797774086393579105)
                ·
                  refine ⟨46411348330564795184329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61881797774086393579105 46411348330564795184329)
                  ·
                    rfl

theorem cell20_101684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_101684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101684 prefixEnd_101684 := by exact prefixLift 101684
  have htrace : WordTrace (prefixWord ++ tailWord_101684) baseStart_101684 baseEnd_101684 := by
    simpa [prefixWord, tailWord_101684, baseEnd_101684] using wordTrace_append hprefix tailTrace_101684
  have hstable : (prefixWord ++ tailWord_101684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101684).length < 2 ^ (prefixWord ++ tailWord_101684).sum := by decide
  have hdescent : baseEnd_101684 < baseStart_101684 := by decide
  rcases family_descends (prefixWord ++ tailWord_101684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101716 : List Nat := [2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_101716 : Nat := 118140960795 + 101716 * 2 ^ 59
def prefixEnd_101716 : Nat := 4983230072969 + 3 ^ 40 * 101716 * 2
def baseEnd_101716 : Nat := 15475318000838302039177

theorem tailTrace_101716 : CollatzResearch.WordTrace tailWord_101716 prefixEnd_101716 15475318000838302039177 := by
  unfold tailWord_101716
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854943649753889277438501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2473258199671852369918001 1854943649753889277438501)
  ·
    refine ⟨347801934328854239519719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1854943649753889277438501 347801934328854239519719)
    ·
      refine ⟨521702901493281359279579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347801934328854239519719 521702901493281359279579)
      ·
        refine ⟨782554352239922038919369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521702901493281359279579 782554352239922038919369)
        ·
          refine ⟨586915764179941529189527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782554352239922038919369 586915764179941529189527)
          ·
            refine ⟨880373646269912293784291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586915764179941529189527 880373646269912293784291)
            ·
              refine ⟨1320560469404868440676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880373646269912293784291 1320560469404868440676437)
              ·
                refine ⟨15475318000838302039177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1320560469404868440676437 15475318000838302039177)
                ·
                  rfl

theorem cell20_101716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_101716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101716 prefixEnd_101716 := by exact prefixLift 101716
  have htrace : WordTrace (prefixWord ++ tailWord_101716) baseStart_101716 baseEnd_101716 := by
    simpa [prefixWord, tailWord_101716, baseEnd_101716] using wordTrace_append hprefix tailTrace_101716
  have hstable : (prefixWord ++ tailWord_101716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101716).length < 2 ^ (prefixWord ++ tailWord_101716).sum := by decide
  have hdescent : baseEnd_101716 < baseStart_101716 := by decide
  rcases family_descends (prefixWord ++ tailWord_101716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101740 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_101740 : Nat := 118140960795 + 101740 * 2 ^ 59
def prefixEnd_101740 : Nat := 4983230072969 + 3 ^ 40 * 101740 * 2
def baseEnd_101740 : Nat := 46436908256477489317433

theorem tailTrace_101740 : CollatzResearch.WordTrace tailWord_101740 prefixEnd_101740 46436908256477489317433 := by
  unfold tailWord_101740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855381325710415326875337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2473841767613887102500449 1855381325710415326875337)
  ·
    refine ⟨1391535994282811495156503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1855381325710415326875337 1391535994282811495156503)
    ·
      refine ⟨2087303991424217242734755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391535994282811495156503 2087303991424217242734755)
      ·
        refine ⟨3130955987136325864102133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087303991424217242734755 3130955987136325864102133)
        ·
          refine ⟨293527123794030549759575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3130955987136325864102133 293527123794030549759575)
          ·
            refine ⟨440290685691045824639363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293527123794030549759575 440290685691045824639363)
            ·
              refine ⟨660436028536568736959045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440290685691045824639363 660436028536568736959045)
              ·
                refine ⟨123831755350606638179821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660436028536568736959045 123831755350606638179821)
                ·
                  refine ⟨46436908256477489317433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123831755350606638179821 46436908256477489317433)
                  ·
                    rfl

theorem cell20_101740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_101740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101740 prefixEnd_101740 := by exact prefixLift 101740
  have htrace : WordTrace (prefixWord ++ tailWord_101740) baseStart_101740 baseEnd_101740 := by
    simpa [prefixWord, tailWord_101740, baseEnd_101740] using wordTrace_append hprefix tailTrace_101740
  have hstable : (prefixWord ++ tailWord_101740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101740).length < 2 ^ (prefixWord ++ tailWord_101740).sum := by decide
  have hdescent : baseEnd_101740 < baseStart_101740 := by decide
  rcases family_descends (prefixWord ++ tailWord_101740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101857 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 2]
def baseStart_101857 : Nat := 118140960795 + 101857 * 2 ^ 59
def prefixEnd_101857 : Nat := 4983230072969 + 3 ^ 40 * 101857 * 2
def baseEnd_101857 : Nat := 46490310244545082416955

theorem tailTrace_101857 : CollatzResearch.WordTrace tailWord_101857 prefixEnd_101857 46490310244545082416955 := by
  unfold tailWord_101857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715029991996959635759825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2476686661331306423839883 3715029991996959635759825)
  ·
    refine ⟨2786272493997719726819869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3715029991996959635759825 2786272493997719726819869)
    ·
      refine ⟨1044852185249144897557451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2786272493997719726819869 1044852185249144897557451)
      ·
        refine ⟨1567278277873717346336177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044852185249144897557451 1567278277873717346336177)
        ·
          refine ⟨1175458708405288009752133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567278277873717346336177 1175458708405288009752133)
          ·
            refine ⟨220398507825991501828525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1175458708405288009752133 220398507825991501828525)
            ·
              refine ⟨82649440434746813185697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220398507825991501828525 82649440434746813185697)
              ·
                refine ⟨61987080326060109889273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82649440434746813185697 61987080326060109889273)
                ·
                  refine ⟨46490310244545082416955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61987080326060109889273 46490310244545082416955)
                  ·
                    rfl

theorem cell20_101857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_101857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101857 prefixEnd_101857 := by exact prefixLift 101857
  have htrace : WordTrace (prefixWord ++ tailWord_101857) baseStart_101857 baseEnd_101857 := by
    simpa [prefixWord, tailWord_101857, baseEnd_101857] using wordTrace_append hprefix tailTrace_101857
  have hstable : (prefixWord ++ tailWord_101857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101857).length < 2 ^ (prefixWord ++ tailWord_101857).sum := by decide
  have hdescent : baseEnd_101857 < baseStart_101857 := by decide
  rcases family_descends (prefixWord ++ tailWord_101857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101882 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_101882 : Nat := 118140960795 + 101882 * 2 ^ 59
def prefixEnd_101882 : Nat := 4983230072969 + 3 ^ 40 * 101882 * 2
def baseEnd_101882 : Nat := 46501720925756106583519

theorem tailTrace_101882 : CollatzResearch.WordTrace tailWord_101882 prefixEnd_101882 46501720925756106583519 := by
  unfold tailWord_101882
  simp only [CollatzResearch.WordTrace]
  refine ⟨928985454226597226354975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2477294544604259270279933 928985454226597226354975)
  ·
    refine ⟨1393478181339895839532463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928985454226597226354975 1393478181339895839532463)
    ·
      refine ⟨2090217272009843759298695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393478181339895839532463 2090217272009843759298695)
      ·
        refine ⟨3135325908014765638948043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090217272009843759298695 3135325908014765638948043)
        ·
          refine ⟨4702988862022148458422065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135325908014765638948043 4702988862022148458422065)
          ·
            refine ⟨3527241646516611343816549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702988862022148458422065 3527241646516611343816549)
            ·
              refine ⟨661357808721864626965603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3527241646516611343816549 661357808721864626965603)
              ·
                refine ⟨992036713082796940448405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661357808721864626965603 992036713082796940448405)
                ·
                  refine ⟨46501720925756106583519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 992036713082796940448405 46501720925756106583519)
                  ·
                    rfl

theorem cell20_101882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_101882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101882 prefixEnd_101882 := by exact prefixLift 101882
  have htrace : WordTrace (prefixWord ++ tailWord_101882) baseStart_101882 baseEnd_101882 := by
    simpa [prefixWord, tailWord_101882, baseEnd_101882] using wordTrace_append hprefix tailTrace_101882
  have hstable : (prefixWord ++ tailWord_101882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101882).length < 2 ^ (prefixWord ++ tailWord_101882).sum := by decide
  have hdescent : baseEnd_101882 < baseStart_101882 := by decide
  rcases family_descends (prefixWord ++ tailWord_101882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101908 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_101908 : Nat := 118140960795 + 101908 * 2 ^ 59
def prefixEnd_101908 : Nat := 4983230072969 + 3 ^ 40 * 101908 * 2
def baseEnd_101908 : Nat := 46513588034215571716747

theorem tailTrace_101908 : CollatzResearch.WordTrace tailWord_101908 prefixEnd_101908 46513588034215571716747 := by
  unfold tailWord_101908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858445057406097672933189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2477926743208130230577585 1858445057406097672933189)
  ·
    refine ⟨348458448263643313674973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1858445057406097672933189 348458448263643313674973)
    ·
      refine ⟨130671918098866242628115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348458448263643313674973 130671918098866242628115)
      ·
        refine ⟨196007877148299363942173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130671918098866242628115 196007877148299363942173)
        ·
          refine ⟨73502953930612261478315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196007877148299363942173 73502953930612261478315)
          ·
            refine ⟨110254430895918392217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73502953930612261478315 110254430895918392217473)
            ·
              refine ⟨82690823171938794163105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110254430895918392217473 82690823171938794163105)
              ·
                refine ⟨62018117378954095622329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82690823171938794163105 62018117378954095622329)
                ·
                  refine ⟨46513588034215571716747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62018117378954095622329 46513588034215571716747)
                  ·
                    rfl

theorem cell20_101908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_101908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101908 prefixEnd_101908 := by exact prefixLift 101908
  have htrace : WordTrace (prefixWord ++ tailWord_101908) baseStart_101908 baseEnd_101908 := by
    simpa [prefixWord, tailWord_101908, baseEnd_101908] using wordTrace_append hprefix tailTrace_101908
  have hstable : (prefixWord ++ tailWord_101908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101908).length < 2 ^ (prefixWord ++ tailWord_101908).sum := by decide
  have hdescent : baseEnd_101908 < baseStart_101908 := by decide
  rcases family_descends (prefixWord ++ tailWord_101908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101912 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_101912 : Nat := 118140960795 + 101912 * 2 ^ 59
def prefixEnd_101912 : Nat := 4983230072969 + 3 ^ 40 * 101912 * 2
def baseEnd_101912 : Nat := 46515413743209335583397

theorem tailTrace_101912 : CollatzResearch.WordTrace tailWord_101912 prefixEnd_101912 46515413743209335583397 := by
  unfold tailWord_101912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858518003398852014505995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2478024004531802686007993 1858518003398852014505995)
  ·
    refine ⟨2787777005098278021758993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858518003398852014505995 2787777005098278021758993)
    ·
      refine ⟨2090832753823708516319245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787777005098278021758993 2090832753823708516319245)
      ·
        refine ⟨784062282683890693619717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2090832753823708516319245 784062282683890693619717)
        ·
          refine ⟨147011678003229505053697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 784062282683890693619717 147011678003229505053697)
          ·
            refine ⟨110258758502422128790273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147011678003229505053697 110258758502422128790273)
            ·
              refine ⟨82694068876816596592705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110258758502422128790273 82694068876816596592705)
              ·
                refine ⟨62020551657612447444529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82694068876816596592705 62020551657612447444529)
                ·
                  refine ⟨46515413743209335583397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62020551657612447444529 46515413743209335583397)
                  ·
                    rfl

theorem cell20_101912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_101912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101912 prefixEnd_101912 := by exact prefixLift 101912
  have htrace : WordTrace (prefixWord ++ tailWord_101912) baseStart_101912 baseEnd_101912 := by
    simpa [prefixWord, tailWord_101912, baseEnd_101912] using wordTrace_append hprefix tailTrace_101912
  have hstable : (prefixWord ++ tailWord_101912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101912).length < 2 ^ (prefixWord ++ tailWord_101912).sum := by decide
  have hdescent : baseEnd_101912 < baseStart_101912 := by decide
  rcases family_descends (prefixWord ++ tailWord_101912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101916 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_101916 : Nat := 118140960795 + 101916 * 2 ^ 59
def prefixEnd_101916 : Nat := 4983230072969 + 3 ^ 40 * 101916 * 2
def baseEnd_101916 : Nat := 46517239452203099450047

theorem tailTrace_101916 : CollatzResearch.WordTrace tailWord_101916 prefixEnd_101916 46517239452203099450047 := by
  unfold tailWord_101916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858590949391606356078801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2478121265855475141438401 1858590949391606356078801)
  ·
    refine ⟨1393943212043704767059101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1858590949391606356078801 1393943212043704767059101)
    ·
      refine ⟨522728704516389287647163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1393943212043704767059101 522728704516389287647163)
      ·
        refine ⟨784093056774583931470745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522728704516389287647163 784093056774583931470745)
        ·
          refine ⟨588069792580937948603059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784093056774583931470745 588069792580937948603059)
          ·
            refine ⟨882104688871406922904589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588069792580937948603059 882104688871406922904589)
            ·
              refine ⟨330789258326777596089221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 882104688871406922904589 330789258326777596089221)
              ·
                refine ⟨62022985936270799266729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330789258326777596089221 62022985936270799266729)
                ·
                  refine ⟨46517239452203099450047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62022985936270799266729 46517239452203099450047)
                  ·
                    rfl

theorem cell20_101916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_101916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101916 prefixEnd_101916 := by exact prefixLift 101916
  have htrace : WordTrace (prefixWord ++ tailWord_101916) baseStart_101916 baseEnd_101916 := by
    simpa [prefixWord, tailWord_101916, baseEnd_101916] using wordTrace_append hprefix tailTrace_101916
  have hstable : (prefixWord ++ tailWord_101916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101916).length < 2 ^ (prefixWord ++ tailWord_101916).sum := by decide
  have hdescent : baseEnd_101916 < baseStart_101916 := by decide
  rcases family_descends (prefixWord ++ tailWord_101916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101923 : List Nat := [1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_101923 : Nat := 118140960795 + 101923 * 2 ^ 59
def prefixEnd_101923 : Nat := 4983230072969 + 3 ^ 40 * 101923 * 2
def baseEnd_101923 : Nat := 15506811480980728738895

theorem tailTrace_101923 : CollatzResearch.WordTrace tailWord_101923 prefixEnd_101923 15506811480980728738895 := by
  unfold tailWord_101923
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717437209757852907662423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2478291473171901938441615 3717437209757852907662423)
  ·
    refine ⟨5576155814636779361493635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717437209757852907662423 5576155814636779361493635)
    ·
      refine ⟨8364233721955169042240453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576155814636779361493635 8364233721955169042240453)
      ·
        refine ⟨1568293822866594195420085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8364233721955169042240453 1568293822866594195420085)
        ·
          refine ⟨147027545893743205820633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1568293822866594195420085 147027545893743205820633)
          ·
            refine ⟨110270659420307404365475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147027545893743205820633 110270659420307404365475)
            ·
              refine ⟨165405989130461106548213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110270659420307404365475 165405989130461106548213)
              ·
                refine ⟨15506811480980728738895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165405989130461106548213 15506811480980728738895)
                ·
                  rfl

theorem cell20_101923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_101923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101923 prefixEnd_101923 := by exact prefixLift 101923
  have htrace : WordTrace (prefixWord ++ tailWord_101923) baseStart_101923 baseEnd_101923 := by
    simpa [prefixWord, tailWord_101923, baseEnd_101923] using wordTrace_append hprefix tailTrace_101923
  have hstable : (prefixWord ++ tailWord_101923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101923).length < 2 ^ (prefixWord ++ tailWord_101923).sum := by decide
  have hdescent : baseEnd_101923 < baseStart_101923 := by decide
  rcases family_descends (prefixWord ++ tailWord_101923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101930 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_101930 : Nat := 118140960795 + 101930 * 2 ^ 59
def prefixEnd_101930 : Nat := 4983230072969 + 3 ^ 40 * 101930 * 2
def baseEnd_101930 : Nat := 46523629433681272983323

theorem tailTrace_101930 : CollatzResearch.WordTrace tailWord_101930 prefixEnd_101930 46523629433681272983323 := by
  unfold tailWord_101930
  simp only [CollatzResearch.WordTrace]
  refine ⟨929423130183123275791811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2478461680488328735444829 929423130183123275791811)
  ·
    refine ⟨1394134695274684913687717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929423130183123275791811 1394134695274684913687717)
    ·
      refine ⟨261400255364003421316447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1394134695274684913687717 261400255364003421316447)
      ·
        refine ⟨392100383046005131974671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261400255364003421316447 392100383046005131974671)
        ·
          refine ⟨588150574569007697962007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392100383046005131974671 588150574569007697962007)
          ·
            refine ⟨882225861853511546943011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588150574569007697962007 882225861853511546943011)
            ·
              refine ⟨1323338792780267320414517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882225861853511546943011 1323338792780267320414517)
              ·
                refine ⟨124063011823150061288861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1323338792780267320414517 124063011823150061288861)
                ·
                  refine ⟨46523629433681272983323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124063011823150061288861 46523629433681272983323)
                  ·
                    rfl

theorem cell20_101930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_101930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101930 prefixEnd_101930 := by exact prefixLift 101930
  have htrace : WordTrace (prefixWord ++ tailWord_101930) baseStart_101930 baseEnd_101930 := by
    simpa [prefixWord, tailWord_101930, baseEnd_101930] using wordTrace_append hprefix tailTrace_101930
  have hstable : (prefixWord ++ tailWord_101930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101930).length < 2 ^ (prefixWord ++ tailWord_101930).sum := by decide
  have hdescent : baseEnd_101930 < baseStart_101930 := by decide
  rcases family_descends (prefixWord ++ tailWord_101930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101975 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_101975 : Nat := 118140960795 + 101975 * 2 ^ 59
def prefixEnd_101975 : Nat := 4983230072969 + 3 ^ 40 * 101975 * 2
def baseEnd_101975 : Nat := 46544168659861116483139

theorem tailTrace_101975 : CollatzResearch.WordTrace tailWord_101975 prefixEnd_101975 46544168659861116483139 := by
  unfold tailWord_101975
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719333805569465788555379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2479555870379643859036919 3719333805569465788555379)
  ·
    refine ⟨5579000708354198682833069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3719333805569465788555379 5579000708354198682833069)
    ·
      refine ⟨2092125265632824506062401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5579000708354198682833069 2092125265632824506062401)
      ·
        refine ⟨1569093949224618379546801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2092125265632824506062401 1569093949224618379546801)
        ·
          refine ⟨1176820461918463784660101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569093949224618379546801 1176820461918463784660101)
          ·
            refine ⟨220653836609711959623769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1176820461918463784660101 220653836609711959623769)
            ·
              refine ⟨165490377457283969717827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220653836609711959623769 165490377457283969717827)
              ·
                refine ⟨248235566185925954576741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165490377457283969717827 248235566185925954576741)
                ·
                  refine ⟨46544168659861116483139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248235566185925954576741 46544168659861116483139)
                  ·
                    rfl

theorem cell20_101975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_101975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101975 prefixEnd_101975 := by exact prefixLift 101975
  have htrace : WordTrace (prefixWord ++ tailWord_101975) baseStart_101975 baseEnd_101975 := by
    simpa [prefixWord, tailWord_101975, baseEnd_101975] using wordTrace_append hprefix tailTrace_101975
  have hstable : (prefixWord ++ tailWord_101975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101975).length < 2 ^ (prefixWord ++ tailWord_101975).sum := by decide
  have hdescent : baseEnd_101975 < baseStart_101975 := by decide
  rcases family_descends (prefixWord ++ tailWord_101975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101981 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_101981 : Nat := 118140960795 + 101981 * 2 ^ 59
def prefixEnd_101981 : Nat := 4983230072969 + 3 ^ 40 * 101981 * 2
def baseEnd_101981 : Nat := 46546907223351762283115

theorem tailTrace_101981 : CollatzResearch.WordTrace tailWord_101981 prefixEnd_101981 46546907223351762283115 := by
  unfold tailWord_101981
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719552643547728813273797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2479701762365152542182531 3719552643547728813273797)
  ·
    refine ⟨697416120665199152488837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3719552643547728813273797 697416120665199152488837)
    ·
      refine ⟨130765522624724841091657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 697416120665199152488837 130765522624724841091657)
      ·
        refine ⟨98074141968543630818743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130765522624724841091657 98074141968543630818743)
        ·
          refine ⟨147111212952815446228115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98074141968543630818743 147111212952815446228115)
          ·
            refine ⟨220666819429223169342173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147111212952815446228115 220666819429223169342173)
            ·
              refine ⟨82750057285958688503315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220666819429223169342173 82750057285958688503315)
              ·
                refine ⟨124125085928938032754973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82750057285958688503315 124125085928938032754973)
                ·
                  refine ⟨46546907223351762283115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124125085928938032754973 46546907223351762283115)
                  ·
                    rfl

theorem cell20_101981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_101981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_101981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_101981 prefixEnd_101981 := by exact prefixLift 101981
  have htrace : WordTrace (prefixWord ++ tailWord_101981) baseStart_101981 baseEnd_101981 := by
    simpa [prefixWord, tailWord_101981, baseEnd_101981] using wordTrace_append hprefix tailTrace_101981
  have hstable : (prefixWord ++ tailWord_101981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101981).length < 2 ^ (prefixWord ++ tailWord_101981).sum := by decide
  have hdescent : baseEnd_101981 < baseStart_101981 := by decide
  rcases family_descends (prefixWord ++ tailWord_101981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102006 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_102006 : Nat := 118140960795 + 102006 * 2 ^ 59
def prefixEnd_102006 : Nat := 4983230072969 + 3 ^ 40 * 102006 * 2
def baseEnd_102006 : Nat := 46558317904562786449679

theorem tailTrace_102006 : CollatzResearch.WordTrace tailWord_102006 prefixEnd_102006 46558317904562786449679 := by
  unfold tailWord_102006
  simp only [CollatzResearch.WordTrace]
  refine ⟨232529029278572380183367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2480309645638105388622581 232529029278572380183367)
  ·
    refine ⟨348793543917858570275051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232529029278572380183367 348793543917858570275051)
    ·
      refine ⟨523190315876787855412577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348793543917858570275051 523190315876787855412577)
      ·
        refine ⟨392392736907590891559433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523190315876787855412577 392392736907590891559433)
        ·
          refine ⟨294294552680693168669575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392392736907590891559433 294294552680693168669575)
          ·
            refine ⟨441441829021039753004363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294294552680693168669575 441441829021039753004363)
            ·
              refine ⟨662162743531559629506545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441441829021039753004363 662162743531559629506545)
              ·
                refine ⟨496622057648669722129909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662162743531559629506545 496622057648669722129909)
                ·
                  refine ⟨46558317904562786449679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496622057648669722129909 46558317904562786449679)
                  ·
                    rfl

theorem cell20_102006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_102006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102006 prefixEnd_102006 := by exact prefixLift 102006
  have htrace : WordTrace (prefixWord ++ tailWord_102006) baseStart_102006 baseEnd_102006 := by
    simpa [prefixWord, tailWord_102006, baseEnd_102006] using wordTrace_append hprefix tailTrace_102006
  have hstable : (prefixWord ++ tailWord_102006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102006).length < 2 ^ (prefixWord ++ tailWord_102006).sum := by decide
  have hdescent : baseEnd_102006 < baseStart_102006 := by decide
  rcases family_descends (prefixWord ++ tailWord_102006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102027 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_102027 : Nat := 118140960795 + 102027 * 2 ^ 59
def prefixEnd_102027 : Nat := 4983230072969 + 3 ^ 40 * 102027 * 2
def baseEnd_102027 : Nat := 46567902876780046749593

theorem tailTrace_102027 : CollatzResearch.WordTrace tailWord_102027 prefixEnd_102027 46567902876780046749593 := by
  unfold tailWord_102027
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721230401381078669448335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2480820267587385779632223 3721230401381078669448335)
  ·
    refine ⟨5581845602071618004172503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721230401381078669448335 5581845602071618004172503)
    ·
      refine ⟨8372768403107427006258755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581845602071618004172503 8372768403107427006258755)
      ·
        refine ⟨12559152604661140509388133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372768403107427006258755 12559152604661140509388133)
        ·
          refine ⟨2354841113373963845510275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12559152604661140509388133 2354841113373963845510275)
          ·
            refine ⟨3532261670060945768265413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354841113373963845510275 3532261670060945768265413)
            ·
              refine ⟨662299063136427331549765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3532261670060945768265413 662299063136427331549765)
              ·
                refine ⟨124181074338080124665581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662299063136427331549765 124181074338080124665581)
                ·
                  refine ⟨46567902876780046749593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124181074338080124665581 46567902876780046749593)
                  ·
                    rfl

theorem cell20_102027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_102027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102027 prefixEnd_102027 := by exact prefixLift 102027
  have htrace : WordTrace (prefixWord ++ tailWord_102027) baseStart_102027 baseEnd_102027 := by
    simpa [prefixWord, tailWord_102027, baseEnd_102027] using wordTrace_append hprefix tailTrace_102027
  have hstable : (prefixWord ++ tailWord_102027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102027).length < 2 ^ (prefixWord ++ tailWord_102027).sum := by decide
  have hdescent : baseEnd_102027 < baseStart_102027 := by decide
  rcases family_descends (prefixWord ++ tailWord_102027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102030 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_102030 : Nat := 118140960795 + 102030 * 2 ^ 59
def prefixEnd_102030 : Nat := 4983230072969 + 3 ^ 40 * 102030 * 2
def baseEnd_102030 : Nat := 46569272158525369649581

theorem tailTrace_102030 : CollatzResearch.WordTrace tailWord_102030 prefixEnd_102030 46569272158525369649581 := by
  unfold tailWord_102030
  simp only [CollatzResearch.WordTrace]
  refine ⟨465167477546276272725943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2480893213580140121205029 465167477546276272725943)
  ·
    refine ⟨697751216319414409088915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465167477546276272725943 697751216319414409088915)
    ·
      refine ⟨1046626824479121613633373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697751216319414409088915 1046626824479121613633373)
      ·
        refine ⟨392485059179670605112515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046626824479121613633373 392485059179670605112515)
        ·
          refine ⟨588727588769505907668773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392485059179670605112515 588727588769505907668773)
          ·
            refine ⟨110386422894282357687895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 588727588769505907668773 110386422894282357687895)
            ·
              refine ⟨165579634341423536531843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110386422894282357687895 165579634341423536531843)
              ·
                refine ⟨248369451512135304797765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165579634341423536531843 248369451512135304797765)
                ·
                  refine ⟨46569272158525369649581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248369451512135304797765 46569272158525369649581)
                  ·
                    rfl

theorem cell20_102030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_102030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102030 prefixEnd_102030 := by exact prefixLift 102030
  have htrace : WordTrace (prefixWord ++ tailWord_102030) baseStart_102030 baseEnd_102030 := by
    simpa [prefixWord, tailWord_102030, baseEnd_102030] using wordTrace_append hprefix tailTrace_102030
  have hstable : (prefixWord ++ tailWord_102030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102030).length < 2 ^ (prefixWord ++ tailWord_102030).sum := by decide
  have hdescent : baseEnd_102030 < baseStart_102030 := by decide
  rcases family_descends (prefixWord ++ tailWord_102030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102092 : List Nat := [2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_102092 : Nat := 118140960795 + 102092 * 2 ^ 59
def prefixEnd_102092 : Nat := 4983230072969 + 3 ^ 40 * 102092 * 2
def baseEnd_102092 : Nat := 15532523549309569860887

theorem tailTrace_102092 : CollatzResearch.WordTrace tailWord_102092 prefixEnd_102092 15532523549309569860887 := by
  unfold tailWord_102092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861800573072797385282265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2482400764097063180376353 1861800573072797385282265)
  ·
    refine ⟨1396350429804598038961699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1861800573072797385282265 1396350429804598038961699)
    ·
      refine ⟨2094525644706897058442549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396350429804598038961699 2094525644706897058442549)
      ·
        refine ⟨196361779191271599228989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2094525644706897058442549 196361779191271599228989)
        ·
          refine ⟨73635667196726849710871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196361779191271599228989 73635667196726849710871)
          ·
            refine ⟨110453500795090274566307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73635667196726849710871 110453500795090274566307)
            ·
              refine ⟨165680251192635411849461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110453500795090274566307 165680251192635411849461)
              ·
                refine ⟨15532523549309569860887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165680251192635411849461 15532523549309569860887)
                ·
                  rfl

theorem cell20_102092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_102092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102092 prefixEnd_102092 := by exact prefixLift 102092
  have htrace : WordTrace (prefixWord ++ tailWord_102092) baseStart_102092 baseEnd_102092 := by
    simpa [prefixWord, tailWord_102092, baseEnd_102092] using wordTrace_append hprefix tailTrace_102092
  have hstable : (prefixWord ++ tailWord_102092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102092).length < 2 ^ (prefixWord ++ tailWord_102092).sum := by decide
  have hdescent : baseEnd_102092 < baseStart_102092 := by decide
  rcases family_descends (prefixWord ++ tailWord_102092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102103 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_102103 : Nat := 118140960795 + 102103 * 2 ^ 59
def prefixEnd_102103 : Nat := 4983230072969 + 3 ^ 40 * 102103 * 2
def baseEnd_102103 : Nat := 46602591347661560215949

theorem tailTrace_102103 : CollatzResearch.WordTrace tailWord_102103 prefixEnd_102103 46602591347661560215949 := by
  unfold tailWord_102103
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724002349105743649214963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2482668232737162432809975 3724002349105743649214963)
  ·
    refine ⟨5586003523658615473822445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724002349105743649214963 5586003523658615473822445)
    ·
      refine ⟨2094751321371980802683417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5586003523658615473822445 2094751321371980802683417)
      ·
        refine ⟨1571063491028985602012563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094751321371980802683417 1571063491028985602012563)
        ·
          refine ⟨2356595236543478403018845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571063491028985602012563 2356595236543478403018845)
          ·
            refine ⟨883723213703804401132067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2356595236543478403018845 883723213703804401132067)
            ·
              refine ⟨1325584820555706601698101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883723213703804401132067 1325584820555706601698101)
              ·
                refine ⟨124273576927097493909197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325584820555706601698101 124273576927097493909197)
                ·
                  refine ⟨46602591347661560215949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124273576927097493909197 46602591347661560215949)
                  ·
                    rfl

theorem cell20_102103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_102103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102103 prefixEnd_102103 := by exact prefixLift 102103
  have htrace : WordTrace (prefixWord ++ tailWord_102103) baseStart_102103 baseEnd_102103 := by
    simpa [prefixWord, tailWord_102103, baseEnd_102103] using wordTrace_append hprefix tailTrace_102103
  have hstable : (prefixWord ++ tailWord_102103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102103).length < 2 ^ (prefixWord ++ tailWord_102103).sum := by decide
  have hdescent : baseEnd_102103 < baseStart_102103 := by decide
  rcases family_descends (prefixWord ++ tailWord_102103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102113 : List Nat := [1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_102113 : Nat := 118140960795 + 102113 * 2 ^ 59
def prefixEnd_102113 : Nat := 4983230072969 + 3 ^ 40 * 102113 * 2
def baseEnd_102113 : Nat := 15535718540048656627525

theorem tailTrace_102113 : CollatzResearch.WordTrace tailWord_102113 prefixEnd_102113 15535718540048656627525 := by
  unfold tailWord_102113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724367079069515357078993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2482911386046343571385995 3724367079069515357078993)
  ·
    refine ⟨2793275309302136517809245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3724367079069515357078993 2793275309302136517809245)
    ·
      refine ⟨1047478240988301194178467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2793275309302136517809245 1047478240988301194178467)
      ·
        refine ⟨1571217361482451791267701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047478240988301194178467 1571217361482451791267701)
        ·
          refine ⟨147301627638979855431347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1571217361482451791267701 147301627638979855431347)
          ·
            refine ⟨220952441458469783147021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147301627638979855431347 220952441458469783147021)
            ·
              refine ⟨82857165546926168680133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220952441458469783147021 82857165546926168680133)
              ·
                refine ⟨15535718540048656627525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82857165546926168680133 15535718540048656627525)
                ·
                  rfl

theorem cell20_102113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_102113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102113 prefixEnd_102113 := by exact prefixLift 102113
  have htrace : WordTrace (prefixWord ++ tailWord_102113) baseStart_102113 baseEnd_102113 := by
    simpa [prefixWord, tailWord_102113, baseEnd_102113] using wordTrace_append hprefix tailTrace_102113
  have hstable : (prefixWord ++ tailWord_102113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102113).length < 2 ^ (prefixWord ++ tailWord_102113).sum := by decide
  have hdescent : baseEnd_102113 < baseStart_102113 := by decide
  rcases family_descends (prefixWord ++ tailWord_102113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102134 : List Nat := [5, 1, 1, 1, 1, 4, 7]
def baseStart_102134 : Nat := 118140960795 + 102134 * 2 ^ 59
def prefixEnd_102134 : Nat := 4983230072969 + 3 ^ 40 * 102134 * 2
def baseEnd_102134 : Nat := 5179637843595914464721

theorem tailTrace_102134 : CollatzResearch.WordTrace tailWord_102134 prefixEnd_102134 5179637843595914464721 := by
  unfold tailWord_102134
  simp only [CollatzResearch.WordTrace]
  refine ⟨232820813249589746474591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2483422007995623962395637 232820813249589746474591)
  ·
    refine ⟨349231219874384619711887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232820813249589746474591 349231219874384619711887)
    ·
      refine ⟨523846829811576929567831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349231219874384619711887 523846829811576929567831)
      ·
        refine ⟨785770244717365394351747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523846829811576929567831 785770244717365394351747)
        ·
          refine ⟨1178655367076048091527621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785770244717365394351747 1178655367076048091527621)
          ·
            refine ⟨220997881326759017161429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1178655367076048091527621 220997881326759017161429)
            ·
              refine ⟨5179637843595914464721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220997881326759017161429 5179637843595914464721)
              ·
                rfl

theorem cell20_102134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_102134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102134 prefixEnd_102134 := by exact prefixLift 102134
  have htrace : WordTrace (prefixWord ++ tailWord_102134) baseStart_102134 baseEnd_102134 := by
    simpa [prefixWord, tailWord_102134, baseEnd_102134] using wordTrace_append hprefix tailTrace_102134
  have hstable : (prefixWord ++ tailWord_102134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102134).length < 2 ^ (prefixWord ++ tailWord_102134).sum := by decide
  have hdescent : baseEnd_102134 < baseStart_102134 := by decide
  rcases family_descends (prefixWord ++ tailWord_102134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102141 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_102141 : Nat := 118140960795 + 102141 * 2 ^ 59
def prefixEnd_102141 : Nat := 4983230072969 + 3 ^ 40 * 102141 * 2
def baseEnd_102141 : Nat := 46619935583102316949127

theorem tailTrace_102141 : CollatzResearch.WordTrace tailWord_102141 prefixEnd_102141 46619935583102316949127 := by
  unfold tailWord_102141
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725388322968076139098277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2483592215312050759398851 3725388322968076139098277)
  ·
    refine ⟨698510310556514276080927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3725388322968076139098277 698510310556514276080927)
    ·
      refine ⟨1047765465834771414121391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698510310556514276080927 1047765465834771414121391)
      ·
        refine ⟨1571648198752157121182087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047765465834771414121391 1571648198752157121182087)
        ·
          refine ⟨2357472298128235681773131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571648198752157121182087 2357472298128235681773131)
          ·
            refine ⟨3536208447192353522659697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357472298128235681773131 3536208447192353522659697)
            ·
              refine ⟨2652156335394265141994773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536208447192353522659697 2652156335394265141994773)
              ·
                refine ⟨124319828221606178531005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2652156335394265141994773 124319828221606178531005)
                ·
                  refine ⟨46619935583102316949127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124319828221606178531005 46619935583102316949127)
                  ·
                    rfl

theorem cell20_102141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_102141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102141 prefixEnd_102141 := by exact prefixLift 102141
  have htrace : WordTrace (prefixWord ++ tailWord_102141) baseStart_102141 baseEnd_102141 := by
    simpa [prefixWord, tailWord_102141, baseEnd_102141] using wordTrace_append hprefix tailTrace_102141
  have hstable : (prefixWord ++ tailWord_102141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102141).length < 2 ^ (prefixWord ++ tailWord_102141).sum := by decide
  have hdescent : baseEnd_102141 < baseStart_102141 := by decide
  rcases family_descends (prefixWord ++ tailWord_102141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102164 : List Nat := [2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_102164 : Nat := 118140960795 + 102164 * 2 ^ 59
def prefixEnd_102164 : Nat := 4983230072969 + 3 ^ 40 * 102164 * 2
def baseEnd_102164 : Nat := 15543477803272153060789

theorem tailTrace_102164 : CollatzResearch.WordTrace tailWord_102164 prefixEnd_102164 15543477803272153060789 := by
  unfold tailWord_102164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863113600942375533592773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2484151467923167378123697 1863113600942375533592773)
  ·
    refine ⟨349333800176695412548645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1863113600942375533592773 349333800176695412548645)
    ·
      refine ⟨65500087533130389852871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349333800176695412548645 65500087533130389852871)
      ·
        refine ⟨98250131299695584779307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65500087533130389852871 98250131299695584779307)
        ·
          refine ⟨147375196949543377168961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98250131299695584779307 147375196949543377168961)
          ·
            refine ⟨110531397712157532876721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147375196949543377168961 110531397712157532876721)
            ·
              refine ⟨82898548284118149657541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110531397712157532876721 82898548284118149657541)
              ·
                refine ⟨15543477803272153060789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82898548284118149657541 15543477803272153060789)
                ·
                  rfl

theorem cell20_102164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_102164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102164 prefixEnd_102164 := by exact prefixLift 102164
  have htrace : WordTrace (prefixWord ++ tailWord_102164) baseStart_102164 baseEnd_102164 := by
    simpa [prefixWord, tailWord_102164, baseEnd_102164] using wordTrace_append hprefix tailTrace_102164
  have hstable : (prefixWord ++ tailWord_102164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102164).length < 2 ^ (prefixWord ++ tailWord_102164).sum := by decide
  have hdescent : baseEnd_102164 < baseStart_102164 := by decide
  rcases family_descends (prefixWord ++ tailWord_102164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
