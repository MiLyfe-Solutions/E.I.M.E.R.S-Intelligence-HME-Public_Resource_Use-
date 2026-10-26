import V185TrunkScan23Chunk1270

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7530293 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 6]
def baseStart_7530293 : Nat := 118140960795 + 7530293 * 2 ^ 59
def prefixEnd_7530293 : Nat := 4983230072969 + 3 ^ 40 * 7530293 * 2
def baseEnd_7530293 : Nat := 429628864243045714189591

theorem tailTrace_7530293 : CollatzResearch.WordTrace tailWord_7530293 prefixEnd_7530293 429628864243045714189591 := by
  unfold tailWord_7530293
  simp only [CollatzResearch.WordTrace]
  refine ⟨274652349308042007500115533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183101566205361338333410355 274652349308042007500115533)
  ·
    refine ⟨102994630990515752812543325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274652349308042007500115533 102994630990515752812543325)
    ·
      refine ⟨38622986621443407304703747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102994630990515752812543325 38622986621443407304703747)
      ·
        refine ⟨57934479932165110957055621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38622986621443407304703747 57934479932165110957055621)
        ·
          refine ⟨10862714987280958304447929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57934479932165110957055621 10862714987280958304447929)
          ·
            refine ⟨8147036240460718728335947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10862714987280958304447929 8147036240460718728335947)
            ·
              refine ⟨12220554360691078092503921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147036240460718728335947 12220554360691078092503921)
              ·
                refine ⟨9165415770518308569377941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220554360691078092503921 9165415770518308569377941)
                ·
                  refine ⟨429628864243045714189591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9165415770518308569377941 429628864243045714189591)
                  ·
                    rfl

theorem cell23_7530293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_7530293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530293 prefixEnd_7530293 := by exact prefixLift 7530293
  have htrace : WordTrace (prefixWord ++ tailWord_7530293) baseStart_7530293 baseEnd_7530293 := by
    simpa [prefixWord, tailWord_7530293, baseEnd_7530293] using wordTrace_append hprefix tailTrace_7530293
  have hstable : (prefixWord ++ tailWord_7530293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530293).length < 2 ^ (prefixWord ++ tailWord_7530293).sum := by decide
  have hdescent : baseEnd_7530293 < baseStart_7530293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530329 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_7530329 : Nat := 118140960795 + 7530329 * 2 ^ 59
def prefixEnd_7530329 : Nat := 4983230072969 + 3 ^ 40 * 7530329 * 2
def baseEnd_7530329 : Nat := 3866678263490973286856153

theorem tailTrace_7530329 : CollatzResearch.WordTrace tailWord_7530329 prefixEnd_7530329 3866678263490973286856153 := by
  unfold tailWord_7530329
  simp only [CollatzResearch.WordTrace]
  refine ⟨274653662335911585648426041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183102441557274390432284027 274653662335911585648426041)
  ·
    refine ⟨205990246751933689236319531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274653662335911585648426041 205990246751933689236319531)
    ·
      refine ⟨308985370127900533854479297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205990246751933689236319531 308985370127900533854479297)
      ·
        refine ⟨231739027595925400390859473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308985370127900533854479297 231739027595925400390859473)
        ·
          refine ⟨173804270696944050293144605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231739027595925400390859473 173804270696944050293144605)
          ·
            refine ⟨65176601511354018859929227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173804270696944050293144605 65176601511354018859929227)
            ·
              refine ⟨97764902267031028289893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65176601511354018859929227 97764902267031028289893841)
              ·
                refine ⟨73323676700273271217420381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97764902267031028289893841 73323676700273271217420381)
                ·
                  refine ⟨27496378762602476706532643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73323676700273271217420381 27496378762602476706532643)
                  ·
                    refine ⟨41244568143903715059798965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27496378762602476706532643 41244568143903715059798965)
                    ·
                      refine ⟨3866678263490973286856153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41244568143903715059798965 3866678263490973286856153)
                      ·
                        rfl

theorem cell23_7530329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_7530329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530329 prefixEnd_7530329 := by exact prefixLift 7530329
  have htrace : WordTrace (prefixWord ++ tailWord_7530329) baseStart_7530329 baseEnd_7530329 := by
    simpa [prefixWord, tailWord_7530329, baseEnd_7530329] using wordTrace_append hprefix tailTrace_7530329
  have hstable : (prefixWord ++ tailWord_7530329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530329).length < 2 ^ (prefixWord ++ tailWord_7530329).sum := by decide
  have hdescent : baseEnd_7530329 < baseStart_7530329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530336 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_7530336 : Nat := 118140960795 + 7530336 * 2 ^ 59
def prefixEnd_7530336 : Nat := 4983230072969 + 3 ^ 40 * 7530336 * 2
def baseEnd_7530336 : Nat := 1288893952618518253156207

theorem tailTrace_7530336 : CollatzResearch.WordTrace tailWord_7530336 prefixEnd_7530336 1288893952618518253156207 := by
  unfold tailWord_7530336
  simp only [CollatzResearch.WordTrace]
  refine ⟨137326958823443112921965431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183102611764590817229287241 137326958823443112921965431)
  ·
    refine ⟨205990438235164669382948147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137326958823443112921965431 205990438235164669382948147)
    ·
      refine ⟨308985657352747004074422221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205990438235164669382948147 308985657352747004074422221)
      ·
        refine ⟨115869621507280126527908333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308985657352747004074422221 115869621507280126527908333)
        ·
          refine ⟨43451108065230047447965625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115869621507280126527908333 43451108065230047447965625)
          ·
            refine ⟨32588331048922535585974219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43451108065230047447965625 32588331048922535585974219)
            ·
              refine ⟨48882496573383803378961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32588331048922535585974219 48882496573383803378961329)
              ·
                refine ⟨36661872430037852534220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48882496573383803378961329 36661872430037852534220997)
                ·
                  refine ⟨6874101080632097350166437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36661872430037852534220997 6874101080632097350166437)
                  ·
                    refine ⟨1288893952618518253156207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874101080632097350166437 1288893952618518253156207)
                    ·
                      rfl

theorem cell23_7530336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_7530336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530336 prefixEnd_7530336 := by exact prefixLift 7530336
  have htrace : WordTrace (prefixWord ++ tailWord_7530336) baseStart_7530336 baseEnd_7530336 := by
    simpa [prefixWord, tailWord_7530336, baseEnd_7530336] using wordTrace_append hprefix tailTrace_7530336
  have hstable : (prefixWord ++ tailWord_7530336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530336).length < 2 ^ (prefixWord ++ tailWord_7530336).sum := by decide
  have hdescent : baseEnd_7530336 < baseStart_7530336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530349 : List Nat := [1, 5, 1, 1, 1, 1, 13]
def baseStart_7530349 : Nat := 118140960795 + 7530349 * 2 ^ 59
def prefixEnd_7530349 : Nat := 4983230072969 + 3 ^ 40 * 7530349 * 2
def baseEnd_7530349 : Nat := 47736895470420533439581

theorem tailTrace_7530349 : CollatzResearch.WordTrace tailWord_7530349 prefixEnd_7530349 47736895470420533439581 := by
  unfold tailWord_7530349
  simp only [CollatzResearch.WordTrace]
  refine ⟨274654391795839129064154101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183102927863892752709436067 274654391795839129064154101)
  ·
    refine ⟨25748849230859918349764447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274654391795839129064154101 25748849230859918349764447)
    ·
      refine ⟨38623273846289877524646671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25748849230859918349764447 38623273846289877524646671)
      ·
        refine ⟨57934910769434816286970007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38623273846289877524646671 57934910769434816286970007)
        ·
          refine ⟨86902366154152224430455011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57934910769434816286970007 86902366154152224430455011)
          ·
            refine ⟨130353549231228336645682517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86902366154152224430455011 130353549231228336645682517)
            ·
              refine ⟨47736895470420533439581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 130353549231228336645682517 47736895470420533439581)
              ·
                rfl

theorem cell23_7530349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 13].length) (baseStart_7530349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530349 prefixEnd_7530349 := by exact prefixLift 7530349
  have htrace : WordTrace (prefixWord ++ tailWord_7530349) baseStart_7530349 baseEnd_7530349 := by
    simpa [prefixWord, tailWord_7530349, baseEnd_7530349] using wordTrace_append hprefix tailTrace_7530349
  have hstable : (prefixWord ++ tailWord_7530349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530349).length < 2 ^ (prefixWord ++ tailWord_7530349).sum := by decide
  have hdescent : baseEnd_7530349 < baseStart_7530349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530446 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7530446 : Nat := 118140960795 + 7530446 * 2 ^ 59
def prefixEnd_7530446 : Nat := 4983230072969 + 3 ^ 40 * 7530446 * 2
def baseEnd_7530446 : Nat := 3866738340727549329093115

theorem tailTrace_7530446 : CollatzResearch.WordTrace tailWord_7530446 prefixEnd_7530446 3866738340727549329093115 := by
  unfold tailWord_7530446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34332241209560964328804399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183105286450991809753623461 34332241209560964328804399)
  ·
    refine ⟨51498361814341446493206599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34332241209560964328804399 51498361814341446493206599)
    ·
      refine ⟨77247542721512169739809899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51498361814341446493206599 77247542721512169739809899)
      ·
        refine ⟨115871314082268254609714849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77247542721512169739809899 115871314082268254609714849)
        ·
          refine ⟨86903485561701190957286137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115871314082268254609714849 86903485561701190957286137)
          ·
            refine ⟨65177614171275893217964603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86903485561701190957286137 65177614171275893217964603)
            ·
              refine ⟨97766421256913839826946905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65177614171275893217964603 97766421256913839826946905)
              ·
                refine ⟨73324815942685379870210179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97766421256913839826946905 73324815942685379870210179)
                ·
                  refine ⟨109987223914028069805315269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73324815942685379870210179 109987223914028069805315269)
                  ·
                    refine ⟨20622604483880263088496613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109987223914028069805315269 20622604483880263088496613)
                    ·
                      refine ⟨3866738340727549329093115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20622604483880263088496613 3866738340727549329093115)
                      ·
                        rfl

theorem cell23_7530446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7530446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530446 prefixEnd_7530446 := by exact prefixLift 7530446
  have htrace : WordTrace (prefixWord ++ tailWord_7530446) baseStart_7530446 baseEnd_7530446 := by
    simpa [prefixWord, tailWord_7530446, baseEnd_7530446] using wordTrace_append hprefix tailTrace_7530446
  have hstable : (prefixWord ++ tailWord_7530446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530446).length < 2 ^ (prefixWord ++ tailWord_7530446).sum := by decide
  have hdescent : baseEnd_7530446 < baseStart_7530446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530454 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7530454 : Nat := 118140960795 + 7530454 * 2 ^ 59
def prefixEnd_7530454 : Nat := 4983230072969 + 3 ^ 40 * 7530454 * 2
def baseEnd_7530454 : Nat := 3866742448572785297793079

theorem tailTrace_7530454 : CollatzResearch.WordTrace tailWord_7530454 prefixEnd_7530454 3866742448572785297793079 := by
  unfold tailWord_7530454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166138841278670749795401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183105480973639154664484277 17166138841278670749795401)
  ·
    refine ⟨12874604130959003062346551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17166138841278670749795401 12874604130959003062346551)
    ·
      refine ⟨19311906196438504593519827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874604130959003062346551 19311906196438504593519827)
      ·
        refine ⟨28967859294657756890279741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19311906196438504593519827 28967859294657756890279741)
        ·
          refine ⟨10862947235496658833854903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28967859294657756890279741 10862947235496658833854903)
          ·
            refine ⟨16294420853244988250782355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862947235496658833854903 16294420853244988250782355)
            ·
              refine ⟨24441631279867482376173533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294420853244988250782355 24441631279867482376173533)
              ·
                refine ⟨9165611729950305891065075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24441631279867482376173533 9165611729950305891065075)
                ·
                  refine ⟨13748417594925458836597613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165611729950305891065075 13748417594925458836597613)
                  ·
                    refine ⟨5155656598097047063724105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13748417594925458836597613 5155656598097047063724105)
                    ·
                      refine ⟨3866742448572785297793079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155656598097047063724105 3866742448572785297793079)
                      ·
                        rfl

theorem cell23_7530454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7530454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530454 prefixEnd_7530454 := by exact prefixLift 7530454
  have htrace : WordTrace (prefixWord ++ tailWord_7530454) baseStart_7530454 baseEnd_7530454 := by
    simpa [prefixWord, tailWord_7530454, baseEnd_7530454] using wordTrace_append hprefix tailTrace_7530454
  have hstable : (prefixWord ++ tailWord_7530454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530454).length < 2 ^ (prefixWord ++ tailWord_7530454).sum := by decide
  have hdescent : baseEnd_7530454 < baseStart_7530454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530467 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7530467 : Nat := 118140960795 + 7530467 * 2 ^ 59
def prefixEnd_7530467 : Nat := 4983230072969 + 3 ^ 40 * 7530467 * 2
def baseEnd_7530467 : Nat := 3866749123821293746930519

theorem tailTrace_7530467 : CollatzResearch.WordTrace tailWord_7530467 prefixEnd_7530467 3866749123821293746930519 := by
  unfold tailWord_7530467
  simp only [CollatzResearch.WordTrace]
  refine ⟨274658695609411635216949655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183105797072941090144633103 274658695609411635216949655)
  ·
    refine ⟨411988043414117452825424483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274658695609411635216949655 411988043414117452825424483)
    ·
      refine ⟨617982065121176179238136725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411988043414117452825424483 617982065121176179238136725)
      ·
        refine ⟨28967909302555133401787659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 617982065121176179238136725 28967909302555133401787659)
        ·
          refine ⟨43451863953832700102681489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28967909302555133401787659 43451863953832700102681489)
          ·
            refine ⟨32588897965374525077011117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43451863953832700102681489 32588897965374525077011117)
            ·
              refine ⟨12220836737015446903879169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32588897965374525077011117 12220836737015446903879169)
              ·
                refine ⟨9165627552761585177909377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220836737015446903879169 9165627552761585177909377)
                ·
                  refine ⟨6874220664571188883432033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165627552761585177909377 6874220664571188883432033)
                  ·
                    refine ⟨5155665498428391662574025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874220664571188883432033 5155665498428391662574025)
                    ·
                      refine ⟨3866749123821293746930519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155665498428391662574025 3866749123821293746930519)
                      ·
                        rfl

theorem cell23_7530467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7530467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530467 prefixEnd_7530467 := by exact prefixLift 7530467
  have htrace : WordTrace (prefixWord ++ tailWord_7530467) baseStart_7530467 baseEnd_7530467 := by
    simpa [prefixWord, tailWord_7530467, baseEnd_7530467] using wordTrace_append hprefix tailTrace_7530467
  have hstable : (prefixWord ++ tailWord_7530467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530467).length < 2 ^ (prefixWord ++ tailWord_7530467).sum := by decide
  have hdescent : baseEnd_7530467 < baseStart_7530467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530493 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_7530493 : Nat := 118140960795 + 7530493 * 2 ^ 59
def prefixEnd_7530493 : Nat := 4983230072969 + 3 ^ 40 * 7530493 * 2
def baseEnd_7530493 : Nat := 3866762474318310645205399

theorem tailTrace_7530493 : CollatzResearch.WordTrace tailWord_7530493 prefixEnd_7530493 3866762474318310645205399 := by
  unfold tailWord_7530493
  simp only [CollatzResearch.WordTrace]
  refine ⟨274659643907317441657396133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183106429271544961104930755 274659643907317441657396133)
  ·
    refine ⟨51498683232622020310761775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274659643907317441657396133 51498683232622020310761775)
    ·
      refine ⟨77248024848933030466142663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51498683232622020310761775 77248024848933030466142663)
      ·
        refine ⟨115872037273399545699213995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77248024848933030466142663 115872037273399545699213995)
        ·
          refine ⟨173808055910099318548820993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115872037273399545699213995 173808055910099318548820993)
          ·
            refine ⟨130356041932574488911615745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173808055910099318548820993 130356041932574488911615745)
            ·
              refine ⟨97767031449430866683711809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130356041932574488911615745 97767031449430866683711809)
              ·
                refine ⟨73325273587073150012783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97767031449430866683711809 73325273587073150012783857)
                ·
                  refine ⟨54993955190304862509587893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73325273587073150012783857 54993955190304862509587893)
                  ·
                    refine ⟨5155683299091080860273865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54993955190304862509587893 5155683299091080860273865)
                    ·
                      refine ⟨3866762474318310645205399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155683299091080860273865 3866762474318310645205399)
                      ·
                        rfl

theorem cell23_7530493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_7530493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530493 prefixEnd_7530493 := by exact prefixLift 7530493
  have htrace : WordTrace (prefixWord ++ tailWord_7530493) baseStart_7530493 baseEnd_7530493 := by
    simpa [prefixWord, tailWord_7530493, baseEnd_7530493] using wordTrace_append hprefix tailTrace_7530493
  have hstable : (prefixWord ++ tailWord_7530493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530493).length < 2 ^ (prefixWord ++ tailWord_7530493).sum := by decide
  have hdescent : baseEnd_7530493 < baseStart_7530493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530523 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 4, 2]
def baseStart_7530523 : Nat := 118140960795 + 7530523 * 2 ^ 59
def prefixEnd_7530523 : Nat := 4983230072969 + 3 ^ 40 * 7530523 * 2
def baseEnd_7530523 : Nat := 3866777878737945527830261

theorem tailTrace_7530523 : CollatzResearch.WordTrace tailWord_7530523 prefixEnd_7530523 3866777878737945527830261 := by
  unfold tailWord_7530523
  simp only [CollatzResearch.WordTrace]
  refine ⟨274660738097208756780988223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183107158731472504520658815 274660738097208756780988223)
  ·
    refine ⟨411991107145813135171482335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274660738097208756780988223 411991107145813135171482335)
    ·
      refine ⟨617986660718719702757223503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411991107145813135171482335 617986660718719702757223503)
      ·
        refine ⟨926979991078079554135835255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617986660718719702757223503 926979991078079554135835255)
        ·
          refine ⟨1390469986617119331203752883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926979991078079554135835255 1390469986617119331203752883)
          ·
            refine ⟨2085704979925678996805629325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390469986617119331203752883 2085704979925678996805629325)
            ·
              refine ⟨782139367472129623802110997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085704979925678996805629325 782139367472129623802110997)
              ·
                refine ⟨36662782850256076115723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 782139367472129623802110997 36662782850256076115723953)
                ·
                  refine ⟨27497087137692057086792965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36662782850256076115723953 27497087137692057086792965)
                  ·
                    refine ⟨5155703838317260703773681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27497087137692057086792965 5155703838317260703773681)
                    ·
                      refine ⟨3866777878737945527830261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155703838317260703773681 3866777878737945527830261)
                      ·
                        rfl

theorem cell23_7530523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4, 2].length) (baseStart_7530523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530523 prefixEnd_7530523 := by exact prefixLift 7530523
  have htrace : WordTrace (prefixWord ++ tailWord_7530523) baseStart_7530523 baseEnd_7530523 := by
    simpa [prefixWord, tailWord_7530523, baseEnd_7530523] using wordTrace_append hprefix tailTrace_7530523
  have hstable : (prefixWord ++ tailWord_7530523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530523).length < 2 ^ (prefixWord ++ tailWord_7530523).sum := by decide
  have hdescent : baseEnd_7530523 < baseStart_7530523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530550 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7530550 : Nat := 118140960795 + 7530550 * 2 ^ 59
def prefixEnd_7530550 : Nat := 4983230072969 + 3 ^ 40 * 7530550 * 2
def baseEnd_7530550 : Nat := 1288930580905205640730879

theorem tailTrace_7530550 : CollatzResearch.WordTrace tailWord_7530550 prefixEnd_7530550 1288930580905205640730879 := by
  unfold tailWord_7530550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166357679256933774513819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183107815245407293594814069 17166357679256933774513819)
  ·
    refine ⟨25749536518885400661770729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166357679256933774513819 25749536518885400661770729)
    ·
      refine ⟨19312152389164050496328047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25749536518885400661770729 19312152389164050496328047)
      ·
        refine ⟨28968228583746075744492071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19312152389164050496328047 28968228583746075744492071)
        ·
          refine ⟨43452342875619113616738107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28968228583746075744492071 43452342875619113616738107)
          ·
            refine ⟨65178514313428670425107161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43452342875619113616738107 65178514313428670425107161)
            ·
              refine ⟨48883885735071502818830371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65178514313428670425107161 48883885735071502818830371)
              ·
                refine ⟨73325828602607254228245557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48883885735071502818830371 73325828602607254228245557)
                ·
                  refine ⟨6874296431494430083898021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73325828602607254228245557 6874296431494430083898021)
                  ·
                    refine ⟨1288930580905205640730879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874296431494430083898021 1288930580905205640730879)
                    ·
                      rfl

theorem cell23_7530550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7530550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530550 prefixEnd_7530550 := by exact prefixLift 7530550
  have htrace : WordTrace (prefixWord ++ tailWord_7530550) baseStart_7530550 baseEnd_7530550 := by
    simpa [prefixWord, tailWord_7530550, baseEnd_7530550] using wordTrace_append hprefix tailTrace_7530550
  have hstable : (prefixWord ++ tailWord_7530550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530550).length < 2 ^ (prefixWord ++ tailWord_7530550).sum := by decide
  have hdescent : baseEnd_7530550 < baseStart_7530550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530560 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_7530560 : Nat := 118140960795 + 7530560 * 2 ^ 59
def prefixEnd_7530560 : Nat := 4983230072969 + 3 ^ 40 * 7530560 * 2
def baseEnd_7530560 : Nat := 3866796877522161883067591

theorem tailTrace_7530560 : CollatzResearch.WordTrace tailWord_7530560 prefixEnd_7530560 3866796877522161883067591 := by
  unfold tailWord_7530560
  simp only [CollatzResearch.WordTrace]
  refine ⟨137331043799037356050042567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183108058398716474733390089 137331043799037356050042567)
  ·
    refine ⟨205996565698556034075063851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137331043799037356050042567 205996565698556034075063851)
    ·
      refine ⟨308994848547834051112595777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205996565698556034075063851 308994848547834051112595777)
      ·
        refine ⟨231746136410875538334446833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308994848547834051112595777 231746136410875538334446833)
        ·
          refine ⟨173809602308156653750835125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231746136410875538334446833 173809602308156653750835125)
          ·
            refine ⟨16294650216389686289140793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173809602308156653750835125 16294650216389686289140793)
            ·
              refine ⟨12220987662292264716855595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16294650216389686289140793 12220987662292264716855595)
              ·
                refine ⟨18331481493438397075283393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220987662292264716855595 18331481493438397075283393)
                ·
                  refine ⟨13748611120078797806462545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18331481493438397075283393 13748611120078797806462545)
                  ·
                    refine ⟨10311458340059098354846909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13748611120078797806462545 10311458340059098354846909)
                    ·
                      refine ⟨3866796877522161883067591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311458340059098354846909 3866796877522161883067591)
                      ·
                        rfl

theorem cell23_7530560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_7530560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530560 prefixEnd_7530560 := by exact prefixLift 7530560
  have htrace : WordTrace (prefixWord ++ tailWord_7530560) baseStart_7530560 baseEnd_7530560 := by
    simpa [prefixWord, tailWord_7530560, baseEnd_7530560] using wordTrace_append hprefix tailTrace_7530560
  have hstable : (prefixWord ++ tailWord_7530560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530560).length < 2 ^ (prefixWord ++ tailWord_7530560).sum := by decide
  have hdescent : baseEnd_7530560 < baseStart_7530560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530584 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 1, 4]
def baseStart_7530584 : Nat := 118140960795 + 7530584 * 2 ^ 59
def prefixEnd_7530584 : Nat := 4983230072969 + 3 ^ 40 * 7530584 * 2
def baseEnd_7530584 : Nat := 1288936400352623263055827

theorem tailTrace_7530584 : CollatzResearch.WordTrace tailWord_7530584 prefixEnd_7530584 1288936400352623263055827 := by
  unfold tailWord_7530584
  simp only [CollatzResearch.WordTrace]
  refine ⟨137331481474993882099479403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183108641966658509465972537 137331481474993882099479403)
  ·
    refine ⟨205997222212490823149219105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137331481474993882099479403 205997222212490823149219105)
    ·
      refine ⟨154497916659368117361914329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205997222212490823149219105 154497916659368117361914329)
      ·
        refine ⟨115873437494526088021435747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154497916659368117361914329 115873437494526088021435747)
        ·
          refine ⟨173810156241789132032153621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115873437494526088021435747 173810156241789132032153621)
          ·
            refine ⟨8147351073833865564007201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173810156241789132032153621 8147351073833865564007201)
            ·
              refine ⟨6110513305375399173005401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8147351073833865564007201 6110513305375399173005401)
              ·
                refine ⟨4582884979031549379754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110513305375399173005401 4582884979031549379754051)
                ·
                  refine ⟨6874327468547324069631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582884979031549379754051 6874327468547324069631077)
                  ·
                    refine ⟨1288936400352623263055827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874327468547324069631077 1288936400352623263055827)
                    ·
                      rfl

theorem cell23_7530584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_7530584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530584 prefixEnd_7530584 := by exact prefixLift 7530584
  have htrace : WordTrace (prefixWord ++ tailWord_7530584) baseStart_7530584 baseEnd_7530584 := by
    simpa [prefixWord, tailWord_7530584, baseEnd_7530584] using wordTrace_append hprefix tailTrace_7530584
  have hstable : (prefixWord ++ tailWord_7530584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530584).length < 2 ^ (prefixWord ++ tailWord_7530584).sum := by decide
  have hdescent : baseEnd_7530584 < baseStart_7530584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530617 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7530617 : Nat := 118140960795 + 7530617 * 2 ^ 59
def prefixEnd_7530617 : Nat := 4983230072969 + 3 ^ 40 * 7530617 * 2
def baseEnd_7530617 : Nat := 3866826145919468160054829

theorem tailTrace_7530617 : CollatzResearch.WordTrace tailWord_7530617 prefixEnd_7530617 3866826145919468160054829 := by
  unfold tailWord_7530617
  simp only [CollatzResearch.WordTrace]
  refine ⟨274664166558868210834910105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183109444372578807223273403 274664166558868210834910105)
  ·
    refine ⟨205998124919151158126182579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274664166558868210834910105 205998124919151158126182579)
    ·
      refine ⟨308997187378726737189273869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205998124919151158126182579 308997187378726737189273869)
      ·
        refine ⟨115873945267022526445977701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308997187378726737189273869 115873945267022526445977701)
        ·
          refine ⟨21726364737566723708620819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115873945267022526445977701 21726364737566723708620819)
          ·
            refine ⟨32589547106350085562931229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21726364737566723708620819 32589547106350085562931229)
            ·
              refine ⟨12221080164881282086099211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32589547106350085562931229 12221080164881282086099211)
              ·
                refine ⟨18331620247321923129148817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12221080164881282086099211 18331620247321923129148817)
                ·
                  refine ⟨13748715185491442346861613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18331620247321923129148817 13748715185491442346861613)
                  ·
                    refine ⟨5155768194559290880073105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13748715185491442346861613 5155768194559290880073105)
                    ·
                      refine ⟨3866826145919468160054829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155768194559290880073105 3866826145919468160054829)
                      ·
                        rfl

theorem cell23_7530617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7530617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530617 prefixEnd_7530617 := by exact prefixLift 7530617
  have htrace : WordTrace (prefixWord ++ tailWord_7530617) baseStart_7530617 baseEnd_7530617 := by
    simpa [prefixWord, tailWord_7530617, baseEnd_7530617] using wordTrace_append hprefix tailTrace_7530617
  have hstable : (prefixWord ++ tailWord_7530617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530617).length < 2 ^ (prefixWord ++ tailWord_7530617).sum := by decide
  have hdescent : baseEnd_7530617 < baseStart_7530617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530627 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 1, 5]
def baseStart_7530627 : Nat := 118140960795 + 7530627 * 2 ^ 59
def prefixEnd_7530627 : Nat := 4983230072969 + 3 ^ 40 * 7530627 * 2
def baseEnd_7530627 : Nat := 1288943760242004373643261

theorem tailTrace_7530627 : CollatzResearch.WordTrace tailWord_7530627 prefixEnd_7530627 1288943760242004373643261 := by
  unfold tailWord_7530627
  simp only [CollatzResearch.WordTrace]
  refine ⟨274664531288831982542774135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183109687525887988361849423 274664531288831982542774135)
  ·
    refine ⟨411996796933247973814161203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274664531288831982542774135 411996796933247973814161203)
    ·
      refine ⟨617995195399871960721241805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411996796933247973814161203 617995195399871960721241805)
      ·
        refine ⟨231748198274951985270465677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617995195399871960721241805 231748198274951985270465677)
        ·
          refine ⟨86905574353106994476424629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231748198274951985270465677 86905574353106994476424629)
          ·
            refine ⟨8147397595603780732164809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86905574353106994476424629 8147397595603780732164809)
            ·
              refine ⟨6110548196702835549123607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8147397595603780732164809 6110548196702835549123607)
              ·
                refine ⟨9165822295054253323685411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110548196702835549123607 9165822295054253323685411)
                ·
                  refine ⟨13748733442581379985528117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165822295054253323685411 13748733442581379985528117)
                  ·
                    refine ⟨1288943760242004373643261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13748733442581379985528117 1288943760242004373643261)
                    ·
                      rfl

theorem cell23_7530627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 5].length) (baseStart_7530627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530627 prefixEnd_7530627 := by exact prefixLift 7530627
  have htrace : WordTrace (prefixWord ++ tailWord_7530627) baseStart_7530627 baseEnd_7530627 := by
    simpa [prefixWord, tailWord_7530627, baseEnd_7530627] using wordTrace_append hprefix tailTrace_7530627
  have hstable : (prefixWord ++ tailWord_7530627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530627).length < 2 ^ (prefixWord ++ tailWord_7530627).sum := by decide
  have hdescent : baseEnd_7530627 < baseStart_7530627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530633 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_7530633 : Nat := 118140960795 + 7530633 * 2 ^ 59
def prefixEnd_7530633 : Nat := 4983230072969 + 3 ^ 40 * 7530633 * 2
def baseEnd_7530633 : Nat := 3866834361609940097454755

theorem tailTrace_7530633 : CollatzResearch.WordTrace tailWord_7530633 prefixEnd_7530633 3866834361609940097454755 := by
  unfold tailWord_7530633
  simp only [CollatzResearch.WordTrace]
  refine ⟨274664750126810245567492553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183109833417873497044995035 274664750126810245567492553)
  ·
    refine ⟨205998562595107684175619415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274664750126810245567492553 205998562595107684175619415)
    ·
      refine ⟨308997843892661526263429123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205998562595107684175619415 308997843892661526263429123)
      ·
        refine ⟨463496765838992289395143685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308997843892661526263429123 463496765838992289395143685)
        ·
          refine ⟨86905643594811054261589441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463496765838992289395143685 86905643594811054261589441)
          ·
            refine ⟨65179232696108290696192081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86905643594811054261589441 65179232696108290696192081)
            ·
              refine ⟨48884424522081218022144061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65179232696108290696192081 48884424522081218022144061)
              ·
                refine ⟨18331659195780456758304023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48884424522081218022144061 18331659195780456758304023)
                ·
                  refine ⟨27497488793670685137456035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18331659195780456758304023 27497488793670685137456035)
                  ·
                    refine ⟨41246233190506027706184053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27497488793670685137456035 41246233190506027706184053)
                    ·
                      refine ⟨3866834361609940097454755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41246233190506027706184053 3866834361609940097454755)
                      ·
                        rfl

theorem cell23_7530633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_7530633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530633 prefixEnd_7530633 := by exact prefixLift 7530633
  have htrace : WordTrace (prefixWord ++ tailWord_7530633) baseStart_7530633 baseEnd_7530633 := by
    simpa [prefixWord, tailWord_7530633, baseEnd_7530633] using wordTrace_append hprefix tailTrace_7530633
  have hstable : (prefixWord ++ tailWord_7530633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530633).length < 2 ^ (prefixWord ++ tailWord_7530633).sum := by decide
  have hdescent : baseEnd_7530633 < baseStart_7530633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530660 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_7530660 : Nat := 118140960795 + 7530660 * 2 ^ 59
def prefixEnd_7530660 : Nat := 4983230072969 + 3 ^ 40 * 7530660 * 2
def baseEnd_7530660 : Nat := 3866848225587611491817131

theorem tailTrace_7530660 : CollatzResearch.WordTrace tailWord_7530660 prefixEnd_7530660 3866848225587611491817131 := by
  unfold tailWord_7530660
  simp only [CollatzResearch.WordTrace]
  refine ⟨137332867448856214589362717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183110489931808286119150289 137332867448856214589362717)
  ·
    refine ⟨51499825293321080471011019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137332867448856214589362717 51499825293321080471011019)
    ·
      refine ⟨77249737939981620706516529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51499825293321080471011019 77249737939981620706516529)
      ·
        refine ⟨57937303454986215529887397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77249737939981620706516529 57937303454986215529887397)
        ·
          refine ⟨10863244397809915411853887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57937303454986215529887397 10863244397809915411853887)
          ·
            refine ⟨16294866596714873117780831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863244397809915411853887 16294866596714873117780831)
            ·
              refine ⟨24442299895072309676671247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294866596714873117780831 24442299895072309676671247)
              ·
                refine ⟨36663449842608464515006871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24442299895072309676671247 36663449842608464515006871)
                ·
                  refine ⟨54995174763912696772510307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36663449842608464515006871 54995174763912696772510307)
                  ·
                    refine ⟨82492762145869045158765461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54995174763912696772510307 82492762145869045158765461)
                    ·
                      refine ⟨3866848225587611491817131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82492762145869045158765461 3866848225587611491817131)
                      ·
                        rfl

theorem cell23_7530660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_7530660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530660 prefixEnd_7530660 := by exact prefixLift 7530660
  have htrace : WordTrace (prefixWord ++ tailWord_7530660) baseStart_7530660 baseEnd_7530660 := by
    simpa [prefixWord, tailWord_7530660, baseEnd_7530660] using wordTrace_append hprefix tailTrace_7530660
  have hstable : (prefixWord ++ tailWord_7530660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530660).length < 2 ^ (prefixWord ++ tailWord_7530660).sum := by decide
  have hdescent : baseEnd_7530660 < baseStart_7530660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530680 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_7530680 : Nat := 118140960795 + 7530680 * 2 ^ 59
def prefixEnd_7530680 : Nat := 4983230072969 + 3 ^ 40 * 7530680 * 2
def baseEnd_7530680 : Nat := 3866858495200701413567039

theorem tailTrace_7530680 : CollatzResearch.WordTrace tailWord_7530680 prefixEnd_7530680 3866858495200701413567039 := by
  unfold tailWord_7530680
  simp only [CollatzResearch.WordTrace]
  refine ⟨137333232178819986297226747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183110976238426648396302329 137333232178819986297226747)
  ·
    refine ⟨205999848268229979445840121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137333232178819986297226747 205999848268229979445840121)
    ·
      refine ⟨154499886201172484584380091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205999848268229979445840121 154499886201172484584380091)
      ·
        refine ⟨231749829301758726876570137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154499886201172484584380091 231749829301758726876570137)
        ·
          refine ⟨173812371976319045157427603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231749829301758726876570137 173812371976319045157427603)
          ·
            refine ⟨260718557964478567736141405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173812371976319045157427603 260718557964478567736141405)
            ·
              refine ⟨97769459236679462901053027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260718557964478567736141405 97769459236679462901053027)
              ·
                refine ⟨146654188855019194351579541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97769459236679462901053027 146654188855019194351579541)
                ·
                  refine ⟨6874415102579024735230291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146654188855019194351579541 6874415102579024735230291)
                  ·
                    refine ⟨10311622653868537102845437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874415102579024735230291 10311622653868537102845437)
                    ·
                      refine ⟨3866858495200701413567039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311622653868537102845437 3866858495200701413567039)
                      ·
                        rfl

theorem cell23_7530680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_7530680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530680 prefixEnd_7530680 := by exact prefixLift 7530680
  have htrace : WordTrace (prefixWord ++ tailWord_7530680) baseStart_7530680 baseEnd_7530680 := by
    simpa [prefixWord, tailWord_7530680, baseEnd_7530680] using wordTrace_append hprefix tailTrace_7530680
  have hstable : (prefixWord ++ tailWord_7530680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530680).length < 2 ^ (prefixWord ++ tailWord_7530680).sum := by decide
  have hdescent : baseEnd_7530680 < baseStart_7530680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530703 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_7530703 : Nat := 118140960795 + 7530703 * 2 ^ 59
def prefixEnd_7530703 : Nat := 4983230072969 + 3 ^ 40 * 7530703 * 2
def baseEnd_7530703 : Nat := 3866870305255754823579433

theorem tailTrace_7530703 : CollatzResearch.WordTrace tailWord_7530703 prefixEnd_7530703 3866870305255754823579433 := by
  unfold tailWord_7530703
  simp only [CollatzResearch.WordTrace]
  refine ⟨274667303236556647522540763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183111535491037765015027175 274667303236556647522540763)
  ·
    refine ⟨412000954854834971283811145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274667303236556647522540763 412000954854834971283811145)
    ·
      refine ⟨309000716141126228462858359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412000954854834971283811145 309000716141126228462858359)
      ·
        refine ⟨463501074211689342694287539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309000716141126228462858359 463501074211689342694287539)
        ·
          refine ⟨695251611317534014041431309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463501074211689342694287539 695251611317534014041431309)
          ·
            refine ⟨260719354244075255265536741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695251611317534014041431309 260719354244075255265536741)
            ·
              refine ⟨48884878920764110362288139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260719354244075255265536741 48884878920764110362288139)
              ·
                refine ⟨73327318381146165543432209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48884878920764110362288139 73327318381146165543432209)
                ·
                  refine ⟨54995488785859624157574157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73327318381146165543432209 54995488785859624157574157)
                  ·
                    refine ⟨20623308294697359059090309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54995488785859624157574157 20623308294697359059090309)
                    ·
                      refine ⟨3866870305255754823579433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20623308294697359059090309 3866870305255754823579433)
                      ·
                        rfl

theorem cell23_7530703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_7530703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530703 prefixEnd_7530703 := by exact prefixLift 7530703
  have htrace : WordTrace (prefixWord ++ tailWord_7530703) baseStart_7530703 baseEnd_7530703 := by
    simpa [prefixWord, tailWord_7530703, baseEnd_7530703] using wordTrace_append hprefix tailTrace_7530703
  have hstable : (prefixWord ++ tailWord_7530703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530703).length < 2 ^ (prefixWord ++ tailWord_7530703).sum := by decide
  have hdescent : baseEnd_7530703 < baseStart_7530703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530713 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_7530713 : Nat := 118140960795 + 7530713 * 2 ^ 59
def prefixEnd_7530713 : Nat := 4983230072969 + 3 ^ 40 * 7530713 * 2
def baseEnd_7530713 : Nat := 1288958480020766594818129

theorem tailTrace_7530713 : CollatzResearch.WordTrace tailWord_7530713 prefixEnd_7530713 1288958480020766594818129 := by
  unfold tailWord_7530713
  simp only [CollatzResearch.WordTrace]
  refine ⟨274667667966520419230404793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183111778644346946153603195 274667667966520419230404793)
  ·
    refine ⟨206000750974890314422803595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274667667966520419230404793 206000750974890314422803595)
    ·
      refine ⟨309001126462335471634205393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206000750974890314422803595 309001126462335471634205393)
      ·
        refine ⟨231750844846751603725654045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309001126462335471634205393 231750844846751603725654045)
        ·
          refine ⟨86906566817531851397120267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231750844846751603725654045 86906566817531851397120267)
          ·
            refine ⟨130359850226297777095680401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86906566817531851397120267 130359850226297777095680401)
            ·
              refine ⟨97769887669723332821760301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130359850226297777095680401 97769887669723332821760301)
              ·
                refine ⟨36663707876146249808160113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97769887669723332821760301 36663707876146249808160113)
                ·
                  refine ⟨27497780907109687356120085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36663707876146249808160113 27497780907109687356120085)
                  ·
                    refine ⟨1288958480020766594818129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27497780907109687356120085 1288958480020766594818129)
                    ·
                      rfl

theorem cell23_7530713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_7530713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530713 prefixEnd_7530713 := by exact prefixLift 7530713
  have htrace : WordTrace (prefixWord ++ tailWord_7530713) baseStart_7530713 baseEnd_7530713 := by
    simpa [prefixWord, tailWord_7530713, baseEnd_7530713] using wordTrace_append hprefix tailTrace_7530713
  have hstable : (prefixWord ++ tailWord_7530713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530713).length < 2 ^ (prefixWord ++ tailWord_7530713).sum := by decide
  have hdescent : baseEnd_7530713 < baseStart_7530713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530714 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_7530714 : Nat := 118140960795 + 7530714 * 2 ^ 59
def prefixEnd_7530714 : Nat := 4983230072969 + 3 ^ 40 * 7530714 * 2
def baseEnd_7530714 : Nat := 3866875953542954280541883

theorem tailTrace_7530714 : CollatzResearch.WordTrace tailWord_7530714 prefixEnd_7530714 3866875953542954280541883 := by
  unfold tailWord_7530714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68666926109879199100297799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183111802959677864267460797 68666926109879199100297799)
  ·
    refine ⟨103000389164818798650446699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68666926109879199100297799 103000389164818798650446699)
    ·
      refine ⟨154500583747228197975670049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103000389164818798650446699 154500583747228197975670049)
      ·
        refine ⟨115875437810421148481752537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154500583747228197975670049 115875437810421148481752537)
        ·
          refine ⟨86906578357815861361314403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115875437810421148481752537 86906578357815861361314403)
          ·
            refine ⟨130359867536723792041971605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86906578357815861361314403 130359867536723792041971605)
            ·
              refine ⟨6110618790783927751967419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130359867536723792041971605 6110618790783927751967419)
              ·
                refine ⟨9165928186175891627951129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110618790783927751967419 9165928186175891627951129)
                ·
                  refine ⟨6874446139631918720963347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165928186175891627951129 6874446139631918720963347)
                  ·
                    refine ⟨10311669209447878081445021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874446139631918720963347 10311669209447878081445021)
                    ·
                      refine ⟨3866875953542954280541883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311669209447878081445021 3866875953542954280541883)
                      ·
                        rfl

theorem cell23_7530714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_7530714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530714 prefixEnd_7530714 := by exact prefixLift 7530714
  have htrace : WordTrace (prefixWord ++ tailWord_7530714) baseStart_7530714 baseEnd_7530714 := by
    simpa [prefixWord, tailWord_7530714, baseEnd_7530714] using wordTrace_append hprefix tailTrace_7530714
  have hstable : (prefixWord ++ tailWord_7530714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530714).length < 2 ^ (prefixWord ++ tailWord_7530714).sum := by decide
  have hdescent : baseEnd_7530714 < baseStart_7530714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530737 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_7530737 : Nat := 118140960795 + 7530737 * 2 ^ 59
def prefixEnd_7530737 : Nat := 4983230072969 + 3 ^ 40 * 7530737 * 2
def baseEnd_7530737 : Nat := 3866887763598007690554277

theorem tailTrace_7530737 : CollatzResearch.WordTrace tailWord_7530737 prefixEnd_7530737 3866887763598007690554277 := by
  unfold tailWord_7530737
  simp only [CollatzResearch.WordTrace]
  refine ⟨274668543318433471329278465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183112362212288980886185643 274668543318433471329278465)
  ·
    refine ⟨206001407488825103496958849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274668543318433471329278465 206001407488825103496958849)
    ·
      refine ⟨154501055616618827622719137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206001407488825103496958849 154501055616618827622719137)
      ·
        refine ⟨115875791712464120717039353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154501055616618827622719137 115875791712464120717039353)
        ·
          refine ⟨86906843784348090537779515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115875791712464120717039353 86906843784348090537779515)
          ·
            refine ⟨130360265676522135806669273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86906843784348090537779515 130360265676522135806669273)
            ·
              refine ⟨97770199257391601855001955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130360265676522135806669273 97770199257391601855001955)
              ·
                refine ⟨146655298886087402782502933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97770199257391601855001955 146655298886087402782502933)
                ·
                  refine ⟨6874467135285347005429825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146655298886087402782502933 6874467135285347005429825)
                  ·
                    refine ⟨5155850351464010254072369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874467135285347005429825 5155850351464010254072369)
                    ·
                      refine ⟨3866887763598007690554277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155850351464010254072369 3866887763598007690554277)
                      ·
                        rfl

theorem cell23_7530737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_7530737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530737 prefixEnd_7530737 := by exact prefixLift 7530737
  have htrace : WordTrace (prefixWord ++ tailWord_7530737) baseStart_7530737 baseEnd_7530737 := by
    simpa [prefixWord, tailWord_7530737, baseEnd_7530737] using wordTrace_append hprefix tailTrace_7530737
  have hstable : (prefixWord ++ tailWord_7530737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530737).length < 2 ^ (prefixWord ++ tailWord_7530737).sum := by decide
  have hdescent : baseEnd_7530737 < baseStart_7530737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530911 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7530911 : Nat := 118140960795 + 7530911 * 2 ^ 59
def prefixEnd_7530911 : Nat := 4983230072969 + 3 ^ 40 * 7530911 * 2
def baseEnd_7530911 : Nat := 3866977109231890009778477

theorem tailTrace_7530911 : CollatzResearch.WordTrace tailWord_7530911 prefixEnd_7530911 3866977109231890009778477 := by
  unfold tailWord_7530911
  simp only [CollatzResearch.WordTrace]
  refine ⟨274674889619803099046112587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183116593079868732697408391 274674889619803099046112587)
  ·
    refine ⟨412012334429704648569168881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274674889619803099046112587 412012334429704648569168881)
    ·
      refine ⟨309009250822278486426876661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412012334429704648569168881 309009250822278486426876661)
      ·
        refine ⟨28969617264588608102519687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309009250822278486426876661 28969617264588608102519687)
        ·
          refine ⟨43454425896882912153779531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28969617264588608102519687 43454425896882912153779531)
          ·
            refine ⟨65181638845324368230669297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43454425896882912153779531 65181638845324368230669297)
            ·
              refine ⟨48886229133993276173001973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65181638845324368230669297 48886229133993276173001973)
              ·
                refine ⟨4583083981311869641218935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48886229133993276173001973 4583083981311869641218935)
                ·
                  refine ⟨6874625971967804461828403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583083981311869641218935 6874625971967804461828403)
                  ·
                    refine ⟨10311938957951706692742605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874625971967804461828403 10311938957951706692742605)
                    ·
                      refine ⟨3866977109231890009778477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311938957951706692742605 3866977109231890009778477)
                      ·
                        rfl

theorem cell23_7530911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7530911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530911 prefixEnd_7530911 := by exact prefixLift 7530911
  have htrace : WordTrace (prefixWord ++ tailWord_7530911) baseStart_7530911 baseEnd_7530911 := by
    simpa [prefixWord, tailWord_7530911, baseEnd_7530911] using wordTrace_append hprefix tailTrace_7530911
  have hstable : (prefixWord ++ tailWord_7530911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530911).length < 2 ^ (prefixWord ++ tailWord_7530911).sum := by decide
  have hdescent : baseEnd_7530911 < baseStart_7530911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530945 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7530945 : Nat := 118140960795 + 7530945 * 2 ^ 59
def prefixEnd_7530945 : Nat := 4983230072969 + 3 ^ 40 * 7530945 * 2
def baseEnd_7530945 : Nat := 3866994567574142876753321

theorem tailTrace_7530945 : CollatzResearch.WordTrace tailWord_7530945 prefixEnd_7530945 3866994567574142876753321 := by
  unfold tailWord_7530945
  simp only [CollatzResearch.WordTrace]
  refine ⟨274676129701679922852850289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183117419801119948568566859 274676129701679922852850289)
  ·
    refine ⟨206007097276259942139637717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274676129701679922852850289 206007097276259942139637717)
    ·
      refine ⟨4828291342412342393897759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 206007097276259942139637717 4828291342412342393897759)
      ·
        refine ⟨7242437013618513590846639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828291342412342393897759 7242437013618513590846639)
        ·
          refine ⟨10863655520427770386269959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242437013618513590846639 10863655520427770386269959)
          ·
            refine ⟨16295483280641655579404939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863655520427770386269959 16295483280641655579404939)
            ·
              refine ⟨24443224920962483369107409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295483280641655579404939 24443224920962483369107409)
              ·
                refine ⟨18332418690721862526830557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24443224920962483369107409 18332418690721862526830557)
                ·
                  refine ⟨6874657009020698447561459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18332418690721862526830557 6874657009020698447561459)
                  ·
                    refine ⟨10311985513531047671342189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874657009020698447561459 10311985513531047671342189)
                    ·
                      refine ⟨3866994567574142876753321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311985513531047671342189 3866994567574142876753321)
                      ·
                        rfl

theorem cell23_7530945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7530945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530945 prefixEnd_7530945 := by exact prefixLift 7530945
  have htrace : WordTrace (prefixWord ++ tailWord_7530945) baseStart_7530945 baseEnd_7530945 := by
    simpa [prefixWord, tailWord_7530945, baseEnd_7530945] using wordTrace_append hprefix tailTrace_7530945
  have hstable : (prefixWord ++ tailWord_7530945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530945).length < 2 ^ (prefixWord ++ tailWord_7530945).sum := by decide
  have hdescent : baseEnd_7530945 < baseStart_7530945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530951 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_7530951 : Nat := 118140960795 + 7530951 * 2 ^ 59
def prefixEnd_7530951 : Nat := 4983230072969 + 3 ^ 40 * 7530951 * 2
def baseEnd_7530951 : Nat := 3866997648458069853278293

theorem tailTrace_7530951 : CollatzResearch.WordTrace tailWord_7530951 prefixEnd_7530951 3866997648458069853278293 := by
  unfold tailWord_7530951
  simp only [CollatzResearch.WordTrace]
  refine ⟨274676348539658185877568707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183117565693105457251712471 274676348539658185877568707)
  ·
    refine ⟨412014522809487278816353061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274676348539658185877568707 412014522809487278816353061)
    ·
      refine ⟨77252723026778864778066199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412014522809487278816353061 77252723026778864778066199)
      ·
        refine ⟨115879084540168297167099299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77252723026778864778066199 115879084540168297167099299)
        ·
          refine ⟨173818626810252445750648949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115879084540168297167099299 173818626810252445750648949)
          ·
            refine ⟨16295496263461166789123339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173818626810252445750648949 16295496263461166789123339)
            ·
              refine ⟨24443244395191750183685009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295496263461166789123339 24443244395191750183685009)
              ·
                refine ⟨18332433296393812637763757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24443244395191750183685009 18332433296393812637763757)
                ·
                  refine ⟨6874662486147679739161409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18332433296393812637763757 6874662486147679739161409)
                  ·
                    refine ⟨5155996864610759804371057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874662486147679739161409 5155996864610759804371057)
                    ·
                      refine ⟨3866997648458069853278293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155996864610759804371057 3866997648458069853278293)
                      ·
                        rfl

theorem cell23_7530951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_7530951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530951 prefixEnd_7530951 := by exact prefixLift 7530951
  have htrace : WordTrace (prefixWord ++ tailWord_7530951) baseStart_7530951 baseEnd_7530951 := by
    simpa [prefixWord, tailWord_7530951, baseEnd_7530951] using wordTrace_append hprefix tailTrace_7530951
  have hstable : (prefixWord ++ tailWord_7530951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530951).length < 2 ^ (prefixWord ++ tailWord_7530951).sum := by decide
  have hdescent : baseEnd_7530951 < baseStart_7530951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530954 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_7530954 : Nat := 118140960795 + 7530954 * 2 ^ 59
def prefixEnd_7530954 : Nat := 4983230072969 + 3 ^ 40 * 7530954 * 2
def baseEnd_7530954 : Nat := 3866999188900033341540779

theorem tailTrace_7530954 : CollatzResearch.WordTrace tailWord_7530954 prefixEnd_7530954 3866999188900033341540779 := by
  unfold tailWord_7530954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669114489661829347481979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183117638639098211593285277 68669114489661829347481979)
  ·
    refine ⟨103003671734492744021222969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68669114489661829347481979 103003671734492744021222969)
    ·
      refine ⟨77252753800869558015917227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103003671734492744021222969 77252753800869558015917227)
      ·
        refine ⟨115879130701304337023875841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77252753800869558015917227 115879130701304337023875841)
        ·
          refine ⟨86909348025978252767906881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115879130701304337023875841 86909348025978252767906881)
          ·
            refine ⟨65182011019483689575930161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86909348025978252767906881 65182011019483689575930161)
            ·
              refine ⟨48886508264612767181947621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65182011019483689575930161 48886508264612767181947621)
              ·
                refine ⟨9166220299614893846615179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48886508264612767181947621 9166220299614893846615179)
                ·
                  refine ⟨13749330449422340769922769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166220299614893846615179 13749330449422340769922769)
                  ·
                    refine ⟨10311997837066755577442077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13749330449422340769922769 10311997837066755577442077)
                    ·
                      refine ⟨3866999188900033341540779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311997837066755577442077 3866999188900033341540779)
                      ·
                        rfl

theorem cell23_7530954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_7530954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530954 prefixEnd_7530954 := by exact prefixLift 7530954
  have htrace : WordTrace (prefixWord ++ tailWord_7530954) baseStart_7530954 baseEnd_7530954 := by
    simpa [prefixWord, tailWord_7530954, baseEnd_7530954] using wordTrace_append hprefix tailTrace_7530954
  have hstable : (prefixWord ++ tailWord_7530954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530954).length < 2 ^ (prefixWord ++ tailWord_7530954).sum := by decide
  have hdescent : baseEnd_7530954 < baseStart_7530954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530964 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7530964 : Nat := 118140960795 + 7530964 * 2 ^ 59
def prefixEnd_7530964 : Nat := 4983230072969 + 3 ^ 40 * 7530964 * 2
def baseEnd_7530964 : Nat := 3867004323706578302415733

theorem tailTrace_7530964 : CollatzResearch.WordTrace tailWord_7530964 prefixEnd_7530964 3867004323706578302415733 := by
  unfold tailWord_7530964
  simp only [CollatzResearch.WordTrace]
  refine ⟨137338411344305544548895973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183117881792407392731861297 137338411344305544548895973)
  ·
    refine ⟨25750952127057289602917995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137338411344305544548895973 25750952127057289602917995)
    ·
      refine ⟨38626428190585934404376993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750952127057289602917995 38626428190585934404376993)
      ·
        refine ⟨28969821142939450803282745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38626428190585934404376993 28969821142939450803282745)
        ·
          refine ⟨21727365857204588102462059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28969821142939450803282745 21727365857204588102462059)
          ·
            refine ⟨32591048785806882153693089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21727365857204588102462059 32591048785806882153693089)
            ·
              refine ⟨24443286589355161615269817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32591048785806882153693089 24443286589355161615269817)
              ·
                refine ⟨18332464942016371211452363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24443286589355161615269817 18332464942016371211452363)
                ·
                  refine ⟨27498697413024556817178545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18332464942016371211452363 27498697413024556817178545)
                  ·
                    refine ⟨20624023059768417612883909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27498697413024556817178545 20624023059768417612883909)
                    ·
                      refine ⟨3867004323706578302415733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20624023059768417612883909 3867004323706578302415733)
                      ·
                        rfl

theorem cell23_7530964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7530964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530964 prefixEnd_7530964 := by exact prefixLift 7530964
  have htrace : WordTrace (prefixWord ++ tailWord_7530964) baseStart_7530964 baseEnd_7530964 := by
    simpa [prefixWord, tailWord_7530964, baseEnd_7530964] using wordTrace_append hprefix tailTrace_7530964
  have hstable : (prefixWord ++ tailWord_7530964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530964).length < 2 ^ (prefixWord ++ tailWord_7530964).sum := by decide
  have hdescent : baseEnd_7530964 < baseStart_7530964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530978 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7530978 : Nat := 118140960795 + 7530978 * 2 ^ 59
def prefixEnd_7530978 : Nat := 4983230072969 + 3 ^ 40 * 7530978 * 2
def baseEnd_7530978 : Nat := 1289003837478580415880223

theorem tailTrace_7530978 : CollatzResearch.WordTrace tailWord_7530978 prefixEnd_7530978 1289003837478580415880223 := by
  unfold tailWord_7530978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669333327640092372200397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183118222207040246325867725 68669333327640092372200397)
  ·
    refine ⟨25750999997865034639575149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68669333327640092372200397 25750999997865034639575149)
    ·
      refine ⟨9656624999199387989840681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25750999997865034639575149 9656624999199387989840681)
      ·
        refine ⟨7242468749399540992380511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9656624999199387989840681 7242468749399540992380511)
        ·
          refine ⟨10863703124099311488570767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242468749399540992380511 10863703124099311488570767)
          ·
            refine ⟨16295554686148967232856151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863703124099311488570767 16295554686148967232856151)
            ·
              refine ⟨24443332029223450849284227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295554686148967232856151 24443332029223450849284227)
              ·
                refine ⟨36664998043835176273926341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24443332029223450849284227 36664998043835176273926341)
                ·
                  refine ⟨6874687133219095551361189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36664998043835176273926341 6874687133219095551361189)
                  ·
                    refine ⟨1289003837478580415880223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874687133219095551361189 1289003837478580415880223)
                    ·
                      rfl

theorem cell23_7530978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7530978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530978 prefixEnd_7530978 := by exact prefixLift 7530978
  have htrace : WordTrace (prefixWord ++ tailWord_7530978) baseStart_7530978 baseEnd_7530978 := by
    simpa [prefixWord, tailWord_7530978, baseEnd_7530978] using wordTrace_append hprefix tailTrace_7530978
  have hstable : (prefixWord ++ tailWord_7530978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530978).length < 2 ^ (prefixWord ++ tailWord_7530978).sum := by decide
  have hdescent : baseEnd_7530978 < baseStart_7530978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531011 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 1, 3, 2]
def baseStart_7531011 : Nat := 118140960795 + 7531011 * 2 ^ 59
def prefixEnd_7531011 : Nat := 4983230072969 + 3 ^ 40 * 7531011 * 2
def baseEnd_7531011 : Nat := 3867028457297339618528017

theorem tailTrace_7531011 : CollatzResearch.WordTrace tailWord_7531011 prefixEnd_7531011 3867028457297339618528017 := by
  unfold tailWord_7531011
  simp only [CollatzResearch.WordTrace]
  refine ⟨274678536919440816124752887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183119024612960544083168591 274678536919440816124752887)
  ·
    refine ⟨412017805379161224187129331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274678536919440816124752887 412017805379161224187129331)
    ·
      refine ⟨618026708068741836280693997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412017805379161224187129331 618026708068741836280693997)
      ·
        refine ⟨231760015525778188605260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618026708068741836280693997 231760015525778188605260249)
        ·
          refine ⟨173820011644333641453945187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231760015525778188605260249 173820011644333641453945187)
          ·
            refine ⟨260730017466500462180917781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173820011644333641453945187 260730017466500462180917781)
            ·
              refine ⟨12221719568742209164730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260730017466500462180917781 12221719568742209164730521)
              ·
                refine ⟨9166289676556656873547891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12221719568742209164730521 9166289676556656873547891)
                ·
                  refine ⟨13749434514834985310321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166289676556656873547891 13749434514834985310321837)
                  ·
                    refine ⟨5156037943063119491370689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13749434514834985310321837 5156037943063119491370689)
                    ·
                      refine ⟨3867028457297339618528017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156037943063119491370689 3867028457297339618528017)
                      ·
                        rfl

theorem cell23_7531011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_7531011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531011 prefixEnd_7531011 := by exact prefixLift 7531011
  have htrace : WordTrace (prefixWord ++ tailWord_7531011) baseStart_7531011 baseEnd_7531011 := by
    simpa [prefixWord, tailWord_7531011, baseEnd_7531011] using wordTrace_append hprefix tailTrace_7531011
  have hstable : (prefixWord ++ tailWord_7531011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531011).length < 2 ^ (prefixWord ++ tailWord_7531011).sum := by decide
  have hdescent : baseEnd_7531011 < baseStart_7531011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531027 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_7531027 : Nat := 118140960795 + 7531027 * 2 ^ 59
def prefixEnd_7531027 : Nat := 4983230072969 + 3 ^ 40 * 7531027 * 2
def baseEnd_7531027 : Nat := 3867036672987811555927943

theorem tailTrace_7531027 : CollatzResearch.WordTrace tailWord_7531027 prefixEnd_7531027 3867036672987811555927943 := by
  unfold tailWord_7531027
  simp only [CollatzResearch.WordTrace]
  refine ⟨274679120487382850857335335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183119413658255233904890223 274679120487382850857335335)
  ·
    refine ⟨412018680731074276286003003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274679120487382850857335335 412018680731074276286003003)
    ·
      refine ⟨618028021096611414429004505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412018680731074276286003003 618028021096611414429004505)
      ·
        refine ⟨463521015822458560821753379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618028021096611414429004505 463521015822458560821753379)
        ·
          refine ⟨695281523733687841232630069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463521015822458560821753379 695281523733687841232630069)
          ·
            refine ⟨65182642850033235115559069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 695281523733687841232630069 65182642850033235115559069)
            ·
              refine ⟨24443491068762463168334651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65182642850033235115559069 24443491068762463168334651)
              ·
                refine ⟨36665236603143694752501977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24443491068762463168334651 36665236603143694752501977)
                ·
                  refine ⟨27498927452357771064376483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36665236603143694752501977 27498927452357771064376483)
                  ·
                    refine ⟨41248391178536656596564725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27498927452357771064376483 41248391178536656596564725)
                    ·
                      refine ⟨3867036672987811555927943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41248391178536656596564725 3867036672987811555927943)
                      ·
                        rfl

theorem cell23_7531027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_7531027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531027 prefixEnd_7531027 := by exact prefixLift 7531027
  have htrace : WordTrace (prefixWord ++ tailWord_7531027) baseStart_7531027 baseEnd_7531027 := by
    simpa [prefixWord, tailWord_7531027, baseEnd_7531027] using wordTrace_append hprefix tailTrace_7531027
  have hstable : (prefixWord ++ tailWord_7531027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531027).length < 2 ^ (prefixWord ++ tailWord_7531027).sum := by decide
  have hdescent : baseEnd_7531027 < baseStart_7531027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531041 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7531041 : Nat := 118140960795 + 7531041 * 2 ^ 59
def prefixEnd_7531041 : Nat := 4983230072969 + 3 ^ 40 * 7531041 * 2
def baseEnd_7531041 : Nat := 3867043861716974501152879

theorem tailTrace_7531041 : CollatzResearch.WordTrace tailWord_7531041 prefixEnd_7531041 3867043861716974501152879 := by
  unfold tailWord_7531041
  simp only [CollatzResearch.WordTrace]
  refine ⟨274679631109332131248344977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183119754072888087498896651 274679631109332131248344977)
  ·
    refine ⟨206009723331999098436258733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274679631109332131248344977 206009723331999098436258733)
    ·
      refine ⟨77253646249499661913597025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206009723331999098436258733 77253646249499661913597025)
      ·
        refine ⟨57940234687124746435197769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77253646249499661913597025 57940234687124746435197769)
        ·
          refine ⟨43455176015343559826398327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57940234687124746435197769 43455176015343559826398327)
          ·
            refine ⟨65182764023015339739597491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43455176015343559826398327 65182764023015339739597491)
            ·
              refine ⟨97774146034523009609396237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65182764023015339739597491 97774146034523009609396237)
              ·
                refine ⟨36665304762946128603523589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97774146034523009609396237 36665304762946128603523589)
                ·
                  refine ⟨6874744643052399113160673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36665304762946128603523589 6874744643052399113160673)
                  ·
                    refine ⟨5156058482289299334870505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874744643052399113160673 5156058482289299334870505)
                    ·
                      refine ⟨3867043861716974501152879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156058482289299334870505 3867043861716974501152879)
                      ·
                        rfl

theorem cell23_7531041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7531041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531041 prefixEnd_7531041 := by exact prefixLift 7531041
  have htrace : WordTrace (prefixWord ++ tailWord_7531041) baseStart_7531041 baseEnd_7531041 := by
    simpa [prefixWord, tailWord_7531041, baseEnd_7531041] using wordTrace_append hprefix tailTrace_7531041
  have hstable : (prefixWord ++ tailWord_7531041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531041).length < 2 ^ (prefixWord ++ tailWord_7531041).sum := by decide
  have hdescent : baseEnd_7531041 < baseStart_7531041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531087 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_7531087 : Nat := 118140960795 + 7531087 * 2 ^ 59
def prefixEnd_7531087 : Nat := 4983230072969 + 3 ^ 40 * 7531087 * 2
def baseEnd_7531087 : Nat := 3867067481827081321177667

theorem tailTrace_7531087 : CollatzResearch.WordTrace tailWord_7531087 prefixEnd_7531087 3867067481827081321177667 := by
  unfold tailWord_7531087
  simp only [CollatzResearch.WordTrace]
  refine ⟨274681308867165481104519515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183120872578110320736346343 274681308867165481104519515)
  ·
    refine ⟨412021963300748221656779273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274681308867165481104519515 412021963300748221656779273)
    ·
      refine ⟨309016472475561166242584455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412021963300748221656779273 309016472475561166242584455)
      ·
        refine ⟨463524708713341749363876683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309016472475561166242584455 463524708713341749363876683)
        ·
          refine ⟨695287063070012624045815025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463524708713341749363876683 695287063070012624045815025)
          ·
            refine ⟨521465297302509468034361269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695287063070012624045815025 521465297302509468034361269)
            ·
              refine ⟨48887371622110262628221369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521465297302509468034361269 48887371622110262628221369)
              ·
                refine ⟨36665528716582696971166027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48887371622110262628221369 36665528716582696971166027)
                ·
                  refine ⟨54998293074874045456749041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36665528716582696971166027 54998293074874045456749041)
                  ·
                    refine ⟨41248719806155534092561781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54998293074874045456749041 41248719806155534092561781)
                    ·
                      refine ⟨3867067481827081321177667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41248719806155534092561781 3867067481827081321177667)
                      ·
                        rfl

theorem cell23_7531087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_7531087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531087 prefixEnd_7531087 := by exact prefixLift 7531087
  have htrace : WordTrace (prefixWord ++ tailWord_7531087) baseStart_7531087 baseEnd_7531087 := by
    simpa [prefixWord, tailWord_7531087, baseEnd_7531087] using wordTrace_append hprefix tailTrace_7531087
  have hstable : (prefixWord ++ tailWord_7531087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531087).length < 2 ^ (prefixWord ++ tailWord_7531087).sum := by decide
  have hdescent : baseEnd_7531087 < baseStart_7531087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531097 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_7531097 : Nat := 118140960795 + 7531097 * 2 ^ 59
def prefixEnd_7531097 : Nat := 4983230072969 + 3 ^ 40 * 7531097 * 2
def baseEnd_7531097 : Nat := 3867072616633626282052621

theorem tailTrace_7531097 : CollatzResearch.WordTrace tailWord_7531097 prefixEnd_7531097 3867072616633626282052621 := by
  unfold tailWord_7531097
  simp only [CollatzResearch.WordTrace]
  refine ⟨274681673597129252812383545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183121115731419501874922363 274681673597129252812383545)
  ·
    refine ⟨206011255197846939609287659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274681673597129252812383545 206011255197846939609287659)
    ·
      refine ⟨309016882796770409413931489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206011255197846939609287659 309016882796770409413931489)
      ·
        refine ⟨231762662097577807060448617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309016882796770409413931489 231762662097577807060448617)
        ·
          refine ⟨173821996573183355295336463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231762662097577807060448617 173821996573183355295336463)
          ·
            refine ⟨260732994859775032943004695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173821996573183355295336463 260732994859775032943004695)
            ·
              refine ⟨391099492289662549414507043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260732994859775032943004695 391099492289662549414507043)
              ·
                refine ⟨586649238434493824121760565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391099492289662549414507043 586649238434493824121760565)
                ·
                  refine ⟨54998366103233796011415053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 586649238434493824121760565 54998366103233796011415053)
                  ·
                    refine ⟨20624387288712673504280645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54998366103233796011415053 20624387288712673504280645)
                    ·
                      refine ⟨3867072616633626282052621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20624387288712673504280645 3867072616633626282052621)
                      ·
                        rfl

theorem cell23_7531097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_7531097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531097 prefixEnd_7531097 := by exact prefixLift 7531097
  have htrace : WordTrace (prefixWord ++ tailWord_7531097) baseStart_7531097 baseEnd_7531097 := by
    simpa [prefixWord, tailWord_7531097, baseEnd_7531097] using wordTrace_append hprefix tailTrace_7531097
  have hstable : (prefixWord ++ tailWord_7531097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531097).length < 2 ^ (prefixWord ++ tailWord_7531097).sum := by decide
  have hdescent : baseEnd_7531097 < baseStart_7531097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531114 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7531114 : Nat := 118140960795 + 7531114 * 2 ^ 59
def prefixEnd_7531114 : Nat := 4983230072969 + 3 ^ 40 * 7531114 * 2
def baseEnd_7531114 : Nat := 3867081345804752715540043

theorem tailTrace_7531114 : CollatzResearch.WordTrace tailWord_7531114 prefixEnd_7531114 3867081345804752715540043 := by
  unfold tailWord_7531114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68670573409516916178938099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183121529092045109810501597 68670573409516916178938099)
  ·
    refine ⟨103005860114275374268407149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68670573409516916178938099 103005860114275374268407149)
    ·
      refine ⟨38627197542853265350652681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103005860114275374268407149 38627197542853265350652681)
      ·
        refine ⟨28970398157139949012989511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38627197542853265350652681 28970398157139949012989511)
        ·
          refine ⟨43455597235709923519484267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28970398157139949012989511 43455597235709923519484267)
          ·
            refine ⟨65183395853564885279226401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43455597235709923519484267 65183395853564885279226401)
            ·
              refine ⟨48887546890173663959419801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65183395853564885279226401 48887546890173663959419801)
              ·
                refine ⟨36665660167630247969564851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48887546890173663959419801 36665660167630247969564851)
                ·
                  refine ⟨54998490251445371954347277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36665660167630247969564851 54998490251445371954347277)
                  ·
                    refine ⟨20624433844292014482880229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54998490251445371954347277 20624433844292014482880229)
                    ·
                      refine ⟨3867081345804752715540043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20624433844292014482880229 3867081345804752715540043)
                      ·
                        rfl

theorem cell23_7531114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7531114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531114 prefixEnd_7531114 := by exact prefixLift 7531114
  have htrace : WordTrace (prefixWord ++ tailWord_7531114) baseStart_7531114 baseEnd_7531114 := by
    simpa [prefixWord, tailWord_7531114, baseEnd_7531114] using wordTrace_append hprefix tailTrace_7531114
  have hstable : (prefixWord ++ tailWord_7531114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531114).length < 2 ^ (prefixWord ++ tailWord_7531114).sum := by decide
  have hdescent : baseEnd_7531114 < baseStart_7531114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531177 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_7531177 : Nat := 118140960795 + 7531177 * 2 ^ 59
def prefixEnd_7531177 : Nat := 4983230072969 + 3 ^ 40 * 7531177 * 2
def baseEnd_7531177 : Nat := 3867113695085985969052253

theorem tailTrace_7531177 : CollatzResearch.WordTrace tailWord_7531177 prefixEnd_7531177 3867113695085985969052253 := by
  unfold tailWord_7531177
  simp only [CollatzResearch.WordTrace]
  refine ⟨274684591436839426475295785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183123060957892950983530523 274684591436839426475295785)
  ·
    refine ⟨206013443577629569856471839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274684591436839426475295785 206013443577629569856471839)
    ·
      refine ⟨309020165366444354784707759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206013443577629569856471839 309020165366444354784707759)
      ·
        refine ⟨463530248049666532177061639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309020165366444354784707759 463530248049666532177061639)
        ·
          refine ⟨695295372074499798265592459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463530248049666532177061639 695295372074499798265592459)
          ·
            refine ⟨1042943058111749697398388689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695295372074499798265592459 1042943058111749697398388689)
            ·
              refine ⟨782207293583812273048791517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042943058111749697398388689 782207293583812273048791517)
              ·
                refine ⟨293327735093929602393296819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 782207293583812273048791517 293327735093929602393296819)
                ·
                  refine ⟨439991602640894403589945229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293327735093929602393296819 439991602640894403589945229)
                  ·
                    refine ⟨164996850990335401346229461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439991602640894403589945229 164996850990335401346229461)
                    ·
                      refine ⟨3867113695085985969052253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164996850990335401346229461 3867113695085985969052253)
                      ·
                        rfl

theorem cell23_7531177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_7531177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531177 prefixEnd_7531177 := by exact prefixLift 7531177
  have htrace : WordTrace (prefixWord ++ tailWord_7531177) baseStart_7531177 baseEnd_7531177 := by
    simpa [prefixWord, tailWord_7531177, baseEnd_7531177] using wordTrace_append hprefix tailTrace_7531177
  have hstable : (prefixWord ++ tailWord_7531177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531177).length < 2 ^ (prefixWord ++ tailWord_7531177).sum := by decide
  have hdescent : baseEnd_7531177 < baseStart_7531177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531208 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_7531208 : Nat := 118140960795 + 7531208 * 2 ^ 59
def prefixEnd_7531208 : Nat := 4983230072969 + 3 ^ 40 * 7531208 * 2
def baseEnd_7531208 : Nat := 3867129612986275347764611

theorem tailTrace_7531208 : CollatzResearch.WordTrace tailWord_7531208 prefixEnd_7531208 3867129612986275347764611 := by
  unfold tailWord_7531208
  simp only [CollatzResearch.WordTrace]
  refine ⟨137342861049863559384837139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183123814733151412513116185 137342861049863559384837139)
  ·
    refine ⟨206014291574795339077255709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137342861049863559384837139 206014291574795339077255709)
    ·
      refine ⟨77255359340548252153970891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206014291574795339077255709 77255359340548252153970891)
      ·
        refine ⟨115883039010822378230956337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77255359340548252153970891 115883039010822378230956337)
        ·
          refine ⟨86912279258116783673217253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115883039010822378230956337 86912279258116783673217253)
          ·
            refine ⟨16296052360896896938728235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86912279258116783673217253 16296052360896896938728235)
            ·
              refine ⟨24444078541345345408092353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16296052360896896938728235 24444078541345345408092353)
              ·
                refine ⟨18333058906009009056069265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24444078541345345408092353 18333058906009009056069265)
                ·
                  refine ⟨13749794179506756792051949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18333058906009009056069265 13749794179506756792051949)
                  ·
                    refine ⟨5156172817315033797019481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13749794179506756792051949 5156172817315033797019481)
                    ·
                      refine ⟨3867129612986275347764611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156172817315033797019481 3867129612986275347764611)
                      ·
                        rfl

theorem cell23_7531208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_7531208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531208 prefixEnd_7531208 := by exact prefixLift 7531208
  have htrace : WordTrace (prefixWord ++ tailWord_7531208) baseStart_7531208 baseEnd_7531208 := by
    simpa [prefixWord, tailWord_7531208, baseEnd_7531208] using wordTrace_append hprefix tailTrace_7531208
  have hstable : (prefixWord ++ tailWord_7531208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531208).length < 2 ^ (prefixWord ++ tailWord_7531208).sum := by decide
  have hdescent : baseEnd_7531208 < baseStart_7531208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531255 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_7531255 : Nat := 118140960795 + 7531255 * 2 ^ 59
def prefixEnd_7531255 : Nat := 4983230072969 + 3 ^ 40 * 7531255 * 2
def baseEnd_7531255 : Nat := 3867153746577036663876895

theorem tailTrace_7531255 : CollatzResearch.WordTrace tailWord_7531255 prefixEnd_7531255 3867153746577036663876895 := by
  unfold tailWord_7531255
  simp only [CollatzResearch.WordTrace]
  refine ⟨274687436330556845796635219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183124957553704563864423479 274687436330556845796635219)
  ·
    refine ⟨412031154495835268694952829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274687436330556845796635219 412031154495835268694952829)
    ·
      refine ⟨154511682935938225760607311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412031154495835268694952829 154511682935938225760607311)
      ·
        refine ⟨231767524403907338640910967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154511682935938225760607311 231767524403907338640910967)
        ·
          refine ⟨347651286605861007961366451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231767524403907338640910967 347651286605861007961366451)
          ·
            refine ⟨521476929908791511942049677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347651286605861007961366451 521476929908791511942049677)
            ·
              refine ⟨195553848715796816978268629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521476929908791511942049677 195553848715796816978268629)
              ·
                refine ⟨4583293329276487897928171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195553848715796816978268629 4583293329276487897928171)
                ·
                  refine ⟨6874939993914731846892257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583293329276487897928171 6874939993914731846892257)
                  ·
                    refine ⟨5156204995436048885169193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874939993914731846892257 5156204995436048885169193)
                    ·
                      refine ⟨3867153746577036663876895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156204995436048885169193 3867153746577036663876895)
                      ·
                        rfl

theorem cell23_7531255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_7531255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531255 prefixEnd_7531255 := by exact prefixLift 7531255
  have htrace : WordTrace (prefixWord ++ tailWord_7531255) baseStart_7531255 baseEnd_7531255 := by
    simpa [prefixWord, tailWord_7531255, baseEnd_7531255] using wordTrace_append hprefix tailTrace_7531255
  have hstable : (prefixWord ++ tailWord_7531255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531255).length < 2 ^ (prefixWord ++ tailWord_7531255).sum := by decide
  have hdescent : baseEnd_7531255 < baseStart_7531255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531272 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_7531272 : Nat := 118140960795 + 7531272 * 2 ^ 59
def prefixEnd_7531272 : Nat := 4983230072969 + 3 ^ 40 * 7531272 * 2
def baseEnd_7531272 : Nat := 3867162475748163097364317

theorem tailTrace_7531272 : CollatzResearch.WordTrace tailWord_7531272 prefixEnd_7531272 3867162475748163097364317 := by
  unfold tailWord_7531272
  simp only [CollatzResearch.WordTrace]
  refine ⟨137344028185747628850002035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183125370914330171800002713 137344028185747628850002035)
  ·
    refine ⟨206016042278621443275003053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137344028185747628850002035 206016042278621443275003053)
    ·
      refine ⟨77256015854483041228126145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206016042278621443275003053 77256015854483041228126145)
      ·
        refine ⟨57942011890862280921094609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77256015854483041228126145 57942011890862280921094609)
        ·
          refine ⟨43456508918146710690820957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57942011890862280921094609 43456508918146710690820957)
          ·
            refine ⟨16296190844305016509057859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43456508918146710690820957 16296190844305016509057859)
            ·
              refine ⟨24444286266457524763586789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16296190844305016509057859 24444286266457524763586789)
              ·
                refine ⟨4583303674960785893172523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24444286266457524763586789 4583303674960785893172523)
                ·
                  refine ⟨6874955512441178839758785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583303674960785893172523 6874955512441178839758785)
                  ·
                    refine ⟨5156216634330884129819089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874955512441178839758785 5156216634330884129819089)
                    ·
                      refine ⟨3867162475748163097364317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156216634330884129819089 3867162475748163097364317)
                      ·
                        rfl

theorem cell23_7531272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_7531272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531272 prefixEnd_7531272 := by exact prefixLift 7531272
  have htrace : WordTrace (prefixWord ++ tailWord_7531272) baseStart_7531272 baseEnd_7531272 := by
    simpa [prefixWord, tailWord_7531272, baseEnd_7531272] using wordTrace_append hprefix tailTrace_7531272
  have hstable : (prefixWord ++ tailWord_7531272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531272).length < 2 ^ (prefixWord ++ tailWord_7531272).sum := by decide
  have hdescent : baseEnd_7531272 < baseStart_7531272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531274 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_7531274 : Nat := 118140960795 + 7531274 * 2 ^ 59
def prefixEnd_7531274 : Nat := 4983230072969 + 3 ^ 40 * 7531274 * 2
def baseEnd_7531274 : Nat := 1289054500903157363179769

theorem tailTrace_7531274 : CollatzResearch.WordTrace tailWord_7531274 prefixEnd_7531274 1289054500903157363179769 := by
  unfold tailWord_7531274
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672032329372003010394219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183125419544992008027717917 68672032329372003010394219)
  ·
    refine ⟨103008048494058004515591329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672032329372003010394219 103008048494058004515591329)
    ·
      refine ⟨77256036370543503386693497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103008048494058004515591329 77256036370543503386693497)
      ·
        refine ⟨57942027277907627540020123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77256036370543503386693497 57942027277907627540020123)
        ·
          refine ⟨86913040916861441310030185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57942027277907627540020123 86913040916861441310030185)
          ·
            refine ⟨65184780687646080982522639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86913040916861441310030185 65184780687646080982522639)
            ·
              refine ⟨97777171031469121473783959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65184780687646080982522639 97777171031469121473783959)
              ·
                refine ⟨146665756547203682210675939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97777171031469121473783959 146665756547203682210675939)
                ·
                  refine ⟨219998634820805523316013909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146665756547203682210675939 219998634820805523316013909)
                  ·
                    refine ⟨1289054500903157363179769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219998634820805523316013909 1289054500903157363179769)
                    ·
                      rfl

theorem cell23_7531274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_7531274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531274 prefixEnd_7531274 := by exact prefixLift 7531274
  have htrace : WordTrace (prefixWord ++ tailWord_7531274) baseStart_7531274 baseEnd_7531274 := by
    simpa [prefixWord, tailWord_7531274, baseEnd_7531274] using wordTrace_append hprefix tailTrace_7531274
  have hstable : (prefixWord ++ tailWord_7531274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531274).length < 2 ^ (prefixWord ++ tailWord_7531274).sum := by decide
  have hdescent : baseEnd_7531274 < baseStart_7531274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531306 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7531306 : Nat := 118140960795 + 7531306 * 2 ^ 59
def prefixEnd_7531306 : Nat := 4983230072969 + 3 ^ 40 * 7531306 * 2
def baseEnd_7531306 : Nat := 3867179934090415964339161

theorem tailTrace_7531306 : CollatzResearch.WordTrace tailWord_7531306 prefixEnd_7531306 3867179934090415964339161 := by
  unfold tailWord_7531306
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672324113343020376685443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183126197635581387671161181 68672324113343020376685443)
  ·
    refine ⟨103008486170014530565028165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672324113343020376685443 103008486170014530565028165)
    ·
      refine ⟨19314091156877724480942781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103008486170014530565028165 19314091156877724480942781)
      ·
        refine ⟨7242784183829146680353543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19314091156877724480942781 7242784183829146680353543)
        ·
          refine ⟨10864176275743720020530315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242784183829146680353543 10864176275743720020530315)
          ·
            refine ⟨16296264413615580030795473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864176275743720020530315 16296264413615580030795473)
            ·
              refine ⟨12222198310211685023096605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16296264413615580030795473 12222198310211685023096605)
              ·
                refine ⟨4583324366329381883661227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12222198310211685023096605 4583324366329381883661227)
                ·
                  refine ⟨6874986549494072825491841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583324366329381883661227 6874986549494072825491841)
                  ·
                    refine ⟨5156239912120554619118881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874986549494072825491841 5156239912120554619118881)
                    ·
                      refine ⟨3867179934090415964339161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156239912120554619118881 3867179934090415964339161)
                      ·
                        rfl

theorem cell23_7531306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7531306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531306 prefixEnd_7531306 := by exact prefixLift 7531306
  have htrace : WordTrace (prefixWord ++ tailWord_7531306) baseStart_7531306 baseEnd_7531306 := by
    simpa [prefixWord, tailWord_7531306, baseEnd_7531306] using wordTrace_append hprefix tailTrace_7531306
  have hstable : (prefixWord ++ tailWord_7531306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531306).length < 2 ^ (prefixWord ++ tailWord_7531306).sum := by decide
  have hdescent : baseEnd_7531306 < baseStart_7531306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531315 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 1, 3, 2]
def baseStart_7531315 : Nat := 118140960795 + 7531315 * 2 ^ 59
def prefixEnd_7531315 : Nat := 4983230072969 + 3 ^ 40 * 7531315 * 2
def baseEnd_7531315 : Nat := 3867184555416306429126619

theorem tailTrace_7531315 : CollatzResearch.WordTrace tailWord_7531315 prefixEnd_7531315 3867184555416306429126619 := by
  unfold tailWord_7531315
  simp only [CollatzResearch.WordTrace]
  refine ⟨274689624710339476043819399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183126416473559650695879599 274689624710339476043819399)
  ·
    refine ⟨412034437065509214065729099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274689624710339476043819399 412034437065509214065729099)
    ·
      refine ⟨618051655598263821098593649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412034437065509214065729099 618051655598263821098593649)
      ·
        refine ⟨463538741698697865823945237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618051655598263821098593649 463538741698697865823945237)
        ·
          refine ⟨21728378517126462460497433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 463538741698697865823945237 21728378517126462460497433)
          ·
            refine ⟨16296283887844846845373075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21728378517126462460497433 16296283887844846845373075)
            ·
              refine ⟨24444425831767270268059613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16296283887844846845373075 24444425831767270268059613)
              ·
                refine ⟨9166659686912726350522355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24444425831767270268059613 9166659686912726350522355)
                ·
                  refine ⟨13749989530369089525783533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166659686912726350522355 13749989530369089525783533)
                  ·
                    refine ⟨5156246073888408572168825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13749989530369089525783533 5156246073888408572168825)
                    ·
                      refine ⟨3867184555416306429126619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156246073888408572168825 3867184555416306429126619)
                      ·
                        rfl

theorem cell23_7531315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 3, 2].length) (baseStart_7531315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531315 prefixEnd_7531315 := by exact prefixLift 7531315
  have htrace : WordTrace (prefixWord ++ tailWord_7531315) baseStart_7531315 baseEnd_7531315 := by
    simpa [prefixWord, tailWord_7531315, baseEnd_7531315] using wordTrace_append hprefix tailTrace_7531315
  have hstable : (prefixWord ++ tailWord_7531315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531315).length < 2 ^ (prefixWord ++ tailWord_7531315).sum := by decide
  have hdescent : baseEnd_7531315 < baseStart_7531315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531322 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_7531322 : Nat := 118140960795 + 7531322 * 2 ^ 59
def prefixEnd_7531322 : Nat := 4983230072969 + 3 ^ 40 * 7531322 * 2
def baseEnd_7531322 : Nat := 3867188149780887901739087

theorem tailTrace_7531322 : CollatzResearch.WordTrace tailWord_7531322 prefixEnd_7531322 3867188149780887901739087 := by
  unfold tailWord_7531322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672470005328529059831055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183126586680876077492882813 68672470005328529059831055)
  ·
    refine ⟨103008705007992793589746583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672470005328529059831055 103008705007992793589746583)
    ·
      refine ⟨154513057511989190384619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103008705007992793589746583 154513057511989190384619875)
      ·
        refine ⟨231769586267983785576929813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154513057511989190384619875 231769586267983785576929813)
        ·
          refine ⟨10864199356311739948918585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231769586267983785576929813 10864199356311739948918585)
          ·
            refine ⟨8148149517233804961688939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10864199356311739948918585 8148149517233804961688939)
            ·
              refine ⟨12222224275850707442533409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148149517233804961688939 12222224275850707442533409)
              ·
                refine ⟨9166668206888030581900057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222224275850707442533409 9166668206888030581900057)
                ·
                  refine ⟨6875001155166022936425043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9166668206888030581900057 6875001155166022936425043)
                  ·
                    refine ⟨10312501732749034404637565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6875001155166022936425043 10312501732749034404637565)
                    ·
                      refine ⟨3867188149780887901739087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10312501732749034404637565 3867188149780887901739087)
                      ·
                        rfl

theorem cell23_7531322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_7531322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531322 prefixEnd_7531322 := by exact prefixLift 7531322
  have htrace : WordTrace (prefixWord ++ tailWord_7531322) baseStart_7531322 baseEnd_7531322 := by
    simpa [prefixWord, tailWord_7531322, baseEnd_7531322] using wordTrace_append hprefix tailTrace_7531322
  have hstable : (prefixWord ++ tailWord_7531322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531322).length < 2 ^ (prefixWord ++ tailWord_7531322).sum := by decide
  have hdescent : baseEnd_7531322 < baseStart_7531322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531351 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 7]
def baseStart_7531351 : Nat := 118140960795 + 7531351 * 2 ^ 59
def prefixEnd_7531351 : Nat := 4983230072969 + 3 ^ 40 * 7531351 * 2
def baseEnd_7531351 : Nat := 429689226746652032030717

theorem tailTrace_7531351 : CollatzResearch.WordTrace tailWord_7531351 prefixEnd_7531351 429689226746652032030717 := by
  unfold tailWord_7531351
  simp only [CollatzResearch.WordTrace]
  refine ⟨274690937738209054192129907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183127291825472702794753271 274690937738209054192129907)
  ·
    refine ⟨412036406607313581288194861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274690937738209054192129907 412036406607313581288194861)
    ·
      refine ⟨154513652477742592983073073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412036406607313581288194861 154513652477742592983073073)
      ·
        refine ⟨115885239358306944737304805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154513652477742592983073073 115885239358306944737304805)
        ·
          refine ⟨21728482379682552138244651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115885239358306944737304805 21728482379682552138244651)
          ·
            refine ⟨32592723569523828207366977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21728482379682552138244651 32592723569523828207366977)
            ·
              refine ⟨24444542677142871155525233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32592723569523828207366977 24444542677142871155525233)
              ·
                refine ⟨18333407007857153366643925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24444542677142871155525233 18333407007857153366643925)
                ·
                  refine ⟨429689226746652032030717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18333407007857153366643925 429689226746652032030717)
                  ·
                    rfl

theorem cell23_7531351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 7].length) (baseStart_7531351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531351 prefixEnd_7531351 := by exact prefixLift 7531351
  have htrace : WordTrace (prefixWord ++ tailWord_7531351) baseStart_7531351 baseEnd_7531351 := by
    simpa [prefixWord, tailWord_7531351, baseEnd_7531351] using wordTrace_append hprefix tailTrace_7531351
  have hstable : (prefixWord ++ tailWord_7531351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531351).length < 2 ^ (prefixWord ++ tailWord_7531351).sum := by decide
  have hdescent : baseEnd_7531351 < baseStart_7531351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531361 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_7531361 : Nat := 118140960795 + 7531361 * 2 ^ 59
def prefixEnd_7531361 : Nat := 4983230072969 + 3 ^ 40 * 7531361 * 2
def baseEnd_7531361 : Nat := 3867208175526413249151407

theorem tailTrace_7531361 : CollatzResearch.WordTrace tailWord_7531361 prefixEnd_7531361 3867208175526413249151407 := by
  unfold tailWord_7531361
  simp only [CollatzResearch.WordTrace]
  refine ⟨274691302468172825899993937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183127534978781883933329291 274691302468172825899993937)
  ·
    refine ⟨206018476851129619424995453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274691302468172825899993937 206018476851129619424995453)
    ·
      refine ⟨77256928819173607284373295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206018476851129619424995453 77256928819173607284373295)
      ·
        refine ⟨115885393228760410926559943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77256928819173607284373295 115885393228760410926559943)
        ·
          refine ⟨173828089843140616389839915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115885393228760410926559943 173828089843140616389839915)
          ·
            refine ⟨260742134764710924584759873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173828089843140616389839915 260742134764710924584759873)
            ·
              refine ⟨195556601073533193438569905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260742134764710924584759873 195556601073533193438569905)
              ·
                refine ⟨146667450805149895078927429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195556601073533193438569905 146667450805149895078927429)
                ·
                  refine ⟨27500147025965605327298893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146667450805149895078927429 27500147025965605327298893)
                  ·
                    refine ⟨10312555134737101997737085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27500147025965605327298893 10312555134737101997737085)
                    ·
                      refine ⟨3867208175526413249151407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10312555134737101997737085 3867208175526413249151407)
                      ·
                        rfl

theorem cell23_7531361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_7531361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531361 prefixEnd_7531361 := by exact prefixLift 7531361
  have htrace : WordTrace (prefixWord ++ tailWord_7531361) baseStart_7531361 baseEnd_7531361 := by
    simpa [prefixWord, tailWord_7531361, baseEnd_7531361] using wordTrace_append hprefix tailTrace_7531361
  have hstable : (prefixWord ++ tailWord_7531361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531361).length < 2 ^ (prefixWord ++ tailWord_7531361).sum := by decide
  have hdescent : baseEnd_7531361 < baseStart_7531361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531385 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 5]
def baseStart_7531385 : Nat := 118140960795 + 7531385 * 2 ^ 59
def prefixEnd_7531385 : Nat := 4983230072969 + 3 ^ 40 * 7531385 * 2
def baseEnd_7531385 : Nat := 429691166562457906139033

theorem tailTrace_7531385 : CollatzResearch.WordTrace tailWord_7531385 prefixEnd_7531385 429691166562457906139033 := by
  unfold tailWord_7531385
  simp only [CollatzResearch.WordTrace]
  refine ⟨274692177820085877998867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183128118546723918665911739 274692177820085877998867609)
  ·
    refine ⟨206019133365064408499150707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274692177820085877998867609 206019133365064408499150707)
    ·
      refine ⟨309028700047596612748726061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206019133365064408499150707 309028700047596612748726061)
      ·
        refine ⟨115885762517848729780772273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309028700047596612748726061 115885762517848729780772273)
        ·
          refine ⟨86914321888386547335579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115885762517848729780772273 86914321888386547335579205)
          ·
            refine ⟨16296435354072477625421101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86914321888386547335579205 16296435354072477625421101)
            ·
              refine ⟨6111163257777179109532913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16296435354072477625421101 6111163257777179109532913)
              ·
                refine ⟨4583372443332884332149685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6111163257777179109532913 4583372443332884332149685)
                ·
                  refine ⟨429691166562457906139033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4583372443332884332149685 429691166562457906139033)
                  ·
                    rfl

theorem cell23_7531385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 5].length) (baseStart_7531385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531385 prefixEnd_7531385 := by exact prefixLift 7531385
  have htrace : WordTrace (prefixWord ++ tailWord_7531385) baseStart_7531385 baseEnd_7531385 := by
    simpa [prefixWord, tailWord_7531385, baseEnd_7531385] using wordTrace_append hprefix tailTrace_7531385
  have hstable : (prefixWord ++ tailWord_7531385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531385).length < 2 ^ (prefixWord ++ tailWord_7531385).sum := by decide
  have hdescent : baseEnd_7531385 < baseStart_7531385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531469 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7531469 : Nat := 118140960795 + 7531469 * 2 ^ 59
def prefixEnd_7531469 : Nat := 4983230072969 + 3 ^ 40 * 7531469 * 2
def baseEnd_7531469 : Nat := 3867263631437098826600911

theorem tailTrace_7531469 : CollatzResearch.WordTrace tailWord_7531469 prefixEnd_7531469 3867263631437098826600911 := by
  unfold tailWord_7531469
  simp only [CollatzResearch.WordTrace]
  refine ⟨274695241551781560344925461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183130161034521040229950307 274695241551781560344925461)
  ·
    refine ⟨12876339447739760641168381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274695241551781560344925461 12876339447739760641168381)
    ·
      refine ⟨4828627292902410240438143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12876339447739760641168381 4828627292902410240438143)
      ·
        refine ⟨7242940939353615360657215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828627292902410240438143 7242940939353615360657215)
        ·
          refine ⟨10864411409030423040985823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242940939353615360657215 10864411409030423040985823)
          ·
            refine ⟨16296617113545634561478735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864411409030423040985823 16296617113545634561478735)
            ·
              refine ⟨24444925670318451842218103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16296617113545634561478735 24444925670318451842218103)
              ·
                refine ⟨36667388505477677763327155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24444925670318451842218103 36667388505477677763327155)
                ·
                  refine ⟨55001082758216516644990733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36667388505477677763327155 55001082758216516644990733)
                  ·
                    refine ⟨20625406034331193741871525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55001082758216516644990733 20625406034331193741871525)
                    ·
                      refine ⟨3867263631437098826600911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20625406034331193741871525 3867263631437098826600911)
                      ·
                        rfl

theorem cell23_7531469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7531469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531469 prefixEnd_7531469 := by exact prefixLift 7531469
  have htrace : WordTrace (prefixWord ++ tailWord_7531469) baseStart_7531469 baseEnd_7531469 := by
    simpa [prefixWord, tailWord_7531469, baseEnd_7531469] using wordTrace_append hprefix tailTrace_7531469
  have hstable : (prefixWord ++ tailWord_7531469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531469).length < 2 ^ (prefixWord ++ tailWord_7531469).sum := by decide
  have hdescent : baseEnd_7531469 < baseStart_7531469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531509 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 6]
def baseStart_7531509 : Nat := 118140960795 + 7531509 * 2 ^ 59
def prefixEnd_7531509 : Nat := 4983230072969 + 3 ^ 40 * 7531509 * 2
def baseEnd_7531509 : Nat := 429698241184808741122303

theorem tailTrace_7531509 : CollatzResearch.WordTrace tailWord_7531509 prefixEnd_7531509 429698241184808741122303 := by
  unfold tailWord_7531509
  simp only [CollatzResearch.WordTrace]
  refine ⟨274696700471636647176381581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183131133647757764784254387 274696700471636647176381581)
  ·
    refine ⟨103011262676863742691143093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274696700471636647176381581 103011262676863742691143093)
    ·
      refine ⟨9657305875955975877294665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103011262676863742691143093 9657305875955975877294665)
      ·
        refine ⟨7242979406966981907970999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9657305875955975877294665 7242979406966981907970999)
        ·
          refine ⟨10864469110450472861956499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242979406966981907970999 10864469110450472861956499)
          ·
            refine ⟨16296703665675709292934749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864469110450472861956499 16296703665675709292934749)
            ·
              refine ⟨6111263874628390984850531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16296703665675709292934749 6111263874628390984850531)
              ·
                refine ⟨9166895811942586477275797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111263874628390984850531 9166895811942586477275797)
                ·
                  refine ⟨429698241184808741122303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9166895811942586477275797 429698241184808741122303)
                  ·
                    rfl

theorem cell23_7531509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_7531509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531509 prefixEnd_7531509 := by exact prefixLift 7531509
  have htrace : WordTrace (prefixWord ++ tailWord_7531509) baseStart_7531509 baseEnd_7531509 := by
    simpa [prefixWord, tailWord_7531509, baseEnd_7531509] using wordTrace_append hprefix tailTrace_7531509
  have hstable : (prefixWord ++ tailWord_7531509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531509).length < 2 ^ (prefixWord ++ tailWord_7531509).sum := by decide
  have hdescent : baseEnd_7531509 < baseStart_7531509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531525 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_7531525 : Nat := 118140960795 + 7531525 * 2 ^ 59
def prefixEnd_7531525 : Nat := 4983230072969 + 3 ^ 40 * 7531525 * 2
def baseEnd_7531525 : Nat := 3867292386353750607500653

theorem tailTrace_7531525 : CollatzResearch.WordTrace tailWord_7531525 prefixEnd_7531525 3867292386353750607500653 := by
  unfold tailWord_7531525
  simp only [CollatzResearch.WordTrace]
  refine ⟨274697284039578681908964029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183131522693052454605976019 274697284039578681908964029)
  ·
    refine ⟨103011481514842005715861511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274697284039578681908964029 103011481514842005715861511)
    ·
      refine ⟨154517222272263008573792267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103011481514842005715861511 154517222272263008573792267)
      ·
        refine ⟨231775833408394512860688401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154517222272263008573792267 231775833408394512860688401)
        ·
          refine ⟨173831875056295884645516301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231775833408394512860688401 173831875056295884645516301)
          ·
            refine ⟨65186953146110956742068613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173831875056295884645516301 65186953146110956742068613)
            ·
              refine ⟨12222553714895804389137865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65186953146110956742068613 12222553714895804389137865)
              ·
                refine ⟨9166915286171853291853399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222553714895804389137865 9166915286171853291853399)
                ·
                  refine ⟨13750372929257779937780099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166915286171853291853399 13750372929257779937780099)
                  ·
                    refine ⟨20625559393886669906670149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13750372929257779937780099 20625559393886669906670149)
                    ·
                      refine ⟨3867292386353750607500653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20625559393886669906670149 3867292386353750607500653)
                      ·
                        rfl

theorem cell23_7531525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_7531525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531525 prefixEnd_7531525 := by exact prefixLift 7531525
  have htrace : WordTrace (prefixWord ++ tailWord_7531525) baseStart_7531525 baseEnd_7531525 := by
    simpa [prefixWord, tailWord_7531525, baseEnd_7531525] using wordTrace_append hprefix tailTrace_7531525
  have hstable : (prefixWord ++ tailWord_7531525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531525).length < 2 ^ (prefixWord ++ tailWord_7531525).sum := by decide
  have hdescent : baseEnd_7531525 < baseStart_7531525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531545 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_7531545 : Nat := 118140960795 + 7531545 * 2 ^ 59
def prefixEnd_7531545 : Nat := 4983230072969 + 3 ^ 40 * 7531545 * 2
def baseEnd_7531545 : Nat := 3867302655966840529250561

theorem tailTrace_7531545 : CollatzResearch.WordTrace tailWord_7531545 prefixEnd_7531545 3867302655966840529250561 := by
  unfold tailWord_7531545
  simp only [CollatzResearch.WordTrace]
  refine ⟨274698013499506225324692089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183132008999670816883128059 274698013499506225324692089)
  ·
    refine ⟨206023510124629668993519067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274698013499506225324692089 206023510124629668993519067)
    ·
      refine ⟨309035265186944503490278601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206023510124629668993519067 309035265186944503490278601)
      ·
        refine ⟨231776448890208377617708951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309035265186944503490278601 231776448890208377617708951)
        ·
          refine ⟨347664673335312566426563427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231776448890208377617708951 347664673335312566426563427)
          ·
            refine ⟨521497010002968849639845141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347664673335312566426563427 521497010002968849639845141)
            ·
              refine ⟨24445172343889164826867741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 521497010002968849639845141 24445172343889164826867741)
              ·
                refine ⟨9166939628958436810075403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24445172343889164826867741 9166939628958436810075403)
                ·
                  refine ⟨13750409443437655215113105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166939628958436810075403 13750409443437655215113105)
                  ·
                    refine ⟨10312807082578241411334829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13750409443437655215113105 10312807082578241411334829)
                    ·
                      refine ⟨3867302655966840529250561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10312807082578241411334829 3867302655966840529250561)
                      ·
                        rfl

theorem cell23_7531545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_7531545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531545 prefixEnd_7531545 := by exact prefixLift 7531545
  have htrace : WordTrace (prefixWord ++ tailWord_7531545) baseStart_7531545 baseEnd_7531545 := by
    simpa [prefixWord, tailWord_7531545, baseEnd_7531545] using wordTrace_append hprefix tailTrace_7531545
  have hstable : (prefixWord ++ tailWord_7531545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531545).length < 2 ^ (prefixWord ++ tailWord_7531545).sum := by decide
  have hdescent : baseEnd_7531545 < baseStart_7531545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531608 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_7531608 : Nat := 118140960795 + 7531608 * 2 ^ 59
def prefixEnd_7531608 : Nat := 4983230072969 + 3 ^ 40 * 7531608 * 2
def baseEnd_7531608 : Nat := 1289111668416024594254257

theorem tailTrace_7531608 : CollatzResearch.WordTrace tailWord_7531608 prefixEnd_7531608 1289111668416024594254257 := by
  unfold tailWord_7531608
  simp only [CollatzResearch.WordTrace]
  refine ⟨137350155649138993542117739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183133540865518658056156985 137350155649138993542117739)
  ·
    refine ⟨206025233473708490313176609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137350155649138993542117739 206025233473708490313176609)
    ·
      refine ⟨154518925105281367734882457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206025233473708490313176609 154518925105281367734882457)
      ·
        refine ⟨115889193828961025801161843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154518925105281367734882457 115889193828961025801161843)
        ·
          refine ⟨173833790743441538701742765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115889193828961025801161843 173833790743441538701742765)
          ·
            refine ⟨65187671528790577013153537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173833790743441538701742765 65187671528790577013153537)
            ·
              refine ⟨48890753646592932759865153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65187671528790577013153537 48890753646592932759865153)
              ·
                refine ⟨36668065234944699569898865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48890753646592932759865153 36668065234944699569898865)
                ·
                  refine ⟨27501048926208524677424149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36668065234944699569898865 27501048926208524677424149)
                  ·
                    refine ⟨1289111668416024594254257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27501048926208524677424149 1289111668416024594254257)
                    ·
                      rfl

theorem cell23_7531608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_7531608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531608 prefixEnd_7531608 := by exact prefixLift 7531608
  have htrace : WordTrace (prefixWord ++ tailWord_7531608) baseStart_7531608 baseEnd_7531608 := by
    simpa [prefixWord, tailWord_7531608, baseEnd_7531608] using wordTrace_append hprefix tailTrace_7531608
  have hstable : (prefixWord ++ tailWord_7531608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531608).length < 2 ^ (prefixWord ++ tailWord_7531608).sum := by decide
  have hdescent : baseEnd_7531608 < baseStart_7531608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531615 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 4, 2]
def baseStart_7531615 : Nat := 118140960795 + 7531615 * 2 ^ 59
def prefixEnd_7531615 : Nat := 4983230072969 + 3 ^ 40 * 7531615 * 2
def baseEnd_7531615 : Nat := 3867338599612655255375239

theorem tailTrace_7531615 : CollatzResearch.WordTrace tailWord_7531615 prefixEnd_7531615 3867338599612655255375239 := by
  unfold tailWord_7531615
  simp only [CollatzResearch.WordTrace]
  refine ⟨274700566609252627279740299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183133711072835084853160199 274700566609252627279740299)
  ·
    refine ⟨412050849913878940919610449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274700566609252627279740299 412050849913878940919610449)
    ·
      refine ⟨309038137435409205689707837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412050849913878940919610449 309038137435409205689707837)
      ·
        refine ⟨115889301538278452133640439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309038137435409205689707837 115889301538278452133640439)
        ·
          refine ⟨173833952307417678200460659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115889301538278452133640439 173833952307417678200460659)
          ·
            refine ⟨260750928461126517300690989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173833952307417678200460659 260750928461126517300690989)
            ·
              refine ⟨97781598172922443987759121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260750928461126517300690989 97781598172922443987759121)
              ·
                refine ⟨73336198629691832990819341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97781598172922443987759121 73336198629691832990819341)
                ·
                  refine ⟨27501074486134437371557253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73336198629691832990819341 27501074486134437371557253)
                  ·
                    refine ⟨5156451466150207007166985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27501074486134437371557253 5156451466150207007166985)
                    ·
                      refine ⟨3867338599612655255375239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156451466150207007166985 3867338599612655255375239)
                      ·
                        rfl

theorem cell23_7531615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_7531615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531615 prefixEnd_7531615 := by exact prefixLift 7531615
  have htrace : WordTrace (prefixWord ++ tailWord_7531615) baseStart_7531615 baseEnd_7531615 := by
    simpa [prefixWord, tailWord_7531615, baseEnd_7531615] using wordTrace_append hprefix tailTrace_7531615
  have hstable : (prefixWord ++ tailWord_7531615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531615).length < 2 ^ (prefixWord ++ tailWord_7531615).sum := by decide
  have hdescent : baseEnd_7531615 < baseStart_7531615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531632 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2]
def baseStart_7531632 : Nat := 118140960795 + 7531632 * 2 ^ 59
def prefixEnd_7531632 : Nat := 4983230072969 + 3 ^ 40 * 7531632 * 2
def baseEnd_7531632 : Nat := 3867347328783781688862661

theorem tailTrace_7531632 : CollatzResearch.WordTrace tailWord_7531632 prefixEnd_7531632 3867347328783781688862661 := by
  unfold tailWord_7531632
  simp only [CollatzResearch.WordTrace]
  refine ⟨137350593325095519591554575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183134124433460692788739433 137350593325095519591554575)
  ·
    refine ⟨206025889987643279387331863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137350593325095519591554575 206025889987643279387331863)
    ·
      refine ⟨309038834981464919080997795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206025889987643279387331863 309038834981464919080997795)
      ·
        refine ⟨463558252472197378621496693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309038834981464919080997795 463558252472197378621496693)
        ·
          refine ⟨43458586169268504245765315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 463558252472197378621496693 43458586169268504245765315)
          ·
            refine ⟨65187879253902756368647973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43458586169268504245765315 65187879253902756368647973)
            ·
              refine ⟨12222727360106766819121495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65187879253902756368647973 12222727360106766819121495)
              ·
                refine ⟨18334091040160150228682243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222727360106766819121495 18334091040160150228682243)
                ·
                  refine ⟨27501136560240225343023365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18334091040160150228682243 27501136560240225343023365)
                  ·
                    refine ⟨5156463105045042251816881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27501136560240225343023365 5156463105045042251816881)
                    ·
                      refine ⟨3867347328783781688862661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156463105045042251816881 3867347328783781688862661)
                      ·
                        rfl

theorem cell23_7531632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2].length) (baseStart_7531632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531632 prefixEnd_7531632 := by exact prefixLift 7531632
  have htrace : WordTrace (prefixWord ++ tailWord_7531632) baseStart_7531632 baseEnd_7531632 := by
    simpa [prefixWord, tailWord_7531632, baseEnd_7531632] using wordTrace_append hprefix tailTrace_7531632
  have hstable : (prefixWord ++ tailWord_7531632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531632).length < 2 ^ (prefixWord ++ tailWord_7531632).sum := by decide
  have hdescent : baseEnd_7531632 < baseStart_7531632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531653 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_7531653 : Nat := 118140960795 + 7531653 * 2 ^ 59
def prefixEnd_7531653 : Nat := 4983230072969 + 3 ^ 40 * 7531653 * 2
def baseEnd_7531653 : Nat := 3867358111877526106700065

theorem tailTrace_7531653 : CollatzResearch.WordTrace tailWord_7531653 prefixEnd_7531653 3867358111877526106700065 := by
  unfold tailWord_7531653
  simp only [CollatzResearch.WordTrace]
  refine ⟨274701952583114959769623613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183134635055409973179749075 274701952583114959769623613)
  ·
    refine ⟨103013232218668109913608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274701952583114959769623613 103013232218668109913608855)
    ·
      refine ⟨154519848328002164870413283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103013232218668109913608855 154519848328002164870413283)
      ·
        refine ⟨231779772492003247305619925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154519848328002164870413283 231779772492003247305619925)
        ·
          refine ⟨5432338417781326108725467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231779772492003247305619925 5432338417781326108725467)
          ·
            refine ⟨8148507626671989163088201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432338417781326108725467 8148507626671989163088201)
            ·
              refine ⟨6111380720003991872316151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8148507626671989163088201 6111380720003991872316151)
              ·
                refine ⟨9167071080005987808474227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111380720003991872316151 9167071080005987808474227)
                ·
                  refine ⟨13750606620008981712711341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167071080005987808474227 13750606620008981712711341)
                  ·
                    refine ⟨5156477482503368142266753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13750606620008981712711341 5156477482503368142266753)
                    ·
                      refine ⟨3867358111877526106700065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156477482503368142266753 3867358111877526106700065)
                      ·
                        rfl

theorem cell23_7531653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_7531653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531653 prefixEnd_7531653 := by exact prefixLift 7531653
  have htrace : WordTrace (prefixWord ++ tailWord_7531653) baseStart_7531653 baseEnd_7531653 := by
    simpa [prefixWord, tailWord_7531653, baseEnd_7531653] using wordTrace_append hprefix tailTrace_7531653
  have hstable : (prefixWord ++ tailWord_7531653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531653).length < 2 ^ (prefixWord ++ tailWord_7531653).sum := by decide
  have hdescent : baseEnd_7531653 < baseStart_7531653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531666 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7531666 : Nat := 118140960795 + 7531666 * 2 ^ 59
def prefixEnd_7531666 : Nat := 4983230072969 + 3 ^ 40 * 7531666 * 2
def baseEnd_7531666 : Nat := 3867364787126034555837505

theorem tailTrace_7531666 : CollatzResearch.WordTrace tailWord_7531666 prefixEnd_7531666 3867364787126034555837505 := by
  unfold tailWord_7531666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68675606683016965747461713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183134951154711908659897901 68675606683016965747461713)
  ·
    refine ⟨51506705012262724310596285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68675606683016965747461713 51506705012262724310596285)
    ·
      refine ⟨19315014379598521616473607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51506705012262724310596285 19315014379598521616473607)
      ·
        refine ⟨28972521569397782424710411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19315014379598521616473607 28972521569397782424710411)
        ·
          refine ⟨43458782354096673637065617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28972521569397782424710411 43458782354096673637065617)
          ·
            refine ⟨32594086765572505227799213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43458782354096673637065617 32594086765572505227799213)
            ·
              refine ⟨12222782537089689460424705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32594086765572505227799213 12222782537089689460424705)
              ·
                refine ⟨9167086902817267095318529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222782537089689460424705 9167086902817267095318529)
                ·
                  refine ⟨6875315177112950321488897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167086902817267095318529 6875315177112950321488897)
                  ·
                    refine ⟨5156486382834712741116673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875315177112950321488897 5156486382834712741116673)
                    ·
                      refine ⟨3867364787126034555837505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156486382834712741116673 3867364787126034555837505)
                      ·
                        rfl

theorem cell23_7531666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7531666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531666 prefixEnd_7531666 := by exact prefixLift 7531666
  have htrace : WordTrace (prefixWord ++ tailWord_7531666) baseStart_7531666 baseEnd_7531666 := by
    simpa [prefixWord, tailWord_7531666, baseEnd_7531666] using wordTrace_append hprefix tailTrace_7531666
  have hstable : (prefixWord ++ tailWord_7531666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531666).length < 2 ^ (prefixWord ++ tailWord_7531666).sum := by decide
  have hdescent : baseEnd_7531666 < baseStart_7531666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531672 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 5]
def baseStart_7531672 : Nat := 118140960795 + 7531672 * 2 ^ 59
def prefixEnd_7531672 : Nat := 4983230072969 + 3 ^ 40 * 7531672 * 2
def baseEnd_7531672 : Nat := 429707540889995725818053

theorem tailTrace_7531672 : CollatzResearch.WordTrace tailWord_7531672 prefixEnd_7531672 429707540889995725818053 := by
  unfold tailWord_7531672
  simp only [CollatzResearch.WordTrace]
  refine ⟨137351322785023063007282635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183135097046697417343043513 137351322785023063007282635)
  ·
    refine ⟨206026984177534594510923953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137351322785023063007282635 206026984177534594510923953)
    ·
      refine ⟨154520238133150945883192965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206026984177534594510923953 154520238133150945883192965)
      ·
        refine ⟨28972544649965802353098681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154520238133150945883192965 28972544649965802353098681)
        ·
          refine ⟨21729408487474351764824011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28972544649965802353098681 21729408487474351764824011)
          ·
            refine ⟨32594112731211527647236017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21729408487474351764824011 32594112731211527647236017)
            ·
              refine ⟨24445584548408645735427013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32594112731211527647236017 24445584548408645735427013)
              ·
                refine ⟨4583547102826621075392565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24445584548408645735427013 4583547102826621075392565)
                ·
                  refine ⟨429707540889995725818053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4583547102826621075392565 429707540889995725818053)
                  ·
                    rfl

theorem cell23_7531672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 5].length) (baseStart_7531672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531672 prefixEnd_7531672 := by exact prefixLift 7531672
  have htrace : WordTrace (prefixWord ++ tailWord_7531672) baseStart_7531672 baseEnd_7531672 := by
    simpa [prefixWord, tailWord_7531672, baseEnd_7531672] using wordTrace_append hprefix tailTrace_7531672
  have hstable : (prefixWord ++ tailWord_7531672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531672).length < 2 ^ (prefixWord ++ tailWord_7531672).sum := by decide
  have hdescent : baseEnd_7531672 < baseStart_7531672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531705 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7531705 : Nat := 118140960795 + 7531705 * 2 ^ 59
def prefixEnd_7531705 : Nat := 4983230072969 + 3 ^ 40 * 7531705 * 2
def baseEnd_7531705 : Nat := 3867384812871559903249825

theorem tailTrace_7531705 : CollatzResearch.WordTrace tailWord_7531705 prefixEnd_7531705 3867384812871559903249825 := by
  unfold tailWord_7531705
  simp only [CollatzResearch.WordTrace]
  refine ⟨274703849178926572650516569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183135899452617715100344379 274703849178926572650516569)
  ·
    refine ⟨206027886884194929487887427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274703849178926572650516569 206027886884194929487887427)
    ·
      refine ⟨309041830326292394231831141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206027886884194929487887427 309041830326292394231831141)
      ·
        refine ⟨57945343186179823918468339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309041830326292394231831141 57945343186179823918468339)
        ·
          refine ⟨86918014779269735877702509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57945343186179823918468339 86918014779269735877702509)
          ·
            refine ⟨32594255542226150954138441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86918014779269735877702509 32594255542226150954138441)
            ·
              refine ⟨24445691656669613215603831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32594255542226150954138441 24445691656669613215603831)
              ·
                refine ⟨36668537485004419823405747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24445691656669613215603831 36668537485004419823405747)
                ·
                  refine ⟨55002806227506629735108621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36668537485004419823405747 55002806227506629735108621)
                  ·
                    refine ⟨20626052335314986150665733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55002806227506629735108621 20626052335314986150665733)
                    ·
                      refine ⟨3867384812871559903249825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20626052335314986150665733 3867384812871559903249825)
                      ·
                        rfl

theorem cell23_7531705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7531705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531705 prefixEnd_7531705 := by exact prefixLift 7531705
  have htrace : WordTrace (prefixWord ++ tailWord_7531705) baseStart_7531705 baseEnd_7531705 := by
    simpa [prefixWord, tailWord_7531705, baseEnd_7531705] using wordTrace_append hprefix tailTrace_7531705
  have hstable : (prefixWord ++ tailWord_7531705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531705).length < 2 ^ (prefixWord ++ tailWord_7531705).sum := by decide
  have hdescent : baseEnd_7531705 < baseStart_7531705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531722 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_7531722 : Nat := 118140960795 + 7531722 * 2 ^ 59
def prefixEnd_7531722 : Nat := 4983230072969 + 3 ^ 40 * 7531722 * 2
def baseEnd_7531722 : Nat := 3867393542042686336737247

theorem tailTrace_7531722 : CollatzResearch.WordTrace tailWord_7531722 prefixEnd_7531722 3867393542042686336737247 := by
  unfold tailWord_7531722
  simp only [CollatzResearch.WordTrace]
  refine ⟨68676117304966246138471355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183136312813243323035923613 68676117304966246138471355)
  ·
    refine ⟨103014175957449369207707033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68676117304966246138471355 103014175957449369207707033)
    ·
      refine ⟨77260631968087026905780275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103014175957449369207707033 77260631968087026905780275)
      ·
        refine ⟨115890947952130540358670413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77260631968087026905780275 115890947952130540358670413)
        ·
          refine ⟨43459105482048952634501405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115890947952130540358670413 43459105482048952634501405)
          ·
            refine ⟨16297164555768357237938027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43459105482048952634501405 16297164555768357237938027)
            ·
              refine ⟨24445746833652535856907041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16297164555768357237938027 24445746833652535856907041)
              ·
                refine ⟨18334310125239401892680281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24445746833652535856907041 18334310125239401892680281)
                ·
                  refine ⟨13750732593929551419510211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18334310125239401892680281 13750732593929551419510211)
                  ·
                    refine ⟨20626098890894327129265317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13750732593929551419510211 20626098890894327129265317)
                    ·
                      refine ⟨3867393542042686336737247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20626098890894327129265317 3867393542042686336737247)
                      ·
                        rfl

theorem cell23_7531722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_7531722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531722 prefixEnd_7531722 := by exact prefixLift 7531722
  have htrace : WordTrace (prefixWord ++ tailWord_7531722) baseStart_7531722 baseEnd_7531722 := by
    simpa [prefixWord, tailWord_7531722, baseEnd_7531722] using wordTrace_append hprefix tailTrace_7531722
  have hstable : (prefixWord ++ tailWord_7531722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531722).length < 2 ^ (prefixWord ++ tailWord_7531722).sum := by decide
  have hdescent : baseEnd_7531722 < baseStart_7531722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531759 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_7531759 : Nat := 118140960795 + 7531759 * 2 ^ 59
def prefixEnd_7531759 : Nat := 4983230072969 + 3 ^ 40 * 7531759 * 2
def baseEnd_7531759 : Nat := 3867412540826902691974577

theorem tailTrace_7531759 : CollatzResearch.WordTrace tailWord_7531759 prefixEnd_7531759 3867412540826902691974577 := by
  unfold tailWord_7531759
  simp only [CollatzResearch.WordTrace]
  refine ⟨274705818720730939872982331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183137212480487293248654887 274705818720730939872982331)
  ·
    refine ⟨412058728081096409809473497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274705818720730939872982331 412058728081096409809473497)
    ·
      refine ⟨309044046060822307357105123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412058728081096409809473497 309044046060822307357105123)
      ·
        refine ⟨463566069091233461035657685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309044046060822307357105123 463566069091233461035657685)
        ·
          refine ⟨10864829744325784243023227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 463566069091233461035657685 10864829744325784243023227)
          ·
            refine ⟨16297244616488676364534841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864829744325784243023227 16297244616488676364534841)
            ·
              refine ⟨12222933462366507273401131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16297244616488676364534841 12222933462366507273401131)
              ·
                refine ⟨18334400193549760910101697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222933462366507273401131 18334400193549760910101697)
                ·
                  refine ⟨13750800145162320682576273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18334400193549760910101697 13750800145162320682576273)
                  ·
                    refine ⟨10313100108871740511932205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13750800145162320682576273 10313100108871740511932205)
                    ·
                      refine ⟨3867412540826902691974577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313100108871740511932205 3867412540826902691974577)
                      ·
                        rfl

theorem cell23_7531759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_7531759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531759 prefixEnd_7531759 := by exact prefixLift 7531759
  have htrace : WordTrace (prefixWord ++ tailWord_7531759) baseStart_7531759 baseEnd_7531759 := by
    simpa [prefixWord, tailWord_7531759, baseEnd_7531759] using wordTrace_append hprefix tailTrace_7531759
  have hstable : (prefixWord ++ tailWord_7531759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531759).length < 2 ^ (prefixWord ++ tailWord_7531759).sum := by decide
  have hdescent : baseEnd_7531759 < baseStart_7531759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531812 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7531812 : Nat := 118140960795 + 7531812 * 2 ^ 59
def prefixEnd_7531812 : Nat := 4983230072969 + 3 ^ 40 * 7531812 * 2
def baseEnd_7531812 : Nat := 3867439755301590984611833

theorem tailTrace_7531812 : CollatzResearch.WordTrace tailWord_7531812 prefixEnd_7531812 3867439755301590984611833 := by
  unfold tailWord_7531812
  simp only [CollatzResearch.WordTrace]
  refine ⟨137353875894769464962330845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183138501193025953283107793 137353875894769464962330845)
  ·
    refine ⟨51507703460538549360874067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137353875894769464962330845 51507703460538549360874067)
    ·
      refine ⟨77261555190807824041311101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51507703460538549360874067 77261555190807824041311101)
      ·
        refine ⟨28973083196552934015491663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77261555190807824041311101 28973083196552934015491663)
        ·
          refine ⟨43459624794829401023237495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28973083196552934015491663 43459624794829401023237495)
          ·
            refine ⟨65189437192244101534856243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43459624794829401023237495 65189437192244101534856243)
            ·
              refine ⟨97784155788366152302284365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65189437192244101534856243 97784155788366152302284365)
              ·
                refine ⟨36669058420637307113356637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97784155788366152302284365 36669058420637307113356637)
                ·
                  refine ⟨13750896907738990167508739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36669058420637307113356637 13750896907738990167508739)
                  ·
                    refine ⟨20626345361608485251263109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13750896907738990167508739 20626345361608485251263109)
                    ·
                      refine ⟨3867439755301590984611833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20626345361608485251263109 3867439755301590984611833)
                      ·
                        rfl

theorem cell23_7531812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7531812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531812 prefixEnd_7531812 := by exact prefixLift 7531812
  have htrace : WordTrace (prefixWord ++ tailWord_7531812) baseStart_7531812 baseEnd_7531812 := by
    simpa [prefixWord, tailWord_7531812, baseEnd_7531812] using wordTrace_append hprefix tailTrace_7531812
  have hstable : (prefixWord ++ tailWord_7531812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531812).length < 2 ^ (prefixWord ++ tailWord_7531812).sum := by decide
  have hdescent : baseEnd_7531812 < baseStart_7531812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531816 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7531816 : Nat := 118140960795 + 7531816 * 2 ^ 59
def prefixEnd_7531816 : Nat := 4983230072969 + 3 ^ 40 * 7531816 * 2
def baseEnd_7531816 : Nat := 3867441809224208968961815

theorem tailTrace_7531816 : CollatzResearch.WordTrace tailWord_7531816 prefixEnd_7531816 3867441809224208968961815 := by
  unfold tailWord_7531816
  simp only [CollatzResearch.WordTrace]
  refine ⟨137353948840762219303903651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183138598454349625738538201 137353948840762219303903651)
  ·
    refine ⟨206030923261143328955855477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137353948840762219303903651 206030923261143328955855477)
    ·
      refine ⟨19315399055732187089611451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206030923261143328955855477 19315399055732187089611451)
      ·
        refine ⟨28973098583598280634417177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19315399055732187089611451 28973098583598280634417177)
        ·
          refine ⟨21729823937698710475812883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28973098583598280634417177 21729823937698710475812883)
          ·
            refine ⟨32594735906548065713719325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21729823937698710475812883 32594735906548065713719325)
            ·
              refine ⟨12223025964955524642644747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32594735906548065713719325 12223025964955524642644747)
              ·
                refine ⟨18334538947433286963967121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12223025964955524642644747 18334538947433286963967121)
                ·
                  refine ⟨13750904210574965222975341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18334538947433286963967121 13750904210574965222975341)
                  ·
                    refine ⟨5156589078965611958615753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13750904210574965222975341 5156589078965611958615753)
                    ·
                      refine ⟨3867441809224208968961815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156589078965611958615753 3867441809224208968961815)
                      ·
                        rfl

theorem cell23_7531816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7531816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531816 prefixEnd_7531816 := by exact prefixLift 7531816
  have htrace : WordTrace (prefixWord ++ tailWord_7531816) baseStart_7531816 baseEnd_7531816 := by
    simpa [prefixWord, tailWord_7531816, baseEnd_7531816] using wordTrace_append hprefix tailTrace_7531816
  have hstable : (prefixWord ++ tailWord_7531816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531816).length < 2 ^ (prefixWord ++ tailWord_7531816).sum := by decide
  have hdescent : baseEnd_7531816 < baseStart_7531816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531826 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_7531826 : Nat := 118140960795 + 7531826 * 2 ^ 59
def prefixEnd_7531826 : Nat := 4983230072969 + 3 ^ 40 * 7531826 * 2
def baseEnd_7531826 : Nat := 1289148981343584643278923

theorem tailTrace_7531826 : CollatzResearch.WordTrace tailWord_7531826 prefixEnd_7531826 1289148981343584643278923 := by
  unfold tailWord_7531826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68677065602872052578917833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183138841607658806877114221 68677065602872052578917833)
  ·
    refine ⟨51507799202154039434188375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68677065602872052578917833 51507799202154039434188375)
    ·
      refine ⟨77261698803231059151282563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51507799202154039434188375 77261698803231059151282563)
      ·
        refine ⟨115892548204846588726923845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77261698803231059151282563 115892548204846588726923845)
        ·
          refine ⟨21729852788408735386298221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115892548204846588726923845 21729852788408735386298221)
          ·
            refine ⟨8148694795653275769861833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21729852788408735386298221 8148694795653275769861833)
            ·
              refine ⟨6111521096739956827396375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8148694795653275769861833 6111521096739956827396375)
              ·
                refine ⟨9167281645109935241094563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111521096739956827396375 9167281645109935241094563)
                ·
                  refine ⟨13750922467664902861641845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167281645109935241094563 13750922467664902861641845)
                  ·
                    refine ⟨1289148981343584643278923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13750922467664902861641845 1289148981343584643278923)
                    ·
                      rfl

theorem cell23_7531826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_7531826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531826 prefixEnd_7531826 := by exact prefixLift 7531826
  have htrace : WordTrace (prefixWord ++ tailWord_7531826) baseStart_7531826 baseEnd_7531826 := by
    simpa [prefixWord, tailWord_7531826, baseEnd_7531826] using wordTrace_append hprefix tailTrace_7531826
  have hstable : (prefixWord ++ tailWord_7531826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531826).length < 2 ^ (prefixWord ++ tailWord_7531826).sum := by decide
  have hdescent : baseEnd_7531826 < baseStart_7531826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531829 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7531829 : Nat := 118140960795 + 7531829 * 2 ^ 59
def prefixEnd_7531829 : Nat := 4983230072969 + 3 ^ 40 * 7531829 * 2
def baseEnd_7531829 : Nat := 3867448484472717418099255

theorem tailTrace_7531829 : CollatzResearch.WordTrace tailWord_7531829 prefixEnd_7531829 3867448484472717418099255 := by
  unfold tailWord_7531829
  simp only [CollatzResearch.WordTrace]
  refine ⟨274708371830477341828030541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183138914553651561218687027 274708371830477341828030541)
  ·
    refine ⟨103015639436429003185511453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274708371830477341828030541 103015639436429003185511453)
    ·
      refine ⟨38630864788660876194566795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103015639436429003185511453 38630864788660876194566795)
      ·
        refine ⟨57946297182991314291850193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38630864788660876194566795 57946297182991314291850193)
        ·
          refine ⟨43459722887243485718887645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57946297182991314291850193 43459722887243485718887645)
          ·
            refine ⟨16297396082716307144582867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43459722887243485718887645 16297396082716307144582867)
            ·
              refine ⟨24446094124074460716874301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16297396082716307144582867 24446094124074460716874301)
              ·
                refine ⟨9167285296527922768827863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24446094124074460716874301 9167285296527922768827863)
                ·
                  refine ⟨13750927944791884153241795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167285296527922768827863 13750927944791884153241795)
                  ·
                    refine ⟨20626391917187826229862693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13750927944791884153241795 20626391917187826229862693)
                    ·
                      refine ⟨3867448484472717418099255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20626391917187826229862693 3867448484472717418099255)
                      ·
                        rfl

theorem cell23_7531829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7531829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531829 prefixEnd_7531829 := by exact prefixLift 7531829
  have htrace : WordTrace (prefixWord ++ tailWord_7531829) baseStart_7531829 baseEnd_7531829 := by
    simpa [prefixWord, tailWord_7531829, baseEnd_7531829] using wordTrace_append hprefix tailTrace_7531829
  have hstable : (prefixWord ++ tailWord_7531829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531829).length < 2 ^ (prefixWord ++ tailWord_7531829).sum := by decide
  have hdescent : baseEnd_7531829 < baseStart_7531829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531839 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 2, 4]
def baseStart_7531839 : Nat := 118140960795 + 7531839 * 2 ^ 59
def prefixEnd_7531839 : Nat := 4983230072969 + 3 ^ 40 * 7531839 * 2
def baseEnd_7531839 : Nat := 1289151206426420792991403

theorem tailTrace_7531839 : CollatzResearch.WordTrace tailWord_7531839 prefixEnd_7531839 1289151206426420792991403 := by
  unfold tailWord_7531839
  simp only [CollatzResearch.WordTrace]
  refine ⟨274708736560441113535894571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183139157706960742357263047 274708736560441113535894571)
  ·
    refine ⟨412063104840661670303841857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274708736560441113535894571 412063104840661670303841857)
    ·
      refine ⟨309047328630496252727881393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412063104840661670303841857 309047328630496252727881393)
      ·
        refine ⟨231785496472872189545911045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309047328630496252727881393 231785496472872189545911045)
        ·
          refine ⟨43459780588663535539858321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231785496472872189545911045 43459780588663535539858321)
          ·
            refine ⟨32594835441497651654893741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43459780588663535539858321 32594835441497651654893741)
            ·
              refine ⟨12223063290561619370585153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32594835441497651654893741 12223063290561619370585153)
              ·
                refine ⟨9167297467921214527938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12223063290561619370585153 9167297467921214527938865)
                ·
                  refine ⟨6875473100940910895954149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167297467921214527938865 6875473100940910895954149)
                  ·
                    refine ⟨1289151206426420792991403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875473100940910895954149 1289151206426420792991403)
                    ·
                      rfl

theorem cell23_7531839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_7531839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531839 prefixEnd_7531839 := by exact prefixLift 7531839
  have htrace : WordTrace (prefixWord ++ tailWord_7531839) baseStart_7531839 baseEnd_7531839 := by
    simpa [prefixWord, tailWord_7531839, baseEnd_7531839] using wordTrace_append hprefix tailTrace_7531839
  have hstable : (prefixWord ++ tailWord_7531839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531839).length < 2 ^ (prefixWord ++ tailWord_7531839).sum := by decide
  have hdescent : baseEnd_7531839 < baseStart_7531839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531865 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_7531865 : Nat := 118140960795 + 7531865 * 2 ^ 59
def prefixEnd_7531865 : Nat := 4983230072969 + 3 ^ 40 * 7531865 * 2
def baseEnd_7531865 : Nat := 1289155656592093092416363

theorem tailTrace_7531865 : CollatzResearch.WordTrace tailWord_7531865 prefixEnd_7531865 1289155656592093092416363 := by
  unfold tailWord_7531865
  simp only [CollatzResearch.WordTrace]
  refine ⟨274709684858346919976341049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183139789905564613317560699 274709684858346919976341049)
  ·
    refine ⟨206032263643760189982255787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274709684858346919976341049 206032263643760189982255787)
    ·
      refine ⟨309048395465640284973383681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206032263643760189982255787 309048395465640284973383681)
      ·
        refine ⟨231786296599230213730037761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309048395465640284973383681 231786296599230213730037761)
        ·
          refine ⟨173839722449422660297528321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231786296599230213730037761 173839722449422660297528321)
          ·
            refine ⟨130379791837066995223146241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173839722449422660297528321 130379791837066995223146241)
            ·
              refine ⟨97784843877800246417359681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130379791837066995223146241 97784843877800246417359681)
              ·
                refine ⟨73338632908350184813019761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97784843877800246417359681 73338632908350184813019761)
                ·
                  refine ⟨55003974681262638609764821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73338632908350184813019761 55003974681262638609764821)
                  ·
                    refine ⟨1289155656592093092416363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55003974681262638609764821 1289155656592093092416363)
                    ·
                      rfl

theorem cell23_7531865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_7531865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531865 prefixEnd_7531865 := by exact prefixLift 7531865
  have htrace : WordTrace (prefixWord ++ tailWord_7531865) baseStart_7531865 baseEnd_7531865 := by
    simpa [prefixWord, tailWord_7531865, baseEnd_7531865] using wordTrace_append hprefix tailTrace_7531865
  have hstable : (prefixWord ++ tailWord_7531865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531865).length < 2 ^ (prefixWord ++ tailWord_7531865).sum := by decide
  have hdescent : baseEnd_7531865 < baseStart_7531865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531886 : List Nat := [4, 1, 2, 4, 2, 1, 9]
def baseStart_7531886 : Nat := 118140960795 + 7531886 * 2 ^ 59
def prefixEnd_7531886 : Nat := 4983230072969 + 3 ^ 40 * 7531886 * 2
def baseEnd_7531886 : Nat := 47746638924321280186253

theorem tailTrace_7531886 : CollatzResearch.WordTrace tailWord_7531886 prefixEnd_7531886 47746638924321280186253 := by
  unfold tailWord_7531886
  simp only [CollatzResearch.WordTrace]
  refine ⟨34338806348908855070356939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183140300527513893708570341 34338806348908855070356939)
  ·
    refine ⟨51508209523363282605535409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34338806348908855070356939 51508209523363282605535409)
    ·
      refine ⟨38631157142522461954151557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51508209523363282605535409 38631157142522461954151557)
      ·
        refine ⟨7243341964222961616403417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38631157142522461954151557 7243341964222961616403417)
        ·
          refine ⟨5432506473167221212302563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7243341964222961616403417 5432506473167221212302563)
          ·
            refine ⟨8148759709750831818453845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432506473167221212302563 8148759709750831818453845)
            ·
              refine ⟨47746638924321280186253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8148759709750831818453845 47746638924321280186253)
              ·
                rfl

theorem cell23_7531886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 9].length) (baseStart_7531886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531886 prefixEnd_7531886 := by exact prefixLift 7531886
  have htrace : WordTrace (prefixWord ++ tailWord_7531886) baseStart_7531886 baseEnd_7531886 := by
    simpa [prefixWord, tailWord_7531886, baseEnd_7531886] using wordTrace_append hprefix tailTrace_7531886
  have hstable : (prefixWord ++ tailWord_7531886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531886).length < 2 ^ (prefixWord ++ tailWord_7531886).sum := by decide
  have hdescent : baseEnd_7531886 < baseStart_7531886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531953 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7531953 : Nat := 118140960795 + 7531953 * 2 ^ 59
def prefixEnd_7531953 : Nat := 4983230072969 + 3 ^ 40 * 7531953 * 2
def baseEnd_7531953 : Nat := 3867512156073874932948685

theorem tailTrace_7531953 : CollatzResearch.WordTrace tailWord_7531953 prefixEnd_7531953 3867512156073874932948685 := by
  unfold tailWord_7531953
  simp only [CollatzResearch.WordTrace]
  refine ⟨274712894482028111005544513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183141929654685407337029675 274712894482028111005544513)
  ·
    refine ⟨206034670861521083254158385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274712894482028111005544513 206034670861521083254158385)
    ·
      refine ⟨154526003146140812440618789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206034670861521083254158385 154526003146140812440618789)
      ·
        refine ⟨28973625589901402332616023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154526003146140812440618789 28973625589901402332616023)
        ·
          refine ⟨43460438384852103498924035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28973625589901402332616023 43460438384852103498924035)
          ·
            refine ⟨65190657577278155248386053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43460438384852103498924035 65190657577278155248386053)
            ·
              refine ⟨12223248295739654109072385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65190657577278155248386053 12223248295739654109072385)
              ·
                refine ⟨9167436221804740581804289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12223248295739654109072385 9167436221804740581804289)
                ·
                  refine ⟨6875577166353555436353217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167436221804740581804289 6875577166353555436353217)
                  ·
                    refine ⟨5156682874765166577264913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875577166353555436353217 5156682874765166577264913)
                    ·
                      refine ⟨3867512156073874932948685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156682874765166577264913 3867512156073874932948685)
                      ·
                        rfl

theorem cell23_7531953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7531953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531953 prefixEnd_7531953 := by exact prefixLift 7531953
  have htrace : WordTrace (prefixWord ++ tailWord_7531953) baseStart_7531953 baseEnd_7531953 := by
    simpa [prefixWord, tailWord_7531953, baseEnd_7531953] using wordTrace_append hprefix tailTrace_7531953
  have hstable : (prefixWord ++ tailWord_7531953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531953).length < 2 ^ (prefixWord ++ tailWord_7531953).sum := by decide
  have hdescent : baseEnd_7531953 < baseStart_7531953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531959 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 5]
def baseStart_7531959 : Nat := 118140960795 + 7531959 * 2 ^ 59
def prefixEnd_7531959 : Nat := 4983230072969 + 3 ^ 40 * 7531959 * 2
def baseEnd_7531959 : Nat := 429723915217533545497073

theorem tailTrace_7531959 : CollatzResearch.WordTrace tailWord_7531959 prefixEnd_7531959 429723915217533545497073 := by
  unfold tailWord_7531959
  simp only [CollatzResearch.WordTrace]
  refine ⟨274713113320006374030262931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183142075546670916020175287 274713113320006374030262931)
  ·
    refine ⟨412069669980009561045394397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274713113320006374030262931 412069669980009561045394397)
    ·
      refine ⟨154526126242503585392022899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412069669980009561045394397 154526126242503585392022899)
      ·
        refine ⟨231789189363755378088034349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154526126242503585392022899 231789189363755378088034349)
        ·
          refine ⟨86920946011408266783012881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231789189363755378088034349 86920946011408266783012881)
          ·
            refine ⟨65190709508556200087259661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86920946011408266783012881 65190709508556200087259661)
            ·
              refine ⟨24446516065708575032722373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65190709508556200087259661 24446516065708575032722373)
              ·
                refine ⟨4583721762320357818635445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24446516065708575032722373 4583721762320357818635445)
                ·
                  refine ⟨429723915217533545497073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4583721762320357818635445 429723915217533545497073)
                  ·
                    rfl

theorem cell23_7531959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 5].length) (baseStart_7531959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531959 prefixEnd_7531959 := by exact prefixLift 7531959
  have htrace : WordTrace (prefixWord ++ tailWord_7531959) baseStart_7531959 baseEnd_7531959 := by
    simpa [prefixWord, tailWord_7531959, baseEnd_7531959] using wordTrace_append hprefix tailTrace_7531959
  have hstable : (prefixWord ++ tailWord_7531959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531959).length < 2 ^ (prefixWord ++ tailWord_7531959).sum := by decide
  have hdescent : baseEnd_7531959 < baseStart_7531959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7531982 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7531982 : Nat := 118140960795 + 7531982 * 2 ^ 59
def prefixEnd_7531982 : Nat := 4983230072969 + 3 ^ 40 * 7531982 * 2
def baseEnd_7531982 : Nat := 3867527047012855319486051

theorem tailTrace_7531982 : CollatzResearch.WordTrace tailWord_7531982 prefixEnd_7531982 3867527047012855319486051 := by
  unfold tailWord_7531982
  simp only [CollatzResearch.WordTrace]
  refine ⟨34339244024865381119793775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183142634799282032638900133 34339244024865381119793775)
  ·
    refine ⟨51508866037298071679690663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34339244024865381119793775 51508866037298071679690663)
    ·
      refine ⟨77263299055947107519535995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51508866037298071679690663 77263299055947107519535995)
      ·
        refine ⟨115894948583920661279303993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77263299055947107519535995 115894948583920661279303993)
        ·
          refine ⟨86921211437940495959477995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115894948583920661279303993 86921211437940495959477995)
          ·
            refine ⟨130381817156910743939216993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86921211437940495959477995 130381817156910743939216993)
            ·
              refine ⟨97786362867683057954412745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130381817156910743939216993 97786362867683057954412745)
              ·
                refine ⟨73339772150762293465809559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97786362867683057954412745 73339772150762293465809559)
                ·
                  refine ⟨110009658226143440198714339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73339772150762293465809559 110009658226143440198714339)
                  ·
                    refine ⟨165014487339215160298071509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110009658226143440198714339 165014487339215160298071509)
                    ·
                      refine ⟨3867527047012855319486051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165014487339215160298071509 3867527047012855319486051)
                      ·
                        rfl

theorem cell23_7531982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7531982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7531982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7531982 prefixEnd_7531982 := by exact prefixLift 7531982
  have htrace : WordTrace (prefixWord ++ tailWord_7531982) baseStart_7531982 baseEnd_7531982 := by
    simpa [prefixWord, tailWord_7531982, baseEnd_7531982] using wordTrace_append hprefix tailTrace_7531982
  have hstable : (prefixWord ++ tailWord_7531982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7531982).length < 2 ^ (prefixWord ++ tailWord_7531982).sum := by decide
  have hdescent : baseEnd_7531982 < baseStart_7531982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7531982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532029 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_7532029 : Nat := 118140960795 + 7532029 * 2 ^ 59
def prefixEnd_7532029 : Nat := 4983230072969 + 3 ^ 40 * 7532029 * 2
def baseEnd_7532029 : Nat := 3867551180603616635598335

theorem tailTrace_7532029 : CollatzResearch.WordTrace tailWord_7532029 prefixEnd_7532029 3867551180603616635598335 := by
  unfold tailWord_7532029
  simp only [CollatzResearch.WordTrace]
  refine ⟨274715666429752775985311141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183143777619835183990207427 274715666429752775985311141)
  ·
    refine ⟨51509187455578645497245839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274715666429752775985311141 51509187455578645497245839)
    ·
      refine ⟨77263781183367968245868759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51509187455578645497245839 77263781183367968245868759)
      ·
        refine ⟨115895671775051952368803139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77263781183367968245868759 115895671775051952368803139)
        ·
          refine ⟨173843507662577928553204709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115895671775051952368803139 173843507662577928553204709)
          ·
            refine ⟨32595657686733361603725883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173843507662577928553204709 32595657686733361603725883)
            ·
              refine ⟨48893486530100042405588825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32595657686733361603725883 48893486530100042405588825)
              ·
                refine ⟨36670114897575031804191619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48893486530100042405588825 36670114897575031804191619)
                ·
                  refine ⟨55005172346362547706287429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36670114897575031804191619 55005172346362547706287429)
                  ·
                    refine ⟨10313469814942977694928893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55005172346362547706287429 10313469814942977694928893)
                    ·
                      refine ⟨3867551180603616635598335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313469814942977694928893 3867551180603616635598335)
                      ·
                        rfl

theorem cell23_7532029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_7532029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532029 prefixEnd_7532029 := by exact prefixLift 7532029
  have htrace : WordTrace (prefixWord ++ tailWord_7532029) baseStart_7532029 baseEnd_7532029 := by
    simpa [prefixWord, tailWord_7532029, baseEnd_7532029] using wordTrace_append hprefix tailTrace_7532029
  have hstable : (prefixWord ++ tailWord_7532029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532029).length < 2 ^ (prefixWord ++ tailWord_7532029).sum := by decide
  have hdescent : baseEnd_7532029 < baseStart_7532029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532053 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7532053 : Nat := 118140960795 + 7532053 * 2 ^ 59
def prefixEnd_7532053 : Nat := 4983230072969 + 3 ^ 40 * 7532053 * 2
def baseEnd_7532053 : Nat := 1289187834713108180566075

theorem tailTrace_7532053 : CollatzResearch.WordTrace tailWord_7532053 prefixEnd_7532053 1289187834713108180566075 := by
  unfold tailWord_7532053
  simp only [CollatzResearch.WordTrace]
  refine ⟨274716541781665828084184813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183144361187777218722789875 274716541781665828084184813)
  ·
    refine ⟨103018703168124685531569305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274716541781665828084184813 103018703168124685531569305)
    ·
      refine ⟨77264027376093514148676979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103018703168124685531569305 77264027376093514148676979)
      ·
        refine ⟨115896041064140271223015469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77264027376093514148676979 115896041064140271223015469)
        ·
          refine ⟨43461015399052601708630801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115896041064140271223015469 43461015399052601708630801)
          ·
            refine ⟨32595761549289451281473101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43461015399052601708630801 32595761549289451281473101)
            ·
              refine ⟨12223410580983544230552413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32595761549289451281473101 12223410580983544230552413)
              ·
                refine ⟨4583778967868829086457155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12223410580983544230552413 4583778967868829086457155)
                ·
                  refine ⟨6875668451803243629685733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583778967868829086457155 6875668451803243629685733)
                  ·
                    refine ⟨1289187834713108180566075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875668451803243629685733 1289187834713108180566075)
                    ·
                      rfl

theorem cell23_7532053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7532053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532053 prefixEnd_7532053 := by exact prefixLift 7532053
  have htrace : WordTrace (prefixWord ++ tailWord_7532053) baseStart_7532053 baseEnd_7532053 := by
    simpa [prefixWord, tailWord_7532053, baseEnd_7532053] using wordTrace_append hprefix tailTrace_7532053
  have hstable : (prefixWord ++ tailWord_7532053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532053).length < 2 ^ (prefixWord ++ tailWord_7532053).sum := by decide
  have hdescent : baseEnd_7532053 < baseStart_7532053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532129 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7532129 : Nat := 118140960795 + 7532129 * 2 ^ 59
def prefixEnd_7532129 : Nat := 4983230072969 + 3 ^ 40 * 7532129 * 2
def baseEnd_7532129 : Nat := 3867602528669066244347875

theorem tailTrace_7532129 : CollatzResearch.WordTrace tailWord_7532129 prefixEnd_7532129 3867602528669066244347875 := by
  unfold tailWord_7532129
  simp only [CollatzResearch.WordTrace]
  refine ⟨274719313729390493063951441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183146209152926995375967627 274719313729390493063951441)
  ·
    refine ⟨206039485297042869797963581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274719313729390493063951441 206039485297042869797963581)
    ·
      refine ⟨77264806986391076174236343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206039485297042869797963581 77264806986391076174236343)
      ·
        refine ⟨115897210479586614261354515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77264806986391076174236343 115897210479586614261354515)
        ·
          refine ⟨173845815719379921392031773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115897210479586614261354515 173845815719379921392031773)
          ·
            refine ⟨65192180894767470522011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173845815719379921392031773 65192180894767470522011915)
            ·
              refine ⟨97788271342151205783017873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65192180894767470522011915 97788271342151205783017873)
              ·
                refine ⟨73341203506613404337263405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97788271342151205783017873 73341203506613404337263405)
                ·
                  refine ⟨27502951314980026626473777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73341203506613404337263405 27502951314980026626473777)
                  ·
                    refine ⟨20627213486235019969855333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27502951314980026626473777 20627213486235019969855333)
                    ·
                      refine ⟨3867602528669066244347875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20627213486235019969855333 3867602528669066244347875)
                      ·
                        rfl

theorem cell23_7532129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7532129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532129 prefixEnd_7532129 := by exact prefixLift 7532129
  have htrace : WordTrace (prefixWord ++ tailWord_7532129) baseStart_7532129 baseEnd_7532129 := by
    simpa [prefixWord, tailWord_7532129, baseEnd_7532129] using wordTrace_append hprefix tailTrace_7532129
  have hstable : (prefixWord ++ tailWord_7532129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532129).length < 2 ^ (prefixWord ++ tailWord_7532129).sum := by decide
  have hdescent : baseEnd_7532129 < baseStart_7532129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532146 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7532146 : Nat := 118140960795 + 7532146 * 2 ^ 59
def prefixEnd_7532146 : Nat := 4983230072969 + 3 ^ 40 * 7532146 * 2
def baseEnd_7532146 : Nat := 3867611257840192677835297

theorem tailTrace_7532146 : CollatzResearch.WordTrace tailWord_7532146 prefixEnd_7532146 3867611257840192677835297 := by
  unfold tailWord_7532146
  simp only [CollatzResearch.WordTrace]
  refine ⟨68679983442582226241830073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183146622513552603311546861 68679983442582226241830073)
  ·
    refine ⟨51509987581936669681372555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68679983442582226241830073 51509987581936669681372555)
    ·
      refine ⟨77264981372905004522058833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51509987581936669681372555 77264981372905004522058833)
      ·
        refine ⟨57948736029678753391544125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77264981372905004522058833 57948736029678753391544125)
        ·
          refine ⟨21730776011129532521829047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57948736029678753391544125 21730776011129532521829047)
          ·
            refine ⟨32596164016694298782743571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730776011129532521829047 32596164016694298782743571)
            ·
              refine ⟨48894246025041448174115357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32596164016694298782743571 48894246025041448174115357)
              ·
                refine ⟨18335342259390543065293259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48894246025041448174115357 18335342259390543065293259)
                ·
                  refine ⟨27503013389085814597939889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18335342259390543065293259 27503013389085814597939889)
                  ·
                    refine ⟨20627260041814360948454917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27503013389085814597939889 20627260041814360948454917)
                    ·
                      refine ⟨3867611257840192677835297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20627260041814360948454917 3867611257840192677835297)
                      ·
                        rfl

theorem cell23_7532146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7532146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532146 prefixEnd_7532146 := by exact prefixLift 7532146
  have htrace : WordTrace (prefixWord ++ tailWord_7532146) baseStart_7532146 baseEnd_7532146 := by
    simpa [prefixWord, tailWord_7532146, baseEnd_7532146] using wordTrace_append hprefix tailTrace_7532146
  have hstable : (prefixWord ++ tailWord_7532146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532146).length < 2 ^ (prefixWord ++ tailWord_7532146).sum := by decide
  have hdescent : baseEnd_7532146 < baseStart_7532146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532150 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7532150 : Nat := 118140960795 + 7532150 * 2 ^ 59
def prefixEnd_7532150 : Nat := 4983230072969 + 3 ^ 40 * 7532150 * 2
def baseEnd_7532150 : Nat := 3867613311762810662185279

theorem tailTrace_7532150 : CollatzResearch.WordTrace tailWord_7532150 prefixEnd_7532150 3867613311762810662185279 := by
  unfold tailWord_7532150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170004978894650853154119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183146719774876275766977269 17170004978894650853154119)
  ·
    refine ⟨25755007468341976279731179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17170004978894650853154119 25755007468341976279731179)
    ·
      refine ⟨38632511202512964419596769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25755007468341976279731179 38632511202512964419596769)
      ·
        refine ⟨28974383401884723314697577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38632511202512964419596769 28974383401884723314697577)
        ·
          refine ⟨21730787551413542486023183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28974383401884723314697577 21730787551413542486023183)
          ·
            refine ⟨32596181327120313729034775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730787551413542486023183 32596181327120313729034775)
            ·
              refine ⟨48894271990680470593552163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32596181327120313729034775 48894271990680470593552163)
              ·
                refine ⟨73341407986020705890328245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48894271990680470593552163 73341407986020705890328245)
                ·
                  refine ⟨6875756998689441177218273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73341407986020705890328245 6875756998689441177218273)
                  ·
                    refine ⟨5156817749017080882913705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875756998689441177218273 5156817749017080882913705)
                    ·
                      refine ⟨3867613311762810662185279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156817749017080882913705 3867613311762810662185279)
                      ·
                        rfl

theorem cell23_7532150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7532150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532150 prefixEnd_7532150 := by exact prefixLift 7532150
  have htrace : WordTrace (prefixWord ++ tailWord_7532150) baseStart_7532150 baseEnd_7532150 := by
    simpa [prefixWord, tailWord_7532150, baseEnd_7532150] using wordTrace_append hprefix tailTrace_7532150
  have hstable : (prefixWord ++ tailWord_7532150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532150).length < 2 ^ (prefixWord ++ tailWord_7532150).sum := by decide
  have hdescent : baseEnd_7532150 < baseStart_7532150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532167 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_7532167 : Nat := 118140960795 + 7532167 * 2 ^ 59
def prefixEnd_7532167 : Nat := 4983230072969 + 3 ^ 40 * 7532167 * 2
def baseEnd_7532167 : Nat := 3867622040933937095672701

theorem tailTrace_7532167 : CollatzResearch.WordTrace tailWord_7532167 prefixEnd_7532167 3867622040933937095672701 := by
  unfold tailWord_7532167
  simp only [CollatzResearch.WordTrace]
  refine ⟨274720699703252825553834755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183147133135501883702556503 274720699703252825553834755)
  ·
    refine ⟨412081049554879238330752133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274720699703252825553834755 412081049554879238330752133)
    ·
      refine ⟨77265196791539857187016025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412081049554879238330752133 77265196791539857187016025)
      ·
        refine ⟨57948897593654892890262019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77265196791539857187016025 57948897593654892890262019)
        ·
          refine ⟨86923346390482339335393029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57948897593654892890262019 86923346390482339335393029)
          ·
            refine ⟨16298127448215438625386193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86923346390482339335393029 16298127448215438625386193)
            ·
              refine ⟨12223595586161578969039645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16298127448215438625386193 12223595586161578969039645)
              ·
                refine ⟨4583848344810592113389867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12223595586161578969039645 4583848344810592113389867)
                ·
                  refine ⟨6875772517215888170084801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583848344810592113389867 6875772517215888170084801)
                  ·
                    refine ⟨5156829387911916127563601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875772517215888170084801 5156829387911916127563601)
                    ·
                      refine ⟨3867622040933937095672701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156829387911916127563601 3867622040933937095672701)
                      ·
                        rfl

theorem cell23_7532167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_7532167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532167 prefixEnd_7532167 := by exact prefixLift 7532167
  have htrace : WordTrace (prefixWord ++ tailWord_7532167) baseStart_7532167 baseEnd_7532167 := by
    simpa [prefixWord, tailWord_7532167, baseEnd_7532167] using wordTrace_append hprefix tailTrace_7532167
  have hstable : (prefixWord ++ tailWord_7532167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532167).length < 2 ^ (prefixWord ++ tailWord_7532167).sum := by decide
  have hdescent : baseEnd_7532167 < baseStart_7532167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532170 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_7532170 : Nat := 118140960795 + 7532170 * 2 ^ 59
def prefixEnd_7532170 : Nat := 4983230072969 + 3 ^ 40 * 7532170 * 2
def baseEnd_7532170 : Nat := 3867623581375900583935187

theorem tailTrace_7532170 : CollatzResearch.WordTrace tailWord_7532170 prefixEnd_7532170 3867623581375900583935187 := by
  unfold tailWord_7532170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68680202280560489266548491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183147206081494638044129309 68680202280560489266548491)
  ·
    refine ⟨103020303420840733899822737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68680202280560489266548491 103020303420840733899822737)
    ·
      refine ⟨77265227565630550424867053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103020303420840733899822737 77265227565630550424867053)
      ·
        refine ⟨28974460337111456409325145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77265227565630550424867053 28974460337111456409325145)
        ·
          refine ⟨21730845252833592306993859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28974460337111456409325145 21730845252833592306993859)
          ·
            refine ⟨32596267879250388460490789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730845252833592306993859 32596267879250388460490789)
            ·
              refine ⟨6111800227359447836342023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32596267879250388460490789 6111800227359447836342023)
              ·
                refine ⟨9167700341039171754513035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111800227359447836342023 9167700341039171754513035)
                ·
                  refine ⟨13751550511558757631769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167700341039171754513035 13751550511558757631769553)
                  ·
                    refine ⟨10313662883669068223827165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13751550511558757631769553 10313662883669068223827165)
                    ·
                      refine ⟨3867623581375900583935187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313662883669068223827165 3867623581375900583935187)
                      ·
                        rfl

theorem cell23_7532170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_7532170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532170 prefixEnd_7532170 := by exact prefixLift 7532170
  have htrace : WordTrace (prefixWord ++ tailWord_7532170) baseStart_7532170 baseEnd_7532170 := by
    simpa [prefixWord, tailWord_7532170, baseEnd_7532170] using wordTrace_append hprefix tailTrace_7532170
  have hstable : (prefixWord ++ tailWord_7532170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532170).length < 2 ^ (prefixWord ++ tailWord_7532170).sum := by decide
  have hdescent : baseEnd_7532170 < baseStart_7532170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532183 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_7532183 : Nat := 118140960795 + 7532183 * 2 ^ 59
def prefixEnd_7532183 : Nat := 4983230072969 + 3 ^ 40 * 7532183 * 2
def baseEnd_7532183 : Nat := 3867630256624409033072627

theorem tailTrace_7532183 : CollatzResearch.WordTrace tailWord_7532183 prefixEnd_7532183 3867630256624409033072627 := by
  unfold tailWord_7532183
  simp only [CollatzResearch.WordTrace]
  refine ⟨274721283271194860286417203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183147522180796573524278135 274721283271194860286417203)
  ·
    refine ⟨412081924906792290429625805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274721283271194860286417203 412081924906792290429625805)
    ·
      refine ⟨154530721840047108911109677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412081924906792290429625805 154530721840047108911109677)
      ·
        refine ⟨57949020690017665841666129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154530721840047108911109677 57949020690017665841666129)
        ·
          refine ⟨43461765517513249381249597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57949020690017665841666129 43461765517513249381249597)
          ·
            refine ⟨16298162069067468517968599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43461765517513249381249597 16298162069067468517968599)
            ·
              refine ⟨24447243103601202776952899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16298162069067468517968599 24447243103601202776952899)
              ·
                refine ⟨36670864655401804165429349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24447243103601202776952899 36670864655401804165429349)
                ·
                  refine ⟨6875787122887838281018003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36670864655401804165429349 6875787122887838281018003)
                  ·
                    refine ⟨10313680684331757421527005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6875787122887838281018003 10313680684331757421527005)
                    ·
                      refine ⟨3867630256624409033072627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313680684331757421527005 3867630256624409033072627)
                      ·
                        rfl

theorem cell23_7532183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_7532183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532183 prefixEnd_7532183 := by exact prefixLift 7532183
  have htrace : WordTrace (prefixWord ++ tailWord_7532183) baseStart_7532183 baseEnd_7532183 := by
    simpa [prefixWord, tailWord_7532183, baseEnd_7532183] using wordTrace_append hprefix tailTrace_7532183
  have hstable : (prefixWord ++ tailWord_7532183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532183).length < 2 ^ (prefixWord ++ tailWord_7532183).sum := by decide
  have hdescent : baseEnd_7532183 < baseStart_7532183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532219 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_7532219 : Nat := 118140960795 + 7532219 * 2 ^ 59
def prefixEnd_7532219 : Nat := 4983230072969 + 3 ^ 40 * 7532219 * 2
def baseEnd_7532219 : Nat := 3867648741927970892222461

theorem tailTrace_7532219 : CollatzResearch.WordTrace tailWord_7532219 prefixEnd_7532219 3867648741927970892222461 := by
  unfold tailWord_7532219
  simp only [CollatzResearch.WordTrace]
  refine ⟨274722596299064438434727711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183148397532709625623151807 274722596299064438434727711)
  ·
    refine ⟨412083894448596657652091567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274722596299064438434727711 412083894448596657652091567)
    ·
      refine ⟨618125841672894986478137351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412083894448596657652091567 618125841672894986478137351)
      ·
        refine ⟨927188762509342479717206027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618125841672894986478137351 927188762509342479717206027)
        ·
          refine ⟨1390783143764013719575809041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927188762509342479717206027 1390783143764013719575809041)
          ·
            refine ⟨1043087357823010289681856781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390783143764013719575809041 1043087357823010289681856781)
            ·
              refine ⟨391157759183628858630696293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043087357823010289681856781 391157759183628858630696293)
              ·
                refine ⟨73342079846930410993255555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391157759183628858630696293 73342079846930410993255555)
                ·
                  refine ⟨110013119770395616489883333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73342079846930410993255555 110013119770395616489883333)
                  ·
                    refine ⟨20627459956949178091853125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110013119770395616489883333 20627459956949178091853125)
                    ·
                      refine ⟨3867648741927970892222461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20627459956949178091853125 3867648741927970892222461)
                      ·
                        rfl

theorem cell23_7532219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_7532219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532219 prefixEnd_7532219 := by exact prefixLift 7532219
  have htrace : WordTrace (prefixWord ++ tailWord_7532219) baseStart_7532219 baseEnd_7532219 := by
    simpa [prefixWord, tailWord_7532219, baseEnd_7532219] using wordTrace_append hprefix tailTrace_7532219
  have hstable : (prefixWord ++ tailWord_7532219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532219).length < 2 ^ (prefixWord ++ tailWord_7532219).sum := by decide
  have hdescent : baseEnd_7532219 < baseStart_7532219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532223 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 6, 2, 2]
def baseStart_7532223 : Nat := 118140960795 + 7532223 * 2 ^ 59
def prefixEnd_7532223 : Nat := 4983230072969 + 3 ^ 40 * 7532223 * 2
def baseEnd_7532223 : Nat := 3867650795850588876572443

theorem tailTrace_7532223 : CollatzResearch.WordTrace tailWord_7532223 prefixEnd_7532223 3867650795850588876572443 := by
  unfold tailWord_7532223
  simp only [CollatzResearch.WordTrace]
  refine ⟨274722742191049947117873323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183148494794033298078582215 274722742191049947117873323)
  ·
    refine ⟨412084113286574920676809985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274722742191049947117873323 412084113286574920676809985)
    ·
      refine ⟨309063084964931190507607489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412084113286574920676809985 309063084964931190507607489)
      ·
        refine ⟨231797313723698392880705617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309063084964931190507607489 231797313723698392880705617)
        ·
          refine ⟨173847985292773794660529213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231797313723698392880705617 173847985292773794660529213)
          ·
            refine ⟨65192994484790172997698455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173847985292773794660529213 65192994484790172997698455)
            ·
              refine ⟨97789491727185259496547683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65192994484790172997698455 97789491727185259496547683)
              ·
                refine ⟨146684237590777889244821525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97789491727185259496547683 146684237590777889244821525)
                ·
                  refine ⟨6875823637067713558351009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146684237590777889244821525 6875823637067713558351009)
                  ·
                    refine ⟨5156867727800785168763257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875823637067713558351009 5156867727800785168763257)
                    ·
                      refine ⟨3867650795850588876572443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156867727800785168763257 3867650795850588876572443)
                      ·
                        rfl

theorem cell23_7532223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_7532223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532223 prefixEnd_7532223 := by exact prefixLift 7532223
  have htrace : WordTrace (prefixWord ++ tailWord_7532223) baseStart_7532223 baseEnd_7532223 := by
    simpa [prefixWord, tailWord_7532223, baseEnd_7532223] using wordTrace_append hprefix tailTrace_7532223
  have hstable : (prefixWord ++ tailWord_7532223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532223).length < 2 ^ (prefixWord ++ tailWord_7532223).sum := by decide
  have hdescent : baseEnd_7532223 < baseStart_7532223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532256 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_7532256 : Nat := 118140960795 + 7532256 * 2 ^ 59
def prefixEnd_7532256 : Nat := 4983230072969 + 3 ^ 40 * 7532256 * 2
def baseEnd_7532256 : Nat := 3867667740712187247459791

theorem tailTrace_7532256 : CollatzResearch.WordTrace tailWord_7532256 prefixEnd_7532256 3867667740712187247459791 := by
  unfold tailWord_7532256
  simp only [CollatzResearch.WordTrace]
  refine ⟨137361972899965196876912311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183149297199953595835883081 137361972899965196876912311)
  ·
    refine ⟨206042959349947795315368467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137361972899965196876912311 206042959349947795315368467)
    ·
      refine ⟨309064439024921692973052701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206042959349947795315368467 309064439024921692973052701)
      ·
        refine ⟨115899164634345634864894763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309064439024921692973052701 115899164634345634864894763)
        ·
          refine ⟨173848746951518452297342145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115899164634345634864894763 173848746951518452297342145)
          ·
            refine ⟨130386560213638839223006609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173848746951518452297342145 130386560213638839223006609)
            ·
              refine ⟨97789920160229129417254957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130386560213638839223006609 97789920160229129417254957)
              ·
                refine ⟨36671220060085923531470609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97789920160229129417254957 36671220060085923531470609)
                ·
                  refine ⟨27503415045064442648602957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36671220060085923531470609 27503415045064442648602957)
                  ·
                    refine ⟨10313780641899165993226109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27503415045064442648602957 10313780641899165993226109)
                    ·
                      refine ⟨3867667740712187247459791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313780641899165993226109 3867667740712187247459791)
                      ·
                        rfl

theorem cell23_7532256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_7532256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532256 prefixEnd_7532256 := by exact prefixLift 7532256
  have htrace : WordTrace (prefixWord ++ tailWord_7532256) baseStart_7532256 baseEnd_7532256 := by
    simpa [prefixWord, tailWord_7532256, baseEnd_7532256] using wordTrace_append hprefix tailTrace_7532256
  have hstable : (prefixWord ++ tailWord_7532256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532256).length < 2 ^ (prefixWord ++ tailWord_7532256).sum := by decide
  have hdescent : baseEnd_7532256 < baseStart_7532256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532257 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_7532257 : Nat := 118140960795 + 7532257 * 2 ^ 59
def prefixEnd_7532257 : Nat := 4983230072969 + 3 ^ 40 * 7532257 * 2
def baseEnd_7532257 : Nat := 3867668254192841743547287

theorem tailTrace_7532257 : CollatzResearch.WordTrace tailWord_7532257 prefixEnd_7532257 3867668254192841743547287 := by
  unfold tailWord_7532257
  simp only [CollatzResearch.WordTrace]
  refine ⟨274723982272926770924611025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183149321515284513949740683 274723982272926770924611025)
  ·
    refine ⟨206042986704695078193458269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274723982272926770924611025 206042986704695078193458269)
    ·
      refine ⟨77266120014260654322546851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206042986704695078193458269 77266120014260654322546851)
      ·
        refine ⟨115899180021390981483820277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77266120014260654322546851 115899180021390981483820277)
        ·
          refine ⟨10865548127005404514108151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115899180021390981483820277 10865548127005404514108151)
          ·
            refine ⟨16298322190508106771162227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10865548127005404514108151 16298322190508106771162227)
            ·
              refine ⟨24447483285762160156743341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16298322190508106771162227 24447483285762160156743341)
              ·
                refine ⟨9167806232160810058778753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24447483285762160156743341 9167806232160810058778753)
                ·
                  refine ⟨6875854674120607544084065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167806232160810058778753 6875854674120607544084065)
                  ·
                    refine ⟨5156891005590455658063049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875854674120607544084065 5156891005590455658063049)
                    ·
                      refine ⟨3867668254192841743547287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5156891005590455658063049 3867668254192841743547287)
                      ·
                        rfl

theorem cell23_7532257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_7532257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532257 prefixEnd_7532257 := by exact prefixLift 7532257
  have htrace : WordTrace (prefixWord ++ tailWord_7532257) baseStart_7532257 baseEnd_7532257 := by
    simpa [prefixWord, tailWord_7532257, baseEnd_7532257] using wordTrace_append hprefix tailTrace_7532257
  have hstable : (prefixWord ++ tailWord_7532257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532257).length < 2 ^ (prefixWord ++ tailWord_7532257).sum := by decide
  have hdescent : baseEnd_7532257 < baseStart_7532257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532370 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_7532370 : Nat := 118140960795 + 7532370 * 2 ^ 59
def prefixEnd_7532370 : Nat := 4983230072969 + 3 ^ 40 * 7532370 * 2
def baseEnd_7532370 : Nat := 429747364167422200159363

theorem tailTrace_7532370 : CollatzResearch.WordTrace tailWord_7532370 prefixEnd_7532370 429747364167422200159363 := by
  unfold tailWord_7532370
  simp only [CollatzResearch.WordTrace]
  refine ⟨68682025930379347805868641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183152069147678260815649709 68682025930379347805868641)
  ·
    refine ⟨51511519447784510854401481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68682025930379347805868641 51511519447784510854401481)
    ·
      refine ⟨38633639585838383140801111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51511519447784510854401481 38633639585838383140801111)
      ·
        refine ⟨57950459378757574711201667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38633639585838383140801111 57950459378757574711201667)
        ·
          refine ⟨86925689068136362066802501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57950459378757574711201667 86925689068136362066802501)
          ·
            refine ⟨16298566700275567887525469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86925689068136362066802501 16298566700275567887525469)
            ·
              refine ⟨6111962512603337957822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16298566700275567887525469 6111962512603337957822051)
              ·
                refine ⟨9167943768905006936733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111962512603337957822051 9167943768905006936733077)
                ·
                  refine ⟨429747364167422200159363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9167943768905006936733077 429747364167422200159363)
                  ·
                    rfl

theorem cell23_7532370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_7532370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532370 prefixEnd_7532370 := by exact prefixLift 7532370
  have htrace : WordTrace (prefixWord ++ tailWord_7532370) baseStart_7532370 baseEnd_7532370 := by
    simpa [prefixWord, tailWord_7532370, baseEnd_7532370] using wordTrace_append hprefix tailTrace_7532370
  have hstable : (prefixWord ++ tailWord_7532370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532370).length < 2 ^ (prefixWord ++ tailWord_7532370).sum := by decide
  have hdescent : baseEnd_7532370 < baseStart_7532370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532383 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 1, 5]
def baseStart_7532383 : Nat := 118140960795 + 7532383 * 2 ^ 59
def prefixEnd_7532383 : Nat := 4983230072969 + 3 ^ 40 * 7532383 * 2
def baseEnd_7532383 : Nat := 1289244317585102750190569

theorem tailTrace_7532383 : CollatzResearch.WordTrace tailWord_7532383 prefixEnd_7532383 1289244317585102750190569 := by
  unfold tailWord_7532383
  simp only [CollatzResearch.WordTrace]
  refine ⟨274728577870470294443697803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183152385246980196295798535 274728577870470294443697803)
  ·
    refine ⟨412092866805705441665546705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274728577870470294443697803 412092866805705441665546705)
    ·
      refine ⟨309069650104279081249160029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412092866805705441665546705 309069650104279081249160029)
      ·
        refine ⟨115901118789104655468435011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309069650104279081249160029 115901118789104655468435011)
        ·
          refine ⟨173851678183656983202652517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115901118789104655468435011 173851678183656983202652517)
          ·
            refine ⟨32597189659435684350497347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173851678183656983202652517 32597189659435684350497347)
            ·
              refine ⟨48895784489153526525746021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32597189659435684350497347 48895784489153526525746021)
              ·
                refine ⟨9167959591716286223577379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48895784489153526525746021 9167959591716286223577379)
                ·
                  refine ⟨13751939387574429335366069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167959591716286223577379 13751939387574429335366069)
                  ·
                    refine ⟨1289244317585102750190569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13751939387574429335366069 1289244317585102750190569)
                    ·
                      rfl

theorem cell23_7532383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_7532383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532383 prefixEnd_7532383 := by exact prefixLift 7532383
  have htrace : WordTrace (prefixWord ++ tailWord_7532383) baseStart_7532383 baseEnd_7532383 := by
    simpa [prefixWord, tailWord_7532383, baseEnd_7532383] using wordTrace_append hprefix tailTrace_7532383
  have hstable : (prefixWord ++ tailWord_7532383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532383).length < 2 ^ (prefixWord ++ tailWord_7532383).sum := by decide
  have hdescent : baseEnd_7532383 < baseStart_7532383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532414 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7532414 : Nat := 118140960795 + 7532414 * 2 ^ 59
def prefixEnd_7532414 : Nat := 4983230072969 + 3 ^ 40 * 7532414 * 2
def baseEnd_7532414 : Nat := 3867748870655597629284065

theorem tailTrace_7532414 : CollatzResearch.WordTrace tailWord_7532414 prefixEnd_7532414 3867748870655597629284065 := by
  unfold tailWord_7532414
  simp only [CollatzResearch.WordTrace]
  refine ⟨34341213566669748342259537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183153139022238657825384197 34341213566669748342259537)
  ·
    refine ⟨25755910175002311256694653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34341213566669748342259537 25755910175002311256694653)
    ·
      refine ⟨9658466315625866721260495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25755910175002311256694653 9658466315625866721260495)
      ·
        refine ⟨14487699473438800081890743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658466315625866721260495 14487699473438800081890743)
        ·
          refine ⟨21731549210158200122836115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487699473438800081890743 21731549210158200122836115)
          ·
            refine ⟨32597323815237300184254173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21731549210158200122836115 32597323815237300184254173)
            ·
              refine ⟨12223996430713987569095315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32597323815237300184254173 12223996430713987569095315)
              ·
                refine ⟨18335994646070981353642973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12223996430713987569095315 18335994646070981353642973)
                ·
                  refine ⟨6875997992276618007616115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18335994646070981353642973 6875997992276618007616115)
                  ·
                    refine ⟨10313996988414927011424173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6875997992276618007616115 10313996988414927011424173)
                    ·
                      refine ⟨3867748870655597629284065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10313996988414927011424173 3867748870655597629284065)
                      ·
                        rfl

theorem cell23_7532414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7532414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532414 prefixEnd_7532414 := by exact prefixLift 7532414
  have htrace : WordTrace (prefixWord ++ tailWord_7532414) baseStart_7532414 baseEnd_7532414 := by
    simpa [prefixWord, tailWord_7532414, baseEnd_7532414] using wordTrace_append hprefix tailTrace_7532414
  have hstable : (prefixWord ++ tailWord_7532414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532414).length < 2 ^ (prefixWord ++ tailWord_7532414).sum := by decide
  have hdescent : baseEnd_7532414 < baseStart_7532414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532416 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_7532416 : Nat := 118140960795 + 7532416 * 2 ^ 59
def prefixEnd_7532416 : Nat := 4983230072969 + 3 ^ 40 * 7532416 * 2
def baseEnd_7532416 : Nat := 3867749897616906621459055

theorem tailTrace_7532416 : CollatzResearch.WordTrace tailWord_7532416 prefixEnd_7532416 3867749897616906621459055 := by
  unfold tailWord_7532416
  simp only [CollatzResearch.WordTrace]
  refine ⟨137364890739675370539824551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183153187652900494053099401 137364890739675370539824551)
  ·
    refine ⟨206047336109513055809736827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137364890739675370539824551 206047336109513055809736827)
    ·
      refine ⟨309071004164269583714605241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206047336109513055809736827 309071004164269583714605241)
      ·
        refine ⟨231803253123202187785953931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309071004164269583714605241 231803253123202187785953931)
        ·
          refine ⟨347704879684803281678930897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231803253123202187785953931 347704879684803281678930897)
          ·
            refine ⟨260778659763602461259198173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347704879684803281678930897 260778659763602461259198173)
            ·
              refine ⟨97791997411350922972199315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260778659763602461259198173 97791997411350922972199315)
              ·
                refine ⟨146687996117026384458298973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97791997411350922972199315 146687996117026384458298973)
                ·
                  refine ⟨55007998543884894171862115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146687996117026384458298973 55007998543884894171862115)
                  ·
                    refine ⟨82511997815827341257793173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55007998543884894171862115 82511997815827341257793173)
                    ·
                      refine ⟨3867749897616906621459055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82511997815827341257793173 3867749897616906621459055)
                      ·
                        rfl

theorem cell23_7532416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_7532416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532416 prefixEnd_7532416 := by exact prefixLift 7532416
  have htrace : WordTrace (prefixWord ++ tailWord_7532416) baseStart_7532416 baseEnd_7532416 := by
    simpa [prefixWord, tailWord_7532416, baseEnd_7532416] using wordTrace_append hprefix tailTrace_7532416
  have hstable : (prefixWord ++ tailWord_7532416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532416).length < 2 ^ (prefixWord ++ tailWord_7532416).sum := by decide
  have hdescent : baseEnd_7532416 < baseStart_7532416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532480 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2]
def baseStart_7532480 : Nat := 118140960795 + 7532480 * 2 ^ 59
def prefixEnd_7532480 : Nat := 4983230072969 + 3 ^ 40 * 7532480 * 2
def baseEnd_7532480 : Nat := 3867782760378794371058761

theorem tailTrace_7532480 : CollatzResearch.WordTrace tailWord_7532480 prefixEnd_7532480 3867782760378794371058761 := by
  unfold tailWord_7532480
  simp only [CollatzResearch.WordTrace]
  refine ⟨137366057875559440004989447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183154743834079253339985929 137366057875559440004989447)
  ·
    refine ⟨206049086813339160007484171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137366057875559440004989447 206049086813339160007484171)
    ·
      refine ⟨309073630220008740011226257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206049086813339160007484171 309073630220008740011226257)
      ·
        refine ⟨231805222665006555008419693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309073630220008740011226257 231805222665006555008419693)
        ·
          refine ⟨86926958499377458128157385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231805222665006555008419693 86926958499377458128157385)
          ·
            refine ⟨65195218874533093596118039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86926958499377458128157385 65195218874533093596118039)
            ·
              refine ⟨97792828311799640394177059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65195218874533093596118039 97792828311799640394177059)
              ·
                refine ⟨146689242467699460591265589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97792828311799640394177059 146689242467699460591265589)
                ·
                  refine ⟨13752116481346824430431149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146689242467699460591265589 13752116481346824430431149)
                  ·
                    refine ⟨5157043680505059161411681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13752116481346824430431149 5157043680505059161411681)
                    ·
                      refine ⟨3867782760378794371058761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157043680505059161411681 3867782760378794371058761)
                      ·
                        rfl

theorem cell23_7532480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_7532480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532480 prefixEnd_7532480 := by exact prefixLift 7532480
  have htrace : WordTrace (prefixWord ++ tailWord_7532480) baseStart_7532480 baseEnd_7532480 := by
    simpa [prefixWord, tailWord_7532480, baseEnd_7532480] using wordTrace_append hprefix tailTrace_7532480
  have hstable : (prefixWord ++ tailWord_7532480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532480).length < 2 ^ (prefixWord ++ tailWord_7532480).sum := by decide
  have hdescent : baseEnd_7532480 < baseStart_7532480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532513 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7532513 : Nat := 118140960795 + 7532513 * 2 ^ 59
def prefixEnd_7532513 : Nat := 4983230072969 + 3 ^ 40 * 7532513 * 2
def baseEnd_7532513 : Nat := 3867799705240392741946109

theorem tailTrace_7532513 : CollatzResearch.WordTrace tailWord_7532513 prefixEnd_7532513 3867799705240392741946109 := by
  unfold tailWord_7532513
  simp only [CollatzResearch.WordTrace]
  refine ⟨274733319359999326645930193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183155546239999551097286795 274733319359999326645930193)
  ·
    refine ⟨206049989519999494984447645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274733319359999326645930193 206049989519999494984447645)
    ·
      refine ⟨77268746069999810619167867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206049989519999494984447645 77268746069999810619167867)
      ·
        refine ⟨115903119104999715928751801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77268746069999810619167867 115903119104999715928751801)
        ·
          refine ⟨86927339328749786946563851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115903119104999715928751801 86927339328749786946563851)
          ·
            refine ⟨130391008993124680419845777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86927339328749786946563851 130391008993124680419845777)
            ·
              refine ⟨97793256744843510314884333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130391008993124680419845777 97793256744843510314884333)
              ·
                refine ⟨36672471279316316368081625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97793256744843510314884333 36672471279316316368081625)
                ·
                  refine ⟨27504353459487237276061219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36672471279316316368081625 27504353459487237276061219)
                  ·
                    refine ⟨41256530189230855914091829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27504353459487237276061219 41256530189230855914091829)
                    ·
                      refine ⟨3867799705240392741946109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41256530189230855914091829 3867799705240392741946109)
                      ·
                        rfl

theorem cell23_7532513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7532513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532513 prefixEnd_7532513 := by exact prefixLift 7532513
  have htrace : WordTrace (prefixWord ++ tailWord_7532513) baseStart_7532513 baseEnd_7532513 := by
    simpa [prefixWord, tailWord_7532513, baseEnd_7532513] using wordTrace_append hprefix tailTrace_7532513
  have hstable : (prefixWord ++ tailWord_7532513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532513).length < 2 ^ (prefixWord ++ tailWord_7532513).sum := by decide
  have hdescent : baseEnd_7532513 < baseStart_7532513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532527 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 4, 2, 2]
def baseStart_7532527 : Nat := 118140960795 + 7532527 * 2 ^ 59
def prefixEnd_7532527 : Nat := 4983230072969 + 3 ^ 40 * 7532527 * 2
def baseEnd_7532527 : Nat := 3867806893969555687171045

theorem tailTrace_7532527 : CollatzResearch.WordTrace tailWord_7532527 prefixEnd_7532527 3867806893969555687171045 := by
  unfold tailWord_7532527
  simp only [CollatzResearch.WordTrace]
  refine ⟨274733829981948607036939835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183155886654632404691293223 274733829981948607036939835)
  ·
    refine ⟨412100744972922910555409753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274733829981948607036939835 412100744972922910555409753)
    ·
      refine ⟨309075558729692182916557315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412100744972922910555409753 309075558729692182916557315)
      ·
        refine ⟨463613338094538274374835973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309075558729692182916557315 463613338094538274374835973)
        ·
          refine ⟨86927500892725926445281745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463613338094538274374835973 86927500892725926445281745)
          ·
            refine ⟨65195625669544444833961309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86927500892725926445281745 65195625669544444833961309)
            ·
              refine ⟨24448359626079166812735491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65195625669544444833961309 24448359626079166812735491)
              ·
                refine ⟨36672539439118750219103237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24448359626079166812735491 36672539439118750219103237)
                ·
                  refine ⟨6876101144834765666081857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36672539439118750219103237 6876101144834765666081857)
                  ·
                    refine ⟨5157075858626074249561393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6876101144834765666081857 5157075858626074249561393)
                    ·
                      refine ⟨3867806893969555687171045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157075858626074249561393 3867806893969555687171045)
                      ·
                        rfl

theorem cell23_7532527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 2, 2].length) (baseStart_7532527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532527 prefixEnd_7532527 := by exact prefixLift 7532527
  have htrace : WordTrace (prefixWord ++ tailWord_7532527) baseStart_7532527 baseEnd_7532527 := by
    simpa [prefixWord, tailWord_7532527, baseEnd_7532527] using wordTrace_append hprefix tailTrace_7532527
  have hstable : (prefixWord ++ tailWord_7532527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532527).length < 2 ^ (prefixWord ++ tailWord_7532527).sum := by decide
  have hdescent : baseEnd_7532527 < baseStart_7532527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532563 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 7]
def baseStart_7532563 : Nat := 118140960795 + 7532563 * 2 ^ 59
def prefixEnd_7532563 : Nat := 4983230072969 + 3 ^ 40 * 7532563 * 2
def baseEnd_7532563 : Nat := 1289275126424372515440293

theorem tailTrace_7532563 : CollatzResearch.WordTrace tailWord_7532563 prefixEnd_7532563 1289275126424372515440293 := by
  unfold tailWord_7532563
  simp only [CollatzResearch.WordTrace]
  refine ⟨274735143009818185185250343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183156762006545456790166895 274735143009818185185250343)
  ·
    refine ⟨412102714514727277777875515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274735143009818185185250343 412102714514727277777875515)
    ·
      refine ⟨618154071772090916666813273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412102714514727277777875515 618154071772090916666813273)
      ·
        refine ⟨463615553829068187500109955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618154071772090916666813273 463615553829068187500109955)
        ·
          refine ⟨695423330743602281250164933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463615553829068187500109955 695423330743602281250164933)
          ·
            refine ⟨130391874514425427734405925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695423330743602281250164933 130391874514425427734405925)
            ·
              refine ⟨24448476471454767700201111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130391874514425427734405925 24448476471454767700201111)
              ·
                refine ⟨36672714707182151550301667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24448476471454767700201111 36672714707182151550301667)
                ·
                  refine ⟨55009072060773227325452501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36672714707182151550301667 55009072060773227325452501)
                  ·
                    refine ⟨1289275126424372515440293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55009072060773227325452501 1289275126424372515440293)
                    ·
                      rfl

theorem cell23_7532563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_7532563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532563 prefixEnd_7532563 := by exact prefixLift 7532563
  have htrace : WordTrace (prefixWord ++ tailWord_7532563) baseStart_7532563 baseEnd_7532563 := by
    simpa [prefixWord, tailWord_7532563, baseEnd_7532563] using wordTrace_append hprefix tailTrace_7532563
  have hstable : (prefixWord ++ tailWord_7532563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532563).length < 2 ^ (prefixWord ++ tailWord_7532563).sum := by decide
  have hdescent : baseEnd_7532563 < baseStart_7532563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532564 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7532564 : Nat := 118140960795 + 7532564 * 2 ^ 59
def prefixEnd_7532564 : Nat := 4983230072969 + 3 ^ 40 * 7532564 * 2
def baseEnd_7532564 : Nat := 3867825892753772042408375

theorem tailTrace_7532564 : CollatzResearch.WordTrace tailWord_7532564 prefixEnd_7532564 3867825892753772042408375 := by
  unfold tailWord_7532564
  simp only [CollatzResearch.WordTrace]
  refine ⟨137367589741407281178018373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183156786321876374904024497 137367589741407281178018373)
  ·
    refine ⟨25756423076513865220878445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137367589741407281178018373 25756423076513865220878445)
    ·
      refine ⟨9658658653692699457829417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25756423076513865220878445 9658658653692699457829417)
      ·
        refine ⟨7243993990269524593372063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658658653692699457829417 7243993990269524593372063)
        ·
          refine ⟨10865990985404286890058095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243993990269524593372063 10865990985404286890058095)
          ·
            refine ⟨16298986478106430335087143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10865990985404286890058095 16298986478106430335087143)
            ·
              refine ⟨24448479717159645502630715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16298986478106430335087143 24448479717159645502630715)
              ·
                refine ⟨36672719575739468253946073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24448479717159645502630715 36672719575739468253946073)
                ·
                  refine ⟨27504539681804601190459555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36672719575739468253946073 27504539681804601190459555)
                  ·
                    refine ⟨41256809522706901785689333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27504539681804601190459555 41256809522706901785689333)
                    ·
                      refine ⟨3867825892753772042408375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41256809522706901785689333 3867825892753772042408375)
                      ·
                        rfl

theorem cell23_7532564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7532564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532564 prefixEnd_7532564 := by exact prefixLift 7532564
  have htrace : WordTrace (prefixWord ++ tailWord_7532564) baseStart_7532564 baseEnd_7532564 := by
    simpa [prefixWord, tailWord_7532564, baseEnd_7532564] using wordTrace_append hprefix tailTrace_7532564
  have hstable : (prefixWord ++ tailWord_7532564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532564).length < 2 ^ (prefixWord ++ tailWord_7532564).sum := by decide
  have hdescent : baseEnd_7532564 < baseStart_7532564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532584 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 7]
def baseStart_7532584 : Nat := 118140960795 + 7532584 * 2 ^ 59
def prefixEnd_7532584 : Nat := 4983230072969 + 3 ^ 40 * 7532584 * 2
def baseEnd_7532584 : Nat := 429759573596317996017587

theorem tailTrace_7532584 : CollatzResearch.WordTrace tailWord_7532584 prefixEnd_7532584 429759573596317996017587 := by
  unfold tailWord_7532584
  simp only [CollatzResearch.WordTrace]
  refine ⟨137367954471371052885882403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183157272628494737181176537 137367954471371052885882403)
  ·
    refine ⟨206051931707056579328823605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137367954471371052885882403 206051931707056579328823605)
    ·
      refine ⟨19317368597536554312077213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206051931707056579328823605 19317368597536554312077213)
      ·
        refine ⟨7244013224076207867028955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19317368597536554312077213 7244013224076207867028955)
        ·
          refine ⟨10866019836114311800543433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244013224076207867028955 10866019836114311800543433)
          ·
            refine ⟨8149514877085733850407575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10866019836114311800543433 8149514877085733850407575)
            ·
              refine ⟨12224272315628600775611363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149514877085733850407575 12224272315628600775611363)
              ·
                refine ⟨18336408473442901163417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224272315628600775611363 18336408473442901163417045)
                ·
                  refine ⟨429759573596317996017587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18336408473442901163417045 429759573596317996017587)
                  ·
                    rfl

theorem cell23_7532584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_7532584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532584 prefixEnd_7532584 := by exact prefixLift 7532584
  have htrace : WordTrace (prefixWord ++ tailWord_7532584) baseStart_7532584 baseEnd_7532584 := by
    simpa [prefixWord, tailWord_7532584, baseEnd_7532584] using wordTrace_append hprefix tailTrace_7532584
  have hstable : (prefixWord ++ tailWord_7532584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532584).length < 2 ^ (prefixWord ++ tailWord_7532584).sum := by decide
  have hdescent : baseEnd_7532584 < baseStart_7532584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532590 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7532590 : Nat := 118140960795 + 7532590 * 2 ^ 59
def prefixEnd_7532590 : Nat := 4983230072969 + 3 ^ 40 * 7532590 * 2
def baseEnd_7532590 : Nat := 3867839243250788940683255

theorem tailTrace_7532590 : CollatzResearch.WordTrace tailWord_7532590 prefixEnd_7532590 3867839243250788940683255 := by
  unfold tailWord_7532590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342015972590046099560403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183157418520480245864322149 34342015972590046099560403)
  ·
    refine ⟨51513023958885069149340605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34342015972590046099560403 51513023958885069149340605)
    ·
      refine ⟨19317383984581900931002727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51513023958885069149340605 19317383984581900931002727)
      ·
        refine ⟨28976075976872851396504091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317383984581900931002727 28976075976872851396504091)
        ·
          refine ⟨43464113965309277094756137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28976075976872851396504091 43464113965309277094756137)
          ·
            refine ⟨32598085473981957821067103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43464113965309277094756137 32598085473981957821067103)
            ·
              refine ⟨48897128210972936731600655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32598085473981957821067103 48897128210972936731600655)
              ·
                refine ⟨73345692316459405097400983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48897128210972936731600655 73345692316459405097400983)
                ·
                  refine ⟨110018538474689107646101475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73345692316459405097400983 110018538474689107646101475)
                  ·
                    refine ⟨165027807712033661469152213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110018538474689107646101475 165027807712033661469152213)
                    ·
                      refine ⟨3867839243250788940683255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165027807712033661469152213 3867839243250788940683255)
                      ·
                        rfl

theorem cell23_7532590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7532590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532590 prefixEnd_7532590 := by exact prefixLift 7532590
  have htrace : WordTrace (prefixWord ++ tailWord_7532590) baseStart_7532590 baseEnd_7532590 := by
    simpa [prefixWord, tailWord_7532590, baseEnd_7532590] using wordTrace_append hprefix tailTrace_7532590
  have hstable : (prefixWord ++ tailWord_7532590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532590).length < 2 ^ (prefixWord ++ tailWord_7532590).sum := by decide
  have hdescent : baseEnd_7532590 < baseStart_7532590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532613 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_7532613 : Nat := 118140960795 + 7532613 * 2 ^ 59
def prefixEnd_7532613 : Nat := 4983230072969 + 3 ^ 40 * 7532613 * 2
def baseEnd_7532613 : Nat := 3867851053305842350695649

theorem tailTrace_7532613 : CollatzResearch.WordTrace tailWord_7532613 prefixEnd_7532613 3867851053305842350695649 := by
  unfold tailWord_7532613
  simp only [CollatzResearch.WordTrace]
  refine ⟨274736966659637043724570493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183157977773091362483046995 274736966659637043724570493)
  ·
    refine ⟨103026362497363891396713935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274736966659637043724570493 103026362497363891396713935)
    ·
      refine ⟨154539543746045837095070903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103026362497363891396713935 154539543746045837095070903)
      ·
        refine ⟨231809315619068755642606355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154539543746045837095070903 231809315619068755642606355)
        ·
          refine ⟨347713973428603133463909533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231809315619068755642606355 347713973428603133463909533)
          ·
            refine ⟨130392740035726175048966075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347713973428603133463909533 130392740035726175048966075)
            ·
              refine ⟨195589110053589262573449113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130392740035726175048966075 195589110053589262573449113)
              ·
                refine ⟨146691832540191946930086835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195589110053589262573449113 146691832540191946930086835)
                ·
                  refine ⟨220037748810287920395130253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146691832540191946930086835 220037748810287920395130253)
                  ·
                    refine ⟨82514155803857970148173845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220037748810287920395130253 82514155803857970148173845)
                    ·
                      refine ⟨3867851053305842350695649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82514155803857970148173845 3867851053305842350695649)
                      ·
                        rfl

theorem cell23_7532613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_7532613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532613 prefixEnd_7532613 := by exact prefixLift 7532613
  have htrace : WordTrace (prefixWord ++ tailWord_7532613) baseStart_7532613 baseEnd_7532613 := by
    simpa [prefixWord, tailWord_7532613, baseEnd_7532613] using wordTrace_append hprefix tailTrace_7532613
  have hstable : (prefixWord ++ tailWord_7532613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532613).length < 2 ^ (prefixWord ++ tailWord_7532613).sum := by decide
  have hdescent : baseEnd_7532613 < baseStart_7532613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532614 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_7532614 : Nat := 118140960795 + 7532614 * 2 ^ 59
def prefixEnd_7532614 : Nat := 4983230072969 + 3 ^ 40 * 7532614 * 2
def baseEnd_7532614 : Nat := 1289283855595498948927715

theorem tailTrace_7532614 : CollatzResearch.WordTrace tailWord_7532614 prefixEnd_7532614 1289283855595498948927715 := by
  unfold tailWord_7532614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585531347894794402979903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183158002088422280596904597 8585531347894794402979903)
  ·
    refine ⟨12878297021842191604469855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585531347894794402979903 12878297021842191604469855)
    ·
      refine ⟨19317445532763287406704783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878297021842191604469855 19317445532763287406704783)
      ·
        refine ⟨28976168299144931110057175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317445532763287406704783 28976168299144931110057175)
        ·
          refine ⟨43464252448717396665085763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28976168299144931110057175 43464252448717396665085763)
          ·
            refine ⟨65196378673076094997628645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43464252448717396665085763 65196378673076094997628645)
            ·
              refine ⟨12224321001201767812055371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65196378673076094997628645 12224321001201767812055371)
              ·
                refine ⟨18336481501802651718083057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224321001201767812055371 18336481501802651718083057)
                ·
                  refine ⟨13752361126351988788562293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18336481501802651718083057 13752361126351988788562293)
                  ·
                    refine ⟨1289283855595498948927715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13752361126351988788562293 1289283855595498948927715)
                    ·
                      rfl

theorem cell23_7532614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_7532614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532614 prefixEnd_7532614 := by exact prefixLift 7532614
  have htrace : WordTrace (prefixWord ++ tailWord_7532614) baseStart_7532614 baseEnd_7532614 := by
    simpa [prefixWord, tailWord_7532614, baseEnd_7532614] using wordTrace_append hprefix tailTrace_7532614
  have hstable : (prefixWord ++ tailWord_7532614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532614).length < 2 ^ (prefixWord ++ tailWord_7532614).sum := by decide
  have hdescent : baseEnd_7532614 < baseStart_7532614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532620 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7532620 : Nat := 118140960795 + 7532620 * 2 ^ 59
def prefixEnd_7532620 : Nat := 4983230072969 + 3 ^ 40 * 7532620 * 2
def baseEnd_7532620 : Nat := 3867854647670423823308117

theorem tailTrace_7532620 : CollatzResearch.WordTrace tailWord_7532620 prefixEnd_7532620 3867854647670423823308117 := by
  unfold tailWord_7532620
  simp only [CollatzResearch.WordTrace]
  refine ⟨137368610985305841960037657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183158147980407789280050209 137368610985305841960037657)
  ·
    refine ⟨103026458238979381470028243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137368610985305841960037657 103026458238979381470028243)
    ·
      refine ⟨154539687358469072205042365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103026458238979381470028243 154539687358469072205042365)
      ·
        refine ⟨57952382759425902076890887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154539687358469072205042365 57952382759425902076890887)
        ·
          refine ⟨86928574139138853115336331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57952382759425902076890887 86928574139138853115336331)
          ·
            refine ⟨130392861208708279673004497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86928574139138853115336331 130392861208708279673004497)
            ·
              refine ⟨97794645906531209754753373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130392861208708279673004497 97794645906531209754753373)
              ·
                refine ⟨36672992214949203658032515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97794645906531209754753373 36672992214949203658032515)
                ·
                  refine ⟨55009488322423805487048773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36672992214949203658032515 55009488322423805487048773)
                  ·
                    refine ⟨10314279060454463528821645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55009488322423805487048773 10314279060454463528821645)
                    ·
                      refine ⟨3867854647670423823308117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10314279060454463528821645 3867854647670423823308117)
                      ·
                        rfl

theorem cell23_7532620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7532620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532620 prefixEnd_7532620 := by exact prefixLift 7532620
  have htrace : WordTrace (prefixWord ++ tailWord_7532620) baseStart_7532620 baseEnd_7532620 := by
    simpa [prefixWord, tailWord_7532620, baseEnd_7532620] using wordTrace_append hprefix tailTrace_7532620
  have hstable : (prefixWord ++ tailWord_7532620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532620).length < 2 ^ (prefixWord ++ tailWord_7532620).sum := by decide
  have hdescent : baseEnd_7532620 < baseStart_7532620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532640 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 6]
def baseStart_7532640 : Nat := 118140960795 + 7532640 * 2 ^ 59
def prefixEnd_7532640 : Nat := 4983230072969 + 3 ^ 40 * 7532640 * 2
def baseEnd_7532640 : Nat := 429762768587057082784225

theorem tailTrace_7532640 : CollatzResearch.WordTrace tailWord_7532640 prefixEnd_7532640 429762768587057082784225 := by
  unfold tailWord_7532640
  simp only [CollatzResearch.WordTrace]
  refine ⟨137368975715269613667901687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183158634287026151557202249 137368975715269613667901687)
  ·
    refine ⟨206053463572904420501852531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137368975715269613667901687 206053463572904420501852531)
    ·
      refine ⟨309080195359356630752778797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206053463572904420501852531 309080195359356630752778797)
      ·
        refine ⟨115905073259758736532292049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309080195359356630752778797 115905073259758736532292049)
        ·
          refine ⟨86928804944819052399219037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115905073259758736532292049 86928804944819052399219037)
          ·
            refine ⟨32598301854307144649707139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86928804944819052399219037 32598301854307144649707139)
            ·
              refine ⟨48897452781460716974560709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32598301854307144649707139 48897452781460716974560709)
              ·
                refine ⟨9168272396523884432730133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48897452781460716974560709 9168272396523884432730133)
                ·
                  refine ⟨429762768587057082784225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9168272396523884432730133 429762768587057082784225)
                  ·
                    rfl

theorem cell23_7532640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_7532640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532640 prefixEnd_7532640 := by exact prefixLift 7532640
  have htrace : WordTrace (prefixWord ++ tailWord_7532640) baseStart_7532640 baseEnd_7532640 := by
    simpa [prefixWord, tailWord_7532640, baseEnd_7532640] using wordTrace_append hprefix tailTrace_7532640
  have hstable : (prefixWord ++ tailWord_7532640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532640).length < 2 ^ (prefixWord ++ tailWord_7532640).sum := by decide
  have hdescent : baseEnd_7532640 < baseStart_7532640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532701 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_7532701 : Nat := 118140960795 + 7532701 * 2 ^ 59
def prefixEnd_7532701 : Nat := 4983230072969 + 3 ^ 40 * 7532701 * 2
def baseEnd_7532701 : Nat := 3867896239603438006395245

theorem tailTrace_7532701 : CollatzResearch.WordTrace tailWord_7532701 prefixEnd_7532701 3867896239603438006395245 := by
  unfold tailWord_7532701
  simp only [CollatzResearch.WordTrace]
  refine ⟨274740176283318234753773957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183160117522212156502515971 274740176283318234753773957)
  ·
    refine ⟨51513783053122169016332617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274740176283318234753773957 51513783053122169016332617)
    ·
      refine ⟨38635337289841626762249463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51513783053122169016332617 38635337289841626762249463)
      ·
        refine ⟨57953005934762440143374195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38635337289841626762249463 57953005934762440143374195)
        ·
          refine ⟨86929508902143660215061293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57953005934762440143374195 86929508902143660215061293)
          ·
            refine ⟨32598565838303872580647985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86929508902143660215061293 32598565838303872580647985)
            ·
              refine ⟨24448924378727904435485989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32598565838303872580647985 24448924378727904435485989)
              ·
                refine ⟨4584173321011482081653623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24448924378727904435485989 4584173321011482081653623)
                ·
                  refine ⟨6876259981517223122480435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584173321011482081653623 6876259981517223122480435)
                  ·
                    refine ⟨10314389972275834683720653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6876259981517223122480435 10314389972275834683720653)
                    ·
                      refine ⟨3867896239603438006395245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10314389972275834683720653 3867896239603438006395245)
                      ·
                        rfl

theorem cell23_7532701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_7532701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532701 prefixEnd_7532701 := by exact prefixLift 7532701
  have htrace : WordTrace (prefixWord ++ tailWord_7532701) baseStart_7532701 baseEnd_7532701 := by
    simpa [prefixWord, tailWord_7532701, baseEnd_7532701] using wordTrace_append hprefix tailTrace_7532701
  have hstable : (prefixWord ++ tailWord_7532701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532701).length < 2 ^ (prefixWord ++ tailWord_7532701).sum := by decide
  have hdescent : baseEnd_7532701 < baseStart_7532701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532767 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 7, 2]
def baseStart_7532767 : Nat := 118140960795 + 7532767 * 2 ^ 59
def prefixEnd_7532767 : Nat := 4983230072969 + 3 ^ 40 * 7532767 * 2
def baseEnd_7532767 : Nat := 3867930129326634748169941

theorem tailTrace_7532767 : CollatzResearch.WordTrace tailWord_7532767 prefixEnd_7532767 3867930129326634748169941 := by
  unfold tailWord_7532767
  simp only [CollatzResearch.WordTrace]
  refine ⟨274742583501079128025676555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183161722334052752017117703 274742583501079128025676555)
  ·
    refine ⟨412113875251618692038514833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274742583501079128025676555 412113875251618692038514833)
    ·
      refine ⟨309085406438714019028886125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412113875251618692038514833 309085406438714019028886125)
      ·
        refine ⟨115907027414517757135832297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309085406438714019028886125 115907027414517757135832297)
        ·
          refine ⟨86930270560888317851874223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115907027414517757135832297 86930270560888317851874223)
          ·
            refine ⟨130395405841332476777811335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86930270560888317851874223 130395405841332476777811335)
            ·
              refine ⟨195593108761998715166717003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130395405841332476777811335 195593108761998715166717003)
              ·
                refine ⟨293389663142998072750075505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195593108761998715166717003 293389663142998072750075505)
                ·
                  refine ⟨220042247357248554562556629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293389663142998072750075505 220042247357248554562556629)
                  ·
                    refine ⟨5157240172435512997559921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220042247357248554562556629 5157240172435512997559921)
                    ·
                      refine ⟨3867930129326634748169941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157240172435512997559921 3867930129326634748169941)
                      ·
                        rfl

theorem cell23_7532767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_7532767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532767 prefixEnd_7532767 := by exact prefixLift 7532767
  have htrace : WordTrace (prefixWord ++ tailWord_7532767) baseStart_7532767 baseEnd_7532767 := by
    simpa [prefixWord, tailWord_7532767, baseEnd_7532767] using wordTrace_append hprefix tailTrace_7532767
  have hstable : (prefixWord ++ tailWord_7532767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532767).length < 2 ^ (prefixWord ++ tailWord_7532767).sum := by decide
  have hdescent : baseEnd_7532767 < baseStart_7532767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532814 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7532814 : Nat := 118140960795 + 7532814 * 2 ^ 59
def prefixEnd_7532814 : Nat := 4983230072969 + 3 ^ 40 * 7532814 * 2
def baseEnd_7532814 : Nat := 3867954262917396064282225

theorem tailTrace_7532814 : CollatzResearch.WordTrace tailWord_7532814 prefixEnd_7532814 3867954262917396064282225 := by
  unfold tailWord_7532814
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343037216488606881579687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183162865154605903368424997 34343037216488606881579687)
  ·
    refine ⟨51514555824732910322369531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34343037216488606881579687 51514555824732910322369531)
    ·
      refine ⟨77271833737099365483554297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51514555824732910322369531 77271833737099365483554297)
      ·
        refine ⟨57953875302824524112665723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77271833737099365483554297 57953875302824524112665723)
        ·
          refine ⟨86930812954236786168998585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57953875302824524112665723 86930812954236786168998585)
          ·
            refine ⟨65198109715677589626748939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86930812954236786168998585 65198109715677589626748939)
            ·
              refine ⟨97797164573516384440123409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65198109715677589626748939 97797164573516384440123409)
              ·
                refine ⟨73347873430137288330092557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97797164573516384440123409 73347873430137288330092557)
                ·
                  refine ⟨27505452536301483123784709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73347873430137288330092557 27505452536301483123784709)
                  ·
                    refine ⟨5157272350556528085709633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27505452536301483123784709 5157272350556528085709633)
                    ·
                      refine ⟨3867954262917396064282225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157272350556528085709633 3867954262917396064282225)
                      ·
                        rfl

theorem cell23_7532814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7532814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532814 prefixEnd_7532814 := by exact prefixLift 7532814
  have htrace : WordTrace (prefixWord ++ tailWord_7532814) baseStart_7532814 baseEnd_7532814 := by
    simpa [prefixWord, tailWord_7532814, baseEnd_7532814] using wordTrace_append hprefix tailTrace_7532814
  have hstable : (prefixWord ++ tailWord_7532814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532814).length < 2 ^ (prefixWord ++ tailWord_7532814).sum := by decide
  have hdescent : baseEnd_7532814 < baseStart_7532814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532817 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_7532817 : Nat := 118140960795 + 7532817 * 2 ^ 59
def prefixEnd_7532817 : Nat := 4983230072969 + 3 ^ 40 * 7532817 * 2
def baseEnd_7532817 : Nat := 3867955803359359552544711

theorem tailTrace_7532817 : CollatzResearch.WordTrace tailWord_7532817 prefixEnd_7532817 3867955803359359552544711 := by
  unfold tailWord_7532817
  simp only [CollatzResearch.WordTrace]
  refine ⟨274744407150897986564996705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183162938100598657709997803 274744407150897986564996705)
  ·
    refine ⟨206058305363173489923747529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274744407150897986564996705 206058305363173489923747529)
    ·
      refine ⟨154543729022380117442810647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206058305363173489923747529 154543729022380117442810647)
      ·
        refine ⟨231815593533570176164215971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154543729022380117442810647 231815593533570176164215971)
        ·
          refine ⟨347723390300355264246323957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231815593533570176164215971 347723390300355264246323957)
          ·
            refine ⟨32599067840658306023092871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347723390300355264246323957 32599067840658306023092871)
            ·
              refine ⟨48898601760987459034639307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32599067840658306023092871 48898601760987459034639307)
              ·
                refine ⟨73347902641481188551958961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48898601760987459034639307 73347902641481188551958961)
                ·
                  refine ⟨55010926981110891413969221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73347902641481188551958961 55010926981110891413969221)
                  ·
                    refine ⟨10314548808958292140119229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55010926981110891413969221 10314548808958292140119229)
                    ·
                      refine ⟨3867955803359359552544711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10314548808958292140119229 3867955803359359552544711)
                      ·
                        rfl

theorem cell23_7532817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_7532817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532817 prefixEnd_7532817 := by exact prefixLift 7532817
  have htrace : WordTrace (prefixWord ++ tailWord_7532817) baseStart_7532817 baseEnd_7532817 := by
    simpa [prefixWord, tailWord_7532817, baseEnd_7532817] using wordTrace_append hprefix tailTrace_7532817
  have hstable : (prefixWord ++ tailWord_7532817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532817).length < 2 ^ (prefixWord ++ tailWord_7532817).sum := by decide
  have hdescent : baseEnd_7532817 < baseStart_7532817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532831 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 4, 2]
def baseStart_7532831 : Nat := 118140960795 + 7532831 * 2 ^ 59
def prefixEnd_7532831 : Nat := 4983230072969 + 3 ^ 40 * 7532831 * 2
def baseEnd_7532831 : Nat := 3867962992088522497769647

theorem tailTrace_7532831 : CollatzResearch.WordTrace tailWord_7532831 prefixEnd_7532831 3867962992088522497769647 := by
  unfold tailWord_7532831
  simp only [CollatzResearch.WordTrace]
  refine ⟨274744917772847266956006347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183163278515231511304004231 274744917772847266956006347)
  ·
    refine ⟨412117376659270900434009521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274744917772847266956006347 412117376659270900434009521)
    ·
      refine ⟨309088032494453175325507141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412117376659270900434009521 309088032494453175325507141)
      ·
        refine ⟨57954006092709970373532589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309088032494453175325507141 57954006092709970373532589)
        ·
          refine ⟨21732752284766238890074721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57954006092709970373532589 21732752284766238890074721)
          ·
            refine ⟨16299564213574679167556041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21732752284766238890074721 16299564213574679167556041)
            ·
              refine ⟨12224673160181009375667031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16299564213574679167556041 12224673160181009375667031)
              ·
                refine ⟨18337009740271514063500547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224673160181009375667031 18337009740271514063500547)
                ·
                  refine ⟨27505514610407271095250821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18337009740271514063500547 27505514610407271095250821)
                  ·
                    refine ⟨5157283989451363330359529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27505514610407271095250821 5157283989451363330359529)
                    ·
                      refine ⟨3867962992088522497769647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157283989451363330359529 3867962992088522497769647)
                      ·
                        rfl

theorem cell23_7532831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_7532831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532831 prefixEnd_7532831 := by exact prefixLift 7532831
  have htrace : WordTrace (prefixWord ++ tailWord_7532831) baseStart_7532831 baseEnd_7532831 := by
    simpa [prefixWord, tailWord_7532831, baseEnd_7532831] using wordTrace_append hprefix tailTrace_7532831
  have hstable : (prefixWord ++ tailWord_7532831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532831).length < 2 ^ (prefixWord ++ tailWord_7532831).sum := by decide
  have hdescent : baseEnd_7532831 < baseStart_7532831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532867 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 2, 5]
def baseStart_7532867 : Nat := 118140960795 + 7532867 * 2 ^ 59
def prefixEnd_7532867 : Nat := 4983230072969 + 3 ^ 40 * 7532867 * 2
def baseEnd_7532867 : Nat := 1289327159130694785639827

theorem tailTrace_7532867 : CollatzResearch.WordTrace tailWord_7532867 prefixEnd_7532867 1289327159130694785639827 := by
  unfold tailWord_7532867
  simp only [CollatzResearch.WordTrace]
  refine ⟨274746230800716845104316855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183164153867144563402877903 274746230800716845104316855)
  ·
    refine ⟨412119346201075267656475283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274746230800716845104316855 412119346201075267656475283)
    ·
      refine ⟨618179019301612901484712925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412119346201075267656475283 618179019301612901484712925)
      ·
        refine ⟨231817132238104838056767347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618179019301612901484712925 231817132238104838056767347)
        ·
          refine ⟨347725698357157257085151021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231817132238104838056767347 347725698357157257085151021)
          ·
            refine ⟨130397136883933971406931633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347725698357157257085151021 130397136883933971406931633)
            ·
              refine ⟨97797852662950478555198725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130397136883933971406931633 97797852662950478555198725)
              ·
                refine ⟨18337097374303214729099761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97797852662950478555198725 18337097374303214729099761)
                ·
                  refine ⟨13752823030727411046824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18337097374303214729099761 13752823030727411046824821)
                  ·
                    refine ⟨1289327159130694785639827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13752823030727411046824821 1289327159130694785639827)
                    ·
                      rfl

theorem cell23_7532867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].length) (baseStart_7532867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532867 prefixEnd_7532867 := by exact prefixLift 7532867
  have htrace : WordTrace (prefixWord ++ tailWord_7532867) baseStart_7532867 baseEnd_7532867 := by
    simpa [prefixWord, tailWord_7532867, baseEnd_7532867] using wordTrace_append hprefix tailTrace_7532867
  have hstable : (prefixWord ++ tailWord_7532867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532867).length < 2 ^ (prefixWord ++ tailWord_7532867).sum := by decide
  have hdescent : baseEnd_7532867 < baseStart_7532867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532887 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_7532887 : Nat := 118140960795 + 7532887 * 2 ^ 59
def prefixEnd_7532887 : Nat := 4983230072969 + 3 ^ 40 * 7532887 * 2
def baseEnd_7532887 : Nat := 3867991747005174278669389

theorem tailTrace_7532887 : CollatzResearch.WordTrace tailWord_7532887 prefixEnd_7532887 3867991747005174278669389 := by
  unfold tailWord_7532887
  simp only [CollatzResearch.WordTrace]
  refine ⟨274746960260644388520044915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183164640173762925680029943 274746960260644388520044915)
  ·
    refine ⟨412120440390966582780067373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274746960260644388520044915 412120440390966582780067373)
    ·
      refine ⟨154545165146612468542525265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412120440390966582780067373 154545165146612468542525265)
      ·
        refine ⟨115908873859959351406893949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154545165146612468542525265 115908873859959351406893949)
        ·
          refine ⟨43465827697484756777585231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115908873859959351406893949 43465827697484756777585231)
          ·
            refine ⟨65198741546227135166377847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43465827697484756777585231 65198741546227135166377847)
            ·
              refine ⟨97798112319340702749566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65198741546227135166377847 97798112319340702749566771)
              ·
                refine ⟨146697168479011054124350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97798112319340702749566771 146697168479011054124350157)
                ·
                  refine ⟨55011438179629145296631309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146697168479011054124350157 55011438179629145296631309)
                  ·
                    refine ⟨20629289317360929486236741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55011438179629145296631309 20629289317360929486236741)
                    ·
                      refine ⟨3867991747005174278669389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20629289317360929486236741 3867991747005174278669389)
                      ·
                        rfl

theorem cell23_7532887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_7532887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532887 prefixEnd_7532887 := by exact prefixLift 7532887
  have htrace : WordTrace (prefixWord ++ tailWord_7532887) baseStart_7532887 baseEnd_7532887 := by
    simpa [prefixWord, tailWord_7532887, baseEnd_7532887] using wordTrace_append hprefix tailTrace_7532887
  have hstable : (prefixWord ++ tailWord_7532887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532887).length < 2 ^ (prefixWord ++ tailWord_7532887).sum := by decide
  have hdescent : baseEnd_7532887 < baseStart_7532887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532904 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7532904 : Nat := 118140960795 + 7532904 * 2 ^ 59
def prefixEnd_7532904 : Nat := 4983230072969 + 3 ^ 40 * 7532904 * 2
def baseEnd_7532904 : Nat := 3868000476176300712156811

theorem tailTrace_7532904 : CollatzResearch.WordTrace tailWord_7532904 prefixEnd_7532904 3868000476176300712156811 := by
  unfold tailWord_7532904
  simp only [CollatzResearch.WordTrace]
  refine ⟨137373790150791400211706883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183165053534388533615609177 137373790150791400211706883)
  ·
    refine ⟨206060685226187100317560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137373790150791400211706883 206060685226187100317560325)
    ·
      refine ⟨38636378479910081309542561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206060685226187100317560325 38636378479910081309542561)
      ·
        refine ⟨28977283859932560982156921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38636378479910081309542561 28977283859932560982156921)
        ·
          refine ⟨21732962894949420736617691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28977283859932560982156921 21732962894949420736617691)
          ·
            refine ⟨32599444342424131104926537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21732962894949420736617691 32599444342424131104926537)
            ·
              refine ⟨24449583256818098328694903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32599444342424131104926537 24449583256818098328694903)
              ·
                refine ⟨36674374885227147493042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24449583256818098328694903 36674374885227147493042355)
                ·
                  refine ⟨55011562327840721239563533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36674374885227147493042355 55011562327840721239563533)
                  ·
                    refine ⟨20629335872940270464836325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55011562327840721239563533 20629335872940270464836325)
                    ·
                      refine ⟨3868000476176300712156811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20629335872940270464836325 3868000476176300712156811)
                      ·
                        rfl

theorem cell23_7532904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7532904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532904 prefixEnd_7532904 := by exact prefixLift 7532904
  have htrace : WordTrace (prefixWord ++ tailWord_7532904) baseStart_7532904 baseEnd_7532904 := by
    simpa [prefixWord, tailWord_7532904, baseEnd_7532904] using wordTrace_append hprefix tailTrace_7532904
  have hstable : (prefixWord ++ tailWord_7532904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532904).length < 2 ^ (prefixWord ++ tailWord_7532904).sum := by decide
  have hdescent : baseEnd_7532904 < baseStart_7532904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532918 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7532918 : Nat := 118140960795 + 7532918 * 2 ^ 59
def prefixEnd_7532918 : Nat := 4983230072969 + 3 ^ 40 * 7532918 * 2
def baseEnd_7532918 : Nat := 1289335888301821219127249

theorem tailTrace_7532918 : CollatzResearch.WordTrace tailWord_7532918 prefixEnd_7532918 1289335888301821219127249 := by
  unfold tailWord_7532918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17171755682720755050901463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183165393949021387209615605 17171755682720755050901463)
  ·
    refine ⟨25757633524081132576352195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17171755682720755050901463 25757633524081132576352195)
    ·
      refine ⟨38636450286121698864528293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25757633524081132576352195 38636450286121698864528293)
      ·
        refine ⟨7244334428647818537099055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38636450286121698864528293 7244334428647818537099055)
        ·
          refine ⟨10866501642971727805648583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244334428647818537099055 10866501642971727805648583)
          ·
            refine ⟨16299752464457591708472875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866501642971727805648583 16299752464457591708472875)
            ·
              refine ⟨24449628696686387562709313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16299752464457591708472875 24449628696686387562709313)
              ·
                refine ⟨18337221522514790672031985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24449628696686387562709313 18337221522514790672031985)
                ·
                  refine ⟨13752916141886093004023989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18337221522514790672031985 13752916141886093004023989)
                  ·
                    refine ⟨1289335888301821219127249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13752916141886093004023989 1289335888301821219127249)
                    ·
                      rfl

theorem cell23_7532918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7532918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532918 prefixEnd_7532918 := by exact prefixLift 7532918
  have htrace : WordTrace (prefixWord ++ tailWord_7532918) baseStart_7532918 baseEnd_7532918 := by
    simpa [prefixWord, tailWord_7532918, baseEnd_7532918] using wordTrace_append hprefix tailTrace_7532918
  have hstable : (prefixWord ++ tailWord_7532918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532918).length < 2 ^ (prefixWord ++ tailWord_7532918).sum := by decide
  have hdescent : baseEnd_7532918 < baseStart_7532918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532958 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7532958 : Nat := 118140960795 + 7532958 * 2 ^ 59
def prefixEnd_7532958 : Nat := 4983230072969 + 3 ^ 40 * 7532958 * 2
def baseEnd_7532958 : Nat := 3868028204131643500881563

theorem tailTrace_7532958 : CollatzResearch.WordTrace tailWord_7532958 prefixEnd_7532958 3868028204131643500881563 := by
  unfold tailWord_7532958
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343693730423395955734941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183166366562258111763919685 34343693730423395955734941)
  ·
    refine ⟨12878885148908773483400603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34343693730423395955734941 12878885148908773483400603)
    ·
      refine ⟨19318327723363160225100905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878885148908773483400603 19318327723363160225100905)
      ·
        refine ⟨14488745792522370168825679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19318327723363160225100905 14488745792522370168825679)
        ·
          refine ⟨21733118688783555253238519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14488745792522370168825679 21733118688783555253238519)
          ·
            refine ⟨32599678033175332879857779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21733118688783555253238519 32599678033175332879857779)
            ·
              refine ⟨48899517049762999319786669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32599678033175332879857779 48899517049762999319786669)
              ·
                refine ⟨18337318893661124744920001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48899517049762999319786669 18337318893661124744920001)
                ·
                  refine ⟨13752989170245843558690001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18337318893661124744920001 13752989170245843558690001)
                  ·
                    refine ⟨10314741877684382669017501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13752989170245843558690001 10314741877684382669017501)
                    ·
                      refine ⟨3868028204131643500881563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10314741877684382669017501 3868028204131643500881563)
                      ·
                        rfl

theorem cell23_7532958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7532958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7532958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7532958 prefixEnd_7532958 := by exact prefixLift 7532958
  have htrace : WordTrace (prefixWord ++ tailWord_7532958) baseStart_7532958 baseEnd_7532958 := by
    simpa [prefixWord, tailWord_7532958, baseEnd_7532958] using wordTrace_append hprefix tailTrace_7532958
  have hstable : (prefixWord ++ tailWord_7532958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532958).length < 2 ^ (prefixWord ++ tailWord_7532958).sum := by decide
  have hdescent : baseEnd_7532958 < baseStart_7532958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533021 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7533021 : Nat := 118140960795 + 7533021 * 2 ^ 59
def prefixEnd_7533021 : Nat := 4983230072969 + 3 ^ 40 * 7533021 * 2
def baseEnd_7533021 : Nat := 1289353517804292251464591

theorem tailTrace_7533021 : CollatzResearch.WordTrace tailWord_7533021 prefixEnd_7533021 1289353517804292251464591 := by
  unfold tailWord_7533021
  simp only [CollatzResearch.WordTrace]
  refine ⟨274751847642158929405422917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183167898428105952936948611 274751847642158929405422917)
  ·
    refine ⟨51515971432904799263516797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274751847642158929405422917 51515971432904799263516797)
    ·
      refine ⟨19318489287339299723818799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51515971432904799263516797 19318489287339299723818799)
      ·
        refine ⟨28977733931008949585728199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318489287339299723818799 28977733931008949585728199)
        ·
          refine ⟨43466600896513424378592299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28977733931008949585728199 43466600896513424378592299)
          ·
            refine ⟨65199901344770136567888449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43466600896513424378592299 65199901344770136567888449)
            ·
              refine ⟨48899926008577602425916337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65199901344770136567888449 48899926008577602425916337)
              ·
                refine ⟨36674944506433201819437253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48899926008577602425916337 36674944506433201819437253)
                ·
                  refine ⟨6876552094956225341144485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36674944506433201819437253 6876552094956225341144485)
                  ·
                    refine ⟨1289353517804292251464591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876552094956225341144485 1289353517804292251464591)
                    ·
                      rfl

theorem cell23_7533021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7533021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533021 prefixEnd_7533021 := by exact prefixLift 7533021
  have htrace : WordTrace (prefixWord ++ tailWord_7533021) baseStart_7533021 baseEnd_7533021 := by
    simpa [prefixWord, tailWord_7533021, baseEnd_7533021] using wordTrace_append hprefix tailTrace_7533021
  have hstable : (prefixWord ++ tailWord_7533021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533021).length < 2 ^ (prefixWord ++ tailWord_7533021).sum := by decide
  have hdescent : baseEnd_7533021 < baseStart_7533021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533024 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_7533024 : Nat := 118140960795 + 7533024 * 2 ^ 59
def prefixEnd_7533024 : Nat := 4983230072969 + 3 ^ 40 * 7533024 * 2
def baseEnd_7533024 : Nat := 3868062093854840242656259

theorem tailTrace_7533024 : CollatzResearch.WordTrace tailWord_7533024 prefixEnd_7533024 3868062093854840242656259 := by
  unfold tailWord_7533024
  simp only [CollatzResearch.WordTrace]
  refine ⟨137375978530574030458891063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183167971374098707278521417 137375978530574030458891063)
  ·
    refine ⟨206063967795861045688336595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137375978530574030458891063 206063967795861045688336595)
    ·
      refine ⟨309095951693791568532504893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206063967795861045688336595 309095951693791568532504893)
      ·
        refine ⟨115910981885171838199689335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309095951693791568532504893 115910981885171838199689335)
        ·
          refine ⟨173866472827757757299534003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115910981885171838199689335 173866472827757757299534003)
          ·
            refine ⟨260799709241636635949301005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173866472827757757299534003 260799709241636635949301005)
            ·
              refine ⟨97799890965613738480987877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260799709241636635949301005 97799890965613738480987877)
              ·
                refine ⟨18337479556052575965185227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97799890965613738480987877 18337479556052575965185227)
                ·
                  refine ⟨27506219334078863947777841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18337479556052575965185227 27506219334078863947777841)
                  ·
                    refine ⟨20629664500559147960833381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27506219334078863947777841 20629664500559147960833381)
                    ·
                      refine ⟨3868062093854840242656259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20629664500559147960833381 3868062093854840242656259)
                      ·
                        rfl

theorem cell23_7533024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_7533024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533024 prefixEnd_7533024 := by exact prefixLift 7533024
  have htrace : WordTrace (prefixWord ++ tailWord_7533024) baseStart_7533024 baseEnd_7533024 := by
    simpa [prefixWord, tailWord_7533024, baseEnd_7533024] using wordTrace_append hprefix tailTrace_7533024
  have hstable : (prefixWord ++ tailWord_7533024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533024).length < 2 ^ (prefixWord ++ tailWord_7533024).sum := by decide
  have hdescent : baseEnd_7533024 < baseStart_7533024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533034 : List Nat := [3, 1, 3, 1, 3, 2, 10]
def baseStart_7533034 : Nat := 118140960795 + 7533034 * 2 ^ 59
def prefixEnd_7533034 : Nat := 4983230072969 + 3 ^ 40 * 7533034 * 2
def baseEnd_7533034 : Nat := 47753916403226977821373

theorem tailTrace_7533034 : CollatzResearch.WordTrace tailWord_7533034 prefixEnd_7533034 47753916403226977821373 := by
  unfold tailWord_7533034
  simp only [CollatzResearch.WordTrace]
  refine ⟨68688080447777958156411539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183168214527407888417097437 68688080447777958156411539)
  ·
    refine ⟨103032120671666937234617309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68688080447777958156411539 103032120671666937234617309)
    ·
      refine ⟨38637045251875101462981491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103032120671666937234617309 38637045251875101462981491)
      ·
        refine ⟨57955567877812652194472237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38637045251875101462981491 57955567877812652194472237)
        ·
          refine ⟨21733337954179744572927089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57955567877812652194472237 21733337954179744572927089)
          ·
            refine ⟨16300003465634808429695317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21733337954179744572927089 16300003465634808429695317)
            ·
              refine ⟨47753916403226977821373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16300003465634808429695317 47753916403226977821373)
              ·
                rfl

theorem cell23_7533034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 10].length) (baseStart_7533034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533034 prefixEnd_7533034 := by exact prefixLift 7533034
  have htrace : WordTrace (prefixWord ++ tailWord_7533034) baseStart_7533034 baseEnd_7533034 := by
    simpa [prefixWord, tailWord_7533034, baseEnd_7533034] using wordTrace_append hprefix tailTrace_7533034
  have hstable : (prefixWord ++ tailWord_7533034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533034).length < 2 ^ (prefixWord ++ tailWord_7533034).sum := by decide
  have hdescent : baseEnd_7533034 < baseStart_7533034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533038 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_7533038 : Nat := 118140960795 + 7533038 * 2 ^ 59
def prefixEnd_7533038 : Nat := 4983230072969 + 3 ^ 40 * 7533038 * 2
def baseEnd_7533038 : Nat := 1289356427528001062627065

theorem tailTrace_7533038 : CollatzResearch.WordTrace tailWord_7533038 prefixEnd_7533038 1289356427528001062627065 := by
  unfold tailWord_7533038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34344058460387167663598971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183168311788731560872527845 34344058460387167663598971)
  ·
    refine ⟨51516087690580751495398457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34344058460387167663598971 51516087690580751495398457)
    ·
      refine ⟨38637065767935563621548843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51516087690580751495398457 38637065767935563621548843)
      ·
        refine ⟨57955598651903345432323265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38637065767935563621548843 57955598651903345432323265)
        ·
          refine ⟨43466698988927509074242449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57955598651903345432323265 43466698988927509074242449)
          ·
            refine ⟨32600024241695631805681837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43466698988927509074242449 32600024241695631805681837)
            ·
              refine ⟨12225009090635861927130689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32600024241695631805681837 12225009090635861927130689)
              ·
                refine ⟨9168756817976896445348017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12225009090635861927130689 9168756817976896445348017)
                ·
                  refine ⟨6876567613482672334011013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9168756817976896445348017 6876567613482672334011013)
                  ·
                    refine ⟨1289356427528001062627065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876567613482672334011013 1289356427528001062627065)
                    ·
                      rfl

theorem cell23_7533038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_7533038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533038 prefixEnd_7533038 := by exact prefixLift 7533038
  have htrace : WordTrace (prefixWord ++ tailWord_7533038) baseStart_7533038 baseEnd_7533038 := by
    simpa [prefixWord, tailWord_7533038, baseEnd_7533038] using wordTrace_append hprefix tailTrace_7533038
  have hstable : (prefixWord ++ tailWord_7533038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533038).length < 2 ^ (prefixWord ++ tailWord_7533038).sum := by decide
  have hdescent : baseEnd_7533038 < baseStart_7533038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533058 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7533058 : Nat := 118140960795 + 7533058 * 2 ^ 59
def prefixEnd_7533058 : Nat := 4983230072969 + 3 ^ 40 * 7533058 * 2
def baseEnd_7533058 : Nat := 3868079552197093109631103

theorem tailTrace_7533058 : CollatzResearch.WordTrace tailWord_7533058 prefixEnd_7533058 3868079552197093109631103 := by
  unfold tailWord_7533058
  simp only [CollatzResearch.WordTrace]
  refine ⟨68688299285756221181129957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183168798095349923149679885 68688299285756221181129957)
  ·
    refine ⟨12879056116079291471461867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68688299285756221181129957 12879056116079291471461867)
    ·
      refine ⟨19318584174118937207192801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879056116079291471461867 19318584174118937207192801)
      ·
        refine ⟨14488938130589202905394601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19318584174118937207192801 14488938130589202905394601)
        ·
          refine ⟨10866703597941902179045951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14488938130589202905394601 10866703597941902179045951)
          ·
            refine ⟨16300055396912853268568927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866703597941902179045951 16300055396912853268568927)
            ·
              refine ⟨24450083095369279902853391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300055396912853268568927 24450083095369279902853391)
              ·
                refine ⟨36675124643053919854280087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24450083095369279902853391 36675124643053919854280087)
                ·
                  refine ⟨55012686964580879781420131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36675124643053919854280087 55012686964580879781420131)
                  ·
                    refine ⟨82519030446871319672130197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55012686964580879781420131 82519030446871319672130197)
                    ·
                      refine ⟨3868079552197093109631103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82519030446871319672130197 3868079552197093109631103)
                      ·
                        rfl

theorem cell23_7533058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7533058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533058 prefixEnd_7533058 := by exact prefixLift 7533058
  have htrace : WordTrace (prefixWord ++ tailWord_7533058) baseStart_7533058 baseEnd_7533058 := by
    simpa [prefixWord, tailWord_7533058, baseEnd_7533058] using wordTrace_append hprefix tailTrace_7533058
  have hstable : (prefixWord ++ tailWord_7533058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533058).length < 2 ^ (prefixWord ++ tailWord_7533058).sum := by decide
  have hdescent : baseEnd_7533058 < baseStart_7533058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533061 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_7533061 : Nat := 118140960795 + 7533061 * 2 ^ 59
def prefixEnd_7533061 : Nat := 4983230072969 + 3 ^ 40 * 7533061 * 2
def baseEnd_7533061 : Nat := 3868081092639056597893589

theorem tailTrace_7533061 : CollatzResearch.WordTrace tailWord_7533061 prefixEnd_7533061 3868081092639056597893589 := by
  unfold tailWord_7533061
  simp only [CollatzResearch.WordTrace]
  refine ⟨274753306562014016236879037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183168871041342677491252691 274753306562014016236879037)
  ·
    refine ⟨103032489960755256088829639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274753306562014016236879037 103032489960755256088829639)
    ·
      refine ⟨154548734941132884133244459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103032489960755256088829639 154548734941132884133244459)
      ·
        refine ⟨231823102411699326199866689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154548734941132884133244459 231823102411699326199866689)
        ·
          refine ⟨173867326808774494649900017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231823102411699326199866689 173867326808774494649900017)
          ·
            refine ⟨130400495106580870987425013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173867326808774494649900017 130400495106580870987425013)
            ·
              refine ⟨12225046416241956655071095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130400495106580870987425013 12225046416241956655071095)
              ·
                refine ⟨18337569624362934982606643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225046416241956655071095 18337569624362934982606643)
                ·
                  refine ⟨27506354436544402473909965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18337569624362934982606643 27506354436544402473909965)
                  ·
                    refine ⟨10314882913704150927716237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27506354436544402473909965 10314882913704150927716237)
                    ·
                      refine ⟨3868081092639056597893589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10314882913704150927716237 3868081092639056597893589)
                      ·
                        rfl

theorem cell23_7533061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_7533061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533061 prefixEnd_7533061 := by exact prefixLift 7533061
  have htrace : WordTrace (prefixWord ++ tailWord_7533061) baseStart_7533061 baseEnd_7533061 := by
    simpa [prefixWord, tailWord_7533061, baseEnd_7533061] using wordTrace_append hprefix tailTrace_7533061
  have hstable : (prefixWord ++ tailWord_7533061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533061).length < 2 ^ (prefixWord ++ tailWord_7533061).sum := by decide
  have hdescent : baseEnd_7533061 < baseStart_7533061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533062 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7533062 : Nat := 118140960795 + 7533062 * 2 ^ 59
def prefixEnd_7533062 : Nat := 4983230072969 + 3 ^ 40 * 7533062 * 2
def baseEnd_7533062 : Nat := 3868081606119711093981085

theorem tailTrace_7533062 : CollatzResearch.WordTrace tailWord_7533062 prefixEnd_7533062 3868081606119711093981085 := by
  unfold tailWord_7533062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586041969844074793989545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183168895356673595605110293 8586041969844074793989545)
  ·
    refine ⟨6439531477383056095492159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586041969844074793989545 6439531477383056095492159)
    ·
      refine ⟨9659297216074584143238239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439531477383056095492159 9659297216074584143238239)
      ·
        refine ⟨14488945824111876214857359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659297216074584143238239 14488945824111876214857359)
        ·
          refine ⟨21733418736167814322286039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14488945824111876214857359 21733418736167814322286039)
          ·
            refine ⟨32600128104251721483429059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21733418736167814322286039 32600128104251721483429059)
            ·
              refine ⟨48900192156377582225143589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32600128104251721483429059 48900192156377582225143589)
              ·
                refine ⟨9168786029320796667214423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48900192156377582225143589 9168786029320796667214423)
                ·
                  refine ⟨13753179043981195000821635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9168786029320796667214423 13753179043981195000821635)
                  ·
                    refine ⟨20629768565971792501232453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13753179043981195000821635 20629768565971792501232453)
                    ·
                      refine ⟨3868081606119711093981085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20629768565971792501232453 3868081606119711093981085)
                      ·
                        rfl

theorem cell23_7533062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7533062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533062 prefixEnd_7533062 := by exact prefixLift 7533062
  have htrace : WordTrace (prefixWord ++ tailWord_7533062) baseStart_7533062 baseEnd_7533062 := by
    simpa [prefixWord, tailWord_7533062, baseEnd_7533062] using wordTrace_append hprefix tailTrace_7533062
  have hstable : (prefixWord ++ tailWord_7533062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533062).length < 2 ^ (prefixWord ++ tailWord_7533062).sum := by decide
  have hdescent : baseEnd_7533062 < baseStart_7533062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533121 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7533121 : Nat := 118140960795 + 7533121 * 2 ^ 59
def prefixEnd_7533121 : Nat := 4983230072969 + 3 ^ 40 * 7533121 * 2
def baseEnd_7533121 : Nat := 3868111901478326363143313

theorem tailTrace_7533121 : CollatzResearch.WordTrace tailWord_7533121 prefixEnd_7533121 3868111901478326363143313 := by
  unfold tailWord_7533121
  simp only [CollatzResearch.WordTrace]
  refine ⟨274755494941796646484063217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183170329961197764322708811 274755494941796646484063217)
  ·
    refine ⟨206066621206347484863047413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274755494941796646484063217 206066621206347484863047413)
    ·
      refine ⟨19318745738095076705910695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206066621206347484863047413 19318745738095076705910695)
      ·
        refine ⟨28978118607142615058866043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318745738095076705910695 28978118607142615058866043)
        ·
          refine ⟨43467177910713922588299065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28978118607142615058866043 43467177910713922588299065)
          ·
            refine ⟨32600383433035441941224299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43467177910713922588299065 32600383433035441941224299)
            ·
              refine ⟨48900575149553162911836449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32600383433035441941224299 48900575149553162911836449)
              ·
                refine ⟨36675431362164872183877337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48900575149553162911836449 36675431362164872183877337)
                ·
                  refine ⟨27506573521623654137908003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36675431362164872183877337 27506573521623654137908003)
                  ·
                    refine ⟨41259860282435481206862005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27506573521623654137908003 41259860282435481206862005)
                    ·
                      refine ⟨3868111901478326363143313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41259860282435481206862005 3868111901478326363143313)
                      ·
                        rfl

theorem cell23_7533121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7533121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533121 prefixEnd_7533121 := by exact prefixLift 7533121
  have htrace : WordTrace (prefixWord ++ tailWord_7533121) baseStart_7533121 baseEnd_7533121 := by
    simpa [prefixWord, tailWord_7533121, baseEnd_7533121] using wordTrace_append hprefix tailTrace_7533121
  have hstable : (prefixWord ++ tailWord_7533121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533121).length < 2 ^ (prefixWord ++ tailWord_7533121).sum := by decide
  have hdescent : baseEnd_7533121 < baseStart_7533121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533168 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_7533168 : Nat := 118140960795 + 7533168 * 2 ^ 59
def prefixEnd_7533168 : Nat := 4983230072969 + 3 ^ 40 * 7533168 * 2
def baseEnd_7533168 : Nat := 3868136035069087679255597

theorem tailTrace_7533168 : CollatzResearch.WordTrace tailWord_7533168 prefixEnd_7533168 3868136035069087679255597 := by
  unfold tailWord_7533168
  simp only [CollatzResearch.WordTrace]
  refine ⟨137378604586313186755512079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183171472781750915674016105 137378604586313186755512079)
  ·
    refine ⟨206067906879469780133268119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137378604586313186755512079 206067906879469780133268119)
    ·
      refine ⟨309101860319204670199902179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206067906879469780133268119 309101860319204670199902179)
      ·
        refine ⟨463652790478807005299853269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309101860319204670199902179 463652790478807005299853269)
        ·
          refine ⟨10866862276847039186715311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 463652790478807005299853269 10866862276847039186715311)
          ·
            refine ⟨16300293415270558780072967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866862276847039186715311 16300293415270558780072967)
            ·
              refine ⟨24450440122905838170109451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300293415270558780072967 24450440122905838170109451)
              ·
                refine ⟨36675660184358757255164177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24450440122905838170109451 36675660184358757255164177)
                ·
                  refine ⟨27506745138269067941373133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36675660184358757255164177 27506745138269067941373133)
                  ·
                    refine ⟨10315029426850900478014925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27506745138269067941373133 10315029426850900478014925)
                    ·
                      refine ⟨3868136035069087679255597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315029426850900478014925 3868136035069087679255597)
                      ·
                        rfl

theorem cell23_7533168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_7533168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533168 prefixEnd_7533168 := by exact prefixLift 7533168
  have htrace : WordTrace (prefixWord ++ tailWord_7533168) baseStart_7533168 baseEnd_7533168 := by
    simpa [prefixWord, tailWord_7533168, baseEnd_7533168] using wordTrace_append hprefix tailTrace_7533168
  have hstable : (prefixWord ++ tailWord_7533168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533168).length < 2 ^ (prefixWord ++ tailWord_7533168).sum := by decide
  have hdescent : baseEnd_7533168 < baseStart_7533168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533188 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7533188 : Nat := 118140960795 + 7533188 * 2 ^ 59
def prefixEnd_7533188 : Nat := 4983230072969 + 3 ^ 40 * 7533188 * 2
def baseEnd_7533188 : Nat := 1289382101560725867001835

theorem tailTrace_7533188 : CollatzResearch.WordTrace tailWord_7533188 prefixEnd_7533188 1289382101560725867001835 := by
  unfold tailWord_7533188
  simp only [CollatzResearch.WordTrace]
  refine ⟨137378969316276958463376109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183171959088369277951168145 137378969316276958463376109)
  ·
    refine ⟨51517113493603859423766041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137378969316276958463376109 51517113493603859423766041)
    ·
      refine ⟨38637835120202894567824531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51517113493603859423766041 38637835120202894567824531)
      ·
        refine ⟨57956752680304341851736797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38637835120202894567824531 57956752680304341851736797)
        ·
          refine ⟨21733782255114128194401299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57956752680304341851736797 21733782255114128194401299)
          ·
            refine ⟨32600673382671192291601949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21733782255114128194401299 32600673382671192291601949)
            ·
              refine ⟨12225252518501697109350731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32600673382671192291601949 12225252518501697109350731)
              ·
                refine ⟨18337878777752545664026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225252518501697109350731 18337878777752545664026097)
                ·
                  refine ⟨13753409083314409248019573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18337878777752545664026097 13753409083314409248019573)
                  ·
                    refine ⟨1289382101560725867001835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13753409083314409248019573 1289382101560725867001835)
                    ·
                      rfl

theorem cell23_7533188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7533188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533188 prefixEnd_7533188 := by exact prefixLift 7533188
  have htrace : WordTrace (prefixWord ++ tailWord_7533188) baseStart_7533188 baseEnd_7533188 := by
    simpa [prefixWord, tailWord_7533188, baseEnd_7533188] using wordTrace_append hprefix tailTrace_7533188
  have hstable : (prefixWord ++ tailWord_7533188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533188).length < 2 ^ (prefixWord ++ tailWord_7533188).sum := by decide
  have hdescent : baseEnd_7533188 < baseStart_7533188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533191 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_7533191 : Nat := 118140960795 + 7533191 * 2 ^ 59
def prefixEnd_7533191 : Nat := 4983230072969 + 3 ^ 40 * 7533191 * 2
def baseEnd_7533191 : Nat := 3868147845124141089267991

theorem tailTrace_7533191 : CollatzResearch.WordTrace tailWord_7533191 prefixEnd_7533191 3868147845124141089267991 := by
  unfold tailWord_7533191
  simp only [CollatzResearch.WordTrace]
  refine ⟨274758048051543048439111427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183172032034362032292740951 274758048051543048439111427)
  ·
    refine ⟨412137072077314572658667141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274758048051543048439111427 412137072077314572658667141)
    ·
      refine ⟨77275701014496482373500089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412137072077314572658667141 77275701014496482373500089)
      ·
        refine ⟨57956775760872361780125067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77275701014496482373500089 57956775760872361780125067)
        ·
          refine ⟨86935163641308542670187601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57956775760872361780125067 86935163641308542670187601)
          ·
            refine ⟨65201372730981407002640701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86935163641308542670187601 65201372730981407002640701)
            ·
              refine ⟨24450514774118027625990263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65201372730981407002640701 24450514774118027625990263)
              ·
                refine ⟨36675772161177041438985395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24450514774118027625990263 36675772161177041438985395)
                ·
                  refine ⟨55013658241765562158478093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36675772161177041438985395 55013658241765562158478093)
                  ·
                    refine ⟨20630121840662085809429285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55013658241765562158478093 20630121840662085809429285)
                    ·
                      refine ⟨3868147845124141089267991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20630121840662085809429285 3868147845124141089267991)
                      ·
                        rfl

theorem cell23_7533191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_7533191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533191 prefixEnd_7533191 := by exact prefixLift 7533191
  have htrace : WordTrace (prefixWord ++ tailWord_7533191) baseStart_7533191 baseEnd_7533191 := by
    simpa [prefixWord, tailWord_7533191, baseEnd_7533191] using wordTrace_append hprefix tailTrace_7533191
  have hstable : (prefixWord ++ tailWord_7533191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533191).length < 2 ^ (prefixWord ++ tailWord_7533191).sum := by decide
  have hdescent : baseEnd_7533191 < baseStart_7533191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533208 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7533208 : Nat := 118140960795 + 7533208 * 2 ^ 59
def prefixEnd_7533208 : Nat := 4983230072969 + 3 ^ 40 * 7533208 * 2
def baseEnd_7533208 : Nat := 3868156574295267522755413

theorem tailTrace_7533208 : CollatzResearch.WordTrace tailWord_7533208 prefixEnd_7533208 3868156574295267522755413 := by
  unfold tailWord_7533208
  simp only [CollatzResearch.WordTrace]
  refine ⟨137379334046240730171240139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183172445394987640228320185 137379334046240730171240139)
  ·
    refine ⟨206069001069361095256860209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137379334046240730171240139 206069001069361095256860209)
    ·
      refine ⟨154551750802020821442645157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206069001069361095256860209 154551750802020821442645157)
      ·
        refine ⟨28978453275378904020495967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154551750802020821442645157 28978453275378904020495967)
        ·
          refine ⟨43467679913068356030743951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28978453275378904020495967 43467679913068356030743951)
          ·
            refine ⟨65201519869602534046115927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43467679913068356030743951 65201519869602534046115927)
            ·
              refine ⟨97802279804403801069173891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65201519869602534046115927 97802279804403801069173891)
              ·
                refine ⟨146703419706605701603760837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97802279804403801069173891 146703419706605701603760837)
                ·
                  refine ⟨27506891194988569050705157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146703419706605701603760837 27506891194988569050705157)
                  ·
                    refine ⟨5157542099060356697007217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27506891194988569050705157 5157542099060356697007217)
                    ·
                      refine ⟨3868156574295267522755413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157542099060356697007217 3868156574295267522755413)
                      ·
                        rfl

theorem cell23_7533208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7533208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533208 prefixEnd_7533208 := by exact prefixLift 7533208
  have htrace : WordTrace (prefixWord ++ tailWord_7533208) baseStart_7533208 baseEnd_7533208 := by
    simpa [prefixWord, tailWord_7533208, baseEnd_7533208] using wordTrace_append hprefix tailTrace_7533208
  have hstable : (prefixWord ++ tailWord_7533208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533208).length < 2 ^ (prefixWord ++ tailWord_7533208).sum := by decide
  have hdescent : baseEnd_7533208 < baseStart_7533208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533211 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3]
def baseStart_7533211 : Nat := 118140960795 + 7533211 * 2 ^ 59
def prefixEnd_7533211 : Nat := 4983230072969 + 3 ^ 40 * 7533211 * 2
def baseEnd_7533211 : Nat := 3868158114737231011017899

theorem tailTrace_7533211 : CollatzResearch.WordTrace tailWord_7533211 prefixEnd_7533211 3868158114737231011017899 := by
  unfold tailWord_7533211
  simp only [CollatzResearch.WordTrace]
  refine ⟨274758777511470591854839487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183172518340980394569892991 274758777511470591854839487)
  ·
    refine ⟨412138166267205887782259231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274758777511470591854839487 412138166267205887782259231)
    ·
      refine ⟨618207249400808831673388847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412138166267205887782259231 618207249400808831673388847)
      ·
        refine ⟨927310874101213247510083271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618207249400808831673388847 927310874101213247510083271)
        ·
          refine ⟨1390966311151819871265124907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927310874101213247510083271 1390966311151819871265124907)
          ·
            refine ⟨2086449466727729806897687361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390966311151819871265124907 2086449466727729806897687361)
            ·
              refine ⟨1564837100045797355173265521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086449466727729806897687361 1564837100045797355173265521)
              ·
                refine ⟨1173627825034348016379949141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564837100045797355173265521 1173627825034348016379949141)
                ·
                  refine ⟨13753451074621265816952529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1173627825034348016379949141 13753451074621265816952529)
                  ·
                    refine ⟨10315088305965949362714397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13753451074621265816952529 10315088305965949362714397)
                    ·
                      refine ⟨3868158114737231011017899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315088305965949362714397 3868158114737231011017899)
                      ·
                        rfl

theorem cell23_7533211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].length) (baseStart_7533211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533211 prefixEnd_7533211 := by exact prefixLift 7533211
  have htrace : WordTrace (prefixWord ++ tailWord_7533211) baseStart_7533211 baseEnd_7533211 := by
    simpa [prefixWord, tailWord_7533211, baseEnd_7533211] using wordTrace_append hprefix tailTrace_7533211
  have hstable : (prefixWord ++ tailWord_7533211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533211).length < 2 ^ (prefixWord ++ tailWord_7533211).sum := by decide
  have hdescent : baseEnd_7533211 < baseStart_7533211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533241 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7533241 : Nat := 118140960795 + 7533241 * 2 ^ 59
def prefixEnd_7533241 : Nat := 4983230072969 + 3 ^ 40 * 7533241 * 2
def baseEnd_7533241 : Nat := 3868173519156865893642761

theorem tailTrace_7533241 : CollatzResearch.WordTrace tailWord_7533241 prefixEnd_7533241 3868173519156865893642761 := by
  unfold tailWord_7533241
  simp only [CollatzResearch.WordTrace]
  refine ⟨274759871701361906978431577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183173247800907937985621051 274759871701361906978431577)
  ·
    refine ⟨206069903776021430233823683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274759871701361906978431577 206069903776021430233823683)
    ·
      refine ⟨309104855664032145350735525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206069903776021430233823683 309104855664032145350735525)
      ·
        refine ⟨57957160437006027253262911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309104855664032145350735525 57957160437006027253262911)
        ·
          refine ⟨86935740655509040879894367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57957160437006027253262911 86935740655509040879894367)
          ·
            refine ⟨130403610983263561319841551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86935740655509040879894367 130403610983263561319841551)
            ·
              refine ⟨195605416474895341979762327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130403610983263561319841551 195605416474895341979762327)
              ·
                refine ⟨293408124712343012969643491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195605416474895341979762327 293408124712343012969643491)
                ·
                  refine ⟨440112187068514519454465237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293408124712343012969643491 440112187068514519454465237)
                  ·
                    refine ⟨10315129384418309049714029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 440112187068514519454465237 10315129384418309049714029)
                    ·
                      refine ⟨3868173519156865893642761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315129384418309049714029 3868173519156865893642761)
                      ·
                        rfl

theorem cell23_7533241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7533241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533241 prefixEnd_7533241 := by exact prefixLift 7533241
  have htrace : WordTrace (prefixWord ++ tailWord_7533241) baseStart_7533241 baseEnd_7533241 := by
    simpa [prefixWord, tailWord_7533241, baseEnd_7533241] using wordTrace_append hprefix tailTrace_7533241
  have hstable : (prefixWord ++ tailWord_7533241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533241).length < 2 ^ (prefixWord ++ tailWord_7533241).sum := by decide
  have hdescent : baseEnd_7533241 < baseStart_7533241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533252 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7533252 : Nat := 118140960795 + 7533252 * 2 ^ 59
def prefixEnd_7533252 : Nat := 4983230072969 + 3 ^ 40 * 7533252 * 2
def baseEnd_7533252 : Nat := 1289393055814688450201737

theorem tailTrace_7533252 : CollatzResearch.WordTrace tailWord_7533252 prefixEnd_7533252 1289393055814688450201737 := by
  unfold tailWord_7533252
  simp only [CollatzResearch.WordTrace]
  refine ⟨137380136452161027928541005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183173515269548037238054673 137380136452161027928541005)
  ·
    refine ⟨51517551169560385473202877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137380136452161027928541005 51517551169560385473202877)
    ·
      refine ⟨19319081688585144552451079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51517551169560385473202877 19319081688585144552451079)
      ·
        refine ⟨28978622532877716828676619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19319081688585144552451079 28978622532877716828676619)
        ·
          refine ⟨43467933799316575243014929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28978622532877716828676619 43467933799316575243014929)
          ·
            refine ⟨32600950349487431432261197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43467933799316575243014929 32600950349487431432261197)
            ·
              refine ⟨12225356381057786787097949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32600950349487431432261197 12225356381057786787097949)
              ·
                refine ⟨4584508642896670045161731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12225356381057786787097949 4584508642896670045161731)
                ·
                  refine ⟨6876762964345005067742597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584508642896670045161731 6876762964345005067742597)
                  ·
                    refine ⟨1289393055814688450201737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876762964345005067742597 1289393055814688450201737)
                    ·
                      rfl

theorem cell23_7533252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7533252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533252 prefixEnd_7533252 := by exact prefixLift 7533252
  have htrace : WordTrace (prefixWord ++ tailWord_7533252) baseStart_7533252 baseEnd_7533252 := by
    simpa [prefixWord, tailWord_7533252, baseEnd_7533252] using wordTrace_append hprefix tailTrace_7533252
  have hstable : (prefixWord ++ tailWord_7533252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533252).length < 2 ^ (prefixWord ++ tailWord_7533252).sum := by decide
  have hdescent : baseEnd_7533252 < baseStart_7533252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533269 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7533269 : Nat := 118140960795 + 7533269 * 2 ^ 59
def prefixEnd_7533269 : Nat := 4983230072969 + 3 ^ 40 * 7533269 * 2
def baseEnd_7533269 : Nat := 1289395965538397261364211

theorem tailTrace_7533269 : CollatzResearch.WordTrace tailWord_7533269 prefixEnd_7533269 1289395965538397261364211 := by
  unfold tailWord_7533269
  simp only [CollatzResearch.WordTrace]
  refine ⟨274760892945260467760450861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183173928630173645173633907 274760892945260467760450861)
  ·
    refine ⟨103035334854472675410169073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274760892945260467760450861 103035334854472675410169073)
    ·
      refine ⟨77276501140854506557626805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103035334854472675410169073 77276501140854506557626805)
      ·
        refine ⟨7244671981955109989777513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77276501140854506557626805 7244671981955109989777513)
        ·
          refine ⟨5433503986466332492333135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244671981955109989777513 5433503986466332492333135)
          ·
            refine ⟨8150255979699498738499703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433503986466332492333135 8150255979699498738499703)
            ·
              refine ⟨12225383969549248107749555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150255979699498738499703 12225383969549248107749555)
              ·
                refine ⟨18338075954323872161624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225383969549248107749555 18338075954323872161624333)
                ·
                  refine ⟨6876778482871452060609125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18338075954323872161624333 6876778482871452060609125)
                  ·
                    refine ⟨1289395965538397261364211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876778482871452060609125 1289395965538397261364211)
                    ·
                      rfl

theorem cell23_7533269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7533269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533269 prefixEnd_7533269 := by exact prefixLift 7533269
  have htrace : WordTrace (prefixWord ++ tailWord_7533269) baseStart_7533269 baseEnd_7533269 := by
    simpa [prefixWord, tailWord_7533269, baseEnd_7533269] using wordTrace_append hprefix tailTrace_7533269
  have hstable : (prefixWord ++ tailWord_7533269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533269).length < 2 ^ (prefixWord ++ tailWord_7533269).sum := by decide
  have hdescent : baseEnd_7533269 < baseStart_7533269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533291 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 6]
def baseStart_7533291 : Nat := 118140960795 + 7533291 * 2 ^ 59
def prefixEnd_7533291 : Nat := 4983230072969 + 3 ^ 40 * 7533291 * 2
def baseEnd_7533291 : Nat := 1289399731063196899339177

theorem tailTrace_7533291 : CollatzResearch.WordTrace tailWord_7533291 prefixEnd_7533291 1289399731063196899339177 := by
  unfold tailWord_7533291
  simp only [CollatzResearch.WordTrace]
  refine ⟨274761695351180765517751727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183174463567453843678501151 274761695351180765517751727)
  ·
    refine ⟨412142543026771148276627591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274761695351180765517751727 412142543026771148276627591)
    ·
      refine ⟨618213814540156722414941387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412142543026771148276627591 618213814540156722414941387)
      ·
        refine ⟨927320721810235083622412081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618213814540156722414941387 927320721810235083622412081)
        ·
          refine ⟨695490541357676312716809061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927320721810235083622412081 695490541357676312716809061)
          ·
            refine ⟨130404476504564308634401699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695490541357676312716809061 130404476504564308634401699)
            ·
              refine ⟨195606714756846462951602549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130404476504564308634401699 195606714756846462951602549)
              ·
                refine ⟨18338129508454355901712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195606714756846462951602549 18338129508454355901712739)
                ·
                  refine ⟨27507194262681533852569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18338129508454355901712739 27507194262681533852569109)
                  ·
                    refine ⟨1289399731063196899339177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27507194262681533852569109 1289399731063196899339177)
                    ·
                      rfl

theorem cell23_7533291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_7533291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533291 prefixEnd_7533291 := by exact prefixLift 7533291
  have htrace : WordTrace (prefixWord ++ tailWord_7533291) baseStart_7533291 baseEnd_7533291 := by
    simpa [prefixWord, tailWord_7533291, baseEnd_7533291] using wordTrace_append hprefix tailTrace_7533291
  have hstable : (prefixWord ++ tailWord_7533291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533291).length < 2 ^ (prefixWord ++ tailWord_7533291).sum := by decide
  have hdescent : baseEnd_7533291 < baseStart_7533291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533295 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 1, 5]
def baseStart_7533295 : Nat := 118140960795 + 7533295 * 2 ^ 59
def prefixEnd_7533295 : Nat := 4983230072969 + 3 ^ 40 * 7533295 * 2
def baseEnd_7533295 : Nat := 1289400415704069560789171

theorem tailTrace_7533295 : CollatzResearch.WordTrace tailWord_7533295 prefixEnd_7533295 1289400415704069560789171 := by
  unfold tailWord_7533295
  simp only [CollatzResearch.WordTrace]
  refine ⟨274761841243166274200897339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183174560828777516133931559 274761841243166274200897339)
  ·
    refine ⟨412142761864749411301346009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274761841243166274200897339 412142761864749411301346009)
    ·
      refine ⟨309107071398562058476009507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412142761864749411301346009 309107071398562058476009507)
      ·
        refine ⟨463660607097843087714014261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309107071398562058476009507 463660607097843087714014261)
        ·
          refine ⟨43468181915422789473188837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 463660607097843087714014261 43468181915422789473188837)
          ·
            refine ⟨8150284109141773026222907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43468181915422789473188837 8150284109141773026222907)
            ·
              refine ⟨12225426163712659539334361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150284109141773026222907 12225426163712659539334361)
              ·
                refine ⟨9169069622784494654500771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12225426163712659539334361 9169069622784494654500771)
                ·
                  refine ⟨13753604434176741981751157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169069622784494654500771 13753604434176741981751157)
                  ·
                    refine ⟨1289400415704069560789171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13753604434176741981751157 1289400415704069560789171)
                    ·
                      rfl

theorem cell23_7533295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_7533295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533295 prefixEnd_7533295 := by exact prefixLift 7533295
  have htrace : WordTrace (prefixWord ++ tailWord_7533295) baseStart_7533295 baseEnd_7533295 := by
    simpa [prefixWord, tailWord_7533295, baseEnd_7533295] using wordTrace_append hprefix tailTrace_7533295
  have hstable : (prefixWord ++ tailWord_7533295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533295).length < 2 ^ (prefixWord ++ tailWord_7533295).sum := by decide
  have hdescent : baseEnd_7533295 < baseStart_7533295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533302 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7533302 : Nat := 118140960795 + 7533302 * 2 ^ 59
def prefixEnd_7533302 : Nat := 4983230072969 + 3 ^ 40 * 7533302 * 2
def baseEnd_7533302 : Nat := 3868204841476790154979981

theorem tailTrace_7533302 : CollatzResearch.WordTrace tailWord_7533302 prefixEnd_7533302 3868204841476790154979981 := by
  unfold tailWord_7533302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172631034633807149775135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183174731036093942930934773 17172631034633807149775135)
  ·
    refine ⟨25758946551950710724662703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17172631034633807149775135 25758946551950710724662703)
    ·
      refine ⟨38638419827926066086994055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25758946551950710724662703 38638419827926066086994055)
      ·
        refine ⟨57957629741889099130491083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38638419827926066086994055 57957629741889099130491083)
        ·
          refine ⟨86936444612833648695736625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57957629741889099130491083 86936444612833648695736625)
          ·
            refine ⟨65202333459625236521802469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86936444612833648695736625 65202333459625236521802469)
            ·
              refine ⟨12225437523679731847837963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65202333459625236521802469 12225437523679731847837963)
              ·
                refine ⟨18338156285519597771756945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225437523679731847837963 18338156285519597771756945)
                ·
                  refine ⟨13753617214139698328817709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18338156285519597771756945 13753617214139698328817709)
                  ·
                    refine ⟨5157606455302386873306641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13753617214139698328817709 5157606455302386873306641)
                    ·
                      refine ⟨3868204841476790154979981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5157606455302386873306641 3868204841476790154979981)
                      ·
                        rfl

theorem cell23_7533302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7533302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533302 prefixEnd_7533302 := by exact prefixLift 7533302
  have htrace : WordTrace (prefixWord ++ tailWord_7533302) baseStart_7533302 baseEnd_7533302 := by
    simpa [prefixWord, tailWord_7533302, baseEnd_7533302] using wordTrace_append hprefix tailTrace_7533302
  have hstable : (prefixWord ++ tailWord_7533302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533302).length < 2 ^ (prefixWord ++ tailWord_7533302).sum := by decide
  have hdescent : baseEnd_7533302 < baseStart_7533302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533308 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_7533308 : Nat := 118140960795 + 7533308 * 2 ^ 59
def prefixEnd_7533308 : Nat := 4983230072969 + 3 ^ 40 * 7533308 * 2
def baseEnd_7533308 : Nat := 1289402640786905710501651

theorem tailTrace_7533308 : CollatzResearch.WordTrace tailWord_7533308 prefixEnd_7533308 1289402640786905710501651 := by
  unfold tailWord_7533308
  simp only [CollatzResearch.WordTrace]
  refine ⟨137381157696059588710560289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183174876928079451614080385 137381157696059588710560289)
  ·
    refine ⟨103035868272044691532920217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137381157696059588710560289 103035868272044691532920217)
    ·
      refine ⟨77276901204033518649690163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103035868272044691532920217 77276901204033518649690163)
      ·
        refine ⟨115915351806050277974535245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77276901204033518649690163 115915351806050277974535245)
        ·
          refine ⟨43468256927268854240450717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115915351806050277974535245 43468256927268854240450717)
          ·
            refine ⟨16300596347725820340169019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43468256927268854240450717 16300596347725820340169019)
            ·
              refine ⟨24450894521588730510253529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300596347725820340169019 24450894521588730510253529)
              ·
                refine ⟨18338170891191547882690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24450894521588730510253529 18338170891191547882690147)
                ·
                  refine ⟨27507256336787321824035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18338170891191547882690147 27507256336787321824035221)
                  ·
                    refine ⟨1289402640786905710501651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27507256336787321824035221 1289402640786905710501651)
                    ·
                      rfl

theorem cell23_7533308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_7533308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533308 prefixEnd_7533308 := by exact prefixLift 7533308
  have htrace : WordTrace (prefixWord ++ tailWord_7533308) baseStart_7533308 baseEnd_7533308 := by
    simpa [prefixWord, tailWord_7533308, baseEnd_7533308] using wordTrace_append hprefix tailTrace_7533308
  have hstable : (prefixWord ++ tailWord_7533308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533308).length < 2 ^ (prefixWord ++ tailWord_7533308).sum := by decide
  have hdescent : baseEnd_7533308 < baseStart_7533308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533365 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7533365 : Nat := 118140960795 + 7533365 * 2 ^ 59
def prefixEnd_7533365 : Nat := 4983230072969 + 3 ^ 40 * 7533365 * 2
def baseEnd_7533365 : Nat := 3868237190758023408492191

theorem tailTrace_7533365 : CollatzResearch.WordTrace tailWord_7533365 prefixEnd_7533365 3868237190758023408492191 := by
  unfold tailWord_7533365
  simp only [CollatzResearch.WordTrace]
  refine ⟨274764394352912676155945549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183176262901941784103963699 274764394352912676155945549)
  ·
    refine ⟨103036647882342253558479581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274764394352912676155945549 103036647882342253558479581)
    ·
      refine ⟨38638742955878345084429843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103036647882342253558479581 38638742955878345084429843)
      ·
        refine ⟨57958114433817517626644765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38638742955878345084429843 57958114433817517626644765)
        ·
          refine ⟨21734292912681569109991787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57958114433817517626644765 21734292912681569109991787)
          ·
            refine ⟨32601439369022353664987681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734292912681569109991787 32601439369022353664987681)
            ·
              refine ⟨24451079526766765248740761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32601439369022353664987681 24451079526766765248740761)
              ·
                refine ⟨18338309645075073936555571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24451079526766765248740761 18338309645075073936555571)
                ·
                  refine ⟨27507464467612610904833357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18338309645075073936555571 27507464467612610904833357)
                  ·
                    refine ⟨10315299175354729089312509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27507464467612610904833357 10315299175354729089312509)
                    ·
                      refine ⟨3868237190758023408492191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315299175354729089312509 3868237190758023408492191)
                      ·
                        rfl

theorem cell23_7533365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7533365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533365 prefixEnd_7533365 := by exact prefixLift 7533365
  have htrace : WordTrace (prefixWord ++ tailWord_7533365) baseStart_7533365 baseEnd_7533365 := by
    simpa [prefixWord, tailWord_7533365, baseEnd_7533365] using wordTrace_append hprefix tailTrace_7533365
  have hstable : (prefixWord ++ tailWord_7533365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533365).length < 2 ^ (prefixWord ++ tailWord_7533365).sum := by decide
  have hdescent : baseEnd_7533365 < baseStart_7533365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533366 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7533366 : Nat := 118140960795 + 7533366 * 2 ^ 59
def prefixEnd_7533366 : Nat := 4983230072969 + 3 ^ 40 * 7533366 * 2
def baseEnd_7533366 : Nat := 3868237704238677904579687

theorem tailTrace_7533366 : CollatzResearch.WordTrace tailWord_7533366 prefixEnd_7533366 3868237704238677904579687 := by
  unfold tailWord_7533366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172776926619315832920747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183176287217272702217821301 17172776926619315832920747)
  ·
    refine ⟨25759165389928973749381121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17172776926619315832920747 25759165389928973749381121)
    ·
      refine ⟨19319374042446730312035841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25759165389928973749381121 19319374042446730312035841)
      ·
        refine ⟨14489530531835047734026881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19319374042446730312035841 14489530531835047734026881)
        ·
          refine ⟨10867147898876285800520161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14489530531835047734026881 10867147898876285800520161)
          ·
            refine ⟨8150360924157214350390121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10867147898876285800520161 8150360924157214350390121)
            ·
              refine ⟨6112770693117910762792591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8150360924157214350390121 6112770693117910762792591)
              ·
                refine ⟨9169156039676866144188887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112770693117910762792591 9169156039676866144188887)
                ·
                  refine ⟨13753734059515299216283331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169156039676866144188887 13753734059515299216283331)
                  ·
                    refine ⟨20630601089272948824424997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13753734059515299216283331 20630601089272948824424997)
                    ·
                      refine ⟨3868237704238677904579687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20630601089272948824424997 3868237704238677904579687)
                      ·
                        rfl

theorem cell23_7533366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7533366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533366 prefixEnd_7533366 := by exact prefixLift 7533366
  have htrace : WordTrace (prefixWord ++ tailWord_7533366) baseStart_7533366 baseEnd_7533366 := by
    simpa [prefixWord, tailWord_7533366, baseEnd_7533366] using wordTrace_append hprefix tailTrace_7533366
  have hstable : (prefixWord ++ tailWord_7533366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533366).length < 2 ^ (prefixWord ++ tailWord_7533366).sum := by decide
  have hdescent : baseEnd_7533366 < baseStart_7533366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533399 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_7533399 : Nat := 118140960795 + 7533399 * 2 ^ 59
def prefixEnd_7533399 : Nat := 4983230072969 + 3 ^ 40 * 7533399 * 2
def baseEnd_7533399 : Nat := 3868254649100276275467035

theorem tailTrace_7533399 : CollatzResearch.WordTrace tailWord_7533399 prefixEnd_7533399 3868254649100276275467035 := by
  unfold tailWord_7533399
  simp only [CollatzResearch.WordTrace]
  refine ⟨274765634434789499962683251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183177089623192999975122167 274765634434789499962683251)
  ·
    refine ⟨412148451652184249944024877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274765634434789499962683251 412148451652184249944024877)
    ·
      refine ⟨154555669369569093729009329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412148451652184249944024877 154555669369569093729009329)
      ·
        refine ⟨115916752027176820296756997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154555669369569093729009329 115916752027176820296756997)
        ·
          refine ⟨21734391005095653805641937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115916752027176820296756997 21734391005095653805641937)
          ·
            refine ⟨16300793253821740354231453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21734391005095653805641937 16300793253821740354231453)
            ·
              refine ⟨6112797470183152632836795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16300793253821740354231453 6112797470183152632836795)
              ·
                refine ⟨9169196205274728949255193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112797470183152632836795 9169196205274728949255193)
                ·
                  refine ⟨6876897153956046711941395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169196205274728949255193 6876897153956046711941395)
                  ·
                    refine ⟨10315345730934070067912093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6876897153956046711941395 10315345730934070067912093)
                    ·
                      refine ⟨3868254649100276275467035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315345730934070067912093 3868254649100276275467035)
                      ·
                        rfl

theorem cell23_7533399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_7533399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533399 prefixEnd_7533399 := by exact prefixLift 7533399
  have htrace : WordTrace (prefixWord ++ tailWord_7533399) baseStart_7533399 baseEnd_7533399 := by
    simpa [prefixWord, tailWord_7533399, baseEnd_7533399] using wordTrace_append hprefix tailTrace_7533399
  have hstable : (prefixWord ++ tailWord_7533399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533399).length < 2 ^ (prefixWord ++ tailWord_7533399).sum := by decide
  have hdescent : baseEnd_7533399 < baseStart_7533399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533408 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_7533408 : Nat := 118140960795 + 7533408 * 2 ^ 59
def prefixEnd_7533408 : Nat := 4983230072969 + 3 ^ 40 * 7533408 * 2
def baseEnd_7533408 : Nat := 3868259270426166740254493

theorem tailTrace_7533408 : CollatzResearch.WordTrace tailWord_7533408 prefixEnd_7533408 3868259270426166740254493 := by
  unfold tailWord_7533408
  simp only [CollatzResearch.WordTrace]
  refine ⟨137382981345878447249880439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183177308461171262999840585 137382981345878447249880439)
  ·
    refine ⟨206074472018817670874820659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137382981345878447249880439 206074472018817670874820659)
    ·
      refine ⟨309111708028226506312230989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206074472018817670874820659 309111708028226506312230989)
      ·
        refine ⟨115916890510584939867086621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309111708028226506312230989 115916890510584939867086621)
        ·
          refine ⟨43468833941469352450157483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115916890510584939867086621 43468833941469352450157483)
          ·
            refine ⟨65203250912204028675236225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43468833941469352450157483 65203250912204028675236225)
            ·
              refine ⟨48902438184153021506427169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65203250912204028675236225 48902438184153021506427169)
              ·
                refine ⟨36676828638114766129820377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48902438184153021506427169 36676828638114766129820377)
                ·
                  refine ⟨27507621478586074597365283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36676828638114766129820377 27507621478586074597365283)
                  ·
                    refine ⟨41261432217879111896047925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27507621478586074597365283 41261432217879111896047925)
                    ·
                      refine ⟨3868259270426166740254493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41261432217879111896047925 3868259270426166740254493)
                      ·
                        rfl

theorem cell23_7533408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_7533408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533408 prefixEnd_7533408 := by exact prefixLift 7533408
  have htrace : WordTrace (prefixWord ++ tailWord_7533408) baseStart_7533408 baseEnd_7533408 := by
    simpa [prefixWord, tailWord_7533408, baseEnd_7533408] using wordTrace_append hprefix tailTrace_7533408
  have hstable : (prefixWord ++ tailWord_7533408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533408).length < 2 ^ (prefixWord ++ tailWord_7533408).sum := by decide
  have hdescent : baseEnd_7533408 < baseStart_7533408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533445 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 7]
def baseStart_7533445 : Nat := 118140960795 + 7533445 * 2 ^ 59
def prefixEnd_7533445 : Nat := 4983230072969 + 3 ^ 40 * 7533445 * 2
def baseEnd_7533445 : Nat := 429808696578931455054647

theorem tailTrace_7533445 : CollatzResearch.WordTrace tailWord_7533445 prefixEnd_7533445 429808696578931455054647 := by
  unfold tailWord_7533445
  simp only [CollatzResearch.WordTrace]
  refine ⟨274767312192622849818857789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183178208128415233212571859 274767312192622849818857789)
  ·
    refine ⟨103037742072233568682071671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274767312192622849818857789 103037742072233568682071671)
    ·
      refine ⟨154556613108350353023107507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103037742072233568682071671 154556613108350353023107507)
      ·
        refine ⟨231834919662525529534661261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154556613108350353023107507 231834919662525529534661261)
        ·
          refine ⟨86938094873447073575497973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231834919662525529534661261 86938094873447073575497973)
          ·
            refine ⟨8150446394385663147702935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86938094873447073575497973 8150446394385663147702935)
            ·
              refine ⟨12225669591578494721554403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150446394385663147702935 12225669591578494721554403)
              ·
                refine ⟨18338504387367742082331605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225669591578494721554403 18338504387367742082331605)
                ·
                  refine ⟨429808696578931455054647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18338504387367742082331605 429808696578931455054647)
                  ·
                    rfl

theorem cell23_7533445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_7533445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533445 prefixEnd_7533445 := by exact prefixLift 7533445
  have htrace : WordTrace (prefixWord ++ tailWord_7533445) baseStart_7533445 baseEnd_7533445 := by
    simpa [prefixWord, tailWord_7533445, baseEnd_7533445] using wordTrace_append hprefix tailTrace_7533445
  have hstable : (prefixWord ++ tailWord_7533445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533445).length < 2 ^ (prefixWord ++ tailWord_7533445).sum := by decide
  have hdescent : baseEnd_7533445 < baseStart_7533445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533495 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_7533495 : Nat := 118140960795 + 7533495 * 2 ^ 59
def prefixEnd_7533495 : Nat := 4983230072969 + 3 ^ 40 * 7533495 * 2
def baseEnd_7533495 : Nat := 3868303943243107899866593

theorem tailTrace_7533495 : CollatzResearch.WordTrace tailWord_7533495 prefixEnd_7533495 3868303943243107899866593 := by
  unfold tailWord_7533495
  simp only [CollatzResearch.WordTrace]
  refine ⟨274769135842441708358177939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183179423894961138905451959 274769135842441708358177939)
  ·
    refine ⟨412153703763662562537266909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274769135842441708358177939 412153703763662562537266909)
    ·
      refine ⟨154557638911373460951475091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412153703763662562537266909 154557638911373460951475091)
      ·
        refine ⟨231836458367060191427212637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154557638911373460951475091 231836458367060191427212637)
        ·
          refine ⟨86938671887647571785204739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231836458367060191427212637 86938671887647571785204739)
          ·
            refine ⟨130408007831471357677807109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86938671887647571785204739 130408007831471357677807109)
            ·
              refine ⟨24451501468400879564588833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130408007831471357677807109 24451501468400879564588833)
              ·
                refine ⟨18338626101300659673441625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24451501468400879564588833 18338626101300659673441625)
                ·
                  refine ⟨13753969575975494755081219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18338626101300659673441625 13753969575975494755081219)
                  ·
                    refine ⟨20630954363963242132621829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13753969575975494755081219 20630954363963242132621829)
                    ·
                      refine ⟨3868303943243107899866593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20630954363963242132621829 3868303943243107899866593)
                      ·
                        rfl

theorem cell23_7533495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_7533495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533495 prefixEnd_7533495 := by exact prefixLift 7533495
  have htrace : WordTrace (prefixWord ++ tailWord_7533495) baseStart_7533495 baseEnd_7533495 := by
    simpa [prefixWord, tailWord_7533495, baseEnd_7533495] using wordTrace_append hprefix tailTrace_7533495
  have hstable : (prefixWord ++ tailWord_7533495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533495).length < 2 ^ (prefixWord ++ tailWord_7533495).sum := by decide
  have hdescent : baseEnd_7533495 < baseStart_7533495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533498 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_7533498 : Nat := 118140960795 + 7533498 * 2 ^ 59
def prefixEnd_7533498 : Nat := 4983230072969 + 3 ^ 40 * 7533498 * 2
def baseEnd_7533498 : Nat := 3868305483685071388129079

theorem tailTrace_7533498 : CollatzResearch.WordTrace tailWord_7533498 prefixEnd_7533498 3868305483685071388129079 := by
  unfold tailWord_7533498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68692311315357709967634287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183179496840953893247024765 68692311315357709967634287)
  ·
    refine ⟨103038466973036564951451431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68692311315357709967634287 103038466973036564951451431)
    ·
      refine ⟨154557700459554847427177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103038466973036564951451431 154557700459554847427177147)
      ·
        refine ⟨231836550689332271140765721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154557700459554847427177147 231836550689332271140765721)
        ·
          refine ⟨173877413016999203355574291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231836550689332271140765721 173877413016999203355574291)
          ·
            refine ⟨260816119525498805033361437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173877413016999203355574291 260816119525498805033361437)
            ·
              refine ⟨97806044822062051887510539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260816119525498805033361437 97806044822062051887510539)
              ·
                refine ⟨146709067233093077831265809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97806044822062051887510539 146709067233093077831265809)
                ·
                  refine ⟨110031800424819808373449357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146709067233093077831265809 110031800424819808373449357)
                  ·
                    refine ⟨41261925159307428140043509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110031800424819808373449357 41261925159307428140043509)
                    ·
                      refine ⟨3868305483685071388129079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41261925159307428140043509 3868305483685071388129079)
                      ·
                        rfl

theorem cell23_7533498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_7533498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533498 prefixEnd_7533498 := by exact prefixLift 7533498
  have htrace : WordTrace (prefixWord ++ tailWord_7533498) baseStart_7533498 baseEnd_7533498 := by
    simpa [prefixWord, tailWord_7533498, baseEnd_7533498] using wordTrace_append hprefix tailTrace_7533498
  have hstable : (prefixWord ++ tailWord_7533498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533498).length < 2 ^ (prefixWord ++ tailWord_7533498).sum := by decide
  have hdescent : baseEnd_7533498 < baseStart_7533498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533522 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_7533522 : Nat := 118140960795 + 7533522 * 2 ^ 59
def prefixEnd_7533522 : Nat := 4983230072969 + 3 ^ 40 * 7533522 * 2
def baseEnd_7533522 : Nat := 1289439269073593098076323

theorem tailTrace_7533522 : CollatzResearch.WordTrace tailWord_7533522 prefixEnd_7533522 1289439269073593098076323 := by
  unfold tailWord_7533522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68692530153335972992352705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183180080408895927979607213 68692530153335972992352705)
  ·
    refine ⟨51519397615001979744264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68692530153335972992352705 51519397615001979744264529)
    ·
      refine ⟨38639548211251484808198397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51519397615001979744264529 38639548211251484808198397)
      ·
        refine ⟨14489830579219306803074399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38639548211251484808198397 14489830579219306803074399)
        ·
          refine ⟨21734745868828960204611599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14489830579219306803074399 21734745868828960204611599)
          ·
            refine ⟨32602118803243440306917399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734745868828960204611599 32602118803243440306917399)
            ·
              refine ⟨48903178204865160460376099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32602118803243440306917399 48903178204865160460376099)
              ·
                refine ⟨73354767307297740690564149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48903178204865160460376099 73354767307297740690564149)
                ·
                  refine ⟨6877009435059163189740389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73354767307297740690564149 6877009435059163189740389)
                  ·
                    refine ⟨1289439269073593098076323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877009435059163189740389 1289439269073593098076323)
                    ·
                      rfl

theorem cell23_7533522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_7533522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533522 prefixEnd_7533522 := by exact prefixLift 7533522
  have htrace : WordTrace (prefixWord ++ tailWord_7533522) baseStart_7533522 baseEnd_7533522 := by
    simpa [prefixWord, tailWord_7533522, baseEnd_7533522] using wordTrace_append hprefix tailTrace_7533522
  have hstable : (prefixWord ++ tailWord_7533522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533522).length < 2 ^ (prefixWord ++ tailWord_7533522).sum := by decide
  have hdescent : baseEnd_7533522 < baseStart_7533522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533539 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 1, 4]
def baseStart_7533539 : Nat := 118140960795 + 7533539 * 2 ^ 59
def prefixEnd_7533539 : Nat := 4983230072969 + 3 ^ 40 * 7533539 * 2
def baseEnd_7533539 : Nat := 1289442178797301909238797

theorem tailTrace_7533539 : CollatzResearch.WordTrace tailWord_7533539 prefixEnd_7533539 1289442178797301909238797 := by
  unfold tailWord_7533539
  simp only [CollatzResearch.WordTrace]
  refine ⟨274770740654282303872779671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183180493769521535915186447 274770740654282303872779671)
  ·
    refine ⟨412156110981423455809169507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274770740654282303872779671 412156110981423455809169507)
    ·
      refine ⟨618234166472135183713754261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412156110981423455809169507 618234166472135183713754261)
      ·
        refine ⟨28979726553381336736582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 618234166472135183713754261 28979726553381336736582231)
        ·
          refine ⟨43469589830072005104873347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28979726553381336736582231 43469589830072005104873347)
          ·
            refine ⟨65204384745108007657310021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43469589830072005104873347 65204384745108007657310021)
            ·
              refine ⟨12225822139707751435745629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65204384745108007657310021 12225822139707751435745629)
              ·
                refine ⟨4584683302390406788404611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12225822139707751435745629 4584683302390406788404611)
                ·
                  refine ⟨6877024953585610182606917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584683302390406788404611 6877024953585610182606917)
                  ·
                    refine ⟨1289442178797301909238797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877024953585610182606917 1289442178797301909238797)
                    ·
                      rfl

theorem cell23_7533539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 4].length) (baseStart_7533539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533539 prefixEnd_7533539 := by exact prefixLift 7533539
  have htrace : WordTrace (prefixWord ++ tailWord_7533539) baseStart_7533539 baseEnd_7533539 := by
    simpa [prefixWord, tailWord_7533539, baseEnd_7533539] using wordTrace_append hprefix tailTrace_7533539
  have hstable : (prefixWord ++ tailWord_7533539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533539).length < 2 ^ (prefixWord ++ tailWord_7533539).sum := by decide
  have hdescent : baseEnd_7533539 < baseStart_7533539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533582 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_7533582 : Nat := 118140960795 + 7533582 * 2 ^ 59
def prefixEnd_7533582 : Nat := 4983230072969 + 3 ^ 40 * 7533582 * 2
def baseEnd_7533582 : Nat := 1289449538686683019826231

theorem tailTrace_7533582 : CollatzResearch.WordTrace tailWord_7533582 prefixEnd_7533582 1289449538686683019826231 := by
  unfold tailWord_7533582
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346538624140815277074375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183181539328751014811063333 34346538624140815277074375)
  ·
    refine ⟨51519807936211222915611563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34346538624140815277074375 51519807936211222915611563)
    ·
      refine ⟨77279711904316834373417345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51519807936211222915611563 77279711904316834373417345)
      ·
        refine ⟨57959783928237625780063009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77279711904316834373417345 57959783928237625780063009)
        ·
          refine ⟨43469837946178219335047257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57959783928237625780063009 43469837946178219335047257)
          ·
            refine ⟨32602378459633664501285443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43469837946178219335047257 32602378459633664501285443)
            ·
              refine ⟨48903567689450496751928165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32602378459633664501285443 48903567689450496751928165)
              ·
                refine ⟨9169418941771968140986531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48903567689450496751928165 9169418941771968140986531)
                ·
                  refine ⟨13754128412657952211479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169418941771968140986531 13754128412657952211479797)
                  ·
                    refine ⟨1289449538686683019826231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13754128412657952211479797 1289449538686683019826231)
                    ·
                      rfl

theorem cell23_7533582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_7533582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533582 prefixEnd_7533582 := by exact prefixLift 7533582
  have htrace : WordTrace (prefixWord ++ tailWord_7533582) baseStart_7533582 baseEnd_7533582 := by
    simpa [prefixWord, tailWord_7533582, baseEnd_7533582] using wordTrace_append hprefix tailTrace_7533582
  have hstable : (prefixWord ++ tailWord_7533582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533582).length < 2 ^ (prefixWord ++ tailWord_7533582).sum := by decide
  have hdescent : baseEnd_7533582 < baseStart_7533582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533585 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_7533585 : Nat := 118140960795 + 7533585 * 2 ^ 59
def prefixEnd_7533585 : Nat := 4983230072969 + 3 ^ 40 * 7533585 * 2
def baseEnd_7533585 : Nat := 3868350156502012547741179

theorem tailTrace_7533585 : CollatzResearch.WordTrace tailWord_7533585 prefixEnd_7533585 3868350156502012547741179 := by
  unfold tailWord_7533585
  simp only [CollatzResearch.WordTrace]
  refine ⟨274772418412115653728954209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183181612274743769152636139 274772418412115653728954209)
  ·
    refine ⟨206079313809086740296715657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274772418412115653728954209 206079313809086740296715657)
    ·
      refine ⟨154559485356815055222536743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206079313809086740296715657 154559485356815055222536743)
      ·
        refine ⟨231839228035222582833805115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154559485356815055222536743 231839228035222582833805115)
        ·
          refine ⟨347758842052833874250707673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231839228035222582833805115 347758842052833874250707673)
          ·
            refine ⟨260819131539625405688030755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347758842052833874250707673 260819131539625405688030755)
            ·
              refine ⟨391228697309438108532046133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260819131539625405688030755 391228697309438108532046133)
              ·
                refine ⟨36677690372759822674879325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391228697309438108532046133 36677690372759822674879325)
                ·
                  refine ⟨13754133889784933503079747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36677690372759822674879325 13754133889784933503079747)
                  ·
                    refine ⟨20631200834677400254619621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13754133889784933503079747 20631200834677400254619621)
                    ·
                      refine ⟨3868350156502012547741179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20631200834677400254619621 3868350156502012547741179)
                      ·
                        rfl

theorem cell23_7533585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_7533585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533585 prefixEnd_7533585 := by exact prefixLift 7533585
  have htrace : WordTrace (prefixWord ++ tailWord_7533585) baseStart_7533585 baseEnd_7533585 := by
    simpa [prefixWord, tailWord_7533585, baseEnd_7533585] using wordTrace_append hprefix tailTrace_7533585
  have hstable : (prefixWord ++ tailWord_7533585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533585).length < 2 ^ (prefixWord ++ tailWord_7533585).sum := by decide
  have hdescent : baseEnd_7533585 < baseStart_7533585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533612 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_7533612 : Nat := 118140960795 + 7533612 * 2 ^ 59
def prefixEnd_7533612 : Nat := 4983230072969 + 3 ^ 40 * 7533612 * 2
def baseEnd_7533612 : Nat := 1289454673493227980701185

theorem tailTrace_7533612 : CollatzResearch.WordTrace tailWord_7533612 prefixEnd_7533612 1289454673493227980701185 := by
  unfold tailWord_7533612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137386701591508918670093545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183182268788678558226791393 137386701591508918670093545)
  ·
    refine ⟨103040026193631689002570159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137386701591508918670093545 103040026193631689002570159)
    ·
      refine ⟨154560039290447533503855239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103040026193631689002570159 154560039290447533503855239)
      ·
        refine ⟨231840058935671300255782859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154560039290447533503855239 231840058935671300255782859)
        ·
          refine ⟨347760088403506950383674289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231840058935671300255782859 347760088403506950383674289)
          ·
            refine ⟨260820066302630212787755717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347760088403506950383674289 260820066302630212787755717)
            ·
              refine ⟨48903762431743164897704197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260820066302630212787755717 48903762431743164897704197)
              ·
                refine ⟨9169455455951843418319537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48903762431743164897704197 9169455455951843418319537)
                ·
                  refine ⟨6877091591963882563739653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169455455951843418319537 6877091591963882563739653)
                  ·
                    refine ⟨1289454673493227980701185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877091591963882563739653 1289454673493227980701185)
                    ·
                      rfl

theorem cell23_7533612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_7533612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533612 prefixEnd_7533612 := by exact prefixLift 7533612
  have htrace : WordTrace (prefixWord ++ tailWord_7533612) baseStart_7533612 baseEnd_7533612 := by
    simpa [prefixWord, tailWord_7533612, baseEnd_7533612] using wordTrace_append hprefix tailTrace_7533612
  have hstable : (prefixWord ++ tailWord_7533612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533612).length < 2 ^ (prefixWord ++ tailWord_7533612).sum := by decide
  have hdescent : baseEnd_7533612 < baseStart_7533612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533625 : List Nat := [1, 2, 1, 5, 2, 1, 1, 10]
def baseStart_7533625 : Nat := 118140960795 + 7533625 * 2 ^ 59
def prefixEnd_7533625 : Nat := 4983230072969 + 3 ^ 40 * 7533625 * 2
def baseEnd_7533625 : Nat := 143272988730673792268185

theorem tailTrace_7533625 : CollatzResearch.WordTrace tailWord_7533625 prefixEnd_7533625 143272988730673792268185 := by
  unfold tailWord_7533625
  simp only [CollatzResearch.WordTrace]
  refine ⟨274773877331970740560410329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183182584887980493706940219 274773877331970740560410329)
  ·
    refine ⟨206080407998978055420307747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274773877331970740560410329 206080407998978055420307747)
    ·
      refine ⟨309120611998467083130461621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206080407998978055420307747 309120611998467083130461621)
      ·
        refine ⟨28980057374856289043480777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309120611998467083130461621 28980057374856289043480777)
        ·
          refine ⟨21735043031142216782610583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28980057374856289043480777 21735043031142216782610583)
          ·
            refine ⟨32602564546713325173915875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21735043031142216782610583 32602564546713325173915875)
            ·
              refine ⟨48903846820069987760873813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32602564546713325173915875 48903846820069987760873813)
              ·
                refine ⟨143272988730673792268185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48903846820069987760873813 143272988730673792268185)
                ·
                  rfl

theorem cell23_7533625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 10].length) (baseStart_7533625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533625 prefixEnd_7533625 := by exact prefixLift 7533625
  have htrace : WordTrace (prefixWord ++ tailWord_7533625) baseStart_7533625 baseEnd_7533625 := by
    simpa [prefixWord, tailWord_7533625, baseEnd_7533625] using wordTrace_append hprefix tailTrace_7533625
  have hstable : (prefixWord ++ tailWord_7533625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533625).length < 2 ^ (prefixWord ++ tailWord_7533625).sum := by decide
  have hdescent : baseEnd_7533625 < baseStart_7533625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533629 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_7533629 : Nat := 118140960795 + 7533629 * 2 ^ 59
def prefixEnd_7533629 : Nat := 4983230072969 + 3 ^ 40 * 7533629 * 2
def baseEnd_7533629 : Nat := 1289457583216936791863659

theorem tailTrace_7533629 : CollatzResearch.WordTrace tailWord_7533629 prefixEnd_7533629 1289457583216936791863659 := by
  unfold tailWord_7533629
  simp only [CollatzResearch.WordTrace]
  refine ⟨274774023223956249243555941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183182682149304166162370627 274774023223956249243555941)
  ·
    refine ⟨51520129354491796733166739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274774023223956249243555941 51520129354491796733166739)
    ·
      refine ⟨77280194031737695099750109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51520129354491796733166739 77280194031737695099750109)
      ·
        refine ⟨28980072761901635662406291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77280194031737695099750109 28980072761901635662406291)
        ·
          refine ⟨43470109142852453493609437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28980072761901635662406291 43470109142852453493609437)
          ·
            refine ⟨16301290928569670060103539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43470109142852453493609437 16301290928569670060103539)
            ·
              refine ⟨24451936392854505090155309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16301290928569670060103539 24451936392854505090155309)
              ·
                refine ⟨9169476147320439408808241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24451936392854505090155309 9169476147320439408808241)
                ·
                  refine ⟨6877107110490329556606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169476147320439408808241 6877107110490329556606181)
                  ·
                    refine ⟨1289457583216936791863659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877107110490329556606181 1289457583216936791863659)
                    ·
                      rfl

theorem cell23_7533629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_7533629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533629 prefixEnd_7533629 := by exact prefixLift 7533629
  have htrace : WordTrace (prefixWord ++ tailWord_7533629) baseStart_7533629 baseEnd_7533629 := by
    simpa [prefixWord, tailWord_7533629, baseEnd_7533629] using wordTrace_append hprefix tailTrace_7533629
  have hstable : (prefixWord ++ tailWord_7533629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533629).length < 2 ^ (prefixWord ++ tailWord_7533629).sum := by decide
  have hdescent : baseEnd_7533629 < baseStart_7533629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533639 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_7533639 : Nat := 118140960795 + 7533639 * 2 ^ 59
def prefixEnd_7533639 : Nat := 4983230072969 + 3 ^ 40 * 7533639 * 2
def baseEnd_7533639 : Nat := 3868377884457355336465931

theorem tailTrace_7533639 : CollatzResearch.WordTrace tailWord_7533639 prefixEnd_7533639 3868377884457355336465931 := by
  unfold tailWord_7533639
  simp only [CollatzResearch.WordTrace]
  refine ⟨274774387953920020951419971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183182925302613347300946647 274774387953920020951419971)
  ·
    refine ⟨412161581930880031427129957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274774387953920020951419971 412161581930880031427129957)
    ·
      refine ⟨77280296612040005892586867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412161581930880031427129957 77280296612040005892586867)
      ·
        refine ⟨115920444918060008838880301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77280296612040005892586867 115920444918060008838880301)
        ·
          refine ⟨43470166844272503314580113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115920444918060008838880301 43470166844272503314580113)
          ·
            refine ⟨32602625133204377485935085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43470166844272503314580113 32602625133204377485935085)
            ·
              refine ⟨12225984424951641557225657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32602625133204377485935085 12225984424951641557225657)
              ·
                refine ⟨9169488318713731167919243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12225984424951641557225657 9169488318713731167919243)
                ·
                  refine ⟨13754232478070596751878865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169488318713731167919243 13754232478070596751878865)
                  ·
                    refine ⟨10315674358552947563909149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13754232478070596751878865 10315674358552947563909149)
                    ·
                      refine ⟨3868377884457355336465931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315674358552947563909149 3868377884457355336465931)
                      ·
                        rfl

theorem cell23_7533639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_7533639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533639 prefixEnd_7533639 := by exact prefixLift 7533639
  have htrace : WordTrace (prefixWord ++ tailWord_7533639) baseStart_7533639 baseEnd_7533639 := by
    simpa [prefixWord, tailWord_7533639, baseEnd_7533639] using wordTrace_append hprefix tailTrace_7533639
  have hstable : (prefixWord ++ tailWord_7533639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533639).length < 2 ^ (prefixWord ++ tailWord_7533639).sum := by decide
  have hdescent : baseEnd_7533639 < baseStart_7533639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533652 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_7533652 : Nat := 118140960795 + 7533652 * 2 ^ 59
def prefixEnd_7533652 : Nat := 4983230072969 + 3 ^ 40 * 7533652 * 2
def baseEnd_7533652 : Nat := 3868384559705863785603371

theorem tailTrace_7533652 : CollatzResearch.WordTrace tailWord_7533652 prefixEnd_7533652 3868384559705863785603371 := by
  unfold tailWord_7533652
  simp only [CollatzResearch.WordTrace]
  refine ⟨137387431051436462085821605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183183241401915282781095473 137387431051436462085821605)
  ·
    refine ⟨25760143322144336641091551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137387431051436462085821605 25760143322144336641091551)
    ·
      refine ⟨38640214983216504961637327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760143322144336641091551 38640214983216504961637327)
      ·
        refine ⟨57960322474824757442455991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38640214983216504961637327 57960322474824757442455991)
        ·
          refine ⟨86940483712237136163683987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57960322474824757442455991 86940483712237136163683987)
          ·
            refine ⟨130410725568355704245525981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86940483712237136163683987 130410725568355704245525981)
            ·
              refine ⟨48904022088133389092072243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130410725568355704245525981 48904022088133389092072243)
              ·
                refine ⟨73356033132200083638108365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48904022088133389092072243 73356033132200083638108365)
                ·
                  refine ⟨27508512424575031364290637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73356033132200083638108365 27508512424575031364290637)
                  ·
                    refine ⟨10315692159215636761608989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27508512424575031364290637 10315692159215636761608989)
                    ·
                      refine ⟨3868384559705863785603371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315692159215636761608989 3868384559705863785603371)
                      ·
                        rfl

theorem cell23_7533652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_7533652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533652 prefixEnd_7533652 := by exact prefixLift 7533652
  have htrace : WordTrace (prefixWord ++ tailWord_7533652) baseStart_7533652 baseEnd_7533652 := by
    simpa [prefixWord, tailWord_7533652, baseEnd_7533652] using wordTrace_append hprefix tailTrace_7533652
  have hstable : (prefixWord ++ tailWord_7533652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533652).length < 2 ^ (prefixWord ++ tailWord_7533652).sum := by decide
  have hdescent : baseEnd_7533652 < baseStart_7533652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533665 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7533665 : Nat := 118140960795 + 7533665 * 2 ^ 59
def prefixEnd_7533665 : Nat := 4983230072969 + 3 ^ 40 * 7533665 * 2
def baseEnd_7533665 : Nat := 3868391234954372234740811

theorem tailTrace_7533665 : CollatzResearch.WordTrace tailWord_7533665 prefixEnd_7533665 3868391234954372234740811 := by
  unfold tailWord_7533665
  simp only [CollatzResearch.WordTrace]
  refine ⟨274775336251825827391866449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183183557501217218261244299 274775336251825827391866449)
  ·
    refine ⟨206081502188869370543899837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274775336251825827391866449 206081502188869370543899837)
    ·
      refine ⟨77280563320826013953962439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206081502188869370543899837 77280563320826013953962439)
      ·
        refine ⟨115920844981239020930943659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77280563320826013953962439 115920844981239020930943659)
        ·
          refine ⟨173881267471858531396415489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115920844981239020930943659 173881267471858531396415489)
          ·
            refine ⟨130410950603893898547311617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173881267471858531396415489 130410950603893898547311617)
            ·
              refine ⟨97808212952920423910483713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130410950603893898547311617 97808212952920423910483713)
              ·
                refine ⟨73356159714690317932862785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97808212952920423910483713 73356159714690317932862785)
                ·
                  refine ⟨55017119786017738449647089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73356159714690317932862785 55017119786017738449647089)
                  ·
                    refine ⟨41262839839513303837235317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55017119786017738449647089 41262839839513303837235317)
                    ·
                      refine ⟨3868391234954372234740811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41262839839513303837235317 3868391234954372234740811)
                      ·
                        rfl

theorem cell23_7533665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7533665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533665 prefixEnd_7533665 := by exact prefixLift 7533665
  have htrace : WordTrace (prefixWord ++ tailWord_7533665) baseStart_7533665 baseEnd_7533665 := by
    simpa [prefixWord, tailWord_7533665, baseEnd_7533665] using wordTrace_append hprefix tailTrace_7533665
  have hstable : (prefixWord ++ tailWord_7533665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533665).length < 2 ^ (prefixWord ++ tailWord_7533665).sum := by decide
  have hdescent : baseEnd_7533665 < baseStart_7533665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533686 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7533686 : Nat := 118140960795 + 7533686 * 2 ^ 59
def prefixEnd_7533686 : Nat := 4983230072969 + 3 ^ 40 * 7533686 * 2
def baseEnd_7533686 : Nat := 3868402018048116652578215

theorem tailTrace_7533686 : CollatzResearch.WordTrace tailWord_7533686 prefixEnd_7533686 3868402018048116652578215 := by
  unfold tailWord_7533686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173506386546859248648807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183184068123166498652253941 17173506386546859248648807)
  ·
    refine ⟨25760259579820288872973211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173506386546859248648807 25760259579820288872973211)
    ·
      refine ⟨38640389369730433309459817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760259579820288872973211 38640389369730433309459817)
      ·
        refine ⟨28980292027297824982094863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38640389369730433309459817 28980292027297824982094863)
        ·
          refine ⟨43470438040946737473142295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28980292027297824982094863 43470438040946737473142295)
          ·
            refine ⟨65205657061420106209713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43470438040946737473142295 65205657061420106209713443)
            ·
              refine ⟨97808485592130159314570165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65205657061420106209713443 97808485592130159314570165)
              ·
                refine ⟨9169545524262202435740953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97808485592130159314570165 9169545524262202435740953)
                ·
                  refine ⟨6877159143196651826805715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169545524262202435740953 6877159143196651826805715)
                  ·
                    refine ⟨10315738714794977740208573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877159143196651826805715 10315738714794977740208573)
                    ·
                      refine ⟨3868402018048116652578215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315738714794977740208573 3868402018048116652578215)
                      ·
                        rfl

theorem cell23_7533686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7533686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533686 prefixEnd_7533686 := by exact prefixLift 7533686
  have htrace : WordTrace (prefixWord ++ tailWord_7533686) baseStart_7533686 baseEnd_7533686 := by
    simpa [prefixWord, tailWord_7533686, baseEnd_7533686] using wordTrace_append hprefix tailTrace_7533686
  have hstable : (prefixWord ++ tailWord_7533686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533686).length < 2 ^ (prefixWord ++ tailWord_7533686).sum := by decide
  have hdescent : baseEnd_7533686 < baseStart_7533686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533732 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 7]
def baseStart_7533732 : Nat := 118140960795 + 7533732 * 2 ^ 59
def prefixEnd_7533732 : Nat := 4983230072969 + 3 ^ 40 * 7533732 * 2
def baseEnd_7533732 : Nat := 429825070906469274733667

theorem tailTrace_7533732 : CollatzResearch.WordTrace tailWord_7533732 prefixEnd_7533732 429825070906469274733667 := by
  unfold tailWord_7533732
  simp only [CollatzResearch.WordTrace]
  refine ⟨137388889971291548917277725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183185186628388731889703633 137388889971291548917277725)
  ·
    refine ⟨51520833739234330843979147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137388889971291548917277725 51520833739234330843979147)
    ·
      refine ⟨77281250608851496265968721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51520833739234330843979147 77281250608851496265968721)
      ·
        refine ⟨57960937956638622199476541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77281250608851496265968721 57960937956638622199476541)
        ·
          refine ⟨21735351733739483324803703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57960937956638622199476541 21735351733739483324803703)
          ·
            refine ⟨32603027600609224987205555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21735351733739483324803703 32603027600609224987205555)
            ·
              refine ⟨48904541400913837480808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32603027600609224987205555 48904541400913837480808333)
              ·
                refine ⟨18339203025342689055303125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48904541400913837480808333 18339203025342689055303125)
                ·
                  refine ⟨429825070906469274733667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18339203025342689055303125 429825070906469274733667)
                  ·
                    rfl

theorem cell23_7533732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_7533732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533732 prefixEnd_7533732 := by exact prefixLift 7533732
  have htrace : WordTrace (prefixWord ++ tailWord_7533732) baseStart_7533732 baseEnd_7533732 := by
    simpa [prefixWord, tailWord_7533732, baseEnd_7533732] using wordTrace_append hprefix tailTrace_7533732
  have hstable : (prefixWord ++ tailWord_7533732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533732).length < 2 ^ (prefixWord ++ tailWord_7533732).sum := by decide
  have hdescent : baseEnd_7533732 < baseStart_7533732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533755 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_7533755 : Nat := 118140960795 + 7533755 * 2 ^ 59
def prefixEnd_7533755 : Nat := 4983230072969 + 3 ^ 40 * 7533755 * 2
def baseEnd_7533755 : Nat := 3868437448213276882615397

theorem tailTrace_7533755 : CollatzResearch.WordTrace tailWord_7533755 prefixEnd_7533755 3868437448213276882615397 := by
  unfold tailWord_7533755
  simp only [CollatzResearch.WordTrace]
  refine ⟨274778618821499772762642719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183185745880999848508428479 274778618821499772762642719)
  ·
    refine ⟨412167928232249659143964079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274778618821499772762642719 412167928232249659143964079)
    ·
      refine ⟨618251892348374488715946119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412167928232249659143964079 618251892348374488715946119)
      ·
        refine ⟨927377838522561733073919179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618251892348374488715946119 927377838522561733073919179)
        ·
          refine ⟨1391066757783842599610878769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927377838522561733073919179 1391066757783842599610878769)
          ·
            refine ⟨1043300068337881949708159077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391066757783842599610878769 1043300068337881949708159077)
            ·
              refine ⟨195618762813352865570279827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1043300068337881949708159077 195618762813352865570279827)
              ·
                refine ⟨293428144220029298355419741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195618762813352865570279827 293428144220029298355419741)
                ·
                  refine ⟨110035554082510986883282403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293428144220029298355419741 110035554082510986883282403)
                  ·
                    refine ⟨165053331123766480324923605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110035554082510986883282403 165053331123766480324923605)
                    ·
                      refine ⟨3868437448213276882615397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165053331123766480324923605 3868437448213276882615397)
                      ·
                        rfl

theorem cell23_7533755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_7533755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533755 prefixEnd_7533755 := by exact prefixLift 7533755
  have htrace : WordTrace (prefixWord ++ tailWord_7533755) baseStart_7533755 baseEnd_7533755 := by
    simpa [prefixWord, tailWord_7533755, baseEnd_7533755] using wordTrace_append hprefix tailTrace_7533755
  have hstable : (prefixWord ++ tailWord_7533755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533755).length < 2 ^ (prefixWord ++ tailWord_7533755).sum := by decide
  have hdescent : baseEnd_7533755 < baseStart_7533755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533849 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_7533849 : Nat := 118140960795 + 7533849 * 2 ^ 59
def prefixEnd_7533849 : Nat := 4983230072969 + 3 ^ 40 * 7533849 * 2
def baseEnd_7533849 : Nat := 3868485715394799514839965

theorem tailTrace_7533849 : CollatzResearch.WordTrace tailWord_7533849 prefixEnd_7533849 3868485715394799514839965 := by
  unfold tailWord_7533849
  simp only [CollatzResearch.WordTrace]
  refine ⟨274782047283159226816564601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183188031522106151211043067 274782047283159226816564601)
  ·
    refine ⟨206086535462369420112423451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274782047283159226816564601 206086535462369420112423451)
    ·
      refine ⟨309129803193554130168635177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206086535462369420112423451 309129803193554130168635177)
      ·
        refine ⟨231847352395165597626476383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309129803193554130168635177 231847352395165597626476383)
        ·
          refine ⟨347771028592748396439714575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231847352395165597626476383 347771028592748396439714575)
          ·
            refine ⟨521656542889122594659571863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347771028592748396439714575 521656542889122594659571863)
            ·
              refine ⟨782484814333683891989357795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521656542889122594659571863 782484814333683891989357795)
              ·
                refine ⟨1173727221500525837984036693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782484814333683891989357795 1173727221500525837984036693)
                ·
                  refine ⟨6877307938479643581937715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1173727221500525837984036693 6877307938479643581937715)
                  ·
                    refine ⟨10315961907719465372906573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877307938479643581937715 10315961907719465372906573)
                    ·
                      refine ⟨3868485715394799514839965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10315961907719465372906573 3868485715394799514839965)
                      ·
                        rfl

theorem cell23_7533849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_7533849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533849 prefixEnd_7533849 := by exact prefixLift 7533849
  have htrace : WordTrace (prefixWord ++ tailWord_7533849) baseStart_7533849 baseEnd_7533849 := by
    simpa [prefixWord, tailWord_7533849, baseEnd_7533849] using wordTrace_append hprefix tailTrace_7533849
  have hstable : (prefixWord ++ tailWord_7533849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533849).length < 2 ^ (prefixWord ++ tailWord_7533849).sum := by decide
  have hdescent : baseEnd_7533849 < baseStart_7533849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533886 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7533886 : Nat := 118140960795 + 7533886 * 2 ^ 59
def prefixEnd_7533886 : Nat := 4983230072969 + 3 ^ 40 * 7533886 * 2
def baseEnd_7533886 : Nat := 1289501571393005290025765

theorem tailTrace_7533886 : CollatzResearch.WordTrace tailWord_7533886 prefixEnd_7533886 1289501571393005290025765 := by
  unfold tailWord_7533886
  simp only [CollatzResearch.WordTrace]
  refine ⟨34347924598003147766957689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183188931189350121423774341 34347924598003147766957689)
  ·
    refine ⟨25760943448502360825218267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34347924598003147766957689 25760943448502360825218267)
    ·
      refine ⟨38641415172753541237827401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760943448502360825218267 38641415172753541237827401)
      ·
        refine ⟨28981061379565155928370551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38641415172753541237827401 28981061379565155928370551)
        ·
          refine ⟨43471592069347733892555827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28981061379565155928370551 43471592069347733892555827)
          ·
            refine ⟨65207388104021600838833741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43471592069347733892555827 65207388104021600838833741)
            ·
              refine ⟨24452770539008100314562653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65207388104021600838833741 24452770539008100314562653)
              ·
                refine ⟨9169788952128037617960995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24452770539008100314562653 9169788952128037617960995)
                ·
                  refine ⟨13754683428192056426941493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169788952128037617960995 13754683428192056426941493)
                  ·
                    refine ⟨1289501571393005290025765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13754683428192056426941493 1289501571393005290025765)
                    ·
                      rfl

theorem cell23_7533886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7533886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533886 prefixEnd_7533886 := by exact prefixLift 7533886
  have htrace : WordTrace (prefixWord ++ tailWord_7533886) baseStart_7533886 baseEnd_7533886 := by
    simpa [prefixWord, tailWord_7533886, baseEnd_7533886] using wordTrace_append hprefix tailTrace_7533886
  have hstable : (prefixWord ++ tailWord_7533886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533886).length < 2 ^ (prefixWord ++ tailWord_7533886).sum := by decide
  have hdescent : baseEnd_7533886 < baseStart_7533886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533909 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7533909 : Nat := 118140960795 + 7533909 * 2 ^ 59
def prefixEnd_7533909 : Nat := 4983230072969 + 3 ^ 40 * 7533909 * 2
def baseEnd_7533909 : Nat := 3868516524234069280089689

theorem tailTrace_7533909 : CollatzResearch.WordTrace tailWord_7533909 prefixEnd_7533909 3868516524234069280089689 := by
  unfold tailWord_7533909
  simp only [CollatzResearch.WordTrace]
  refine ⟨274784235662941857063748781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183189490441961238042499187 274784235662941857063748781)
  ·
    refine ⟨103044088373603196398905793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274784235662941857063748781 103044088373603196398905793)
    ·
      refine ⟨77283066280202397299179345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103044088373603196398905793 77283066280202397299179345)
      ·
        refine ⟨57962299710151797974384509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77283066280202397299179345 57962299710151797974384509)
        ·
          refine ⟨21735862391306924240394191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57962299710151797974384509 21735862391306924240394191)
          ·
            refine ⟨32603793586960386360591287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21735862391306924240394191 32603793586960386360591287)
            ·
              refine ⟨48905690380440579540886931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32603793586960386360591287 48905690380440579540886931)
              ·
                refine ⟨73358535570660869311330397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48905690380440579540886931 73358535570660869311330397)
                ·
                  refine ⟨27509450838997825991748899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73358535570660869311330397 27509450838997825991748899)
                  ·
                    refine ⟨41264176258496738987623349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27509450838997825991748899 41264176258496738987623349)
                    ·
                      refine ⟨3868516524234069280089689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41264176258496738987623349 3868516524234069280089689)
                      ·
                        rfl

theorem cell23_7533909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7533909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533909 prefixEnd_7533909 := by exact prefixLift 7533909
  have htrace : WordTrace (prefixWord ++ tailWord_7533909) baseStart_7533909 baseEnd_7533909 := by
    simpa [prefixWord, tailWord_7533909, baseEnd_7533909] using wordTrace_append hprefix tailTrace_7533909
  have hstable : (prefixWord ++ tailWord_7533909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533909).length < 2 ^ (prefixWord ++ tailWord_7533909).sum := by decide
  have hdescent : baseEnd_7533909 < baseStart_7533909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533912 : List Nat := [2, 1, 2, 2, 1, 1, 4, 10]
def baseStart_7533912 : Nat := 118140960795 + 7533912 * 2 ^ 59
def prefixEnd_7533912 : Nat := 4983230072969 + 3 ^ 40 * 7533912 * 2
def baseEnd_7533912 : Nat := 143278446839853065494525

theorem tailTrace_7533912 : CollatzResearch.WordTrace tailWord_7533912 prefixEnd_7533912 143278446839853065494525 := by
  unfold tailWord_7533912
  simp only [CollatzResearch.WordTrace]
  refine ⟨137392172540965494288053995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183189563387953992384071993 137392172540965494288053995)
  ·
    refine ⟨206088258811448241432080993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137392172540965494288053995 206088258811448241432080993)
    ·
      refine ⟨154566194108586181074060745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206088258811448241432080993 154566194108586181074060745)
      ·
        refine ⟨115924645581439635805545559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154566194108586181074060745 115924645581439635805545559)
        ·
          refine ⟨173886968372159453708318339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115924645581439635805545559 173886968372159453708318339)
          ·
            refine ⟨260830452558239180562477509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173886968372159453708318339 260830452558239180562477509)
            ·
              refine ⟨48905709854669846355464533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260830452558239180562477509 48905709854669846355464533)
              ·
                refine ⟨143278446839853065494525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48905709854669846355464533 143278446839853065494525)
                ·
                  rfl

theorem cell23_7533912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 10].length) (baseStart_7533912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533912 prefixEnd_7533912 := by exact prefixLift 7533912
  have htrace : WordTrace (prefixWord ++ tailWord_7533912) baseStart_7533912 baseEnd_7533912 := by
    simpa [prefixWord, tailWord_7533912, baseEnd_7533912] using wordTrace_append hprefix tailTrace_7533912
  have hstable : (prefixWord ++ tailWord_7533912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533912).length < 2 ^ (prefixWord ++ tailWord_7533912).sum := by decide
  have hdescent : baseEnd_7533912 < baseStart_7533912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533923 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 3, 2, 2]
def baseStart_7533923 : Nat := 118140960795 + 7533923 * 2 ^ 59
def prefixEnd_7533923 : Nat := 4983230072969 + 3 ^ 40 * 7533923 * 2
def baseEnd_7533923 : Nat := 3868523712963232225314625

theorem tailTrace_7533923 : CollatzResearch.WordTrace tailWord_7533923 prefixEnd_7533923 3868523712963232225314625 := by
  unfold tailWord_7533923
  simp only [CollatzResearch.WordTrace]
  refine ⟨274784746284891137454758423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183189830856594091636505615 274784746284891137454758423)
  ·
    refine ⟨412177119427336706182137635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274784746284891137454758423 412177119427336706182137635)
    ·
      refine ⟨618265679141005059273206453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412177119427336706182137635 618265679141005059273206453)
      ·
        refine ⟨57962407419469224306863105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 618265679141005059273206453 57962407419469224306863105)
        ·
          refine ⟨43471805564601918230147329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57962407419469224306863105 43471805564601918230147329)
          ·
            refine ⟨32603854173451438672610497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43471805564601918230147329 32603854173451438672610497)
            ·
              refine ⟨24452890630088579004457873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32603854173451438672610497 24452890630088579004457873)
              ·
                refine ⟨18339667972566434253343405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24452890630088579004457873 18339667972566434253343405)
                ·
                  refine ⟨6877375489712412845003777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18339667972566434253343405 6877375489712412845003777)
                  ·
                    refine ⟨5158031617284309633752833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6877375489712412845003777 5158031617284309633752833)
                    ·
                      refine ⟨3868523712963232225314625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158031617284309633752833 3868523712963232225314625)
                      ·
                        rfl

theorem cell23_7533923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_7533923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533923 prefixEnd_7533923 := by exact prefixLift 7533923
  have htrace : WordTrace (prefixWord ++ tailWord_7533923) baseStart_7533923 baseEnd_7533923 := by
    simpa [prefixWord, tailWord_7533923, baseEnd_7533923] using wordTrace_append hprefix tailTrace_7533923
  have hstable : (prefixWord ++ tailWord_7533923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533923).length < 2 ^ (prefixWord ++ tailWord_7533923).sum := by decide
  have hdescent : baseEnd_7533923 < baseStart_7533923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533934 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7533934 : Nat := 118140960795 + 7533934 * 2 ^ 59
def prefixEnd_7533934 : Nat := 4983230072969 + 3 ^ 40 * 7533934 * 2
def baseEnd_7533934 : Nat := 3868529361250431682277075

theorem tailTrace_7533934 : CollatzResearch.WordTrace tailWord_7533934 prefixEnd_7533934 3868529361250431682277075 := by
  unfold tailWord_7533934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348143435981410791676107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183190098325234190888939237 34348143435981410791676107)
  ·
    refine ⟨51522215153972116187514161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34348143435981410791676107 51522215153972116187514161)
    ·
      refine ⟨38641661365479087140635621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51522215153972116187514161 38641661365479087140635621)
      ·
        refine ⟨7245311506027328838869179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38641661365479087140635621 7245311506027328838869179)
        ·
          refine ⟨10867967259040993258303769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7245311506027328838869179 10867967259040993258303769)
          ·
            refine ⟨8150975444280744943727827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10867967259040993258303769 8150975444280744943727827)
            ·
              refine ⟨12226463166421117415591741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150975444280744943727827 12226463166421117415591741)
              ·
                refine ⟨4584923687407919030846903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12226463166421117415591741 4584923687407919030846903)
                ·
                  refine ⟨6877385531111878546270355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584923687407919030846903 6877385531111878546270355)
                  ·
                    refine ⟨10316078296667817819405533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877385531111878546270355 10316078296667817819405533)
                    ·
                      refine ⟨3868529361250431682277075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316078296667817819405533 3868529361250431682277075)
                      ·
                        rfl

theorem cell23_7533934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7533934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533934 prefixEnd_7533934 := by exact prefixLift 7533934
  have htrace : WordTrace (prefixWord ++ tailWord_7533934) baseStart_7533934 baseEnd_7533934 := by
    simpa [prefixWord, tailWord_7533934, baseEnd_7533934] using wordTrace_append hprefix tailTrace_7533934
  have hstable : (prefixWord ++ tailWord_7533934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533934).length < 2 ^ (prefixWord ++ tailWord_7533934).sum := by decide
  have hdescent : baseEnd_7533934 < baseStart_7533934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533983 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7533983 : Nat := 118140960795 + 7533983 * 2 ^ 59
def prefixEnd_7533983 : Nat := 4983230072969 + 3 ^ 40 * 7533983 * 2
def baseEnd_7533983 : Nat := 3868554521802501990564349

theorem tailTrace_7533983 : CollatzResearch.WordTrace tailWord_7533983 prefixEnd_7533983 3868554521802501990564349 := by
  unfold tailWord_7533983
  simp only [CollatzResearch.WordTrace]
  refine ⟨274786934664673767701942603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183191289776449178467961735 274786934664673767701942603)
  ·
    refine ⟨412180401997010651552913905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274786934664673767701942603 412180401997010651552913905)
    ·
      refine ⟨309135301497757988664685429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412180401997010651552913905 309135301497757988664685429)
      ·
        refine ⟨28981434515414811437314259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309135301497757988664685429 28981434515414811437314259)
        ·
          refine ⟨43472151773122217155971389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28981434515414811437314259 43472151773122217155971389)
          ·
            refine ⟨16302056914920831433489271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43472151773122217155971389 16302056914920831433489271)
            ·
              refine ⟨24453085372381247150233907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16302056914920831433489271 24453085372381247150233907)
              ·
                refine ⟨36679628058571870725350861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24453085372381247150233907 36679628058571870725350861)
                ·
                  refine ⟨13754860521964451522006573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36679628058571870725350861 13754860521964451522006573)
                  ·
                    refine ⟨5158072695736669320752465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13754860521964451522006573 5158072695736669320752465)
                    ·
                      refine ⟨3868554521802501990564349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158072695736669320752465 3868554521802501990564349)
                      ·
                        rfl

theorem cell23_7533983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7533983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533983 prefixEnd_7533983 := by exact prefixLift 7533983
  have htrace : WordTrace (prefixWord ++ tailWord_7533983) baseStart_7533983 baseEnd_7533983 := by
    simpa [prefixWord, tailWord_7533983, baseEnd_7533983] using wordTrace_append hprefix tailTrace_7533983
  have hstable : (prefixWord ++ tailWord_7533983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533983).length < 2 ^ (prefixWord ++ tailWord_7533983).sum := by decide
  have hdescent : baseEnd_7533983 < baseStart_7533983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533996 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_7533996 : Nat := 118140960795 + 7533996 * 2 ^ 59
def prefixEnd_7533996 : Nat := 4983230072969 + 3 ^ 40 * 7533996 * 2
def baseEnd_7533996 : Nat := 3868561197051010439701789

theorem tailTrace_7533996 : CollatzResearch.WordTrace tailWord_7533996 prefixEnd_7533996 3868561197051010439701789 := by
  unfold tailWord_7533996
  simp only [CollatzResearch.WordTrace]
  refine ⟨137393704406813335461082921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183191605875751113948110561 137393704406813335461082921)
  ·
    refine ⟨103045278305110001595812191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137393704406813335461082921 103045278305110001595812191)
    ·
      refine ⟨154567917457665002393718287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103045278305110001595812191 154567917457665002393718287)
      ·
        refine ⟨231851876186497503590577431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154567917457665002393718287 231851876186497503590577431)
        ·
          refine ⟨347777814279746255385866147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231851876186497503590577431 347777814279746255385866147)
          ·
            refine ⟨521666721419619383078799221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347777814279746255385866147 521666721419619383078799221)
            ·
              refine ⟨48906255133089317163637427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521666721419619383078799221 48906255133089317163637427)
              ·
                refine ⟨73359382699633975745456141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48906255133089317163637427 73359382699633975745456141)
                ·
                  refine ⟨27509768512362740904546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73359382699633975745456141 27509768512362740904546053)
                  ·
                    refine ⟨5158081596068013919602385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27509768512362740904546053 5158081596068013919602385)
                    ·
                      refine ⟨3868561197051010439701789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158081596068013919602385 3868561197051010439701789)
                      ·
                        rfl

theorem cell23_7533996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_7533996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533996 prefixEnd_7533996 := by exact prefixLift 7533996
  have htrace : WordTrace (prefixWord ++ tailWord_7533996) baseStart_7533996 baseEnd_7533996 := by
    simpa [prefixWord, tailWord_7533996, baseEnd_7533996] using wordTrace_append hprefix tailTrace_7533996
  have hstable : (prefixWord ++ tailWord_7533996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533996).length < 2 ^ (prefixWord ++ tailWord_7533996).sum := by decide
  have hdescent : baseEnd_7533996 < baseStart_7533996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533999 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_7533999 : Nat := 118140960795 + 7533999 * 2 ^ 59
def prefixEnd_7533999 : Nat := 4983230072969 + 3 ^ 40 * 7533999 * 2
def baseEnd_7533999 : Nat := 3868562737492973927964275

theorem tailTrace_7533999 : CollatzResearch.WordTrace tailWord_7533999 prefixEnd_7533999 3868562737492973927964275 := by
  unfold tailWord_7533999
  simp only [CollatzResearch.WordTrace]
  refine ⟨274787518232615802434525051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183191678821743868289683367 274787518232615802434525051)
  ·
    refine ⟨412181277348923703651787577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274787518232615802434525051 412181277348923703651787577)
    ·
      refine ⟨309135958011692777738840683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412181277348923703651787577 309135958011692777738840683)
      ·
        refine ⟨463703937017539166608261025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309135958011692777738840683 463703937017539166608261025)
        ·
          refine ⟨347777952763154374956195769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463703937017539166608261025 347777952763154374956195769)
          ·
            refine ⟨260833464572365781217146827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347777952763154374956195769 260833464572365781217146827)
            ·
              refine ⟨391250196858548671825720241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260833464572365781217146827 391250196858548671825720241)
              ·
                refine ⟨293437647643911503869290181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391250196858548671825720241 293437647643911503869290181)
                ·
                  refine ⟨55019558933233406975491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293437647643911503869290181 55019558933233406975491909)
                  ·
                    refine ⟨10316167299981263807904733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55019558933233406975491909 10316167299981263807904733)
                    ·
                      refine ⟨3868562737492973927964275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316167299981263807904733 3868562737492973927964275)
                      ·
                        rfl

theorem cell23_7533999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_7533999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7533999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7533999 prefixEnd_7533999 := by exact prefixLift 7533999
  have htrace : WordTrace (prefixWord ++ tailWord_7533999) baseStart_7533999 baseEnd_7533999 := by
    simpa [prefixWord, tailWord_7533999, baseEnd_7533999] using wordTrace_append hprefix tailTrace_7533999
  have hstable : (prefixWord ++ tailWord_7533999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533999).length < 2 ^ (prefixWord ++ tailWord_7533999).sum := by decide
  have hdescent : baseEnd_7533999 < baseStart_7533999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534026 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_7534026 : Nat := 118140960795 + 7534026 * 2 ^ 59
def prefixEnd_7534026 : Nat := 4983230072969 + 3 ^ 40 * 7534026 * 2
def baseEnd_7534026 : Nat := 3868576601470645322326651

theorem tailTrace_7534026 : CollatzResearch.WordTrace tailWord_7534026 prefixEnd_7534026 3868576601470645322326651 := by
  unfold tailWord_7534026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68697125750879496511439483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183192335335678657363838621 68697125750879496511439483)
  ·
    refine ⟨103045688626319244767159225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68697125750879496511439483 103045688626319244767159225)
    ·
      refine ⟨77284266469739433575369419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103045688626319244767159225 77284266469739433575369419)
      ·
        refine ⟨115926399704609150363054129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77284266469739433575369419 115926399704609150363054129)
        ·
          refine ⟨86944799778456862772290597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115926399704609150363054129 86944799778456862772290597)
          ·
            refine ⟨16302149958460661769804487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86944799778456862772290597 16302149958460661769804487)
            ·
              refine ⟨24453224937690992654706731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16302149958460661769804487 24453224937690992654706731)
              ·
                refine ⟨36679837406536488982060097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24453224937690992654706731 36679837406536488982060097)
                ·
                  refine ⟨27509878054902366736545073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36679837406536488982060097 27509878054902366736545073)
                  ·
                    refine ⟨20632408541176775052408805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27509878054902366736545073 20632408541176775052408805)
                    ·
                      refine ⟨3868576601470645322326651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20632408541176775052408805 3868576601470645322326651)
                      ·
                        rfl

theorem cell23_7534026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_7534026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534026 prefixEnd_7534026 := by exact prefixLift 7534026
  have htrace : WordTrace (prefixWord ++ tailWord_7534026) baseStart_7534026 baseEnd_7534026 := by
    simpa [prefixWord, tailWord_7534026, baseEnd_7534026] using wordTrace_append hprefix tailTrace_7534026
  have hstable : (prefixWord ++ tailWord_7534026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534026).length < 2 ^ (prefixWord ++ tailWord_7534026).sum := by decide
  have hdescent : baseEnd_7534026 < baseStart_7534026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534030 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_7534030 : Nat := 118140960795 + 7534030 * 2 ^ 59
def prefixEnd_7534030 : Nat := 4983230072969 + 3 ^ 40 * 7534030 * 2
def baseEnd_7534030 : Nat := 3868578655393263306676633

theorem tailTrace_7534030 : CollatzResearch.WordTrace tailWord_7534030 prefixEnd_7534030 3868578655393263306676633 := by
  unfold tailWord_7534030
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348581111937936841112943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183192432597002329819269029 34348581111937936841112943)
  ·
    refine ⟨51522871667906905261669415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34348581111937936841112943 51522871667906905261669415)
    ·
      refine ⟨77284307501860357892504123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51522871667906905261669415 77284307501860357892504123)
      ·
        refine ⟨115926461252790536838756185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77284307501860357892504123 115926461252790536838756185)
        ·
          refine ⟨86944845939592902629067139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115926461252790536838756185 86944845939592902629067139)
          ·
            refine ⟨130417268909389353943600709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86944845939592902629067139 130417268909389353943600709)
            ·
              refine ⟨24453237920510503864425133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130417268909389353943600709 24453237920510503864425133)
              ·
                refine ⟨9169964220191438949159425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24453237920510503864425133 9169964220191438949159425)
                ·
                  refine ⟨6877473165143579211869569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169964220191438949159425 6877473165143579211869569)
                  ·
                    refine ⟨5158104873857684408902177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6877473165143579211869569 5158104873857684408902177)
                    ·
                      refine ⟨3868578655393263306676633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158104873857684408902177 3868578655393263306676633)
                      ·
                        rfl

theorem cell23_7534030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_7534030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534030 prefixEnd_7534030 := by exact prefixLift 7534030
  have htrace : WordTrace (prefixWord ++ tailWord_7534030) baseStart_7534030 baseEnd_7534030 := by
    simpa [prefixWord, tailWord_7534030, baseEnd_7534030] using wordTrace_append hprefix tailTrace_7534030
  have hstable : (prefixWord ++ tailWord_7534030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534030).length < 2 ^ (prefixWord ++ tailWord_7534030).sum := by decide
  have hdescent : baseEnd_7534030 < baseStart_7534030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534053 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 5]
def baseStart_7534053 : Nat := 118140960795 + 7534053 * 2 ^ 59
def prefixEnd_7534053 : Nat := 4983230072969 + 3 ^ 40 * 7534053 * 2
def baseEnd_7534053 : Nat := 429843385049812968521003

theorem tailTrace_7534053 : CollatzResearch.WordTrace tailWord_7534053 prefixEnd_7534053 429843385049812968521003 := by
  unfold tailWord_7534053
  simp only [CollatzResearch.WordTrace]
  refine ⟨274789487774420169656990813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183192991849613446437993875 274789487774420169656990813)
  ·
    refine ⟨103046057915407563621371555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274789487774420169656990813 103046057915407563621371555)
    ·
      refine ⟨154569086873111345432057333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103046057915407563621371555 154569086873111345432057333)
      ·
        refine ⟨14490851894354188634255375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154569086873111345432057333 14490851894354188634255375)
        ·
          refine ⟨21736277841531282951383063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490851894354188634255375 21736277841531282951383063)
          ·
            refine ⟨32604416762296924427074595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21736277841531282951383063 32604416762296924427074595)
            ·
              refine ⟨48906625143445386640611893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32604416762296924427074595 48906625143445386640611893)
              ·
                refine ⟨4584996107198004997557365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48906625143445386640611893 4584996107198004997557365)
                ·
                  refine ⟨429843385049812968521003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4584996107198004997557365 429843385049812968521003)
                  ·
                    rfl

theorem cell23_7534053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_7534053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534053 prefixEnd_7534053 := by exact prefixLift 7534053
  have htrace : WordTrace (prefixWord ++ tailWord_7534053) baseStart_7534053 baseEnd_7534053 := by
    simpa [prefixWord, tailWord_7534053, baseEnd_7534053] using wordTrace_append hprefix tailTrace_7534053
  have hstable : (prefixWord ++ tailWord_7534053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534053).length < 2 ^ (prefixWord ++ tailWord_7534053).sum := by decide
  have hdescent : baseEnd_7534053 < baseStart_7534053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534059 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_7534059 : Nat := 118140960795 + 7534059 * 2 ^ 59
def prefixEnd_7534059 : Nat := 4983230072969 + 3 ^ 40 * 7534059 * 2
def baseEnd_7534059 : Nat := 3868593546332243693213999

theorem tailTrace_7534059 : CollatzResearch.WordTrace tailWord_7534059 prefixEnd_7534059 3868593546332243693213999 := by
  unfold tailWord_7534059
  simp only [CollatzResearch.WordTrace]
  refine ⟨274789706612398432681709231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183193137741598955121139487 274789706612398432681709231)
  ·
    refine ⟨412184559918597649022563847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274789706612398432681709231 412184559918597649022563847)
    ·
      refine ⟨618276839877896473533845771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412184559918597649022563847 618276839877896473533845771)
      ·
        refine ⟨927415259816844710300768657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618276839877896473533845771 927415259816844710300768657)
        ·
          refine ⟨695561444862633532725576493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927415259816844710300768657 695561444862633532725576493)
          ·
            refine ⟨260835541823487574772091185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695561444862633532725576493 260835541823487574772091185)
            ·
              refine ⟨195626656367615681079068389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260835541823487574772091185 195626656367615681079068389)
              ·
                refine ⟨36679998068927940202325323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195626656367615681079068389 36679998068927940202325323)
                ·
                  refine ⟨55019997103391910303487985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36679998068927940202325323 55019997103391910303487985)
                  ·
                    refine ⟨41264997827543932727615989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55019997103391910303487985 41264997827543932727615989)
                    ·
                      refine ⟨3868593546332243693213999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41264997827543932727615989 3868593546332243693213999)
                      ·
                        rfl

theorem cell23_7534059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_7534059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534059 prefixEnd_7534059 := by exact prefixLift 7534059
  have htrace : WordTrace (prefixWord ++ tailWord_7534059) baseStart_7534059 baseEnd_7534059 := by
    simpa [prefixWord, tailWord_7534059, baseEnd_7534059] using wordTrace_append hprefix tailTrace_7534059
  have hstable : (prefixWord ++ tailWord_7534059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534059).length < 2 ^ (prefixWord ++ tailWord_7534059).sum := by decide
  have hdescent : baseEnd_7534059 < baseStart_7534059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534120 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7534120 : Nat := 118140960795 + 7534120 * 2 ^ 59
def prefixEnd_7534120 : Nat := 4983230072969 + 3 ^ 40 * 7534120 * 2
def baseEnd_7534120 : Nat := 3868624868652167954551219

theorem tailTrace_7534120 : CollatzResearch.WordTrace tailWord_7534120 prefixEnd_7534120 3868624868652167954551219 := by
  unfold tailWord_7534120
  simp only [CollatzResearch.WordTrace]
  refine ⟨137395965732588720049839907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183194620976784960066453209 137395965732588720049839907)
  ·
    refine ⟨206093948598883080074759861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137395965732588720049839907 206093948598883080074759861)
    ·
      refine ⟨19321307681145288757008737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206093948598883080074759861 19321307681145288757008737)
      ·
        refine ⟨14490980760858966567756553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19321307681145288757008737 14490980760858966567756553)
        ·
          refine ⟨10868235570644224925817415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14490980760858966567756553 10868235570644224925817415)
          ·
            refine ⟨16302353355966337388726123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868235570644224925817415 16302353355966337388726123)
            ·
              refine ⟨24453530033949506083089185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16302353355966337388726123 24453530033949506083089185)
              ·
                refine ⟨18340147525462129562316889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24453530033949506083089185 18340147525462129562316889)
                ·
                  refine ⟨13755110644096597171737667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18340147525462129562316889 13755110644096597171737667)
                  ·
                    refine ⟨20632665966144895757606501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13755110644096597171737667 20632665966144895757606501)
                    ·
                      refine ⟨3868624868652167954551219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20632665966144895757606501 3868624868652167954551219)
                      ·
                        rfl

theorem cell23_7534120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7534120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534120 prefixEnd_7534120 := by exact prefixLift 7534120
  have htrace : WordTrace (prefixWord ++ tailWord_7534120) baseStart_7534120 baseEnd_7534120 := by
    simpa [prefixWord, tailWord_7534120, baseEnd_7534120] using wordTrace_append hprefix tailTrace_7534120
  have hstable : (prefixWord ++ tailWord_7534120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534120).length < 2 ^ (prefixWord ++ tailWord_7534120).sum := by decide
  have hdescent : baseEnd_7534120 < baseStart_7534120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534143 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 6]
def baseStart_7534143 : Nat := 118140960795 + 7534143 * 2 ^ 59
def prefixEnd_7534143 : Nat := 4983230072969 + 3 ^ 40 * 7534143 * 2
def baseEnd_7534143 : Nat := 429848519856357929395957

theorem tailTrace_7534143 : CollatzResearch.WordTrace tailWord_7534143 prefixEnd_7534143 429848519856357929395957 := by
  unfold tailWord_7534143
  simp only [CollatzResearch.WordTrace]
  refine ⟨274792770344094115027767083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183195180229396076685178055 274792770344094115027767083)
  ·
    refine ⟨412189155516141172541650625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274792770344094115027767083 412189155516141172541650625)
    ·
      refine ⟨309141866637105879406237969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412189155516141172541650625 309141866637105879406237969)
      ·
        refine ⟨231856399977829409554678477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309141866637105879406237969 231856399977829409554678477)
        ·
          refine ⟨86946149991686028583004429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231856399977829409554678477 86946149991686028583004429)
          ·
            refine ⟨32604806246882260718626661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86946149991686028583004429 32604806246882260718626661)
            ·
              refine ⟨6113401171290423884742499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32604806246882260718626661 6113401171290423884742499)
              ·
                refine ⟨9170101756935635827113749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113401171290423884742499 9170101756935635827113749)
                ·
                  refine ⟨429848519856357929395957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9170101756935635827113749 429848519856357929395957)
                  ·
                    rfl

theorem cell23_7534143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 6].length) (baseStart_7534143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534143 prefixEnd_7534143 := by exact prefixLift 7534143
  have htrace : WordTrace (prefixWord ++ tailWord_7534143) baseStart_7534143 baseEnd_7534143 := by
    simpa [prefixWord, tailWord_7534143, baseEnd_7534143] using wordTrace_append hprefix tailTrace_7534143
  have hstable : (prefixWord ++ tailWord_7534143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534143).length < 2 ^ (prefixWord ++ tailWord_7534143).sum := by decide
  have hdescent : baseEnd_7534143 < baseStart_7534143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534153 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_7534153 : Nat := 118140960795 + 7534153 * 2 ^ 59
def prefixEnd_7534153 : Nat := 4983230072969 + 3 ^ 40 * 7534153 * 2
def baseEnd_7534153 : Nat := 3868641813513766325438567

theorem tailTrace_7534153 : CollatzResearch.WordTrace tailWord_7534153 prefixEnd_7534153 3868641813513766325438567 := by
  unfold tailWord_7534153
  simp only [CollatzResearch.WordTrace]
  refine ⟨274793135074057886735631113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183195423382705257823754075 274793135074057886735631113)
  ·
    refine ⟨206094851305543415051723335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274793135074057886735631113 206094851305543415051723335)
    ·
      refine ⟨309142276958315122577585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206094851305543415051723335 309142276958315122577585003)
      ·
        refine ⟨463713415437472683866377505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309142276958315122577585003 463713415437472683866377505)
        ·
          refine ⟨347785061578104512899783129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463713415437472683866377505 347785061578104512899783129)
          ·
            refine ⟨260838796183578384674837347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347785061578104512899783129 260838796183578384674837347)
            ·
              refine ⟨391258194275367577012256021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260838796183578384674837347 391258194275367577012256021)
              ·
                refine ⟨18340227856657855172449501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391258194275367577012256021 18340227856657855172449501)
                ·
                  refine ⟨6877585446246695689668563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18340227856657855172449501 6877585446246695689668563)
                  ·
                    refine ⟨10316378169370043534502845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877585446246695689668563 10316378169370043534502845)
                    ·
                      refine ⟨3868641813513766325438567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316378169370043534502845 3868641813513766325438567)
                      ·
                        rfl

theorem cell23_7534153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_7534153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534153 prefixEnd_7534153 := by exact prefixLift 7534153
  have htrace : WordTrace (prefixWord ++ tailWord_7534153) baseStart_7534153 baseEnd_7534153 := by
    simpa [prefixWord, tailWord_7534153, baseEnd_7534153] using wordTrace_append hprefix tailTrace_7534153
  have hstable : (prefixWord ++ tailWord_7534153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534153).length < 2 ^ (prefixWord ++ tailWord_7534153).sum := by decide
  have hdescent : baseEnd_7534153 < baseStart_7534153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534157 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7534157 : Nat := 118140960795 + 7534157 * 2 ^ 59
def prefixEnd_7534157 : Nat := 4983230072969 + 3 ^ 40 * 7534157 * 2
def baseEnd_7534157 : Nat := 3868643867436384309788549

theorem tailTrace_7534157 : CollatzResearch.WordTrace tailWord_7534157 prefixEnd_7534157 3868643867436384309788549 := by
  unfold tailWord_7534157
  simp only [CollatzResearch.WordTrace]
  refine ⟨274793280966043395418776725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183195520644028930279184483 274793280966043395418776725)
  ·
    refine ⟨12880935045283284160255159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274793280966043395418776725 12880935045283284160255159)
    ·
      refine ⟨19321402567924926240382739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12880935045283284160255159 19321402567924926240382739)
      ·
        refine ⟨28982103851887389360574109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19321402567924926240382739 28982103851887389360574109)
        ·
          refine ⟨10868288944457771010215291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28982103851887389360574109 10868288944457771010215291)
          ·
            refine ⟨16302433416686656515322937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868288944457771010215291 16302433416686656515322937)
            ·
              refine ⟨12226825062514992386492203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16302433416686656515322937 12226825062514992386492203)
              ·
                refine ⟨18340237593772488579738305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12226825062514992386492203 18340237593772488579738305)
                ·
                  refine ⟨13755178195329366434803729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18340237593772488579738305 13755178195329366434803729)
                  ·
                    refine ⟨10316383646497024826102797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13755178195329366434803729 10316383646497024826102797)
                    ·
                      refine ⟨3868643867436384309788549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316383646497024826102797 3868643867436384309788549)
                      ·
                        rfl

theorem cell23_7534157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7534157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534157 prefixEnd_7534157 := by exact prefixLift 7534157
  have htrace : WordTrace (prefixWord ++ tailWord_7534157) baseStart_7534157 baseEnd_7534157 := by
    simpa [prefixWord, tailWord_7534157, baseEnd_7534157] using wordTrace_append hprefix tailTrace_7534157
  have hstable : (prefixWord ++ tailWord_7534157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534157).length < 2 ^ (prefixWord ++ tailWord_7534157).sum := by decide
  have hdescent : baseEnd_7534157 < baseStart_7534157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534180 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_7534180 : Nat := 118140960795 + 7534180 * 2 ^ 59
def prefixEnd_7534180 : Nat := 4983230072969 + 3 ^ 40 * 7534180 * 2
def baseEnd_7534180 : Nat := 3868655677491437719800943

theorem tailTrace_7534180 : CollatzResearch.WordTrace tailWord_7534180 prefixEnd_7534180 3868655677491437719800943 := by
  unfold tailWord_7534180
  simp only [CollatzResearch.WordTrace]
  refine ⟨137397059922480035173431997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183196079896640046897909329 137397059922480035173431997)
  ·
    refine ⟨51523897470930013190036999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137397059922480035173431997 51523897470930013190036999)
    ·
      refine ⟨77285846206395019785055499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51523897470930013190036999 77285846206395019785055499)
      ·
        refine ⟨115928769309592529677583249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77285846206395019785055499 115928769309592529677583249)
        ·
          refine ⟨86946576982194397258187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115928769309592529677583249 86946576982194397258187437)
          ·
            refine ⟨32604966368322898971820289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86946576982194397258187437 32604966368322898971820289)
            ·
              refine ⟨24453724776242174228865217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32604966368322898971820289 24453724776242174228865217)
              ·
                refine ⟨18340293582181630671648913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24453724776242174228865217 18340293582181630671648913)
                ·
                  refine ⟨13755220186636223003736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18340293582181630671648913 13755220186636223003736685)
                  ·
                    refine ⟨5158207569988583626401257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13755220186636223003736685 5158207569988583626401257)
                    ·
                      refine ⟨3868655677491437719800943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158207569988583626401257 3868655677491437719800943)
                      ·
                        rfl

theorem cell23_7534180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_7534180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534180 prefixEnd_7534180 := by exact prefixLift 7534180
  have htrace : WordTrace (prefixWord ++ tailWord_7534180) baseStart_7534180 baseEnd_7534180 := by
    simpa [prefixWord, tailWord_7534180, baseEnd_7534180] using wordTrace_append hprefix tailTrace_7534180
  have hstable : (prefixWord ++ tailWord_7534180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534180).length < 2 ^ (prefixWord ++ tailWord_7534180).sum := by decide
  have hdescent : baseEnd_7534180 < baseStart_7534180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534203 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 2, 4]
def baseStart_7534203 : Nat := 118140960795 + 7534203 * 2 ^ 59
def prefixEnd_7534203 : Nat := 4983230072969 + 3 ^ 40 * 7534203 * 2
def baseEnd_7534203 : Nat := 1289555829182163709937779

theorem tailTrace_7534203 : CollatzResearch.WordTrace tailWord_7534203 prefixEnd_7534203 1289555829182163709937779 := by
  unfold tailWord_7534203
  simp only [CollatzResearch.WordTrace]
  refine ⟨274794958723876745274951263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183196639149251163516634175 274794958723876745274951263)
  ·
    refine ⟨412192438085815117912426895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274794958723876745274951263 412192438085815117912426895)
    ·
      refine ⟨618288657128722676868640343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412192438085815117912426895 618288657128722676868640343)
      ·
        refine ⟨927432985693084015302960515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618288657128722676868640343 927432985693084015302960515)
        ·
          refine ⟨1391149478539626022954440773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927432985693084015302960515 1391149478539626022954440773)
          ·
            refine ⟨260840527226179879303957645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1391149478539626022954440773 260840527226179879303957645)
            ·
              refine ⟨97815197709817454738984117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260840527226179879303957645 97815197709817454738984117)
              ·
                refine ⟨9170174785295386381779761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97815197709817454738984117 9170174785295386381779761)
                ·
                  refine ⟨6877631088971539786334821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9170174785295386381779761 6877631088971539786334821)
                  ·
                    refine ⟨1289555829182163709937779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877631088971539786334821 1289555829182163709937779)
                    ·
                      rfl

theorem cell23_7534203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 4].length) (baseStart_7534203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534203 prefixEnd_7534203 := by exact prefixLift 7534203
  have htrace : WordTrace (prefixWord ++ tailWord_7534203) baseStart_7534203 baseEnd_7534203 := by
    simpa [prefixWord, tailWord_7534203, baseEnd_7534203] using wordTrace_append hprefix tailTrace_7534203
  have hstable : (prefixWord ++ tailWord_7534203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534203).length < 2 ^ (prefixWord ++ tailWord_7534203).sum := by decide
  have hdescent : baseEnd_7534203 < baseStart_7534203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534213 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_7534213 : Nat := 118140960795 + 7534213 * 2 ^ 59
def prefixEnd_7534213 : Nat := 4983230072969 + 3 ^ 40 * 7534213 * 2
def baseEnd_7534213 : Nat := 3868672622353036090688291

theorem tailTrace_7534213 : CollatzResearch.WordTrace tailWord_7534213 prefixEnd_7534213 3868672622353036090688291 := by
  unfold tailWord_7534213
  simp only [CollatzResearch.WordTrace]
  refine ⟨274795323453840516982815293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183196882302560344655210195 274795323453840516982815293)
  ·
    refine ⟨103048246295190193868555735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274795323453840516982815293 103048246295190193868555735)
    ·
      refine ⟨154572369442785290802833603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103048246295190193868555735 154572369442785290802833603)
      ·
        refine ⟨231858554164177936204250405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154572369442785290802833603 231858554164177936204250405)
        ·
          refine ⟨43473478905783363038296951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231858554164177936204250405 43473478905783363038296951)
          ·
            refine ⟨65210218358675044557445427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43473478905783363038296951 65210218358675044557445427)
            ·
              refine ⟨97815327538012566836168141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65210218358675044557445427 97815327538012566836168141)
              ·
                refine ⟨36680747826754712563563053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97815327538012566836168141 36680747826754712563563053)
                ·
                  refine ⟨13755280435033017211336145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36680747826754712563563053 13755280435033017211336145)
                  ·
                    refine ⟨10316460326274762908502109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13755280435033017211336145 10316460326274762908502109)
                    ·
                      refine ⟨3868672622353036090688291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316460326274762908502109 3868672622353036090688291)
                      ·
                        rfl

theorem cell23_7534213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_7534213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534213 prefixEnd_7534213 := by exact prefixLift 7534213
  have htrace : WordTrace (prefixWord ++ tailWord_7534213) baseStart_7534213 baseEnd_7534213 := by
    simpa [prefixWord, tailWord_7534213, baseEnd_7534213] using wordTrace_append hprefix tailTrace_7534213
  have hstable : (prefixWord ++ tailWord_7534213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534213).length < 2 ^ (prefixWord ++ tailWord_7534213).sum := by decide
  have hdescent : baseEnd_7534213 < baseStart_7534213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534244 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_7534244 : Nat := 118140960795 + 7534244 * 2 ^ 59
def prefixEnd_7534244 : Nat := 4983230072969 + 3 ^ 40 * 7534244 * 2
def baseEnd_7534244 : Nat := 3868688540253325469400649

theorem tailTrace_7534244 : CollatzResearch.WordTrace tailWord_7534244 prefixEnd_7534244 3868688540253325469400649 := by
  unfold tailWord_7534244
  simp only [CollatzResearch.WordTrace]
  refine ⟨137398227058364104638596893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183197636077818806184795857 137398227058364104638596893)
  ·
    refine ⟨51524335146886539239473835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137398227058364104638596893 51524335146886539239473835)
    ·
      refine ⟨77286502720329808859210753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51524335146886539239473835 77286502720329808859210753)
      ·
        refine ⟨57964877040247356644408065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77286502720329808859210753 57964877040247356644408065)
        ·
          refine ⟨43473657780185517483306049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57964877040247356644408065 43473657780185517483306049)
          ·
            refine ⟨32605243335139138112479537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43473657780185517483306049 32605243335139138112479537)
            ·
              refine ⟨24453932501354353584359653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32605243335139138112479537 24453932501354353584359653)
              ·
                refine ⟨4585112344003941297067435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24453932501354353584359653 4585112344003941297067435)
                ·
                  refine ⟨6877668516005911945601153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585112344003941297067435 6877668516005911945601153)
                  ·
                    refine ⟨5158251387004433959200865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6877668516005911945601153 5158251387004433959200865)
                    ·
                      refine ⟨3868688540253325469400649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158251387004433959200865 3868688540253325469400649)
                      ·
                        rfl

theorem cell23_7534244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_7534244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534244 prefixEnd_7534244 := by exact prefixLift 7534244
  have htrace : WordTrace (prefixWord ++ tailWord_7534244) baseStart_7534244 baseEnd_7534244 := by
    simpa [prefixWord, tailWord_7534244, baseEnd_7534244] using wordTrace_append hprefix tailTrace_7534244
  have hstable : (prefixWord ++ tailWord_7534244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534244).length < 2 ^ (prefixWord ++ tailWord_7534244).sum := by decide
  have hdescent : baseEnd_7534244 < baseStart_7534244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534254 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7534254 : Nat := 118140960795 + 7534254 * 2 ^ 59
def prefixEnd_7534254 : Nat := 4983230072969 + 3 ^ 40 * 7534254 * 2
def baseEnd_7534254 : Nat := 1289564558353290143425201

theorem tailTrace_7534254 : CollatzResearch.WordTrace tailWord_7534254 prefixEnd_7534254 1289564558353290143425201 := by
  unfold tailWord_7534254
  simp only [CollatzResearch.WordTrace]
  refine ⟨34349602355836497623132227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183197879231127987323371877 34349602355836497623132227)
  ·
    refine ⟨51524403533754746434698341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34349602355836497623132227 51524403533754746434698341)
    ·
      refine ⟨9660825662579014956505939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51524403533754746434698341 9660825662579014956505939)
      ·
        refine ⟨14491238493868522434758909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660825662579014956505939 14491238493868522434758909)
        ·
          refine ⟨5434214435200695913034591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14491238493868522434758909 5434214435200695913034591)
          ·
            refine ⟨8151321652801043869551887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434214435200695913034591 8151321652801043869551887)
            ·
              refine ⟨12226982479201565804327831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151321652801043869551887 12226982479201565804327831)
              ·
                refine ⟨18340473718802348706491747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12226982479201565804327831 18340473718802348706491747)
                ·
                  refine ⟨27510710578203523059737621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18340473718802348706491747 27510710578203523059737621)
                  ·
                    refine ⟨1289564558353290143425201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27510710578203523059737621 1289564558353290143425201)
                    ·
                      rfl

theorem cell23_7534254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7534254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534254 prefixEnd_7534254 := by exact prefixLift 7534254
  have htrace : WordTrace (prefixWord ++ tailWord_7534254) baseStart_7534254 baseEnd_7534254 := by
    simpa [prefixWord, tailWord_7534254, baseEnd_7534254] using wordTrace_append hprefix tailTrace_7534254
  have hstable : (prefixWord ++ tailWord_7534254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534254).length < 2 ^ (prefixWord ++ tailWord_7534254).sum := by decide
  have hdescent : baseEnd_7534254 < baseStart_7534254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534303 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_7534303 : Nat := 118140960795 + 7534303 * 2 ^ 59
def prefixEnd_7534303 : Nat := 4983230072969 + 3 ^ 40 * 7534303 * 2
def baseEnd_7534303 : Nat := 3868718835611940738562877

theorem tailTrace_7534303 : CollatzResearch.WordTrace tailWord_7534303 prefixEnd_7534303 3868718835611940738562877 := by
  unfold tailWord_7534303
  simp only [CollatzResearch.WordTrace]
  refine ⟨274798606023514462353591563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183199070682342974902394375 274798606023514462353591563)
  ·
    refine ⟨412197909035271693530387345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274798606023514462353591563 412197909035271693530387345)
    ·
      refine ⟨309148431776453770147790509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412197909035271693530387345 309148431776453770147790509)
      ·
        refine ⟨115930661916170163805421441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309148431776453770147790509 115930661916170163805421441)
        ·
          refine ⟨86947996437127622854066081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115930661916170163805421441 86947996437127622854066081)
          ·
            refine ⟨65210997327845717140549561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86947996437127622854066081 65210997327845717140549561)
            ·
              refine ⟨48908247995884287855412171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65210997327845717140549561 48908247995884287855412171)
              ·
                refine ⟨73362371993826431783118257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48908247995884287855412171 73362371993826431783118257)
                ·
                  refine ⟨55021778995369823837338693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73362371993826431783118257 55021778995369823837338693)
                  ·
                    refine ⟨10316583561631841969501005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55021778995369823837338693 10316583561631841969501005)
                    ·
                      refine ⟨3868718835611940738562877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316583561631841969501005 3868718835611940738562877)
                      ·
                        rfl

theorem cell23_7534303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_7534303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534303 prefixEnd_7534303 := by exact prefixLift 7534303
  have htrace : WordTrace (prefixWord ++ tailWord_7534303) baseStart_7534303 baseEnd_7534303 := by
    simpa [prefixWord, tailWord_7534303, baseEnd_7534303] using wordTrace_append hprefix tailTrace_7534303
  have hstable : (prefixWord ++ tailWord_7534303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534303).length < 2 ^ (prefixWord ++ tailWord_7534303).sum := by decide
  have hdescent : baseEnd_7534303 < baseStart_7534303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534333 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_7534333 : Nat := 118140960795 + 7534333 * 2 ^ 59
def prefixEnd_7534333 : Nat := 4983230072969 + 3 ^ 40 * 7534333 * 2
def baseEnd_7534333 : Nat := 3868734240031575621187739

theorem tailTrace_7534333 : CollatzResearch.WordTrace tailWord_7534333 prefixEnd_7534333 3868734240031575621187739 := by
  unfold tailWord_7534333
  simp only [CollatzResearch.WordTrace]
  refine ⟨274799700213405777477183653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183199800142270518318122435 274799700213405777477183653)
  ·
    refine ⟨51524943790013583276971935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274799700213405777477183653 51524943790013583276971935)
    ·
      refine ⟨77287415685020374915457903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51524943790013583276971935 77287415685020374915457903)
      ·
        refine ⟨115931123527530562373186855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77287415685020374915457903 115931123527530562373186855)
        ·
          refine ⟨173896685291295843559780283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115931123527530562373186855 173896685291295843559780283)
          ·
            refine ⟨260845027936943765339670425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173896685291295843559780283 260845027936943765339670425)
            ·
              refine ⟨195633770952707824004752819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260845027936943765339670425 195633770952707824004752819)
              ·
                refine ⟨293450656429061736007129229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195633770952707824004752819 293450656429061736007129229)
                ·
                  refine ⟨110043996160898151002673461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293450656429061736007129229 110043996160898151002673461)
                  ·
                    refine ⟨10316624640084201656500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110043996160898151002673461 10316624640084201656500637)
                    ·
                      refine ⟨3868734240031575621187739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316624640084201656500637 3868734240031575621187739)
                      ·
                        rfl

theorem cell23_7534333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_7534333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534333 prefixEnd_7534333 := by exact prefixLift 7534333
  have htrace : WordTrace (prefixWord ++ tailWord_7534333) baseStart_7534333 baseEnd_7534333 := by
    simpa [prefixWord, tailWord_7534333, baseEnd_7534333] using wordTrace_append hprefix tailTrace_7534333
  have hstable : (prefixWord ++ tailWord_7534333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534333).length < 2 ^ (prefixWord ++ tailWord_7534333).sum := by decide
  have hdescent : baseEnd_7534333 < baseStart_7534333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534334 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7534334 : Nat := 118140960795 + 7534334 * 2 ^ 59
def prefixEnd_7534334 : Nat := 4983230072969 + 3 ^ 40 * 7534334 * 2
def baseEnd_7534334 : Nat := 3868734753512230117275235

theorem tailTrace_7534334 : CollatzResearch.WordTrace tailWord_7534334 prefixEnd_7534334 3868734753512230117275235 := by
  unfold tailWord_7534334
  simp only [CollatzResearch.WordTrace]
  refine ⟨34349967085800269330996257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183199824457601436431980037 34349967085800269330996257)
  ·
    refine ⟨25762475314350201998247193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34349967085800269330996257 25762475314350201998247193)
    ·
      refine ⟨19321856485762651498685395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25762475314350201998247193 19321856485762651498685395)
      ·
        refine ⟨28982784728643977248028093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19321856485762651498685395 28982784728643977248028093)
        ·
          refine ⟨10868544273241491468010535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28982784728643977248028093 10868544273241491468010535)
          ·
            refine ⟨16302816409862237202015803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868544273241491468010535 16302816409862237202015803)
            ·
              refine ⟨24454224614793355803023705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16302816409862237202015803 24454224614793355803023705)
              ·
                refine ⟨18340668461095016852267779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24454224614793355803023705 18340668461095016852267779)
                ·
                  refine ⟨27511002691642525278401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18340668461095016852267779 27511002691642525278401669)
                  ·
                    refine ⟨5158313004682973489700313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27511002691642525278401669 5158313004682973489700313)
                    ·
                      refine ⟨3868734753512230117275235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158313004682973489700313 3868734753512230117275235)
                      ·
                        rfl

theorem cell23_7534334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7534334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534334 prefixEnd_7534334 := by exact prefixLift 7534334
  have htrace : WordTrace (prefixWord ++ tailWord_7534334) baseStart_7534334 baseEnd_7534334 := by
    simpa [prefixWord, tailWord_7534334, baseEnd_7534334] using wordTrace_append hprefix tailTrace_7534334
  have hstable : (prefixWord ++ tailWord_7534334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534334).length < 2 ^ (prefixWord ++ tailWord_7534334).sum := by decide
  have hdescent : baseEnd_7534334 < baseStart_7534334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534357 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 5]
def baseStart_7534357 : Nat := 118140960795 + 7534357 * 2 ^ 59
def prefixEnd_7534357 : Nat := 4983230072969 + 3 ^ 40 * 7534357 * 2
def baseEnd_7534357 : Nat := 429860729285253725254181

theorem tailTrace_7534357 : CollatzResearch.WordTrace tailWord_7534357 prefixEnd_7534357 429860729285253725254181 := by
  unfold tailWord_7534357
  simp only [CollatzResearch.WordTrace]
  refine ⟨274800575565318829576057325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183200383710212553050704883 274800575565318829576057325)
  ·
    refine ⟨103050215836994561091021497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274800575565318829576057325 103050215836994561091021497)
    ·
      refine ⟨77287661877745920818266123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103050215836994561091021497 77287661877745920818266123)
      ·
        refine ⟨115931492816618881227399185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77287661877745920818266123 115931492816618881227399185)
        ·
          refine ⟨86948619612464160920549389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115931492816618881227399185 86948619612464160920549389)
          ·
            refine ⟨32605732354674060345206021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86948619612464160920549389 32605732354674060345206021)
            ·
              refine ⟨6113574816501386314726129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32605732354674060345206021 6113574816501386314726129)
              ·
                refine ⟨4585181112376039736044597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113574816501386314726129 4585181112376039736044597)
                ·
                  refine ⟨429860729285253725254181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585181112376039736044597 429860729285253725254181)
                  ·
                    rfl

theorem cell23_7534357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_7534357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534357 prefixEnd_7534357 := by exact prefixLift 7534357
  have htrace : WordTrace (prefixWord ++ tailWord_7534357) baseStart_7534357 baseEnd_7534357 := by
    simpa [prefixWord, tailWord_7534357, baseEnd_7534357] using wordTrace_append hprefix tailTrace_7534357
  have hstable : (prefixWord ++ tailWord_7534357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534357).length < 2 ^ (prefixWord ++ tailWord_7534357).sum := by decide
  have hdescent : baseEnd_7534357 < baseStart_7534357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534360 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_7534360 : Nat := 118140960795 + 7534360 * 2 ^ 59
def prefixEnd_7534360 : Nat := 4983230072969 + 3 ^ 40 * 7534360 * 2
def baseEnd_7534360 : Nat := 3868748104009247015550115

theorem tailTrace_7534360 : CollatzResearch.WordTrace tailWord_7534360 prefixEnd_7534360 3868748104009247015550115 := by
  unfold tailWord_7534360
  simp only [CollatzResearch.WordTrace]
  refine ⟨137400342492153980544208267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183200456656205307392277689 137400342492153980544208267)
  ·
    refine ⟨206100513738230970816312401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137400342492153980544208267 206100513738230970816312401)
    ·
      refine ⟨154575385303673228112234301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206100513738230970816312401 154575385303673228112234301)
      ·
        refine ⟨57965769488877460542087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154575385303673228112234301 57965769488877460542087863)
        ·
          refine ⟨86948654233316190813131795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57965769488877460542087863 86948654233316190813131795)
          ·
            refine ⟨130422981349974286219697693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86948654233316190813131795 130422981349974286219697693)
            ·
              refine ⟨48908618006240357332386635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130422981349974286219697693 48908618006240357332386635)
              ·
                refine ⟨73362927009360535998579953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48908618006240357332386635 73362927009360535998579953)
                ·
                  refine ⟨55022195257020401998934965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73362927009360535998579953 55022195257020401998934965)
                  ·
                    refine ⟨5158330805345662687400153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55022195257020401998934965 5158330805345662687400153)
                    ·
                      refine ⟨3868748104009247015550115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158330805345662687400153 3868748104009247015550115)
                      ·
                        rfl

theorem cell23_7534360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_7534360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534360 prefixEnd_7534360 := by exact prefixLift 7534360
  have htrace : WordTrace (prefixWord ++ tailWord_7534360) baseStart_7534360 baseEnd_7534360 := by
    simpa [prefixWord, tailWord_7534360, baseEnd_7534360] using wordTrace_append hprefix tailTrace_7534360
  have hstable : (prefixWord ++ tailWord_7534360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534360).length < 2 ^ (prefixWord ++ tailWord_7534360).sum := by decide
  have hdescent : baseEnd_7534360 < baseStart_7534360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534387 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 2, 5]
def baseStart_7534387 : Nat := 118140960795 + 7534387 * 2 ^ 59
def prefixEnd_7534387 : Nat := 4983230072969 + 3 ^ 40 * 7534387 * 2
def baseEnd_7534387 : Nat := 1289587322662306136637497

theorem tailTrace_7534387 : CollatzResearch.WordTrace tailWord_7534387 prefixEnd_7534387 1289587322662306136637497 := by
  unfold tailWord_7534387
  simp only [CollatzResearch.WordTrace]
  refine ⟨274801669755210144699649415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183201113170140096466432943 274801669755210144699649415)
  ·
    refine ⟨412202504632815217049474123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274801669755210144699649415 412202504632815217049474123)
    ·
      refine ⟨618303756949222825574211185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412202504632815217049474123 618303756949222825574211185)
      ·
        refine ⟨463727817711917119180658389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618303756949222825574211185 463727817711917119180658389)
        ·
          refine ⟨10868620727623057480796681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 463727817711917119180658389 10868620727623057480796681)
          ·
            refine ⟨8151465545717293110597511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10868620727623057480796681 8151465545717293110597511)
            ·
              refine ⟨12227198318575939665896267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151465545717293110597511 12227198318575939665896267)
              ·
                refine ⟨18340797477863909498844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227198318575939665896267 18340797477863909498844401)
                ·
                  refine ⟨13755598108397932124133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18340797477863909498844401 13755598108397932124133301)
                  ·
                    refine ⟨1289587322662306136637497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13755598108397932124133301 1289587322662306136637497)
                    ·
                      rfl

theorem cell23_7534387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 5].length) (baseStart_7534387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534387 prefixEnd_7534387 := by exact prefixLift 7534387
  have htrace : WordTrace (prefixWord ++ tailWord_7534387) baseStart_7534387 baseEnd_7534387 := by
    simpa [prefixWord, tailWord_7534387, baseEnd_7534387] using wordTrace_append hprefix tailTrace_7534387
  have hstable : (prefixWord ++ tailWord_7534387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534387).length < 2 ^ (prefixWord ++ tailWord_7534387).sum := by decide
  have hdescent : baseEnd_7534387 < baseStart_7534387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534403 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_7534403 : Nat := 118140960795 + 7534403 * 2 ^ 59
def prefixEnd_7534403 : Nat := 4983230072969 + 3 ^ 40 * 7534403 * 2
def baseEnd_7534403 : Nat := 3868770183677390347312417

theorem tailTrace_7534403 : CollatzResearch.WordTrace tailWord_7534403 prefixEnd_7534403 3868770183677390347312417 := by
  unfold tailWord_7534403
  simp only [CollatzResearch.WordTrace]
  refine ⟨274802253323152179432231863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183201502215434786288154575 274802253323152179432231863)
  ·
    refine ⟨412203379984728269148347795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274802253323152179432231863 412203379984728269148347795)
    ·
      refine ⟨618305069977092403722521693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412203379984728269148347795 618305069977092403722521693)
      ·
        refine ⟨231864401241409651395945635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618305069977092403722521693 231864401241409651395945635)
        ·
          refine ⟨347796601862114477093918453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231864401241409651395945635 347796601862114477093918453)
          ·
            refine ⟨32605931424573232227554855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347796601862114477093918453 32605931424573232227554855)
            ·
              refine ⟨48908897136859848341332283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32605931424573232227554855 48908897136859848341332283)
              ·
                refine ⟨73363345705289772511998425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48908897136859848341332283 73363345705289772511998425)
                ·
                  refine ⟨55022509278967329383998819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73363345705289772511998425 55022509278967329383998819)
                  ·
                    refine ⟨82533763918450994075998229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55022509278967329383998819 82533763918450994075998229)
                    ·
                      refine ⟨3868770183677390347312417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82533763918450994075998229 3868770183677390347312417)
                      ·
                        rfl

theorem cell23_7534403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_7534403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534403 prefixEnd_7534403 := by exact prefixLift 7534403
  have htrace : WordTrace (prefixWord ++ tailWord_7534403) baseStart_7534403 baseEnd_7534403 := by
    simpa [prefixWord, tailWord_7534403, baseEnd_7534403] using wordTrace_append hprefix tailTrace_7534403
  have hstable : (prefixWord ++ tailWord_7534403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534403).length < 2 ^ (prefixWord ++ tailWord_7534403).sum := by decide
  have hdescent : baseEnd_7534403 < baseStart_7534403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534410 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_7534410 : Nat := 118140960795 + 7534410 * 2 ^ 59
def prefixEnd_7534410 : Nat := 4983230072969 + 3 ^ 40 * 7534410 * 2
def baseEnd_7534410 : Nat := 3868773778041971819924885

theorem tailTrace_7534410 : CollatzResearch.WordTrace tailWord_7534410 prefixEnd_7534410 3868773778041971819924885 := by
  unfold tailWord_7534410
  simp only [CollatzResearch.WordTrace]
  refine ⟨68700627158531704906934171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183201672422751213085157789 68700627158531704906934171)
  ·
    refine ⟨103050940737797557360401257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68700627158531704906934171 103050940737797557360401257)
    ·
      refine ⟨77288205553348168020300943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103050940737797557360401257 77288205553348168020300943)
      ·
        refine ⟨115932308330022252030451415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77288205553348168020300943 115932308330022252030451415)
        ·
          refine ⟨173898462495033378045677123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115932308330022252030451415 173898462495033378045677123)
          ·
            refine ⟨260847693742550067068515685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173898462495033378045677123 260847693742550067068515685)
            ·
              refine ⟨48908942576728137575346691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260847693742550067068515685 48908942576728137575346691)
              ·
                refine ⟨73363413865092206363020037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48908942576728137575346691 73363413865092206363020037)
                ·
                  refine ⟨13755640099704788693066257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73363413865092206363020037 13755640099704788693066257)
                  ·
                    refine ⟨10316730074778591519799693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13755640099704788693066257 10316730074778591519799693)
                    ·
                      refine ⟨3868773778041971819924885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316730074778591519799693 3868773778041971819924885)
                      ·
                        rfl

theorem cell23_7534410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_7534410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534410 prefixEnd_7534410 := by exact prefixLift 7534410
  have htrace : WordTrace (prefixWord ++ tailWord_7534410) baseStart_7534410 baseEnd_7534410 := by
    simpa [prefixWord, tailWord_7534410, baseEnd_7534410] using wordTrace_append hprefix tailTrace_7534410
  have hstable : (prefixWord ++ tailWord_7534410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534410).length < 2 ^ (prefixWord ++ tailWord_7534410).sum := by decide
  have hdescent : baseEnd_7534410 < baseStart_7534410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534417 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_7534417 : Nat := 118140960795 + 7534417 * 2 ^ 59
def prefixEnd_7534417 : Nat := 4983230072969 + 3 ^ 40 * 7534417 * 2
def baseEnd_7534417 : Nat := 1289592457468851097512451

theorem tailTrace_7534417 : CollatzResearch.WordTrace tailWord_7534417 prefixEnd_7534417 1289592457468851097512451 := by
  unfold tailWord_7534417
  simp only [CollatzResearch.WordTrace]
  refine ⟨274802763945101459823241505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183201842630067639882161003 274802763945101459823241505)
  ·
    refine ⟨206102072958826094867431129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274802763945101459823241505 206102072958826094867431129)
    ·
      refine ⟨154576554719119571150573347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206102072958826094867431129 154576554719119571150573347)
      ·
        refine ⟨231864832078679356725860021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154576554719119571150573347 231864832078679356725860021)
        ·
          refine ⟨21737328007376189693049377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231864832078679356725860021 21737328007376189693049377)
          ·
            refine ⟨16302996005532142269787033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21737328007376189693049377 16302996005532142269787033)
            ·
              refine ⟨12227247004149106702340275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16302996005532142269787033 12227247004149106702340275)
              ·
                refine ⟨18340870506223660053510413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227247004149106702340275 18340870506223660053510413)
                ·
                  refine ⟨6877826439833872520066405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18340870506223660053510413 6877826439833872520066405)
                  ·
                    refine ⟨1289592457468851097512451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877826439833872520066405 1289592457468851097512451)
                    ·
                      rfl

theorem cell23_7534417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_7534417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534417 prefixEnd_7534417 := by exact prefixLift 7534417
  have htrace : WordTrace (prefixWord ++ tailWord_7534417) baseStart_7534417 baseEnd_7534417 := by
    simpa [prefixWord, tailWord_7534417, baseEnd_7534417] using wordTrace_append hprefix tailTrace_7534417
  have hstable : (prefixWord ++ tailWord_7534417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534417).length < 2 ^ (prefixWord ++ tailWord_7534417).sum := by decide
  have hdescent : baseEnd_7534417 < baseStart_7534417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534433 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7534433 : Nat := 118140960795 + 7534433 * 2 ^ 59
def prefixEnd_7534433 : Nat := 4983230072969 + 3 ^ 40 * 7534433 * 2
def baseEnd_7534433 : Nat := 3868785588097025229937279

theorem tailTrace_7534433 : CollatzResearch.WordTrace tailWord_7534433 prefixEnd_7534433 3868785588097025229937279 := by
  unfold tailWord_7534433
  simp only [CollatzResearch.WordTrace]
  refine ⟨274803347513043494555823953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183202231675362329703882635 274803347513043494555823953)
  ·
    refine ⟨206102510634782620916867965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274803347513043494555823953 206102510634782620916867965)
    ·
      refine ⟨77288441488043482843825487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206102510634782620916867965 77288441488043482843825487)
      ·
        refine ⟨115932662232065224265738231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77288441488043482843825487 115932662232065224265738231)
        ·
          refine ⟨173898993348097836398607347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115932662232065224265738231 173898993348097836398607347)
          ·
            refine ⟨260848490022146754597911021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173898993348097836398607347 260848490022146754597911021)
            ·
              refine ⟨97818183758305032974216633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260848490022146754597911021 97818183758305032974216633)
              ·
                refine ⟨73363637818728774730662475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97818183758305032974216633 73363637818728774730662475)
                ·
                  refine ⟨110045456728093162095993713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73363637818728774730662475 110045456728093162095993713)
                  ·
                    refine ⟨82534092546069871571995285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110045456728093162095993713 82534092546069871571995285)
                    ·
                      refine ⟨3868785588097025229937279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82534092546069871571995285 3868785588097025229937279)
                      ·
                        rfl

theorem cell23_7534433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7534433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534433 prefixEnd_7534433 := by exact prefixLift 7534433
  have htrace : WordTrace (prefixWord ++ tailWord_7534433) baseStart_7534433 baseEnd_7534433 := by
    simpa [prefixWord, tailWord_7534433, baseEnd_7534433] using wordTrace_append hprefix tailTrace_7534433
  have hstable : (prefixWord ++ tailWord_7534433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534433).length < 2 ^ (prefixWord ++ tailWord_7534433).sum := by decide
  have hdescent : baseEnd_7534433 < baseStart_7534433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534440 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7534440 : Nat := 118140960795 + 7534440 * 2 ^ 59
def prefixEnd_7534440 : Nat := 4983230072969 + 3 ^ 40 * 7534440 * 2
def baseEnd_7534440 : Nat := 3868789182461606702549747

theorem tailTrace_7534440 : CollatzResearch.WordTrace tailWord_7534440 prefixEnd_7534440 3868789182461606702549747 := by
  unfold tailWord_7534440
  simp only [CollatzResearch.WordTrace]
  refine ⟨137401801412009067375664387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183202401882678756500885849 137401801412009067375664387)
  ·
    refine ⟨206102702118013601063496581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137401801412009067375664387 206102702118013601063496581)
    ·
      refine ⟨38644256647127550199405609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206102702118013601063496581 38644256647127550199405609)
      ·
        refine ⟨28983192485345662649554207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38644256647127550199405609 28983192485345662649554207)
        ·
          refine ⟨43474788728018493974331311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28983192485345662649554207 43474788728018493974331311)
          ·
            refine ⟨65212183092027740961496967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43474788728018493974331311 65212183092027740961496967)
            ·
              refine ⟨97818274638041611442245451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65212183092027740961496967 97818274638041611442245451)
              ·
                refine ⟨146727411957062417163368177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97818274638041611442245451 146727411957062417163368177)
                ·
                  refine ⟨110045558967796812872526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146727411957062417163368177 110045558967796812872526133)
                  ·
                    refine ⟨10316771153230951206799325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110045558967796812872526133 10316771153230951206799325)
                    ·
                      refine ⟨3868789182461606702549747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10316771153230951206799325 3868789182461606702549747)
                      ·
                        rfl

theorem cell23_7534440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7534440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534440 prefixEnd_7534440 := by exact prefixLift 7534440
  have htrace : WordTrace (prefixWord ++ tailWord_7534440) baseStart_7534440 baseEnd_7534440 := by
    simpa [prefixWord, tailWord_7534440, baseEnd_7534440] using wordTrace_append hprefix tailTrace_7534440
  have hstable : (prefixWord ++ tailWord_7534440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534440).length < 2 ^ (prefixWord ++ tailWord_7534440).sum := by decide
  have hdescent : baseEnd_7534440 < baseStart_7534440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534467 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 4, 3, 2]
def baseStart_7534467 : Nat := 118140960795 + 7534467 * 2 ^ 59
def prefixEnd_7534467 : Nat := 4983230072969 + 3 ^ 40 * 7534467 * 2
def baseEnd_7534467 : Nat := 3868803046439278096912123

theorem tailTrace_7534467 : CollatzResearch.WordTrace tailWord_7534467 prefixEnd_7534467 3868803046439278096912123 := by
  unfold tailWord_7534467
  simp only [CollatzResearch.WordTrace]
  refine ⟨274804587594920318362561655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183203058396613545575041103 274804587594920318362561655)
  ·
    refine ⟨412206881392380477543842483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274804587594920318362561655 412206881392380477543842483)
    ·
      refine ⟨618310322088570716315763725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412206881392380477543842483 618310322088570716315763725)
      ·
        refine ⟨231866370783214018618411397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618310322088570716315763725 231866370783214018618411397)
        ·
          refine ⟨43474944521852628490952137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231866370783214018618411397 43474944521852628490952137)
          ·
            refine ⟨32606208391389471368214103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43474944521852628490952137 32606208391389471368214103)
            ·
              refine ⟨48909312587084207052321155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32606208391389471368214103 48909312587084207052321155)
              ·
                refine ⟨73363968880626310578481733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48909312587084207052321155 73363968880626310578481733)
                ·
                  refine ⟨13755744165117433233465325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73363968880626310578481733 13755744165117433233465325)
                  ·
                    refine ⟨5158404061919037462549497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13755744165117433233465325 5158404061919037462549497)
                    ·
                      refine ⟨3868803046439278096912123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158404061919037462549497 3868803046439278096912123)
                      ·
                        rfl

theorem cell23_7534467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_7534467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534467 prefixEnd_7534467 := by exact prefixLift 7534467
  have htrace : WordTrace (prefixWord ++ tailWord_7534467) baseStart_7534467 baseEnd_7534467 := by
    simpa [prefixWord, tailWord_7534467, baseEnd_7534467] using wordTrace_append hprefix tailTrace_7534467
  have hstable : (prefixWord ++ tailWord_7534467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534467).length < 2 ^ (prefixWord ++ tailWord_7534467).sum := by decide
  have hdescent : baseEnd_7534467 < baseStart_7534467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534483 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_7534483 : Nat := 118140960795 + 7534483 * 2 ^ 59
def prefixEnd_7534483 : Nat := 4983230072969 + 3 ^ 40 * 7534483 * 2
def baseEnd_7534483 : Nat := 3868811262129750034312049

theorem tailTrace_7534483 : CollatzResearch.WordTrace tailWord_7534483 prefixEnd_7534483 3868811262129750034312049 := by
  unfold tailWord_7534483
  simp only [CollatzResearch.WordTrace]
  refine ⟨274805171162862353095144103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183203447441908235396762735 274805171162862353095144103)
  ·
    refine ⟨412207756744293529642716155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274805171162862353095144103 412207756744293529642716155)
    ·
      refine ⟨618311635116440294464074233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412207756744293529642716155 618311635116440294464074233)
      ·
        refine ⟨463733726337330220848055675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618311635116440294464074233 463733726337330220848055675)
        ·
          refine ⟨695600589505995331272083513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463733726337330220848055675 695600589505995331272083513)
          ·
            refine ⟨521700442129496498454062635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695600589505995331272083513 521700442129496498454062635)
            ·
              refine ⟨782550663194244747681093953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521700442129496498454062635 782550663194244747681093953)
              ·
                refine ⟨586912997395683560760820465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782550663194244747681093953 586912997395683560760820465)
                ·
                  refine ⟨440184748046762670570615349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586912997395683560760820465 440184748046762670570615349)
                  ·
                    refine ⟨41267320129384000365995189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 440184748046762670570615349 41267320129384000365995189)
                    ·
                      refine ⟨3868811262129750034312049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41267320129384000365995189 3868811262129750034312049)
                      ·
                        rfl

theorem cell23_7534483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_7534483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534483 prefixEnd_7534483 := by exact prefixLift 7534483
  have htrace : WordTrace (prefixWord ++ tailWord_7534483) baseStart_7534483 baseEnd_7534483 := by
    simpa [prefixWord, tailWord_7534483, baseEnd_7534483] using wordTrace_append hprefix tailTrace_7534483
  have hstable : (prefixWord ++ tailWord_7534483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534483).length < 2 ^ (prefixWord ++ tailWord_7534483).sum := by decide
  have hdescent : baseEnd_7534483 < baseStart_7534483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534517 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7534517 : Nat := 118140960795 + 7534517 * 2 ^ 59
def prefixEnd_7534517 : Nat := 4983230072969 + 3 ^ 40 * 7534517 * 2
def baseEnd_7534517 : Nat := 3868828720472002901286893

theorem tailTrace_7534517 : CollatzResearch.WordTrace tailWord_7534517 prefixEnd_7534517 3868828720472002901286893 := by
  unfold tailWord_7534517
  simp only [CollatzResearch.WordTrace]
  refine ⟨274806411244739176901881805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183204274163159451267921203 274806411244739176901881805)
  ·
    refine ⟨103052404216777191338205677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274806411244739176901881805 103052404216777191338205677)
    ·
      refine ⟨38644651581291446751827129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103052404216777191338205677 38644651581291446751827129)
      ·
        refine ⟨28983488685968585063870347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38644651581291446751827129 28983488685968585063870347)
        ·
          refine ⟨43475233028952877595805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28983488685968585063870347 43475233028952877595805521)
          ·
            refine ⟨32606424771714658196854141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43475233028952877595805521 32606424771714658196854141)
            ·
              refine ⟨12227409289392996823820303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32606424771714658196854141 12227409289392996823820303)
              ·
                refine ⟨18341113934089495235730455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227409289392996823820303 18341113934089495235730455)
                ·
                  refine ⟨27511670901134242853595683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18341113934089495235730455 27511670901134242853595683)
                  ·
                    refine ⟨41267506351701364280393525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27511670901134242853595683 41267506351701364280393525)
                    ·
                      refine ⟨3868828720472002901286893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41267506351701364280393525 3868828720472002901286893)
                      ·
                        rfl

theorem cell23_7534517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7534517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534517 prefixEnd_7534517 := by exact prefixLift 7534517
  have htrace : WordTrace (prefixWord ++ tailWord_7534517) baseStart_7534517 baseEnd_7534517 := by
    simpa [prefixWord, tailWord_7534517, baseEnd_7534517] using wordTrace_append hprefix tailTrace_7534517
  have hstable : (prefixWord ++ tailWord_7534517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534517).length < 2 ^ (prefixWord ++ tailWord_7534517).sum := by decide
  have hdescent : baseEnd_7534517 < baseStart_7534517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534587 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 4, 2]
def baseStart_7534587 : Nat := 118140960795 + 7534587 * 2 ^ 59
def prefixEnd_7534587 : Nat := 4983230072969 + 3 ^ 40 * 7534587 * 2
def baseEnd_7534587 : Nat := 3868864664117817627411571

theorem tailTrace_7534587 : CollatzResearch.WordTrace tailWord_7534587 prefixEnd_7534587 3868864664117817627411571 := by
  unfold tailWord_7534587
  simp only [CollatzResearch.WordTrace]
  refine ⟨274808964354485578856930015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183205976236323719237953343 274808964354485578856930015)
  ·
    refine ⟨412213446531728368285395023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274808964354485578856930015 412213446531728368285395023)
    ·
      refine ⟨618320169797592552428092535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412213446531728368285395023 618320169797592552428092535)
      ·
        refine ⟨927480254696388828642138803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618320169797592552428092535 927480254696388828642138803)
        ·
          refine ⟨1391220382044583242963208205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927480254696388828642138803 1391220382044583242963208205)
          ·
            refine ⟨521707643266718716111203077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391220382044583242963208205 521707643266718716111203077)
            ·
              refine ⟨97820183112509759270850577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 521707643266718716111203077 97820183112509759270850577)
              ·
                refine ⟨73365137334382319453137933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97820183112509759270850577 73365137334382319453137933)
                ·
                  refine ⟨27511926500393369794926725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73365137334382319453137933 27511926500393369794926725)
                  ·
                    refine ⟨5158486218823756836548761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27511926500393369794926725 5158486218823756836548761)
                    ·
                      refine ⟨3868864664117817627411571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158486218823756836548761 3868864664117817627411571)
                      ·
                        rfl

theorem cell23_7534587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4, 2].length) (baseStart_7534587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534587 prefixEnd_7534587 := by exact prefixLift 7534587
  have htrace : WordTrace (prefixWord ++ tailWord_7534587) baseStart_7534587 baseEnd_7534587 := by
    simpa [prefixWord, tailWord_7534587, baseEnd_7534587] using wordTrace_append hprefix tailTrace_7534587
  have hstable : (prefixWord ++ tailWord_7534587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534587).length < 2 ^ (prefixWord ++ tailWord_7534587).sum := by decide
  have hdescent : baseEnd_7534587 < baseStart_7534587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534605 : List Nat := [1, 7, 1, 2, 2, 1, 2, 7]
def baseStart_7534605 : Nat := 118140960795 + 7534605 * 2 ^ 59
def prefixEnd_7534605 : Nat := 4983230072969 + 3 ^ 40 * 7534605 * 2
def baseEnd_7534605 : Nat := 143291626176651798406907

theorem tailTrace_7534605 : CollatzResearch.WordTrace tailWord_7534605 prefixEnd_7534605 143291626176651798406907 := by
  unfold tailWord_7534605
  simp only [CollatzResearch.WordTrace]
  refine ⟨274809620868420367931085269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183206413912280245287390179 274809620868420367931085269)
  ·
    refine ⟨6440850489103602373384811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 274809620868420367931085269 6440850489103602373384811)
    ·
      refine ⟨9661275733655403560077217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440850489103602373384811 9661275733655403560077217)
      ·
        refine ⟨7245956800241552670057913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661275733655403560077217 7245956800241552670057913)
        ·
          refine ⟨5434467600181164502543435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245956800241552670057913 5434467600181164502543435)
          ·
            refine ⟨8151701400271746753815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434467600181164502543435 8151701400271746753815153)
            ·
              refine ⟨6113776050203810065361365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8151701400271746753815153 6113776050203810065361365)
              ·
                refine ⟨143291626176651798406907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6113776050203810065361365 143291626176651798406907)
                ·
                  rfl

theorem cell23_7534605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 7].length) (baseStart_7534605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534605 prefixEnd_7534605 := by exact prefixLift 7534605
  have htrace : WordTrace (prefixWord ++ tailWord_7534605) baseStart_7534605 baseEnd_7534605 := by
    simpa [prefixWord, tailWord_7534605, baseEnd_7534605] using wordTrace_append hprefix tailTrace_7534605
  have hstable : (prefixWord ++ tailWord_7534605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534605).length < 2 ^ (prefixWord ++ tailWord_7534605).sum := by decide
  have hdescent : baseEnd_7534605 < baseStart_7534605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534621 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_7534621 : Nat := 118140960795 + 7534621 * 2 ^ 59
def prefixEnd_7534621 : Nat := 4983230072969 + 3 ^ 40 * 7534621 * 2
def baseEnd_7534621 : Nat := 3868882122460070494386415

theorem tailTrace_7534621 : CollatzResearch.WordTrace tailWord_7534621 prefixEnd_7534621 3868882122460070494386415 := by
  unfold tailWord_7534621
  simp only [CollatzResearch.WordTrace]
  refine ⟨274810204436362402663667717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183206802957574935109111811 274810204436362402663667717)
  ·
    refine ⟨51526913331817950499437697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274810204436362402663667717 51526913331817950499437697)
    ·
      refine ⟨38645184998863462874578273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51526913331817950499437697 38645184998863462874578273)
      ·
        refine ⟨28983888749147597155933705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38645184998863462874578273 28983888749147597155933705)
        ·
          refine ⟨21737916561860697866950279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28983888749147597155933705 21737916561860697866950279)
          ·
            refine ⟨32606874842791046800425419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21737916561860697866950279 32606874842791046800425419)
            ·
              refine ⟨48910312264186570200638129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32606874842791046800425419 48910312264186570200638129)
              ·
                refine ⟨36682734198139927650478597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48910312264186570200638129 36682734198139927650478597)
                ·
                  refine ⟨6878012662151236434464737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36682734198139927650478597 6878012662151236434464737)
                  ·
                    refine ⟨5158509496613427325848553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878012662151236434464737 5158509496613427325848553)
                    ·
                      refine ⟨3868882122460070494386415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158509496613427325848553 3868882122460070494386415)
                      ·
                        rfl

theorem cell23_7534621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_7534621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534621 prefixEnd_7534621 := by exact prefixLift 7534621
  have htrace : WordTrace (prefixWord ++ tailWord_7534621) baseStart_7534621 baseEnd_7534621 := by
    simpa [prefixWord, tailWord_7534621, baseEnd_7534621] using wordTrace_append hprefix tailTrace_7534621
  have hstable : (prefixWord ++ tailWord_7534621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534621).length < 2 ^ (prefixWord ++ tailWord_7534621).sum := by decide
  have hdescent : baseEnd_7534621 < baseStart_7534621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534687 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 7, 4]
def baseStart_7534687 : Nat := 118140960795 + 7534687 * 2 ^ 59
def prefixEnd_7534687 : Nat := 4983230072969 + 3 ^ 40 * 7534687 * 2
def baseEnd_7534687 : Nat := 1289638670727755745387037

theorem tailTrace_7534687 : CollatzResearch.WordTrace tailWord_7534687 prefixEnd_7534687 1289638670727755745387037 := by
  unfold tailWord_7534687
  simp only [CollatzResearch.WordTrace]
  refine ⟨274812611654123295935570315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183208407769415530623713543 274812611654123295935570315)
  ·
    refine ⟨412218917481184943903355473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274812611654123295935570315 412218917481184943903355473)
    ·
      refine ⟨309164188110888707927516605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412218917481184943903355473 309164188110888707927516605)
      ·
        refine ⟨115936570541583265472818727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309164188110888707927516605 115936570541583265472818727)
        ·
          refine ⟨173904855812374898209228091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115936570541583265472818727 173904855812374898209228091)
          ·
            refine ⟨260857283718562347313842137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173904855812374898209228091 260857283718562347313842137)
            ·
              refine ⟨195642962788921760485381603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260857283718562347313842137 195642962788921760485381603)
              ·
                refine ⟨293464444183382640728072405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195642962788921760485381603 293464444183382640728072405)
                ·
                  refine ⟨6878072910548030642064197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293464444183382640728072405 6878072910548030642064197)
                  ·
                    refine ⟨1289638670727755745387037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878072910548030642064197 1289638670727755745387037)
                    ·
                      rfl

theorem cell23_7534687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_7534687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534687 prefixEnd_7534687 := by exact prefixLift 7534687
  have htrace : WordTrace (prefixWord ++ tailWord_7534687) baseStart_7534687 baseEnd_7534687 := by
    simpa [prefixWord, tailWord_7534687, baseEnd_7534687] using wordTrace_append hprefix tailTrace_7534687
  have hstable : (prefixWord ++ tailWord_7534687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534687).length < 2 ^ (prefixWord ++ tailWord_7534687).sum := by decide
  have hdescent : baseEnd_7534687 < baseStart_7534687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534721 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7534721 : Nat := 118140960795 + 7534721 * 2 ^ 59
def prefixEnd_7534721 : Nat := 4983230072969 + 3 ^ 40 * 7534721 * 2
def baseEnd_7534721 : Nat := 1289644490175173367711985

theorem tailTrace_7534721 : CollatzResearch.WordTrace tailWord_7534721 prefixEnd_7534721 1289644490175173367711985 := by
  unfold tailWord_7534721
  simp only [CollatzResearch.WordTrace]
  refine ⟨274813851736000119742308017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183209234490666746494872011 274813851736000119742308017)
  ·
    refine ⟨206110388802000089806731013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274813851736000119742308017 206110388802000089806731013)
    ·
      refine ⟨38645697900375016838762065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206110388802000089806731013 38645697900375016838762065)
      ·
        refine ⟨28984273425281262629071549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38645697900375016838762065 28984273425281262629071549)
        ·
          refine ⟨10869102534480473485901831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28984273425281262629071549 10869102534480473485901831)
          ·
            refine ⟨16303653801720710228852747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869102534480473485901831 16303653801720710228852747)
            ·
              refine ⟨24455480702581065343279121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16303653801720710228852747 24455480702581065343279121)
              ·
                refine ⟨18341610526935799007459341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24455480702581065343279121 18341610526935799007459341)
                ·
                  refine ⟨6878103947600924627797253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18341610526935799007459341 6878103947600924627797253)
                  ·
                    refine ⟨1289644490175173367711985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878103947600924627797253 1289644490175173367711985)
                    ·
                      rfl

theorem cell23_7534721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7534721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534721 prefixEnd_7534721 := by exact prefixLift 7534721
  have htrace : WordTrace (prefixWord ++ tailWord_7534721) baseStart_7534721 baseEnd_7534721 := by
    simpa [prefixWord, tailWord_7534721, baseEnd_7534721] using wordTrace_append hprefix tailTrace_7534721
  have hstable : (prefixWord ++ tailWord_7534721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534721).length < 2 ^ (prefixWord ++ tailWord_7534721).sum := by decide
  have hdescent : baseEnd_7534721 < baseStart_7534721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534738 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7534738 : Nat := 118140960795 + 7534738 * 2 ^ 59
def prefixEnd_7534738 : Nat := 4983230072969 + 3 ^ 40 * 7534738 * 2
def baseEnd_7534738 : Nat := 1289647399898882178874459

theorem tailTrace_7534738 : CollatzResearch.WordTrace tailWord_7534738 prefixEnd_7534738 1289647399898882178874459 := by
  unfold tailWord_7534738
  simp only [CollatzResearch.WordTrace]
  refine ⟨68703617944234632911419217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183209647851292354430451245 68703617944234632911419217)
  ·
    refine ⟨51527713458175974683564413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68703617944234632911419217 51527713458175974683564413)
    ·
      refine ⟨19322892546815990506336655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51527713458175974683564413 19322892546815990506336655)
      ·
        refine ⟨28984338820223985759504983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19322892546815990506336655 28984338820223985759504983)
        ·
          refine ⟨43476508230335978639257475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28984338820223985759504983 43476508230335978639257475)
          ·
            refine ⟨65214762345503967958886213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43476508230335978639257475 65214762345503967958886213)
            ·
              refine ⟨12227767939781993992291165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65214762345503967958886213 12227767939781993992291165)
              ·
                refine ⟨4585412977418247747109187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12227767939781993992291165 4585412977418247747109187)
                ·
                  refine ⟨6878119466127371620663781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585412977418247747109187 6878119466127371620663781)
                  ·
                    refine ⟨1289647399898882178874459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878119466127371620663781 1289647399898882178874459)
                    ·
                      rfl

theorem cell23_7534738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7534738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534738 prefixEnd_7534738 := by exact prefixLift 7534738
  have htrace : WordTrace (prefixWord ++ tailWord_7534738) baseStart_7534738 baseEnd_7534738 := by
    simpa [prefixWord, tailWord_7534738, baseEnd_7534738] using wordTrace_append hprefix tailTrace_7534738
  have hstable : (prefixWord ++ tailWord_7534738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534738).length < 2 ^ (prefixWord ++ tailWord_7534738).sum := by decide
  have hdescent : baseEnd_7534738 < baseStart_7534738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534751 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 6]
def baseStart_7534751 : Nat := 118140960795 + 7534751 * 2 ^ 59
def prefixEnd_7534751 : Nat := 4983230072969 + 3 ^ 40 * 7534751 * 2
def baseEnd_7534751 : Nat := 429883208327239442862313

theorem tailTrace_7534751 : CollatzResearch.WordTrace tailWord_7534751 prefixEnd_7534751 429883208327239442862313 := by
  unfold tailWord_7534751
  simp only [CollatzResearch.WordTrace]
  refine ⟨274814945925891434865900107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183209963950594289910600071 274814945925891434865900107)
  ·
    refine ⟨412222418888837152298850161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274814945925891434865900107 412222418888837152298850161)
    ·
      refine ⟨309166814166627864224137621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412222418888837152298850161 309166814166627864224137621)
      ·
        refine ⟨14492194414060681135506451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309166814166627864224137621 14492194414060681135506451)
        ·
          refine ⟨21738291621091021703259677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492194414060681135506451 21738291621091021703259677)
          ·
            refine ⟨8151859357909133138722379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21738291621091021703259677 8151859357909133138722379)
            ·
              refine ⟨12227789036863699708083569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151859357909133138722379 12227789036863699708083569)
              ·
                refine ⟨9170841777647774781062677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12227789036863699708083569 9170841777647774781062677)
                ·
                  refine ⟨429883208327239442862313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9170841777647774781062677 429883208327239442862313)
                  ·
                    rfl

theorem cell23_7534751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 6].length) (baseStart_7534751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534751 prefixEnd_7534751 := by exact prefixLift 7534751
  have htrace : WordTrace (prefixWord ++ tailWord_7534751) baseStart_7534751 baseEnd_7534751 := by
    simpa [prefixWord, tailWord_7534751, baseEnd_7534751] using wordTrace_append hprefix tailTrace_7534751
  have hstable : (prefixWord ++ tailWord_7534751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534751).length < 2 ^ (prefixWord ++ tailWord_7534751).sum := by decide
  have hdescent : baseEnd_7534751 < baseStart_7534751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534754 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7534754 : Nat := 118140960795 + 7534754 * 2 ^ 59
def prefixEnd_7534754 : Nat := 4983230072969 + 3 ^ 40 * 7534754 * 2
def baseEnd_7534754 : Nat := 3868950415387118474023303

theorem tailTrace_7534754 : CollatzResearch.WordTrace tailWord_7534754 prefixEnd_7534754 3868950415387118474023303 := by
  unfold tailWord_7534754
  simp only [CollatzResearch.WordTrace]
  refine ⟨68703763836220141594564829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183210036896587044252172877 68703763836220141594564829)
  ·
    refine ⟨25763911438582553097961811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68703763836220141594564829 25763911438582553097961811)
    ·
      refine ⟨38645867157873829646942717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25763911438582553097961811 38645867157873829646942717)
      ·
        refine ⟨14492200184202686117603519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38645867157873829646942717 14492200184202686117603519)
        ·
          refine ⟨21738300276304029176405279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492200184202686117603519 21738300276304029176405279)
          ·
            refine ⟨32607450414456043764607919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21738300276304029176405279 32607450414456043764607919)
            ·
              refine ⟨48911175621684065646911879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32607450414456043764607919 48911175621684065646911879)
              ·
                refine ⟨73366763432526098470367819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48911175621684065646911879 73366763432526098470367819)
                ·
                  refine ⟨110050145148789147705551729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73366763432526098470367819 110050145148789147705551729)
                  ·
                    refine ⟨82537608861591860779163797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110050145148789147705551729 82537608861591860779163797)
                    ·
                      refine ⟨3868950415387118474023303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82537608861591860779163797 3868950415387118474023303)
                      ·
                        rfl

theorem cell23_7534754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7534754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534754 prefixEnd_7534754 := by exact prefixLift 7534754
  have htrace : WordTrace (prefixWord ++ tailWord_7534754) baseStart_7534754 baseEnd_7534754 := by
    simpa [prefixWord, tailWord_7534754, baseEnd_7534754] using wordTrace_append hprefix tailTrace_7534754
  have hstable : (prefixWord ++ tailWord_7534754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534754).length < 2 ^ (prefixWord ++ tailWord_7534754).sum := by decide
  have hdescent : baseEnd_7534754 < baseStart_7534754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534794 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_7534794 : Nat := 118140960795 + 7534794 * 2 ^ 59
def prefixEnd_7534794 : Nat := 4983230072969 + 3 ^ 40 * 7534794 * 2
def baseEnd_7534794 : Nat := 1289656984871099439174373

theorem tailTrace_7534794 : CollatzResearch.WordTrace tailWord_7534794 prefixEnd_7534794 1289656984871099439174373 := by
  unfold tailWord_7534794
  simp only [CollatzResearch.WordTrace]
  refine ⟨68704128566183913302428859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183211009509823768806476957 68704128566183913302428859)
  ·
    refine ⟨103056192849275869953643289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68704128566183913302428859 103056192849275869953643289)
    ·
      refine ⟨77292144636956902465232467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103056192849275869953643289 77292144636956902465232467)
      ·
        refine ⟨115938216955435353697848701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77292144636956902465232467 115938216955435353697848701)
        ·
          refine ⟨43476831358288257636693263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115938216955435353697848701 43476831358288257636693263)
          ·
            refine ⟨65215247037432386455039895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43476831358288257636693263 65215247037432386455039895)
            ·
              refine ⟨97822870556148579682559843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65215247037432386455039895 97822870556148579682559843)
              ·
                refine ⟨146734305834222869523839765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97822870556148579682559843 146734305834222869523839765)
                ·
                  refine ⟨6878170585979197008929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146734305834222869523839765 6878170585979197008929989)
                  ·
                    refine ⟨1289656984871099439174373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878170585979197008929989 1289656984871099439174373)
                    ·
                      rfl

theorem cell23_7534794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_7534794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534794 prefixEnd_7534794 := by exact prefixLift 7534794
  have htrace : WordTrace (prefixWord ++ tailWord_7534794) baseStart_7534794 baseEnd_7534794 := by
    simpa [prefixWord, tailWord_7534794, baseEnd_7534794] using wordTrace_append hprefix tailTrace_7534794
  have hstable : (prefixWord ++ tailWord_7534794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534794).length < 2 ^ (prefixWord ++ tailWord_7534794).sum := by decide
  have hdescent : baseEnd_7534794 < baseStart_7534794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534801 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_7534801 : Nat := 118140960795 + 7534801 * 2 ^ 59
def prefixEnd_7534801 : Nat := 4983230072969 + 3 ^ 40 * 7534801 * 2
def baseEnd_7534801 : Nat := 3868974548977879790135587

theorem tailTrace_7534801 : CollatzResearch.WordTrace tailWord_7534801 prefixEnd_7534801 3868974548977879790135587 := by
  unfold tailWord_7534801
  simp only [CollatzResearch.WordTrace]
  refine ⟨274816769575710293405220257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183211179717140195603480171 274816769575710293405220257)
  ·
    refine ⟨206112577181782720053915193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274816769575710293405220257 206112577181782720053915193)
    ·
      refine ⟨154584432886337040040436395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206112577181782720053915193 154584432886337040040436395)
      ·
        refine ⟨231876649329505560060654593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154584432886337040040436395 231876649329505560060654593)
        ·
          refine ⟨173907486997129170045490945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231876649329505560060654593 173907486997129170045490945)
          ·
            refine ⟨130430615247846877534118209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173907486997129170045490945 130430615247846877534118209)
            ·
              refine ⟨97822961435885158150588657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130430615247846877534118209 97822961435885158150588657)
              ·
                refine ⟨73367221076913868612941493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97822961435885158150588657 73367221076913868612941493)
                ·
                  refine ⟨6878176975960675182463265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73367221076913868612941493 6878176975960675182463265)
                  ·
                    refine ⟨5158632731970506386847449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878176975960675182463265 5158632731970506386847449)
                    ·
                      refine ⟨3868974548977879790135587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158632731970506386847449 3868974548977879790135587)
                      ·
                        rfl

theorem cell23_7534801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_7534801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534801 prefixEnd_7534801 := by exact prefixLift 7534801
  have htrace : WordTrace (prefixWord ++ tailWord_7534801) baseStart_7534801 baseEnd_7534801 := by
    simpa [prefixWord, tailWord_7534801, baseEnd_7534801] using wordTrace_append hprefix tailTrace_7534801
  have hstable : (prefixWord ++ tailWord_7534801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534801).length < 2 ^ (prefixWord ++ tailWord_7534801).sum := by decide
  have hdescent : baseEnd_7534801 < baseStart_7534801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534812 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7534812 : Nat := 118140960795 + 7534812 * 2 ^ 59
def prefixEnd_7534812 : Nat := 4983230072969 + 3 ^ 40 * 7534812 * 2
def baseEnd_7534812 : Nat := 3868980197265079247098037

theorem tailTrace_7534812 : CollatzResearch.WordTrace tailWord_7534812 prefixEnd_7534812 3868980197265079247098037 := by
  unfold tailWord_7534812
  simp only [CollatzResearch.WordTrace]
  refine ⟨137408585389335221141935345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183211447185780294855913793 137408585389335221141935345)
  ·
    refine ⟨103056439042001415856451509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137408585389335221141935345 103056439042001415856451509)
    ·
      refine ⟨9661541160187632736542329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103056439042001415856451509 9661541160187632736542329)
      ·
        refine ⟨7246155870140724552406747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661541160187632736542329 7246155870140724552406747)
        ·
          refine ⟨10869233805211086828610121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246155870140724552406747 10869233805211086828610121)
          ·
            refine ⟨8151925353908315121457591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869233805211086828610121 8151925353908315121457591)
            ·
              refine ⟨12227888030862472682186387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151925353908315121457591 12227888030862472682186387)
              ·
                refine ⟨18341832046293709023279581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227888030862472682186387 18341832046293709023279581)
                ·
                  refine ⟨6878187017360140883729843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18341832046293709023279581 6878187017360140883729843)
                  ·
                    refine ⟨10317280526040211325594765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878187017360140883729843 10317280526040211325594765)
                    ·
                      refine ⟨3868980197265079247098037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317280526040211325594765 3868980197265079247098037)
                      ·
                        rfl

theorem cell23_7534812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7534812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534812 prefixEnd_7534812 := by exact prefixLift 7534812
  have htrace : WordTrace (prefixWord ++ tailWord_7534812) baseStart_7534812 baseEnd_7534812 := by
    simpa [prefixWord, tailWord_7534812, baseEnd_7534812] using wordTrace_append hprefix tailTrace_7534812
  have hstable : (prefixWord ++ tailWord_7534812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534812).length < 2 ^ (prefixWord ++ tailWord_7534812).sum := by decide
  have hdescent : baseEnd_7534812 < baseStart_7534812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534824 : List Nat := [2, 1, 4, 1, 2, 3, 2, 8]
def baseStart_7534824 : Nat := 118140960795 + 7534824 * 2 ^ 59
def prefixEnd_7534824 : Nat := 4983230072969 + 3 ^ 40 * 7534824 * 2
def baseEnd_7534824 : Nat := 143295791075293822227703

theorem tailTrace_7534824 : CollatzResearch.WordTrace tailWord_7534824 prefixEnd_7534824 143295791075293822227703 := by
  unfold tailWord_7534824
  simp only [CollatzResearch.WordTrace]
  refine ⟨137408804227313484166653763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183211738969751312222205017 137408804227313484166653763)
  ·
    refine ⟨206113206340970226249980645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137408804227313484166653763 206113206340970226249980645)
    ·
      refine ⟨38646226188931917421871371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206113206340970226249980645 38646226188931917421871371)
      ·
        refine ⟨57969339283397876132807057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38646226188931917421871371 57969339283397876132807057)
        ·
          refine ⟨43477004462548407099605293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57969339283397876132807057 43477004462548407099605293)
          ·
            refine ⟨16303876673455652662351985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43477004462548407099605293 16303876673455652662351985)
            ·
              refine ⟨12227907505091739496763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16303876673455652662351985 12227907505091739496763989)
              ·
                refine ⟨143295791075293822227703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12227907505091739496763989 143295791075293822227703)
                ·
                  rfl

theorem cell23_7534824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 8].length) (baseStart_7534824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534824 prefixEnd_7534824 := by exact prefixLift 7534824
  have htrace : WordTrace (prefixWord ++ tailWord_7534824) baseStart_7534824 baseEnd_7534824 := by
    simpa [prefixWord, tailWord_7534824, baseEnd_7534824] using wordTrace_append hprefix tailTrace_7534824
  have hstable : (prefixWord ++ tailWord_7534824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534824).length < 2 ^ (prefixWord ++ tailWord_7534824).sum := by decide
  have hdescent : baseEnd_7534824 < baseStart_7534824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534827 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_7534827 : Nat := 118140960795 + 7534827 * 2 ^ 59
def prefixEnd_7534827 : Nat := 4983230072969 + 3 ^ 40 * 7534827 * 2
def baseEnd_7534827 : Nat := 3868987899474896688410467

theorem tailTrace_7534827 : CollatzResearch.WordTrace tailWord_7534827 prefixEnd_7534827 3868987899474896688410467 := by
  unfold tailWord_7534827
  simp only [CollatzResearch.WordTrace]
  refine ⟨274817717873616099845666735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183211811915744066563777823 274817717873616099845666735)
  ·
    refine ⟨412226576810424149768500103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274817717873616099845666735 412226576810424149768500103)
    ·
      refine ⟨618339865215636224652750155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412226576810424149768500103 618339865215636224652750155)
      ·
        refine ⟨927509797823454336979125233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618339865215636224652750155 927509797823454336979125233)
        ·
          refine ⟨695632348367590752734343925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927509797823454336979125233 695632348367590752734343925)
          ·
            refine ⟨65215532659461633068844743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 695632348367590752734343925 65215532659461633068844743)
            ·
              refine ⟨97823298989192449603267115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65215532659461633068844743 97823298989192449603267115)
              ·
                refine ⟨146734948483788674404900673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97823298989192449603267115 146734948483788674404900673)
                ·
                  refine ⟨110051211362841505803675505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146734948483788674404900673 110051211362841505803675505)
                  ·
                    refine ⟨82538408522131129352756629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110051211362841505803675505 82538408522131129352756629)
                    ·
                      refine ⟨3868987899474896688410467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82538408522131129352756629 3868987899474896688410467)
                      ·
                        rfl

theorem cell23_7534827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_7534827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534827 prefixEnd_7534827 := by exact prefixLift 7534827
  have htrace : WordTrace (prefixWord ++ tailWord_7534827) baseStart_7534827 baseEnd_7534827 := by
    simpa [prefixWord, tailWord_7534827, baseEnd_7534827] using wordTrace_append hprefix tailTrace_7534827
  have hstable : (prefixWord ++ tailWord_7534827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534827).length < 2 ^ (prefixWord ++ tailWord_7534827).sum := by decide
  have hdescent : baseEnd_7534827 < baseStart_7534827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534838 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7534838 : Nat := 118140960795 + 7534838 * 2 ^ 59
def prefixEnd_7534838 : Nat := 4983230072969 + 3 ^ 40 * 7534838 * 2
def baseEnd_7534838 : Nat := 3868993547762096145372917

theorem tailTrace_7534838 : CollatzResearch.WordTrace tailWord_7534838 prefixEnd_7534838 3868993547762096145372917 := by
  unfold tailWord_7534838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176132442286015545269823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183212079384384165816211445 17176132442286015545269823)
  ·
    refine ⟨25764198663429023317904735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17176132442286015545269823 25764198663429023317904735)
    ·
      refine ⟨38646297995143534976857103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25764198663429023317904735 38646297995143534976857103)
      ·
        refine ⟨57969446992715302465285655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38646297995143534976857103 57969446992715302465285655)
        ·
          refine ⟨86954170489072953697928483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57969446992715302465285655 86954170489072953697928483)
          ·
            refine ⟨130431255733609430546892725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86954170489072953697928483 130431255733609430546892725)
            ·
              refine ⟨12227930225025884113771193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130431255733609430546892725 12227930225025884113771193)
              ·
                refine ⟨9170947668769413085328395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12227930225025884113771193 9170947668769413085328395)
                ·
                  refine ⟨13756421503154119627992593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9170947668769413085328395 13756421503154119627992593)
                  ·
                    refine ⟨10317316127365589720994445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13756421503154119627992593 10317316127365589720994445)
                    ·
                      refine ⟨3868993547762096145372917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317316127365589720994445 3868993547762096145372917)
                      ·
                        rfl

theorem cell23_7534838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7534838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534838 prefixEnd_7534838 := by exact prefixLift 7534838
  have htrace : WordTrace (prefixWord ++ tailWord_7534838) baseStart_7534838 baseEnd_7534838 := by
    simpa [prefixWord, tailWord_7534838, baseEnd_7534838] using wordTrace_append hprefix tailTrace_7534838
  have hstable : (prefixWord ++ tailWord_7534838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534838).length < 2 ^ (prefixWord ++ tailWord_7534838).sum := by decide
  have hdescent : baseEnd_7534838 < baseStart_7534838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534855 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7534855 : Nat := 118140960795 + 7534855 * 2 ^ 59
def prefixEnd_7534855 : Nat := 4983230072969 + 3 ^ 40 * 7534855 * 2
def baseEnd_7534855 : Nat := 3869002276933222578860339

theorem tailTrace_7534855 : CollatzResearch.WordTrace tailWord_7534855 prefixEnd_7534855 3869002276933222578860339 := by
  unfold tailWord_7534855
  simp only [CollatzResearch.WordTrace]
  refine ⟨274818739117514660627686019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183212492745009773751790679 274818739117514660627686019)
  ·
    refine ⟨412228108676271990941529029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274818739117514660627686019 412228108676271990941529029)
    ·
      refine ⟨77292770376800998301536693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412228108676271990941529029 77292770376800998301536693)
      ·
        refine ⟨7246197222825093590769065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77292770376800998301536693 7246197222825093590769065)
        ·
          refine ⟨5434647917118820193076799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7246197222825093590769065 5434647917118820193076799)
          ·
            refine ⟨8151971875678230289615199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434647917118820193076799 8151971875678230289615199)
            ·
              refine ⟨12227957813517345434422799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151971875678230289615199 12227957813517345434422799)
              ·
                refine ⟨18341936720276018151634199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227957813517345434422799 18341936720276018151634199)
                ·
                  refine ⟨27512905080414027227451299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18341936720276018151634199 27512905080414027227451299)
                  ·
                    refine ⟨41269357620621040841176949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27512905080414027227451299 41269357620621040841176949)
                    ·
                      refine ⟨3869002276933222578860339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41269357620621040841176949 3869002276933222578860339)
                      ·
                        rfl

theorem cell23_7534855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7534855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534855 prefixEnd_7534855 := by exact prefixLift 7534855
  have htrace : WordTrace (prefixWord ++ tailWord_7534855) baseStart_7534855 baseEnd_7534855 := by
    simpa [prefixWord, tailWord_7534855, baseEnd_7534855] using wordTrace_append hprefix tailTrace_7534855
  have hstable : (prefixWord ++ tailWord_7534855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534855).length < 2 ^ (prefixWord ++ tailWord_7534855).sum := by decide
  have hdescent : baseEnd_7534855 < baseStart_7534855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534867 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 8]
def baseStart_7534867 : Nat := 118140960795 + 7534867 * 2 ^ 59
def prefixEnd_7534867 : Nat := 4983230072969 + 3 ^ 40 * 7534867 * 2
def baseEnd_7534867 : Nat := 1289669479567025510636761

theorem tailTrace_7534867 : CollatzResearch.WordTrace tailWord_7534867 prefixEnd_7534867 1289669479567025510636761 := by
  unfold tailWord_7534867
  simp only [CollatzResearch.WordTrace]
  refine ⟨274819176793471186677122855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183212784528980791118081903 274819176793471186677122855)
  ·
    refine ⟨412228765190206780015684283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274819176793471186677122855 412228765190206780015684283)
    ·
      refine ⟨618343147785310170023526425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412228765190206780015684283 618343147785310170023526425)
      ·
        refine ⟨463757360838982627517644819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618343147785310170023526425 463757360838982627517644819)
        ·
          refine ⟨695636041258473941276467229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463757360838982627517644819 695636041258473941276467229)
          ·
            refine ⟨260863515471927727978675211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695636041258473941276467229 260863515471927727978675211)
            ·
              refine ⟨391295273207891591968012817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260863515471927727978675211 391295273207891591968012817)
              ·
                refine ⟨293471454905918693976009613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391295273207891591968012817 293471454905918693976009613)
                ·
                  refine ⟨110051795589719510241003605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293471454905918693976009613 110051795589719510241003605)
                  ·
                    refine ⟨1289669479567025510636761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110051795589719510241003605 1289669479567025510636761)
                    ·
                      rfl

theorem cell23_7534867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_7534867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534867 prefixEnd_7534867 := by exact prefixLift 7534867
  have htrace : WordTrace (prefixWord ++ tailWord_7534867) baseStart_7534867 baseEnd_7534867 := by
    simpa [prefixWord, tailWord_7534867, baseEnd_7534867] using wordTrace_append hprefix tailTrace_7534867
  have hstable : (prefixWord ++ tailWord_7534867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534867).length < 2 ^ (prefixWord ++ tailWord_7534867).sum := by decide
  have hdescent : baseEnd_7534867 < baseStart_7534867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534884 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_7534884 : Nat := 118140960795 + 7534884 * 2 ^ 59
def prefixEnd_7534884 : Nat := 4983230072969 + 3 ^ 40 * 7534884 * 2
def baseEnd_7534884 : Nat := 1289672389290734321799235

theorem tailTrace_7534884 : CollatzResearch.WordTrace tailWord_7534884 prefixEnd_7534884 1289672389290734321799235 := by
  unfold tailWord_7534884
  simp only [CollatzResearch.WordTrace]
  refine ⟨137409898417204799290245853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183213197889606399053661137 137409898417204799290245853)
  ·
    refine ⟨51528711906451799733842195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137409898417204799290245853 51528711906451799733842195)
    ·
      refine ⟨77293067859677699600763293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51528711906451799733842195 77293067859677699600763293)
      ·
        refine ⟨28984900447379137350286235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77293067859677699600763293 28984900447379137350286235)
        ·
          refine ⟨43477350671068706025429353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28984900447379137350286235 43477350671068706025429353)
          ·
            refine ⟨32608013003301529519072015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43477350671068706025429353 32608013003301529519072015)
            ·
              refine ⟨48912019504952294278608023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32608013003301529519072015 48912019504952294278608023)
              ·
                refine ⟨73368029257428441417912035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48912019504952294278608023 73368029257428441417912035)
                ·
                  refine ⟨110052043886142662126868053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73368029257428441417912035 110052043886142662126868053)
                  ·
                    refine ⟨1289672389290734321799235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110052043886142662126868053 1289672389290734321799235)
                    ·
                      rfl

theorem cell23_7534884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_7534884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534884 prefixEnd_7534884 := by exact prefixLift 7534884
  have htrace : WordTrace (prefixWord ++ tailWord_7534884) baseStart_7534884 baseEnd_7534884 := by
    simpa [prefixWord, tailWord_7534884, baseEnd_7534884] using wordTrace_append hprefix tailTrace_7534884
  have hstable : (prefixWord ++ tailWord_7534884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534884).length < 2 ^ (prefixWord ++ tailWord_7534884).sum := by decide
  have hdescent : baseEnd_7534884 < baseStart_7534884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534908 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_7534908 : Nat := 118140960795 + 7534908 * 2 ^ 59
def prefixEnd_7534908 : Nat := 4983230072969 + 3 ^ 40 * 7534908 * 2
def baseEnd_7534908 : Nat := 3869029491407910871497595

theorem tailTrace_7534908 : CollatzResearch.WordTrace tailWord_7534908 prefixEnd_7534908 3869029491407910871497595 := by
  unfold tailWord_7534908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137410336093161325339682689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183213781457548433786243585 137410336093161325339682689)
  ·
    refine ⟨103057752069870994004762017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137410336093161325339682689 103057752069870994004762017)
    ·
      refine ⟨77293314052403245503571513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103057752069870994004762017 77293314052403245503571513)
      ·
        refine ⟨57969985539302434127678635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77293314052403245503571513 57969985539302434127678635)
        ·
          refine ⟨86954978308953651191517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57969985539302434127678635 86954978308953651191517953)
          ·
            refine ⟨65216233731715238393638465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86954978308953651191517953 65216233731715238393638465)
            ·
              refine ⟨48912175298786428795228849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65216233731715238393638465 48912175298786428795228849)
              ·
                refine ⟨36684131474089821596421637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48912175298786428795228849 36684131474089821596421637)
                ·
                  refine ⟨6878274651391841549329057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36684131474089821596421637 6878274651391841549329057)
                  ·
                    refine ⟨5158705988543881161996793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878274651391841549329057 5158705988543881161996793)
                    ·
                      refine ⟨3869029491407910871497595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158705988543881161996793 3869029491407910871497595)
                      ·
                        rfl

theorem cell23_7534908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_7534908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534908 prefixEnd_7534908 := by exact prefixLift 7534908
  have htrace : WordTrace (prefixWord ++ tailWord_7534908) baseStart_7534908 baseEnd_7534908 := by
    simpa [prefixWord, tailWord_7534908, baseEnd_7534908] using wordTrace_append hprefix tailTrace_7534908
  have hstable : (prefixWord ++ tailWord_7534908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534908).length < 2 ^ (prefixWord ++ tailWord_7534908).sum := by decide
  have hdescent : baseEnd_7534908 < baseStart_7534908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7534965 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 5]
def baseStart_7534965 : Nat := 118140960795 + 7534965 * 2 ^ 59
def prefixEnd_7534965 : Nat := 4983230072969 + 3 ^ 40 * 7534965 * 2
def baseEnd_7534965 : Nat := 429895417756135238720537

theorem tailTrace_7534965 : CollatzResearch.WordTrace tailWord_7534965 prefixEnd_7534965 429895417756135238720537 := by
  unfold tailWord_7534965
  simp only [CollatzResearch.WordTrace]
  refine ⟨274822751147116149414190349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183215167431410766276126899 274822751147116149414190349)
  ·
    refine ⟨103058531680168556030321381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274822751147116149414190349 103058531680168556030321381)
    ·
      refine ⟨19323474690031604255685259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103058531680168556030321381 19323474690031604255685259)
      ·
        refine ⟨28985212035047406383527889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19323474690031604255685259 28985212035047406383527889)
        ·
          refine ⟨21738909026285554787645917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28985212035047406383527889 21738909026285554787645917)
          ·
            refine ⟨8152090884857083045367219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21738909026285554787645917 8152090884857083045367219)
            ·
              refine ⟨12228136327285624568050829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152090884857083045367219 12228136327285624568050829)
              ·
                refine ⟨4585551122732109213019061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12228136327285624568050829 4585551122732109213019061)
                ·
                  refine ⟨429895417756135238720537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585551122732109213019061 429895417756135238720537)
                  ·
                    rfl

theorem cell23_7534965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_7534965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7534965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7534965 prefixEnd_7534965 := by exact prefixLift 7534965
  have htrace : WordTrace (prefixWord ++ tailWord_7534965) baseStart_7534965 baseEnd_7534965 := by
    simpa [prefixWord, tailWord_7534965, baseEnd_7534965] using wordTrace_append hprefix tailTrace_7534965
  have hstable : (prefixWord ++ tailWord_7534965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7534965).length < 2 ^ (prefixWord ++ tailWord_7534965).sum := by decide
  have hdescent : baseEnd_7534965 < baseStart_7534965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7534965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535001 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_7535001 : Nat := 118140960795 + 7535001 * 2 ^ 59
def prefixEnd_7535001 : Nat := 4983230072969 + 3 ^ 40 * 7535001 * 2
def baseEnd_7535001 : Nat := 3869077245108779007634667

theorem tailTrace_7535001 : CollatzResearch.WordTrace tailWord_7535001 prefixEnd_7535001 3869077245108779007634667 := by
  unfold tailWord_7535001
  simp only [CollatzResearch.WordTrace]
  refine ⟨274824064174985727562500857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183216042783323818375000571 274824064174985727562500857)
  ·
    refine ⟨206118048131239295671875643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274824064174985727562500857 206118048131239295671875643)
    ·
      refine ⟨309177072196858943507813465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206118048131239295671875643 309177072196858943507813465)
      ·
        refine ⟨231882804147644207630860099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309177072196858943507813465 231882804147644207630860099)
        ·
          refine ⟨347824206221466311446290149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231882804147644207630860099 347824206221466311446290149)
          ·
            refine ⟨65217038666524933396179403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347824206221466311446290149 65217038666524933396179403)
            ·
              refine ⟨97825557999787400094269105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65217038666524933396179403 97825557999787400094269105)
              ·
                refine ⟨73369168499840550070701829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97825557999787400094269105 73369168499840550070701829)
                ·
                  refine ⟨13756719093720103138256593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73369168499840550070701829 13756719093720103138256593)
                  ·
                    refine ⟨10317539320290077353692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13756719093720103138256593 10317539320290077353692445)
                    ·
                      refine ⟨3869077245108779007634667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317539320290077353692445 3869077245108779007634667)
                      ·
                        rfl

theorem cell23_7535001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_7535001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535001 prefixEnd_7535001 := by exact prefixLift 7535001
  have htrace : WordTrace (prefixWord ++ tailWord_7535001) baseStart_7535001 baseEnd_7535001 := by
    simpa [prefixWord, tailWord_7535001, baseEnd_7535001] using wordTrace_append hprefix tailTrace_7535001
  have hstable : (prefixWord ++ tailWord_7535001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535001).length < 2 ^ (prefixWord ++ tailWord_7535001).sum := by decide
  have hdescent : baseEnd_7535001 < baseStart_7535001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535075 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7535075 : Nat := 118140960795 + 7535075 * 2 ^ 59
def prefixEnd_7535075 : Nat := 4983230072969 + 3 ^ 40 * 7535075 * 2
def baseEnd_7535075 : Nat := 3869115242677211718109327

theorem tailTrace_7535075 : CollatzResearch.WordTrace tailWord_7535075 prefixEnd_7535075 3869115242677211718109327 := by
  unfold tailWord_7535075
  simp only [CollatzResearch.WordTrace]
  refine ⟨274826763176717638200694679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183217842117811758800463119 274826763176717638200694679)
  ·
    refine ⟨412240144765076457301042019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274826763176717638200694679 412240144765076457301042019)
    ·
      refine ⟨618360217147614685951563029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412240144765076457301042019 618360217147614685951563029)
      ·
        refine ⟨28985635178794438403979517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 618360217147614685951563029 28985635178794438403979517)
        ·
          refine ⟨10869613192047914401492319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28985635178794438403979517 10869613192047914401492319)
          ·
            refine ⟨16304419788071871602238479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869613192047914401492319 16304419788071871602238479)
            ·
              refine ⟨24456629682107807403357719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16304419788071871602238479 24456629682107807403357719)
              ·
                refine ⟨36684944523161711105036579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24456629682107807403357719 36684944523161711105036579)
                ·
                  refine ⟨55027416784742566657554869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36684944523161711105036579 55027416784742566657554869)
                  ·
                    refine ⟨5158820323569615624145769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55027416784742566657554869 5158820323569615624145769)
                    ·
                      refine ⟨3869115242677211718109327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158820323569615624145769 3869115242677211718109327)
                      ·
                        rfl

theorem cell23_7535075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7535075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535075 prefixEnd_7535075 := by exact prefixLift 7535075
  have htrace : WordTrace (prefixWord ++ tailWord_7535075) baseStart_7535075 baseEnd_7535075 := by
    simpa [prefixWord, tailWord_7535075, baseEnd_7535075] using wordTrace_append hprefix tailTrace_7535075
  have hstable : (prefixWord ++ tailWord_7535075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535075).length < 2 ^ (prefixWord ++ tailWord_7535075).sum := by decide
  have hdescent : baseEnd_7535075 < baseStart_7535075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535082 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_7535082 : Nat := 118140960795 + 7535082 * 2 ^ 59
def prefixEnd_7535082 : Nat := 4983230072969 + 3 ^ 40 * 7535082 * 2
def baseEnd_7535082 : Nat := 3869118837041793190721795

theorem tailTrace_7535082 : CollatzResearch.WordTrace tailWord_7535082 prefixEnd_7535082 3869118837041793190721795 := by
  unfold tailWord_7535082
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706754621923069599049875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183218012325128185597466333 68706754621923069599049875)
  ·
    refine ⟨103060131932884604398574813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68706754621923069599049875 103060131932884604398574813)
    ·
      refine ⟨38647549474831726649465555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103060131932884604398574813 38647549474831726649465555)
      ·
        refine ⟨57971324212247589974198333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38647549474831726649465555 57971324212247589974198333)
        ·
          refine ⟨21739246579592846240324375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57971324212247589974198333 21739246579592846240324375)
          ·
            refine ⟨32608869869389269360486563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739246579592846240324375 32608869869389269360486563)
            ·
              refine ⟨48913304804083904040729845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32608869869389269360486563 48913304804083904040729845)
              ·
                refine ⟨4585622325382866003818423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48913304804083904040729845 4585622325382866003818423)
                ·
                  refine ⟨6878433488074299005727635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585622325382866003818423 6878433488074299005727635)
                  ·
                    refine ⟨10317650232111448508591453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878433488074299005727635 10317650232111448508591453)
                    ·
                      refine ⟨3869118837041793190721795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317650232111448508591453 3869118837041793190721795)
                      ·
                        rfl

theorem cell23_7535082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_7535082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535082 prefixEnd_7535082 := by exact prefixLift 7535082
  have htrace : WordTrace (prefixWord ++ tailWord_7535082) baseStart_7535082 baseEnd_7535082 := by
    simpa [prefixWord, tailWord_7535082, baseEnd_7535082] using wordTrace_append hprefix tailTrace_7535082
  have hstable : (prefixWord ++ tailWord_7535082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535082).length < 2 ^ (prefixWord ++ tailWord_7535082).sum := by decide
  have hdescent : baseEnd_7535082 < baseStart_7535082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535085 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_7535085 : Nat := 118140960795 + 7535085 * 2 ^ 59
def prefixEnd_7535085 : Nat := 4983230072969 + 3 ^ 40 * 7535085 * 2
def baseEnd_7535085 : Nat := 1289706792494585559661427

theorem tailTrace_7535085 : CollatzResearch.WordTrace tailWord_7535085 prefixEnd_7535085 1289706792494585559661427 := by
  unfold tailWord_7535085
  simp only [CollatzResearch.WordTrace]
  refine ⟨274827127906681409908558709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183218085271120939939039139 274827127906681409908558709)
  ·
    refine ⟨25765043241251382178927379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274827127906681409908558709 25765043241251382178927379)
    ·
      refine ⟨38647564861877073268391069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25765043241251382178927379 38647564861877073268391069)
      ·
        refine ⟨14492836823203902475646651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38647564861877073268391069 14492836823203902475646651)
        ·
          refine ⟨21739255234805853713469977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492836823203902475646651 21739255234805853713469977)
          ·
            refine ⟨16304441426104390285102483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21739255234805853713469977 16304441426104390285102483)
            ·
              refine ⟨24456662139156585427653725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16304441426104390285102483 24456662139156585427653725)
              ·
                refine ⟨9171248302183719535370147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24456662139156585427653725 9171248302183719535370147)
                ·
                  refine ⟨13756872453275579303055221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171248302183719535370147 13756872453275579303055221)
                  ·
                    refine ⟨1289706792494585559661427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13756872453275579303055221 1289706792494585559661427)
                    ·
                      rfl

theorem cell23_7535085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_7535085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535085 prefixEnd_7535085 := by exact prefixLift 7535085
  have htrace : WordTrace (prefixWord ++ tailWord_7535085) baseStart_7535085 baseEnd_7535085 := by
    simpa [prefixWord, tailWord_7535085, baseEnd_7535085] using wordTrace_append hprefix tailTrace_7535085
  have hstable : (prefixWord ++ tailWord_7535085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535085).length < 2 ^ (prefixWord ++ tailWord_7535085).sum := by decide
  have hdescent : baseEnd_7535085 < baseStart_7535085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535088 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_7535088 : Nat := 118140960795 + 7535088 * 2 ^ 59
def prefixEnd_7535088 : Nat := 4983230072969 + 3 ^ 40 * 7535088 * 2
def baseEnd_7535088 : Nat := 3869121917925720167246767

theorem tailTrace_7535088 : CollatzResearch.WordTrace tailWord_7535088 prefixEnd_7535088 3869121917925720167246767 := by
  unfold tailWord_7535088
  simp only [CollatzResearch.WordTrace]
  refine ⟨137413618662835270710458959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183218158217113694280611945 137413618662835270710458959)
  ·
    refine ⟨206120427994252906065688439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137413618662835270710458959 206120427994252906065688439)
    ·
      refine ⟨309180641991379359098532659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206120427994252906065688439 309180641991379359098532659)
      ·
        refine ⟨463770962987069038647798989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309180641991379359098532659 463770962987069038647798989)
        ·
          refine ⟨173914111120150889492924621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463770962987069038647798989 173914111120150889492924621)
          ·
            refine ⟨65217791670056583559846733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173914111120150889492924621 65217791670056583559846733)
            ·
              refine ⟨24456671876271218834942525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65217791670056583559846733 24456671876271218834942525)
              ·
                refine ⟨9171251953601707063103447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24456671876271218834942525 9171251953601707063103447)
                ·
                  refine ⟨13756877930402560594655171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171251953601707063103447 13756877930402560594655171)
                  ·
                    refine ⟨20635316895603840891982757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13756877930402560594655171 20635316895603840891982757)
                    ·
                      refine ⟨3869121917925720167246767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20635316895603840891982757 3869121917925720167246767)
                      ·
                        rfl

theorem cell23_7535088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_7535088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535088 prefixEnd_7535088 := by exact prefixLift 7535088
  have htrace : WordTrace (prefixWord ++ tailWord_7535088) baseStart_7535088 baseEnd_7535088 := by
    simpa [prefixWord, tailWord_7535088, baseEnd_7535088] using wordTrace_append hprefix tailTrace_7535088
  have hstable : (prefixWord ++ tailWord_7535088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535088).length < 2 ^ (prefixWord ++ tailWord_7535088).sum := by decide
  have hdescent : baseEnd_7535088 < baseStart_7535088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535091 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_7535091 : Nat := 118140960795 + 7535091 * 2 ^ 59
def prefixEnd_7535091 : Nat := 4983230072969 + 3 ^ 40 * 7535091 * 2
def baseEnd_7535091 : Nat := 3869123458367683655509253

theorem tailTrace_7535091 : CollatzResearch.WordTrace tailWord_7535091 prefixEnd_7535091 3869123458367683655509253 := by
  unfold tailWord_7535091
  simp only [CollatzResearch.WordTrace]
  refine ⟨274827346744659672933277127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183218231163106448622184751 274827346744659672933277127)
  ·
    refine ⟨412241020116989509399915691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274827346744659672933277127 412241020116989509399915691)
    ·
      refine ⟨618361530175484264099873537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412241020116989509399915691 618361530175484264099873537)
      ·
        refine ⟨463771147631613198074905153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618361530175484264099873537 463771147631613198074905153)
        ·
          refine ⟨347828360723709898556178865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463771147631613198074905153 347828360723709898556178865)
          ·
            refine ⟨260871270542782423917134149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347828360723709898556178865 260871270542782423917134149)
            ·
              refine ⟨48913363226771704484462653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260871270542782423917134149 48913363226771704484462653)
              ·
                refine ⟨18342511210039389181673495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48913363226771704484462653 18342511210039389181673495)
                ·
                  refine ⟨27513766815059083772510243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18342511210039389181673495 27513766815059083772510243)
                  ·
                    refine ⟨41270650222588625658765365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27513766815059083772510243 41270650222588625658765365)
                    ·
                      refine ⟨3869123458367683655509253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41270650222588625658765365 3869123458367683655509253)
                      ·
                        rfl

theorem cell23_7535091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_7535091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535091 prefixEnd_7535091 := by exact prefixLift 7535091
  have htrace : WordTrace (prefixWord ++ tailWord_7535091) baseStart_7535091 baseEnd_7535091 := by
    simpa [prefixWord, tailWord_7535091, baseEnd_7535091] using wordTrace_append hprefix tailTrace_7535091
  have hstable : (prefixWord ++ tailWord_7535091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535091).length < 2 ^ (prefixWord ++ tailWord_7535091).sum := by decide
  have hdescent : baseEnd_7535091 < baseStart_7535091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535098 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_7535098 : Nat := 118140960795 + 7535098 * 2 ^ 59
def prefixEnd_7535098 : Nat := 4983230072969 + 3 ^ 40 * 7535098 * 2
def baseEnd_7535098 : Nat := 1289709017577421709373907

theorem tailTrace_7535098 : CollatzResearch.WordTrace tailWord_7535098 prefixEnd_7535098 1289709017577421709373907 := by
  unfold tailWord_7535098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706900513908578282195487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183218401370422875419187965 68706900513908578282195487)
  ·
    refine ⟨103060350770862867423293231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68706900513908578282195487 103060350770862867423293231)
    ·
      refine ⟨154590526156294301134939847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103060350770862867423293231 154590526156294301134939847)
      ·
        refine ⟨231885789234441451702409771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154590526156294301134939847 231885789234441451702409771)
        ·
          refine ⟨347828683851662177553614657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231885789234441451702409771 347828683851662177553614657)
          ·
            refine ⟨260871512888746633165210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347828683851662177553614657 260871512888746633165210993)
            ·
              refine ⟨195653634666559974873908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260871512888746633165210993 195653634666559974873908245)
              ·
                refine ⟨9171264124994998822214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195653634666559974873908245 9171264124994998822214449)
                ·
                  refine ⟨6878448093746249116660837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171264124994998822214449 6878448093746249116660837)
                  ·
                    refine ⟨1289709017577421709373907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878448093746249116660837 1289709017577421709373907)
                    ·
                      rfl

theorem cell23_7535098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_7535098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535098 prefixEnd_7535098 := by exact prefixLift 7535098
  have htrace : WordTrace (prefixWord ++ tailWord_7535098) baseStart_7535098 baseEnd_7535098 := by
    simpa [prefixWord, tailWord_7535098, baseEnd_7535098] using wordTrace_append hprefix tailTrace_7535098
  have hstable : (prefixWord ++ tailWord_7535098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535098).length < 2 ^ (prefixWord ++ tailWord_7535098).sum := by decide
  have hdescent : baseEnd_7535098 < baseStart_7535098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535101 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7535101 : Nat := 118140960795 + 7535101 * 2 ^ 59
def prefixEnd_7535101 : Nat := 4983230072969 + 3 ^ 40 * 7535101 * 2
def baseEnd_7535101 : Nat := 3869128593174228616384207

theorem tailTrace_7535101 : CollatzResearch.WordTrace tailWord_7535101 prefixEnd_7535101 3869128593174228616384207 := by
  unfold tailWord_7535101
  simp only [CollatzResearch.WordTrace]
  refine ⟨274827711474623444641141157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183218474316415629760760771 274827711474623444641141157)
  ·
    refine ⟨51530195901491895870213967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274827711474623444641141157 51530195901491895870213967)
    ·
      refine ⟨77295293852237843805320951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530195901491895870213967 77295293852237843805320951)
      ·
        refine ⟨115942940778356765707981427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77295293852237843805320951 115942940778356765707981427)
        ·
          refine ⟨173914411167535148561972141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115942940778356765707981427 173914411167535148561972141)
          ·
            refine ⟨65217904187825680710739553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173914411167535148561972141 65217904187825680710739553)
            ·
              refine ⟨48913428140869260533054665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65217904187825680710739553 48913428140869260533054665)
              ·
                refine ⟨36685071105651945399790999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48913428140869260533054665 36685071105651945399790999)
                ·
                  refine ⟨55027606658477918099686499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36685071105651945399790999 55027606658477918099686499)
                  ·
                    refine ⟨82541409987716877149529749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55027606658477918099686499 82541409987716877149529749)
                    ·
                      refine ⟨3869128593174228616384207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82541409987716877149529749 3869128593174228616384207)
                      ·
                        rfl

theorem cell23_7535101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7535101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535101 prefixEnd_7535101 := by exact prefixLift 7535101
  have htrace : WordTrace (prefixWord ++ tailWord_7535101) baseStart_7535101 baseEnd_7535101 := by
    simpa [prefixWord, tailWord_7535101, baseEnd_7535101] using wordTrace_append hprefix tailTrace_7535101
  have hstable : (prefixWord ++ tailWord_7535101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535101).length < 2 ^ (prefixWord ++ tailWord_7535101).sum := by decide
  have hdescent : baseEnd_7535101 < baseStart_7535101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535108 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7535108 : Nat := 118140960795 + 7535108 * 2 ^ 59
def prefixEnd_7535108 : Nat := 4983230072969 + 3 ^ 40 * 7535108 * 2
def baseEnd_7535108 : Nat := 3869132187538810088996675

theorem tailTrace_7535108 : CollatzResearch.WordTrace tailWord_7535108 prefixEnd_7535108 3869132187538810088996675 := by
  unfold tailWord_7535108
  simp only [CollatzResearch.WordTrace]
  refine ⟨137413983392799042418322989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183218644523732056557763985 137413983392799042418322989)
  ·
    refine ⟨51530243772299640906871121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137413983392799042418322989 51530243772299640906871121)
    ·
      refine ⟨38647682829224730680153341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51530243772299640906871121 38647682829224730680153341)
      ·
        refine ⟨14492881060959274005057503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38647682829224730680153341 14492881060959274005057503)
        ·
          refine ⟨21739321591438911007586255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492881060959274005057503 21739321591438911007586255)
          ·
            refine ⟨32608982387158366511379383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739321591438911007586255 32608982387158366511379383)
            ·
              refine ⟨48913473580737549767069075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32608982387158366511379383 48913473580737549767069075)
              ·
                refine ⟨73370210371106324650603613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48913473580737549767069075 73370210371106324650603613)
                ·
                  refine ⟨27513828889164871743976355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73370210371106324650603613 27513828889164871743976355)
                  ·
                    refine ⟨41270743333747307615964533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27513828889164871743976355 41270743333747307615964533)
                    ·
                      refine ⟨3869132187538810088996675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41270743333747307615964533 3869132187538810088996675)
                      ·
                        rfl

theorem cell23_7535108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7535108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535108 prefixEnd_7535108 := by exact prefixLift 7535108
  have htrace : WordTrace (prefixWord ++ tailWord_7535108) baseStart_7535108 baseEnd_7535108 := by
    simpa [prefixWord, tailWord_7535108, baseEnd_7535108] using wordTrace_append hprefix tailTrace_7535108
  have hstable : (prefixWord ++ tailWord_7535108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535108).length < 2 ^ (prefixWord ++ tailWord_7535108).sum := by decide
  have hdescent : baseEnd_7535108 < baseStart_7535108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535118 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7535118 : Nat := 118140960795 + 7535118 * 2 ^ 59
def prefixEnd_7535118 : Nat := 4983230072969 + 3 ^ 40 * 7535118 * 2
def baseEnd_7535118 : Nat := 3869137322345355049871629

theorem tailTrace_7535118 : CollatzResearch.WordTrace tailWord_7535118 prefixEnd_7535118 3869137322345355049871629 := by
  unfold tailWord_7535118
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353541439445232068063751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183218887677041237696340005 34353541439445232068063751)
  ·
    refine ⟨51530312159167848102095627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34353541439445232068063751 51530312159167848102095627)
    ·
      refine ⟨77295468238751772153143441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530312159167848102095627 77295468238751772153143441)
      ·
        refine ⟨57971601179063829114857581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77295468238751772153143441 57971601179063829114857581)
        ·
          refine ⟨21739350442148935918071593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57971601179063829114857581 21739350442148935918071593)
          ·
            refine ⟨16304512831611701938553695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21739350442148935918071593 16304512831611701938553695)
            ·
              refine ⟨24456769247417552907830543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16304512831611701938553695 24456769247417552907830543)
              ·
                refine ⟨36685153871126329361745815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24456769247417552907830543 36685153871126329361745815)
                ·
                  refine ⟨55027730806689494042618723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36685153871126329361745815 55027730806689494042618723)
                  ·
                    refine ⟨82541596210034241063928085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55027730806689494042618723 82541596210034241063928085)
                    ·
                      refine ⟨3869137322345355049871629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82541596210034241063928085 3869137322345355049871629)
                      ·
                        rfl

theorem cell23_7535118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7535118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535118 prefixEnd_7535118 := by exact prefixLift 7535118
  have htrace : WordTrace (prefixWord ++ tailWord_7535118) baseStart_7535118 baseEnd_7535118 := by
    simpa [prefixWord, tailWord_7535118, baseEnd_7535118] using wordTrace_append hprefix tailTrace_7535118
  have hstable : (prefixWord ++ tailWord_7535118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535118).length < 2 ^ (prefixWord ++ tailWord_7535118).sum := by decide
  have hdescent : baseEnd_7535118 < baseStart_7535118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535125 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_7535125 : Nat := 118140960795 + 7535125 * 2 ^ 59
def prefixEnd_7535125 : Nat := 4983230072969 + 3 ^ 40 * 7535125 * 2
def baseEnd_7535125 : Nat := 3869140916709936522484097

theorem tailTrace_7535125 : CollatzResearch.WordTrace tailWord_7535125 prefixEnd_7535125 3869140916709936522484097 := by
  unfold tailWord_7535125
  simp only [CollatzResearch.WordTrace]
  refine ⟨274828586826536496740014829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183219057884357664493343219 274828586826536496740014829)
  ·
    refine ⟨103060720059951186277505561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274828586826536496740014829 103060720059951186277505561)
    ·
      refine ⟨77295540044963389708129171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103060720059951186277505561 77295540044963389708129171)
      ·
        refine ⟨115943310067445084562193757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77295540044963389708129171 115943310067445084562193757)
        ·
          refine ⟨43478741275291906710822659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115943310067445084562193757 43478741275291906710822659)
          ·
            refine ⟨65218111912937860066233989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43478741275291906710822659 65218111912937860066233989)
            ·
              refine ⟨12228395983675848762418873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65218111912937860066233989 12228395983675848762418873)
              ·
                refine ⟨9171296987756886571814155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12228395983675848762418873 9171296987756886571814155)
                ·
                  refine ⟨13756945481635329857721233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171296987756886571814155 13756945481635329857721233)
                  ·
                    refine ⟨10317709111226497393290925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13756945481635329857721233 10317709111226497393290925)
                    ·
                      refine ⟨3869140916709936522484097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317709111226497393290925 3869140916709936522484097)
                      ·
                        rfl

theorem cell23_7535125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_7535125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535125 prefixEnd_7535125 := by exact prefixLift 7535125
  have htrace : WordTrace (prefixWord ++ tailWord_7535125) baseStart_7535125 baseEnd_7535125 := by
    simpa [prefixWord, tailWord_7535125, baseEnd_7535125] using wordTrace_append hprefix tailTrace_7535125
  have hstable : (prefixWord ++ tailWord_7535125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535125).length < 2 ^ (prefixWord ++ tailWord_7535125).sum := by decide
  have hdescent : baseEnd_7535125 < baseStart_7535125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535128 : List Nat := [2, 1, 2, 3, 3, 1, 4, 7]
def baseStart_7535128 : Nat := 118140960795 + 7535128 * 2 ^ 59
def prefixEnd_7535128 : Nat := 4983230072969 + 3 ^ 40 * 7535128 * 2
def baseEnd_7535128 : Nat := 143301572487107407805429

theorem tailTrace_7535128 : CollatzResearch.WordTrace tailWord_7535128 prefixEnd_7535128 143301572487107407805429 := by
  unfold tailWord_7535128
  simp only [CollatzResearch.WordTrace]
  refine ⟨137414348122762814126187019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183219130830350418834916025 137414348122762814126187019)
  ·
    refine ⟨206121522184144221189280529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137414348122762814126187019 206121522184144221189280529)
    ·
      refine ⟨154591141638108165891960397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206121522184144221189280529 154591141638108165891960397)
      ·
        refine ⟨57971678114290562209485149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154591141638108165891960397 57971678114290562209485149)
        ·
          refine ⟨21739379292858960828556931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57971678114290562209485149 21739379292858960828556931)
          ·
            refine ⟨32609068939288441242835397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739379292858960828556931 32609068939288441242835397)
            ·
              refine ⟨6114200426116582733031637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32609068939288441242835397 6114200426116582733031637)
              ·
                refine ⟨143301572487107407805429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6114200426116582733031637 143301572487107407805429)
                ·
                  rfl

theorem cell23_7535128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 7].length) (baseStart_7535128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535128 prefixEnd_7535128 := by exact prefixLift 7535128
  have htrace : WordTrace (prefixWord ++ tailWord_7535128) baseStart_7535128 baseEnd_7535128 := by
    simpa [prefixWord, tailWord_7535128, baseEnd_7535128] using wordTrace_append hprefix tailTrace_7535128
  have hstable : (prefixWord ++ tailWord_7535128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535128).length < 2 ^ (prefixWord ++ tailWord_7535128).sum := by decide
  have hdescent : baseEnd_7535128 < baseStart_7535128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535138 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_7535138 : Nat := 118140960795 + 7535138 * 2 ^ 59
def prefixEnd_7535138 : Nat := 4983230072969 + 3 ^ 40 * 7535138 * 2
def baseEnd_7535138 : Nat := 3869147591958444971621537

theorem tailTrace_7535138 : CollatzResearch.WordTrace tailWord_7535138 prefixEnd_7535138 3869147591958444971621537 := by
  unfold tailWord_7535138
  simp only [CollatzResearch.WordTrace]
  refine ⟨68707265243872349990059517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183219373983659599973492045 68707265243872349990059517)
  ·
    refine ⟨25765224466452131246272319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68707265243872349990059517 25765224466452131246272319)
    ·
      refine ⟨38647836699678196869408479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25765224466452131246272319 38647836699678196869408479)
      ·
        refine ⟨57971755049517295304112719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38647836699678196869408479 57971755049517295304112719)
        ·
          refine ⟨86957632574275942956169079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57971755049517295304112719 86957632574275942956169079)
          ·
            refine ⟨130436448861413914434253619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86957632574275942956169079 130436448861413914434253619)
            ·
              refine ⟨195654673292120871651380429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130436448861413914434253619 195654673292120871651380429)
              ·
                refine ⟨73370502484545326869267661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195654673292120871651380429 73370502484545326869267661)
                ·
                  refine ⟨27513938431704497575975373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73370502484545326869267661 27513938431704497575975373)
                  ·
                    refine ⟨10317726911889186590990765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27513938431704497575975373 10317726911889186590990765)
                    ·
                      refine ⟨3869147591958444971621537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317726911889186590990765 3869147591958444971621537)
                      ·
                        rfl

theorem cell23_7535138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_7535138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535138 prefixEnd_7535138 := by exact prefixLift 7535138
  have htrace : WordTrace (prefixWord ++ tailWord_7535138) baseStart_7535138 baseEnd_7535138 := by
    simpa [prefixWord, tailWord_7535138, baseEnd_7535138] using wordTrace_append hprefix tailTrace_7535138
  have hstable : (prefixWord ++ tailWord_7535138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535138).length < 2 ^ (prefixWord ++ tailWord_7535138).sum := by decide
  have hdescent : baseEnd_7535138 < baseStart_7535138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535139 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 1, 2, 2]
def baseStart_7535139 : Nat := 118140960795 + 7535139 * 2 ^ 59
def prefixEnd_7535139 : Nat := 4983230072969 + 3 ^ 40 * 7535139 * 2
def baseEnd_7535139 : Nat := 3869148105439099467709033

theorem tailTrace_7535139 : CollatzResearch.WordTrace tailWord_7535139 prefixEnd_7535139 3869148105439099467709033 := by
  unfold tailWord_7535139
  simp only [CollatzResearch.WordTrace]
  refine ⟨274829097448485777131024471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183219398298990518087349647 274829097448485777131024471)
  ·
    refine ⟨412243646172728665696536707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274829097448485777131024471 412243646172728665696536707)
    ·
      refine ⟨618365469259092998544805061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412243646172728665696536707 618365469259092998544805061)
      ·
        refine ⟨115943525486079937227150949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 618365469259092998544805061 115943525486079937227150949)
        ·
          refine ⟨21739411028639988230090803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115943525486079937227150949 21739411028639988230090803)
          ·
            refine ⟨32609116542959982345136205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739411028639988230090803 32609116542959982345136205)
            ·
              refine ⟨12228418703609993379426077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32609116542959982345136205 12228418703609993379426077)
              ·
                refine ⟨4585657013853747517284779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12228418703609993379426077 4585657013853747517284779)
                ·
                  refine ⟨6878485520780621275927169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585657013853747517284779 6878485520780621275927169)
                  ·
                    refine ⟨5158864140585465956945377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878485520780621275927169 5158864140585465956945377)
                    ·
                      refine ⟨3869148105439099467709033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158864140585465956945377 3869148105439099467709033)
                      ·
                        rfl

theorem cell23_7535139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_7535139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535139 prefixEnd_7535139 := by exact prefixLift 7535139
  have htrace : WordTrace (prefixWord ++ tailWord_7535139) baseStart_7535139 baseEnd_7535139 := by
    simpa [prefixWord, tailWord_7535139, baseEnd_7535139] using wordTrace_append hprefix tailTrace_7535139
  have hstable : (prefixWord ++ tailWord_7535139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535139).length < 2 ^ (prefixWord ++ tailWord_7535139).sum := by decide
  have hdescent : baseEnd_7535139 < baseStart_7535139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535155 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 3]
def baseStart_7535155 : Nat := 118140960795 + 7535155 * 2 ^ 59
def prefixEnd_7535155 : Nat := 4983230072969 + 3 ^ 40 * 7535155 * 2
def baseEnd_7535155 : Nat := 3869156321129571405108959

theorem tailTrace_7535155 : CollatzResearch.WordTrace tailWord_7535155 prefixEnd_7535155 3869156321129571405108959 := by
  unfold tailWord_7535155
  simp only [CollatzResearch.WordTrace]
  refine ⟨274829681016427811863606919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183219787344285207909071279 274829681016427811863606919)
  ·
    refine ⟨412244521524641717795410379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274829681016427811863606919 412244521524641717795410379)
    ·
      refine ⟨618366782286962576693115569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412244521524641717795410379 618366782286962576693115569)
      ·
        refine ⟨463775086715221932519836677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618366782286962576693115569 463775086715221932519836677)
        ·
          refine ⟨86957828759104112347469377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463775086715221932519836677 86957828759104112347469377)
          ·
            refine ⟨65218371569328084260602033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86957828759104112347469377 65218371569328084260602033)
            ·
              refine ⟨48913778676996063195451525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65218371569328084260602033 48913778676996063195451525)
              ·
                refine ⟨9171333501936761849147161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48913778676996063195451525 9171333501936761849147161)
                ·
                  refine ⟨6878500126452571386860371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171333501936761849147161 6878500126452571386860371)
                  ·
                    refine ⟨10317750189678857080290557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878500126452571386860371 10317750189678857080290557)
                    ·
                      refine ⟨3869156321129571405108959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317750189678857080290557 3869156321129571405108959)
                      ·
                        rfl

theorem cell23_7535155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_7535155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535155 prefixEnd_7535155 := by exact prefixLift 7535155
  have htrace : WordTrace (prefixWord ++ tailWord_7535155) baseStart_7535155 baseEnd_7535155 := by
    simpa [prefixWord, tailWord_7535155, baseEnd_7535155] using wordTrace_append hprefix tailTrace_7535155
  have hstable : (prefixWord ++ tailWord_7535155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535155).length < 2 ^ (prefixWord ++ tailWord_7535155).sum := by decide
  have hdescent : baseEnd_7535155 < baseStart_7535155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535166 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_7535166 : Nat := 118140960795 + 7535166 * 2 ^ 59
def prefixEnd_7535166 : Nat := 4983230072969 + 3 ^ 40 * 7535166 * 2
def baseEnd_7535166 : Nat := 1289720656472256954023803

theorem tailTrace_7535166 : CollatzResearch.WordTrace tailWord_7535166 prefixEnd_7535166 1289720656472256954023803 := by
  unfold tailWord_7535166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353760277423495092782169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183220054812925307161504901 34353760277423495092782169)
  ·
    refine ⟨25765320208067621319586627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34353760277423495092782169 25765320208067621319586627)
    ·
      refine ⟨38647980312101431979379941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25765320208067621319586627 38647980312101431979379941)
      ·
        refine ⟨7246496308519018496133739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38647980312101431979379941 7246496308519018496133739)
        ·
          refine ⟨10869744462778527744200609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246496308519018496133739 10869744462778527744200609)
          ·
            refine ⟨8152308347083895808150457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869744462778527744200609 8152308347083895808150457)
            ·
              refine ⟨6114231260312921856112843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8152308347083895808150457 6114231260312921856112843)
              ·
                refine ⟨9171346890469382784169265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114231260312921856112843 9171346890469382784169265)
                ·
                  refine ⟨6878510167852037088126949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171346890469382784169265 6878510167852037088126949)
                  ·
                    refine ⟨1289720656472256954023803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878510167852037088126949 1289720656472256954023803)
                    ·
                      rfl

theorem cell23_7535166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_7535166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535166 prefixEnd_7535166 := by exact prefixLift 7535166
  have htrace : WordTrace (prefixWord ++ tailWord_7535166) baseStart_7535166 baseEnd_7535166 := by
    simpa [prefixWord, tailWord_7535166, baseEnd_7535166] using wordTrace_append hprefix tailTrace_7535166
  have hstable : (prefixWord ++ tailWord_7535166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535166).length < 2 ^ (prefixWord ++ tailWord_7535166).sum := by decide
  have hdescent : baseEnd_7535166 < baseStart_7535166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535171 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 6]
def baseStart_7535171 : Nat := 118140960795 + 7535171 * 2 ^ 59
def prefixEnd_7535171 : Nat := 4983230072969 + 3 ^ 40 * 7535171 * 2
def baseEnd_7535171 : Nat := 1289721512273347780836295

theorem tailTrace_7535171 : CollatzResearch.WordTrace tailWord_7535171 prefixEnd_7535171 1289721512273347780836295 := by
  unfold tailWord_7535171
  simp only [CollatzResearch.WordTrace]
  refine ⟨274830264584369846596189367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183220176389579897730792911 274830264584369846596189367)
  ·
    refine ⟨412245396876554769894284051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274830264584369846596189367 412245396876554769894284051)
    ·
      refine ⟨618368095314832154841426077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412245396876554769894284051 618368095314832154841426077)
      ·
        refine ⟨231888035743062058065534779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618368095314832154841426077 231888035743062058065534779)
        ·
          refine ⟨347832053614593087098302169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231888035743062058065534779 347832053614593087098302169)
          ·
            refine ⟨260874040210944815323726627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347832053614593087098302169 260874040210944815323726627)
            ·
              refine ⟨391311060316417222985589941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260874040210944815323726627 391311060316417222985589941)
              ·
                refine ⟨36685411904664114654899057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391311060316417222985589941 36685411904664114654899057)
                ·
                  refine ⟨27514058928498085991174293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36685411904664114654899057 27514058928498085991174293)
                  ·
                    refine ⟨1289721512273347780836295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27514058928498085991174293 1289721512273347780836295)
                    ·
                      rfl

theorem cell23_7535171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_7535171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535171 prefixEnd_7535171 := by exact prefixLift 7535171
  have htrace : WordTrace (prefixWord ++ tailWord_7535171) baseStart_7535171 baseEnd_7535171 := by
    simpa [prefixWord, tailWord_7535171, baseEnd_7535171] using wordTrace_append hprefix tailTrace_7535171
  have hstable : (prefixWord ++ tailWord_7535171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535171).length < 2 ^ (prefixWord ++ tailWord_7535171).sum := by decide
  have hdescent : baseEnd_7535171 < baseStart_7535171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535182 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_7535182 : Nat := 118140960795 + 7535182 * 2 ^ 59
def prefixEnd_7535182 : Nat := 4983230072969 + 3 ^ 40 * 7535182 * 2
def baseEnd_7535182 : Nat := 3869170185107242799471335

theorem tailTrace_7535182 : CollatzResearch.WordTrace tailWord_7535182 prefixEnd_7535182 3869170185107242799471335 := by
  unfold tailWord_7535182
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353833223416249434354975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183220443858219996983226533 34353833223416249434354975)
  ·
    refine ⟨51530749835124374151532463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34353833223416249434354975 51530749835124374151532463)
    ·
      refine ⟨77296124752686561227298695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530749835124374151532463 77296124752686561227298695)
      ·
        refine ⟨115944187129029841840948043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77296124752686561227298695 115944187129029841840948043)
        ·
          refine ⟨173916280693544762761422065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115944187129029841840948043 173916280693544762761422065)
          ·
            refine ⟨130437210520158572071066549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173916280693544762761422065 130437210520158572071066549)
            ·
              refine ⟨12228488486264866131662489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130437210520158572071066549 12228488486264866131662489)
              ·
                refine ⟨9171366364698649598746867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12228488486264866131662489 9171366364698649598746867)
                ·
                  refine ⟨13757049547047974398120301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171366364698649598746867 13757049547047974398120301)
                  ·
                    refine ⟨5158893580142990399295113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13757049547047974398120301 5158893580142990399295113)
                    ·
                      refine ⟨3869170185107242799471335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158893580142990399295113 3869170185107242799471335)
                      ·
                        rfl

theorem cell23_7535182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_7535182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535182 prefixEnd_7535182 := by exact prefixLift 7535182
  have htrace : WordTrace (prefixWord ++ tailWord_7535182) baseStart_7535182 baseEnd_7535182 := by
    simpa [prefixWord, tailWord_7535182, baseEnd_7535182] using wordTrace_append hprefix tailTrace_7535182
  have hstable : (prefixWord ++ tailWord_7535182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535182).length < 2 ^ (prefixWord ++ tailWord_7535182).sum := by decide
  have hdescent : baseEnd_7535182 < baseStart_7535182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535212 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_7535212 : Nat := 118140960795 + 7535212 * 2 ^ 59
def prefixEnd_7535212 : Nat := 4983230072969 + 3 ^ 40 * 7535212 * 2
def baseEnd_7535212 : Nat := 3869185589526877682096197

theorem tailTrace_7535212 : CollatzResearch.WordTrace tailWord_7535212 prefixEnd_7535212 3869185589526877682096197 := by
  unfold tailWord_7535212
  simp only [CollatzResearch.WordTrace]
  refine ⟨137415879988610655299215945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183221173318147540398954593 137415879988610655299215945)
  ·
    refine ⟨103061909991457991474411959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137415879988610655299215945 103061909991457991474411959)
    ·
      refine ⟨154592864987186987211617939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103061909991457991474411959 154592864987186987211617939)
      ·
        refine ⟨231889297480780480817426909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154592864987186987211617939 231889297480780480817426909)
        ·
          refine ⟨86958486555292680306535091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231889297480780480817426909 86958486555292680306535091)
          ·
            refine ⟨130437729832939020459802637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86958486555292680306535091 130437729832939020459802637)
            ·
              refine ⟨48914148687352132672425989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130437729832939020459802637 48914148687352132672425989)
              ·
                refine ⟨9171402878878524876079873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48914148687352132672425989 9171402878878524876079873)
                ·
                  refine ⟨6878552159158893657059905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171402878878524876079873 6878552159158893657059905)
                  ·
                    refine ⟨5158914119369170242794929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878552159158893657059905 5158914119369170242794929)
                    ·
                      refine ⟨3869185589526877682096197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5158914119369170242794929 3869185589526877682096197)
                      ·
                        rfl

theorem cell23_7535212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_7535212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535212 prefixEnd_7535212 := by exact prefixLift 7535212
  have htrace : WordTrace (prefixWord ++ tailWord_7535212) baseStart_7535212 baseEnd_7535212 := by
    simpa [prefixWord, tailWord_7535212, baseEnd_7535212] using wordTrace_append hprefix tailTrace_7535212
  have hstable : (prefixWord ++ tailWord_7535212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535212).length < 2 ^ (prefixWord ++ tailWord_7535212).sum := by decide
  have hdescent : baseEnd_7535212 < baseStart_7535212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535228 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_7535228 : Nat := 118140960795 + 7535228 * 2 ^ 59
def prefixEnd_7535228 : Nat := 4983230072969 + 3 ^ 40 * 7535228 * 2
def baseEnd_7535228 : Nat := 3869193805217349619496123

theorem tailTrace_7535228 : CollatzResearch.WordTrace tailWord_7535228 prefixEnd_7535228 3869193805217349619496123 := by
  unfold tailWord_7535228
  simp only [CollatzResearch.WordTrace]
  refine ⟨137416171772581672665507169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183221562363442230220676225 137416171772581672665507169)
  ·
    refine ⟨103062128829436254499130377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137416171772581672665507169 103062128829436254499130377)
    ·
      refine ⟨77296596622077190874347783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103062128829436254499130377 77296596622077190874347783)
      ·
        refine ⟨115944894933115786311521675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77296596622077190874347783 115944894933115786311521675)
        ·
          refine ⟨173917342399673679467282513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115944894933115786311521675 173917342399673679467282513)
          ·
            refine ⟨130438006799755259600461885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173917342399673679467282513 130438006799755259600461885)
            ·
              refine ⟨48914252549908222350173207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130438006799755259600461885 48914252549908222350173207)
              ·
                refine ⟨73371378824862333525259811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48914252549908222350173207 73371378824862333525259811)
                ·
                  refine ⟨110057068237293500287889717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73371378824862333525259811 110057068237293500287889717)
                  ·
                    refine ⟨10317850147246265651989661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110057068237293500287889717 10317850147246265651989661)
                    ·
                      refine ⟨3869193805217349619496123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10317850147246265651989661 3869193805217349619496123)
                      ·
                        rfl

theorem cell23_7535228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_7535228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535228 prefixEnd_7535228 := by exact prefixLift 7535228
  have htrace : WordTrace (prefixWord ++ tailWord_7535228) baseStart_7535228 baseEnd_7535228 := by
    simpa [prefixWord, tailWord_7535228, baseEnd_7535228] using wordTrace_append hprefix tailTrace_7535228
  have hstable : (prefixWord ++ tailWord_7535228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535228).length < 2 ^ (prefixWord ++ tailWord_7535228).sum := by decide
  have hdescent : baseEnd_7535228 < baseStart_7535228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535252 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 5]
def baseStart_7535252 : Nat := 118140960795 + 7535252 * 2 ^ 59
def prefixEnd_7535252 : Nat := 4983230072969 + 3 ^ 40 * 7535252 * 2
def baseEnd_7535252 : Nat := 429911792083673058399557

theorem tailTrace_7535252 : CollatzResearch.WordTrace tailWord_7535252 prefixEnd_7535252 429911792083673058399557 := by
  unfold tailWord_7535252
  simp only [CollatzResearch.WordTrace]
  refine ⟨137416609448538198714944005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183222145931384264953258673 137416609448538198714944005)
  ·
    refine ⟨25765614271600912259052001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137416609448538198714944005 25765614271600912259052001)
    ·
      refine ⟨19324210703700684194289001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25765614271600912259052001 19324210703700684194289001)
      ·
        refine ⟨14493158027775513145716751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19324210703700684194289001 14493158027775513145716751)
        ·
          refine ⟨21739737041663269718575127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493158027775513145716751 21739737041663269718575127)
          ·
            refine ⟨32609605562494904577862691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739737041663269718575127 32609605562494904577862691)
            ·
              refine ⟨48914408343742356866794037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32609605562494904577862691 48914408343742356866794037)
              ·
                refine ⟨4585725782225845956261941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48914408343742356866794037 4585725782225845956261941)
                ·
                  refine ⟨429911792083673058399557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585725782225845956261941 429911792083673058399557)
                  ·
                    rfl

theorem cell23_7535252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_7535252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535252 prefixEnd_7535252 := by exact prefixLift 7535252
  have htrace : WordTrace (prefixWord ++ tailWord_7535252) baseStart_7535252 baseEnd_7535252 := by
    simpa [prefixWord, tailWord_7535252, baseEnd_7535252] using wordTrace_append hprefix tailTrace_7535252
  have hstable : (prefixWord ++ tailWord_7535252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535252).length < 2 ^ (prefixWord ++ tailWord_7535252).sum := by decide
  have hdescent : baseEnd_7535252 < baseStart_7535252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535285 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7535285 : Nat := 118140960795 + 7535285 * 2 ^ 59
def prefixEnd_7535285 : Nat := 4983230072969 + 3 ^ 40 * 7535285 * 2
def baseEnd_7535285 : Nat := 3869223073614655896483361

theorem tailTrace_7535285 : CollatzResearch.WordTrace tailWord_7535285 prefixEnd_7535285 3869223073614655896483361 := by
  unfold tailWord_7535285
  simp only [CollatzResearch.WordTrace]
  refine ⟨274834422505956844065839309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183222948337304562710559539 274834422505956844065839309)
  ·
    refine ⟨103062908439733816524689741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274834422505956844065839309 103062908439733816524689741)
    ·
      refine ⟨38648590664900181196758653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103062908439733816524689741 38648590664900181196758653)
      ·
        refine ⟨14493221499337567948784495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38648590664900181196758653 14493221499337567948784495)
        ·
          refine ⟨21739832249006351923176743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493221499337567948784495 21739832249006351923176743)
          ·
            refine ⟨32609748373509527884765115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739832249006351923176743 32609748373509527884765115)
            ·
              refine ⟨48914622560264291827147673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32609748373509527884765115 48914622560264291827147673)
              ·
                refine ⟨36685966920198218870360755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48914622560264291827147673 36685966920198218870360755)
                ·
                  refine ⟨55028950380297328305541133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36685966920198218870360755 55028950380297328305541133)
                  ·
                    refine ⟨20635856392611498114577925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55028950380297328305541133 20635856392611498114577925)
                    ·
                      refine ⟨3869223073614655896483361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20635856392611498114577925 3869223073614655896483361)
                      ·
                        rfl

theorem cell23_7535285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7535285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535285 prefixEnd_7535285 := by exact prefixLift 7535285
  have htrace : WordTrace (prefixWord ++ tailWord_7535285) baseStart_7535285 baseEnd_7535285 := by
    simpa [prefixWord, tailWord_7535285, baseEnd_7535285] using wordTrace_append hprefix tailTrace_7535285
  have hstable : (prefixWord ++ tailWord_7535285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535285).length < 2 ^ (prefixWord ++ tailWord_7535285).sum := by decide
  have hdescent : baseEnd_7535285 < baseStart_7535285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535295 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 3, 4]
def baseStart_7535295 : Nat := 118140960795 + 7535295 * 2 ^ 59
def prefixEnd_7535295 : Nat := 4983230072969 + 3 ^ 40 * 7535295 * 2
def baseEnd_7535295 : Nat := 1289742736140400285786105

theorem tailTrace_7535295 : CollatzResearch.WordTrace tailWord_7535295 prefixEnd_7535295 1289742736140400285786105 := by
  unfold tailWord_7535295
  simp only [CollatzResearch.WordTrace]
  refine ⟨274834787235920615773703339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183223191490613743849135559 274834787235920615773703339)
  ·
    refine ⟨412252180853880923660555009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274834787235920615773703339 412252180853880923660555009)
    ·
      refine ⟨309189135640410692745416257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412252180853880923660555009 309189135640410692745416257)
      ·
        refine ⟨231891851730308019559062193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309189135640410692745416257 231891851730308019559062193)
        ·
          refine ⟨173918888797731014669296645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231891851730308019559062193 173918888797731014669296645)
          ·
            refine ⟨32609791649574565250493121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173918888797731014669296645 32609791649574565250493121)
            ·
              refine ⟨24457343737180923937869841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32609791649574565250493121 24457343737180923937869841)
              ·
                refine ⟨18343007802885692953402381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24457343737180923937869841 18343007802885692953402381)
                ·
                  refine ⟨6878627926082134857525893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18343007802885692953402381 6878627926082134857525893)
                  ·
                    refine ⟨1289742736140400285786105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878627926082134857525893 1289742736140400285786105)
                    ·
                      rfl

theorem cell23_7535295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_7535295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535295 prefixEnd_7535295 := by exact prefixLift 7535295
  have htrace : WordTrace (prefixWord ++ tailWord_7535295) baseStart_7535295 baseEnd_7535295 := by
    simpa [prefixWord, tailWord_7535295, baseEnd_7535295] using wordTrace_append hprefix tailTrace_7535295
  have hstable : (prefixWord ++ tailWord_7535295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535295).length < 2 ^ (prefixWord ++ tailWord_7535295).sum := by decide
  have hdescent : baseEnd_7535295 < baseStart_7535295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535338 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7535338 : Nat := 118140960795 + 7535338 * 2 ^ 59
def prefixEnd_7535338 : Nat := 4983230072969 + 3 ^ 40 * 7535338 * 2
def baseEnd_7535338 : Nat := 1289750096029781396373539

theorem tailTrace_7535338 : CollatzResearch.WordTrace tailWord_7535338 prefixEnd_7535338 1289750096029781396373539 := by
  unfold tailWord_7535338
  simp only [CollatzResearch.WordTrace]
  refine ⟨68709088893691208529379667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183224237049843222745012445 68709088893691208529379667)
  ·
    refine ⟨103063633340536812794069501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68709088893691208529379667 103063633340536812794069501)
    ·
      refine ⟨38648862502701304797776063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103063633340536812794069501 38648862502701304797776063)
      ·
        refine ⟨57973293754051957196664095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38648862502701304797776063 57973293754051957196664095)
        ·
          refine ⟨86959940631077935794996143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57973293754051957196664095 86959940631077935794996143)
          ·
            refine ⟨130439910946616903692494215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86959940631077935794996143 130439910946616903692494215)
            ·
              refine ⟨195659866419925355538741323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130439910946616903692494215 195659866419925355538741323)
              ·
                refine ⟨293489799629888033308111985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195659866419925355538741323 293489799629888033308111985)
                ·
                  refine ⟨220117349722416024981083989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293489799629888033308111985 220117349722416024981083989)
                  ·
                    refine ⟨1289750096029781396373539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220117349722416024981083989 1289750096029781396373539)
                    ·
                      rfl

theorem cell23_7535338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7535338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535338 prefixEnd_7535338 := by exact prefixLift 7535338
  have htrace : WordTrace (prefixWord ++ tailWord_7535338) baseStart_7535338 baseEnd_7535338 := by
    simpa [prefixWord, tailWord_7535338, baseEnd_7535338] using wordTrace_append hprefix tailTrace_7535338
  have hstable : (prefixWord ++ tailWord_7535338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535338).length < 2 ^ (prefixWord ++ tailWord_7535338).sum := by decide
  have hdescent : baseEnd_7535338 < baseStart_7535338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535342 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_7535342 : Nat := 118140960795 + 7535342 * 2 ^ 59
def prefixEnd_7535342 : Nat := 4983230072969 + 3 ^ 40 * 7535342 * 2
def baseEnd_7535342 : Nat := 429916926890218019274511

theorem tailTrace_7535342 : CollatzResearch.WordTrace tailWord_7535342 prefixEnd_7535342 429916926890218019274511 := by
  unfold tailWord_7535342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34354562683343792850083035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183224334311166895200442853 34354562683343792850083035)
  ·
    refine ⟨51531844025015689275124553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34354562683343792850083035 51531844025015689275124553)
    ·
      refine ⟨38648883018761766956343415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51531844025015689275124553 38648883018761766956343415)
      ·
        refine ⟨57973324528142650434515123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38648883018761766956343415 57973324528142650434515123)
        ·
          refine ⟨86959986792213975651772685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57973324528142650434515123 86959986792213975651772685)
          ·
            refine ⟨32609995047080240869414757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86959986792213975651772685 32609995047080240869414757)
            ·
              refine ⟨6114374071327545163015267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32609995047080240869414757 6114374071327545163015267)
              ·
                refine ⟨9171561106991317744522901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114374071327545163015267 9171561106991317744522901)
                ·
                  refine ⟨429916926890218019274511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9171561106991317744522901 429916926890218019274511)
                  ·
                    rfl

theorem cell23_7535342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_7535342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535342 prefixEnd_7535342 := by exact prefixLift 7535342
  have htrace : WordTrace (prefixWord ++ tailWord_7535342) baseStart_7535342 baseEnd_7535342 := by
    simpa [prefixWord, tailWord_7535342, baseEnd_7535342] using wordTrace_append hprefix tailTrace_7535342
  have hstable : (prefixWord ++ tailWord_7535342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535342).length < 2 ^ (prefixWord ++ tailWord_7535342).sum := by decide
  have hdescent : baseEnd_7535342 < baseStart_7535342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535408 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_7535408 : Nat := 118140960795 + 7535408 * 2 ^ 59
def prefixEnd_7535408 : Nat := 4983230072969 + 3 ^ 40 * 7535408 * 2
def baseEnd_7535408 : Nat := 3869286231735158915245295

theorem tailTrace_7535408 : CollatzResearch.WordTrace tailWord_7535408 prefixEnd_7535408 3869286231735158915245295 := by
  unfold tailWord_7535408
  simp only [CollatzResearch.WordTrace]
  refine ⟨137419454342255618036283439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183225939123007490715044585 137419454342255618036283439)
  ·
    refine ⟨206129181513383427054425159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137419454342255618036283439 206129181513383427054425159)
    ·
      refine ⟨309193772270075140581637739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206129181513383427054425159 309193772270075140581637739)
      ·
        refine ⟨463790658405112710872456609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309193772270075140581637739 463790658405112710872456609)
        ·
          refine ⟨347842993803834533154342457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463790658405112710872456609 347842993803834533154342457)
          ·
            refine ⟨260882245352875899865756843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347842993803834533154342457 260882245352875899865756843)
            ·
              refine ⟨391323368029313849798635265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260882245352875899865756843 391323368029313849798635265)
              ·
                refine ⟨293492526021985387348976449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391323368029313849798635265 293492526021985387348976449)
                ·
                  refine ⟨220119394516489040511732337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293492526021985387348976449 220119394516489040511732337)
                  ·
                    refine ⟨165089545887366780383799253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220119394516489040511732337 165089545887366780383799253)
                    ·
                      refine ⟨3869286231735158915245295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165089545887366780383799253 3869286231735158915245295)
                      ·
                        rfl

theorem cell23_7535408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_7535408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535408 prefixEnd_7535408 := by exact prefixLift 7535408
  have htrace : WordTrace (prefixWord ++ tailWord_7535408) baseStart_7535408 baseEnd_7535408 := by
    simpa [prefixWord, tailWord_7535408, baseEnd_7535408] using wordTrace_append hprefix tailTrace_7535408
  have hstable : (prefixWord ++ tailWord_7535408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535408).length < 2 ^ (prefixWord ++ tailWord_7535408).sum := by decide
  have hdescent : baseEnd_7535408 < baseStart_7535408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535409 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_7535409 : Nat := 118140960795 + 7535409 * 2 ^ 59
def prefixEnd_7535409 : Nat := 4983230072969 + 3 ^ 40 * 7535409 * 2
def baseEnd_7535409 : Nat := 3869286745215813411332791

theorem tailTrace_7535409 : CollatzResearch.WordTrace tailWord_7535409 prefixEnd_7535409 3869286745215813411332791 := by
  unfold tailWord_7535409
  simp only [CollatzResearch.WordTrace]
  refine ⟨274838945157507613243353281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183225963438338408828902187 274838945157507613243353281)
  ·
    refine ⟨206129208868130709932514961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274838945157507613243353281 206129208868130709932514961)
    ·
      refine ⟨154596906651098032449386221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206129208868130709932514961 154596906651098032449386221)
      ·
        refine ⟨57973839994161762168519833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154596906651098032449386221 57973839994161762168519833)
        ·
          refine ⟨43480379995621321626389875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57973839994161762168519833 43480379995621321626389875)
          ·
            refine ⟨65220569993431982439584813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43480379995621321626389875 65220569993431982439584813)
            ·
              refine ⟨24457713747536993414844305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65220569993431982439584813 24457713747536993414844305)
              ·
                refine ⟨18343285310652745061133229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24457713747536993414844305 18343285310652745061133229)
                ·
                  refine ⟨6878731991494779397924961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18343285310652745061133229 6878731991494779397924961)
                  ·
                    refine ⟨5159048993621084548443721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878731991494779397924961 5159048993621084548443721)
                    ·
                      refine ⟨3869286745215813411332791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159048993621084548443721 3869286745215813411332791)
                      ·
                        rfl

theorem cell23_7535409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_7535409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535409 prefixEnd_7535409 := by exact prefixLift 7535409
  have htrace : WordTrace (prefixWord ++ tailWord_7535409) baseStart_7535409 baseEnd_7535409 := by
    simpa [prefixWord, tailWord_7535409, baseEnd_7535409] using wordTrace_append hprefix tailTrace_7535409
  have hstable : (prefixWord ++ tailWord_7535409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535409).length < 2 ^ (prefixWord ++ tailWord_7535409).sum := by decide
  have hdescent : baseEnd_7535409 < baseStart_7535409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535415 : List Nat := [1, 1, 3, 1, 2, 1, 7, 7]
def baseStart_7535415 : Nat := 118140960795 + 7535415 * 2 ^ 59
def prefixEnd_7535415 : Nat := 4983230072969 + 3 ^ 40 * 7535415 * 2
def baseEnd_7535415 : Nat := 143307030596286681031769

theorem tailTrace_7535415 : CollatzResearch.WordTrace tailWord_7535415 prefixEnd_7535415 143307030596286681031769 := by
  unfold tailWord_7535415
  simp only [CollatzResearch.WordTrace]
  refine ⟨274839163995485876268071699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183226109330323917512047799 274839163995485876268071699)
  ·
    refine ⟨412258745993228814402107549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274839163995485876268071699 412258745993228814402107549)
    ·
      refine ⟨154597029747460805400790331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412258745993228814402107549 154597029747460805400790331)
      ·
        refine ⟨231895544621191208101185497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154597029747460805400790331 231895544621191208101185497)
        ·
          refine ⟨173921658465893406075889123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231895544621191208101185497 173921658465893406075889123)
          ·
            refine ⟨260882487698840109113833685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173921658465893406075889123 260882487698840109113833685)
            ·
              refine ⟨6114433305441565057355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 260882487698840109113833685 6114433305441565057355477)
              ·
                refine ⟨143307030596286681031769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6114433305441565057355477 143307030596286681031769)
                ·
                  rfl

theorem cell23_7535415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 7].length) (baseStart_7535415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535415 prefixEnd_7535415 := by exact prefixLift 7535415
  have htrace : WordTrace (prefixWord ++ tailWord_7535415) baseStart_7535415 baseEnd_7535415 := by
    simpa [prefixWord, tailWord_7535415, baseEnd_7535415] using wordTrace_append hprefix tailTrace_7535415
  have hstable : (prefixWord ++ tailWord_7535415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535415).length < 2 ^ (prefixWord ++ tailWord_7535415).sum := by decide
  have hdescent : baseEnd_7535415 < baseStart_7535415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535459 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 3]
def baseStart_7535459 : Nat := 118140960795 + 7535459 * 2 ^ 59
def prefixEnd_7535459 : Nat := 4983230072969 + 3 ^ 40 * 7535459 * 2
def baseEnd_7535459 : Nat := 3869312419248538215707561

theorem tailTrace_7535459 : CollatzResearch.WordTrace tailWord_7535459 prefixEnd_7535459 3869312419248538215707561 := by
  unfold tailWord_7535459
  simp only [CollatzResearch.WordTrace]
  refine ⟨274840768807326471782673431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183227179204884314521782287 274840768807326471782673431)
  ·
    refine ⟨412261153210989707674010147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274840768807326471782673431 412261153210989707674010147)
    ·
      refine ⟨618391729816484561511015221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412261153210989707674010147 618391729816484561511015221)
      ·
        refine ⟨57974224670295427641657677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 618391729816484561511015221 57974224670295427641657677)
        ·
          refine ⟨21740334251360785365621629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57974224670295427641657677 21740334251360785365621629)
          ·
            refine ⟨8152625344260294512108111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21740334251360785365621629 8152625344260294512108111)
            ·
              refine ⟨12228938016390441768162167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152625344260294512108111 12228938016390441768162167)
              ·
                refine ⟨18343407024585662652243251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12228938016390441768162167 18343407024585662652243251)
                ·
                  refine ⟨27515110536878493978364877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18343407024585662652243251 27515110536878493978364877)
                  ·
                    refine ⟨10318166451329435241886829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27515110536878493978364877 10318166451329435241886829)
                    ·
                      refine ⟨3869312419248538215707561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318166451329435241886829 3869312419248538215707561)
                      ·
                        rfl

theorem cell23_7535459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_7535459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535459 prefixEnd_7535459 := by exact prefixLift 7535459
  have htrace : WordTrace (prefixWord ++ tailWord_7535459) baseStart_7535459 baseEnd_7535459 := by
    simpa [prefixWord, tailWord_7535459, baseEnd_7535459] using wordTrace_append hprefix tailTrace_7535459
  have hstable : (prefixWord ++ tailWord_7535459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535459).length < 2 ^ (prefixWord ++ tailWord_7535459).sum := by decide
  have hdescent : baseEnd_7535459 < baseStart_7535459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535482 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_7535482 : Nat := 118140960795 + 7535482 * 2 ^ 59
def prefixEnd_7535482 : Nat := 4983230072969 + 3 ^ 40 * 7535482 * 2
def baseEnd_7535482 : Nat := 3869324229303591625719955

theorem tailTrace_7535482 : CollatzResearch.WordTrace tailWord_7535482 prefixEnd_7535482 3869324229303591625719955 := by
  unfold tailWord_7535482
  simp only [CollatzResearch.WordTrace]
  refine ⟨68710401921560786677690175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183227738457495431140507133 68710401921560786677690175)
  ·
    refine ⟨103065602882341180016535263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68710401921560786677690175 103065602882341180016535263)
    ·
      refine ⟨154598404323511770024802895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103065602882341180016535263 154598404323511770024802895)
      ·
        refine ⟨231897606485267655037204343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154598404323511770024802895 231897606485267655037204343)
        ·
          refine ⟨347846409727901482555806515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231897606485267655037204343 347846409727901482555806515)
          ·
            refine ⟨521769614591852223833709773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347846409727901482555806515 521769614591852223833709773)
            ·
              refine ⟨195663605471944583937641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521769614591852223833709773 195663605471944583937641165)
              ·
                refine ⟨73373852051979218976615437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195663605471944583937641165 73373852051979218976615437)
                ·
                  refine ⟨27515194519492207116230789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73373852051979218976615437 27515194519492207116230789)
                  ·
                    refine ⟨5159098972404788834293273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27515194519492207116230789 5159098972404788834293273)
                    ·
                      refine ⟨3869324229303591625719955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159098972404788834293273 3869324229303591625719955)
                      ·
                        rfl

theorem cell23_7535482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_7535482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535482 prefixEnd_7535482 := by exact prefixLift 7535482
  have htrace : WordTrace (prefixWord ++ tailWord_7535482) baseStart_7535482 baseEnd_7535482 := by
    simpa [prefixWord, tailWord_7535482, baseEnd_7535482] using wordTrace_append hprefix tailTrace_7535482
  have hstable : (prefixWord ++ tailWord_7535482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535482).length < 2 ^ (prefixWord ++ tailWord_7535482).sum := by decide
  have hdescent : baseEnd_7535482 < baseStart_7535482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535485 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7535485 : Nat := 118140960795 + 7535485 * 2 ^ 59
def prefixEnd_7535485 : Nat := 4983230072969 + 3 ^ 40 * 7535485 * 2
def baseEnd_7535485 : Nat := 3869325769745555113982441

theorem tailTrace_7535485 : CollatzResearch.WordTrace tailWord_7535485 prefixEnd_7535485 3869325769745555113982441 := by
  unfold tailWord_7535485
  simp only [CollatzResearch.WordTrace]
  refine ⟨274841717105232278223119909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183227811403488185482079939 274841717105232278223119909)
  ·
    refine ⟨51532821957231052166834983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274841717105232278223119909 51532821957231052166834983)
    ·
      refine ⟨77299232935846578250252475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51532821957231052166834983 77299232935846578250252475)
      ·
        refine ⟨115948849403769867375378713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77299232935846578250252475 115948849403769867375378713)
        ·
          refine ⟨86961637052827400531534035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115948849403769867375378713 86961637052827400531534035)
          ·
            refine ⟨130442455579241100797301053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86961637052827400531534035 130442455579241100797301053)
            ·
              refine ⟨48915920842215412798987895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130442455579241100797301053 48915920842215412798987895)
              ·
                refine ⟨73373881263323119198481843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48915920842215412798987895 73373881263323119198481843)
                ·
                  refine ⟨110060821894984678797722765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73373881263323119198481843 110060821894984678797722765)
                  ·
                    refine ⟨41272808210619254549146037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110060821894984678797722765 41272808210619254549146037)
                    ·
                      refine ⟨3869325769745555113982441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41272808210619254549146037 3869325769745555113982441)
                      ·
                        rfl

theorem cell23_7535485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7535485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535485 prefixEnd_7535485 := by exact prefixLift 7535485
  have htrace : WordTrace (prefixWord ++ tailWord_7535485) baseStart_7535485 baseEnd_7535485 := by
    simpa [prefixWord, tailWord_7535485, baseEnd_7535485] using wordTrace_append hprefix tailTrace_7535485
  have hstable : (prefixWord ++ tailWord_7535485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535485).length < 2 ^ (prefixWord ++ tailWord_7535485).sum := by decide
  have hdescent : baseEnd_7535485 < baseStart_7535485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535499 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 4, 2, 2]
def baseStart_7535499 : Nat := 118140960795 + 7535499 * 2 ^ 59
def prefixEnd_7535499 : Nat := 4983230072969 + 3 ^ 40 * 7535499 * 2
def baseEnd_7535499 : Nat := 3869332958474718059207377

theorem tailTrace_7535499 : CollatzResearch.WordTrace tailWord_7535499 prefixEnd_7535499 3869332958474718059207377 := by
  unfold tailWord_7535499
  simp only [CollatzResearch.WordTrace]
  refine ⟨274842227727181558614129551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183228151818121039076086367 274842227727181558614129551)
  ·
    refine ⟨412263341590772337921194327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274842227727181558614129551 412263341590772337921194327)
    ·
      refine ⟨618395012386158506881791491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412263341590772337921194327 618395012386158506881791491)
      ·
        refine ⟨927592518579237760322687237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618395012386158506881791491 927592518579237760322687237)
        ·
          refine ⟨173923597233607080060503857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 927592518579237760322687237 173923597233607080060503857)
          ·
            refine ⟨130442697925205310045377893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173923597233607080060503857 130442697925205310045377893)
            ·
              refine ⟨24458005860975995633508355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130442697925205310045377893 24458005860975995633508355)
              ·
                refine ⟨36687008791463993450262533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24458005860975995633508355 36687008791463993450262533)
                ·
                  refine ⟨6878814148399498771924225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36687008791463993450262533 6878814148399498771924225)
                  ·
                    refine ⟨5159110611299624078943169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878814148399498771924225 5159110611299624078943169)
                    ·
                      refine ⟨3869332958474718059207377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159110611299624078943169 3869332958474718059207377)
                      ·
                        rfl

theorem cell23_7535499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 2, 2].length) (baseStart_7535499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535499 prefixEnd_7535499 := by exact prefixLift 7535499
  have htrace : WordTrace (prefixWord ++ tailWord_7535499) baseStart_7535499 baseEnd_7535499 := by
    simpa [prefixWord, tailWord_7535499, baseEnd_7535499] using wordTrace_append hprefix tailTrace_7535499
  have hstable : (prefixWord ++ tailWord_7535499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535499).length < 2 ^ (prefixWord ++ tailWord_7535499).sum := by decide
  have hdescent : baseEnd_7535499 < baseStart_7535499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535510 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7535510 : Nat := 118140960795 + 7535510 * 2 ^ 59
def prefixEnd_7535510 : Nat := 4983230072969 + 3 ^ 40 * 7535510 * 2
def baseEnd_7535510 : Nat := 3869338606761917516169827

theorem tailTrace_7535510 : CollatzResearch.WordTrace tailWord_7535510 prefixEnd_7535510 3869338606761917516169827 := by
  unfold tailWord_7535510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177664308133856718298749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183228419286761138328519989 17177664308133856718298749)
  ·
    refine ⟨6441624115550196269362031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17177664308133856718298749 6441624115550196269362031)
    ·
      refine ⟨9662436173325294404043047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441624115550196269362031 9662436173325294404043047)
      ·
        refine ⟨14493654259987941606064571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662436173325294404043047 14493654259987941606064571)
        ·
          refine ⟨21740481389981912409096857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493654259987941606064571 21740481389981912409096857)
          ·
            refine ⟨16305361042486434306822643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21740481389981912409096857 16305361042486434306822643)
            ·
              refine ⟨24458041563729651460233965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305361042486434306822643 24458041563729651460233965)
              ·
                refine ⟨9171765586398619297587737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24458041563729651460233965 9171765586398619297587737)
                ·
                  refine ⟨6878824189798964473190803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171765586398619297587737 6878824189798964473190803)
                  ·
                    refine ⟨10318236284698446709786205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878824189798964473190803 10318236284698446709786205)
                    ·
                      refine ⟨3869338606761917516169827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318236284698446709786205 3869338606761917516169827)
                      ·
                        rfl

theorem cell23_7535510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7535510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535510 prefixEnd_7535510 := by exact prefixLift 7535510
  have htrace : WordTrace (prefixWord ++ tailWord_7535510) baseStart_7535510 baseEnd_7535510 := by
    simpa [prefixWord, tailWord_7535510, baseEnd_7535510] using wordTrace_append hprefix tailTrace_7535510
  have hstable : (prefixWord ++ tailWord_7535510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535510).length < 2 ^ (prefixWord ++ tailWord_7535510).sum := by decide
  have hdescent : baseEnd_7535510 < baseStart_7535510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535533 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7535533 : Nat := 118140960795 + 7535533 * 2 ^ 59
def prefixEnd_7535533 : Nat := 4983230072969 + 3 ^ 40 * 7535533 * 2
def baseEnd_7535533 : Nat := 3869350416816970926182221

theorem tailTrace_7535533 : CollatzResearch.WordTrace tailWord_7535533 prefixEnd_7535533 3869350416816970926182221 := by
  unfold tailWord_7535533
  simp only [CollatzResearch.WordTrace]
  refine ⟨274843467809058382420867253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183228978539372254947244835 274843467809058382420867253)
  ·
    refine ⟨25766575107099223351956305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274843467809058382420867253 25766575107099223351956305)
    ·
      refine ⟨19324931330324417513967229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25766575107099223351956305 19324931330324417513967229)
      ·
        refine ⟨7246849248871656567737711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19324931330324417513967229 7246849248871656567737711)
        ·
          refine ⟨10870273873307484851606567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246849248871656567737711 10870273873307484851606567)
          ·
            refine ⟨16305410809961227277409851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870273873307484851606567 16305410809961227277409851)
            ·
              refine ⟨24458116214941840916114777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305410809961227277409851 24458116214941840916114777)
              ·
                refine ⟨18343587161206380687086083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24458116214941840916114777 18343587161206380687086083)
                ·
                  refine ⟨27515380741809571030629125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18343587161206380687086083 27515380741809571030629125)
                  ·
                    refine ⟨5159133889089294568242961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27515380741809571030629125 5159133889089294568242961)
                    ·
                      refine ⟨3869350416816970926182221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159133889089294568242961 3869350416816970926182221)
                      ·
                        rfl

theorem cell23_7535533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7535533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535533 prefixEnd_7535533 := by exact prefixLift 7535533
  have htrace : WordTrace (prefixWord ++ tailWord_7535533) baseStart_7535533 baseEnd_7535533 := by
    simpa [prefixWord, tailWord_7535533, baseEnd_7535533] using wordTrace_append hprefix tailTrace_7535533
  have hstable : (prefixWord ++ tailWord_7535533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535533).length < 2 ^ (prefixWord ++ tailWord_7535533).sum := by decide
  have hdescent : baseEnd_7535533 < baseStart_7535533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535552 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_7535552 : Nat := 118140960795 + 7535552 * 2 ^ 59
def prefixEnd_7535552 : Nat := 4983230072969 + 3 ^ 40 * 7535552 * 2
def baseEnd_7535552 : Nat := 1289786724316468783948211

theorem tailTrace_7535552 : CollatzResearch.WordTrace tailWord_7535552 prefixEnd_7535552 1289786724316468783948211 := by
  unfold tailWord_7535552
  simp only [CollatzResearch.WordTrace]
  refine ⟨137422080397994774332904455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183229440530659699110539273 137422080397994774332904455)
  ·
    refine ⟨206133120596992161499356683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137422080397994774332904455 206133120596992161499356683)
    ·
      refine ⟨309199680895488242249035025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206133120596992161499356683 309199680895488242249035025)
      ·
        refine ⟨231899760671616181686776269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309199680895488242249035025 231899760671616181686776269)
        ·
          refine ⟨86962410251856068132541101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231899760671616181686776269 86962410251856068132541101)
          ·
            refine ⟨32610903844446025549702913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86962410251856068132541101 32610903844446025549702913)
            ·
              refine ⟨24458177883334519162277185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32610903844446025549702913 24458177883334519162277185)
              ·
                refine ⟨18343633412500889371707889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24458177883334519162277185 18343633412500889371707889)
                ·
                  refine ⟨13757725059375667028780917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18343633412500889371707889 13757725059375667028780917)
                  ·
                    refine ⟨1289786724316468783948211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13757725059375667028780917 1289786724316468783948211)
                    ·
                      rfl

theorem cell23_7535552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_7535552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535552 prefixEnd_7535552 := by exact prefixLift 7535552
  have htrace : WordTrace (prefixWord ++ tailWord_7535552) baseStart_7535552 baseEnd_7535552 := by
    simpa [prefixWord, tailWord_7535552, baseEnd_7535552] using wordTrace_append hprefix tailTrace_7535552
  have hstable : (prefixWord ++ tailWord_7535552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535552).length < 2 ^ (prefixWord ++ tailWord_7535552).sum := by decide
  have hdescent : baseEnd_7535552 < baseStart_7535552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535586 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7535586 : Nat := 118140960795 + 7535586 * 2 ^ 59
def prefixEnd_7535586 : Nat := 4983230072969 + 3 ^ 40 * 7535586 * 2
def baseEnd_7535586 : Nat := 1289792543763886406273159

theorem tailTrace_7535586 : CollatzResearch.WordTrace tailWord_7535586 prefixEnd_7535586 1289792543763886406273159 := by
  unfold tailWord_7535586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68711350219466593118136653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183230267251910914981697741 68711350219466593118136653)
  ·
    refine ⟨25766756332299972419301245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68711350219466593118136653 25766756332299972419301245)
    ·
      refine ⟨9662533624612489657237967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25766756332299972419301245 9662533624612489657237967)
      ·
        refine ⟨14493800436918734485856951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662533624612489657237967 14493800436918734485856951)
        ·
          refine ⟨21740700655378101728785427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493800436918734485856951 21740700655378101728785427)
          ·
            refine ⟨32611050983067152593178141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21740700655378101728785427 32611050983067152593178141)
            ·
              refine ⟨12229144118650182222441803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32611050983067152593178141 12229144118650182222441803)
              ·
                refine ⟨18343716177975273333662705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229144118650182222441803 18343716177975273333662705)
                ·
                  refine ⟨13757787133481455000247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18343716177975273333662705 13757787133481455000247029)
                  ·
                    refine ⟨1289792543763886406273159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13757787133481455000247029 1289792543763886406273159)
                    ·
                      rfl

theorem cell23_7535586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7535586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535586 prefixEnd_7535586 := by exact prefixLift 7535586
  have htrace : WordTrace (prefixWord ++ tailWord_7535586) baseStart_7535586 baseEnd_7535586 := by
    simpa [prefixWord, tailWord_7535586, baseEnd_7535586] using wordTrace_append hprefix tailTrace_7535586
  have hstable : (prefixWord ++ tailWord_7535586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535586).length < 2 ^ (prefixWord ++ tailWord_7535586).sum := by decide
  have hdescent : baseEnd_7535586 < baseStart_7535586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535606 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7535606 : Nat := 118140960795 + 7535606 * 2 ^ 59
def prefixEnd_7535606 : Nat := 4983230072969 + 3 ^ 40 * 7535606 * 2
def baseEnd_7535606 : Nat := 3869387900904749140569385

theorem tailTrace_7535606 : CollatzResearch.WordTrace tailWord_7535606 prefixEnd_7535606 3869387900904749140569385 := by
  unfold tailWord_7535606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177883146112119743017167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183230753558529277258849781 17177883146112119743017167)
  ·
    refine ⟨25766824719168179614525751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17177883146112119743017167 25766824719168179614525751)
    ·
      refine ⟨38650237078752269421788627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25766824719168179614525751 38650237078752269421788627)
      ·
        refine ⟨57975355618128404132682941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38650237078752269421788627 57975355618128404132682941)
        ·
          refine ⟨21740758356798151549756103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57975355618128404132682941 21740758356798151549756103)
          ·
            refine ⟨32611137535197227324634155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21740758356798151549756103 32611137535197227324634155)
            ·
              refine ⟨48916706302795840986951233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32611137535197227324634155 48916706302795840986951233)
              ·
                refine ⟨36687529727096880740213425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48916706302795840986951233 36687529727096880740213425)
                ·
                  refine ⟨27515647295322660555160069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36687529727096880740213425 27515647295322660555160069)
                  ·
                    refine ⟨5159183867872998854092513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27515647295322660555160069 5159183867872998854092513)
                    ·
                      refine ⟨3869387900904749140569385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159183867872998854092513 3869387900904749140569385)
                      ·
                        rfl

theorem cell23_7535606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7535606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535606 prefixEnd_7535606 := by exact prefixLift 7535606
  have htrace : WordTrace (prefixWord ++ tailWord_7535606) baseStart_7535606 baseEnd_7535606 := by
    simpa [prefixWord, tailWord_7535606, baseEnd_7535606] using wordTrace_append hprefix tailTrace_7535606
  have hstable : (prefixWord ++ tailWord_7535606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535606).length < 2 ^ (prefixWord ++ tailWord_7535606).sum := by decide
  have hdescent : baseEnd_7535606 < baseStart_7535606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535612 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 8]
def baseStart_7535612 : Nat := 118140960795 + 7535612 * 2 ^ 59
def prefixEnd_7535612 : Nat := 4983230072969 + 3 ^ 40 * 7535612 * 2
def baseEnd_7535612 : Nat := 429932331309852901899373

theorem tailTrace_7535612 : CollatzResearch.WordTrace tailWord_7535612 prefixEnd_7535612 429932331309852901899373 := by
  unfold tailWord_7535612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137423174587886089456496545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183230899450514785941995393 137423174587886089456496545)
  ·
    refine ⟨103067380940914567092372409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137423174587886089456496545 103067380940914567092372409)
    ·
      refine ⟨77300535705685925319279307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103067380940914567092372409 77300535705685925319279307)
      ·
        refine ⟨115950803558528887978918961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77300535705685925319279307 115950803558528887978918961)
        ·
          refine ⟨86963102668896665984189221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115950803558528887978918961 86963102668896665984189221)
          ·
            refine ⟨16305581750418124872035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86963102668896665984189221 16305581750418124872035479)
            ·
              refine ⟨24458372625627187308053219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305581750418124872035479 24458372625627187308053219)
              ·
                refine ⟨36687558938440780962079829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24458372625627187308053219 36687558938440780962079829)
                ·
                  refine ⟨429932331309852901899373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36687558938440780962079829 429932331309852901899373)
                  ·
                    rfl

theorem cell23_7535612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_7535612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535612 prefixEnd_7535612 := by exact prefixLift 7535612
  have htrace : WordTrace (prefixWord ++ tailWord_7535612) baseStart_7535612 baseEnd_7535612 := by
    simpa [prefixWord, tailWord_7535612, baseEnd_7535612] using wordTrace_append hprefix tailTrace_7535612
  have hstable : (prefixWord ++ tailWord_7535612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535612).length < 2 ^ (prefixWord ++ tailWord_7535612).sum := by decide
  have hdescent : baseEnd_7535612 < baseStart_7535612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535666 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_7535666 : Nat := 118140960795 + 7535666 * 2 ^ 59
def prefixEnd_7535666 : Nat := 4983230072969 + 3 ^ 40 * 7535666 * 2
def baseEnd_7535666 : Nat := 3869418709744018905819109

theorem tailTrace_7535666 : CollatzResearch.WordTrace tailWord_7535666 prefixEnd_7535666 3869418709744018905819109 := by
  unfold tailWord_7535666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68712079679394136533864713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183232212478384364090305901 68712079679394136533864713)
  ·
    refine ⟨51534059759545602400398535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68712079679394136533864713 51534059759545602400398535)
    ·
      refine ⟨77301089639318403600597803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51534059759545602400398535 77301089639318403600597803)
      ·
        refine ⟨115951634458977605400896705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77301089639318403600597803 115951634458977605400896705)
        ·
          refine ⟨86963725844233204050672529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115951634458977605400896705 86963725844233204050672529)
          ·
            refine ⟨65222794383174903038004397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86963725844233204050672529 65222794383174903038004397)
            ·
              refine ⟨24458547893690588639251649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65222794383174903038004397 24458547893690588639251649)
              ·
                refine ⟨18343910920267941479438737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24458547893690588639251649 18343910920267941479438737)
                ·
                  refine ⟨13757933190200956109579053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18343910920267941479438737 13757933190200956109579053)
                  ·
                    refine ⟨5159224946325358541092145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13757933190200956109579053 5159224946325358541092145)
                    ·
                      refine ⟨3869418709744018905819109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159224946325358541092145 3869418709744018905819109)
                      ·
                        rfl

theorem cell23_7535666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_7535666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535666 prefixEnd_7535666 := by exact prefixLift 7535666
  have htrace : WordTrace (prefixWord ++ tailWord_7535666) baseStart_7535666 baseEnd_7535666 := by
    simpa [prefixWord, tailWord_7535666, baseEnd_7535666] using wordTrace_append hprefix tailTrace_7535666
  have hstable : (prefixWord ++ tailWord_7535666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535666).length < 2 ^ (prefixWord ++ tailWord_7535666).sum := by decide
  have hdescent : baseEnd_7535666 < baseStart_7535666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535673 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7535673 : Nat := 118140960795 + 7535673 * 2 ^ 59
def prefixEnd_7535673 : Nat := 4983230072969 + 3 ^ 40 * 7535673 * 2
def baseEnd_7535673 : Nat := 3869422304108600378431577

theorem tailTrace_7535673 : CollatzResearch.WordTrace tailWord_7535673 prefixEnd_7535673 3869422304108600378431577 := by
  unfold tailWord_7535673
  simp only [CollatzResearch.WordTrace]
  refine ⟨274848574028551186330963673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183232382685700790887309115 274848574028551186330963673)
  ·
    refine ⟨206136430521413389748222755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274848574028551186330963673 206136430521413389748222755)
    ·
      refine ⟨309204645782120084622334133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206136430521413389748222755 309204645782120084622334133)
      ·
        refine ⟨28987935542073757933343825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309204645782120084622334133 28987935542073757933343825)
        ·
          refine ⟨21740951656555318450007869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28987935542073757933343825 21740951656555318450007869)
          ·
            refine ⟨8152856871208244418752951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21740951656555318450007869 8152856871208244418752951)
            ·
              refine ⟨12229285306812366628129427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152856871208244418752951 12229285306812366628129427)
              ·
                refine ⟨18343927960218549942194141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229285306812366628129427 18343927960218549942194141)
                ·
                  refine ⟨6878972985081956228322803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18343927960218549942194141 6878972985081956228322803)
                  ·
                    refine ⟨10318459477622934342484205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878972985081956228322803 10318459477622934342484205)
                    ·
                      refine ⟨3869422304108600378431577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318459477622934342484205 3869422304108600378431577)
                      ·
                        rfl

theorem cell23_7535673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7535673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535673 prefixEnd_7535673 := by exact prefixLift 7535673
  have htrace : WordTrace (prefixWord ++ tailWord_7535673) baseStart_7535673 baseEnd_7535673 := by
    simpa [prefixWord, tailWord_7535673, baseEnd_7535673] using wordTrace_append hprefix tailTrace_7535673
  have hstable : (prefixWord ++ tailWord_7535673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535673).length < 2 ^ (prefixWord ++ tailWord_7535673).sum := by decide
  have hdescent : baseEnd_7535673 < baseStart_7535673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535693 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7535693 : Nat := 118140960795 + 7535693 * 2 ^ 59
def prefixEnd_7535693 : Nat := 4983230072969 + 3 ^ 40 * 7535693 * 2
def baseEnd_7535693 : Nat := 1289810857907230100060495

theorem tailTrace_7535693 : CollatzResearch.WordTrace tailWord_7535693 prefixEnd_7535693 1289810857907230100060495 := by
  unfold tailWord_7535693
  simp only [CollatzResearch.WordTrace]
  refine ⟨274849303488478729746691733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183232868992319153164461155 274849303488478729746691733)
  ·
    refine ⟨12883561101022440456876175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274849303488478729746691733 12883561101022440456876175)
    ·
      refine ⟨19325341651533660685314263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12883561101022440456876175 19325341651533660685314263)
      ·
        refine ⟨28988012477300491027971395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19325341651533660685314263 28988012477300491027971395)
        ·
          refine ⟨43482018715950736541957093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28988012477300491027971395 43482018715950736541957093)
          ·
            refine ⟨8152878509240763101616955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43482018715950736541957093 8152878509240763101616955)
            ·
              refine ⟨12229317763861144652425433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152878509240763101616955 12229317763861144652425433)
              ·
                refine ⟨9171988322895858489319075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12229317763861144652425433 9171988322895858489319075)
                ·
                  refine ⟨13757982484343787733978613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171988322895858489319075 13757982484343787733978613)
                  ·
                    refine ⟨1289810857907230100060495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13757982484343787733978613 1289810857907230100060495)
                    ·
                      rfl

theorem cell23_7535693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7535693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535693 prefixEnd_7535693 := by exact prefixLift 7535693
  have htrace : WordTrace (prefixWord ++ tailWord_7535693) baseStart_7535693 baseEnd_7535693 := by
    simpa [prefixWord, tailWord_7535693, baseEnd_7535693] using wordTrace_append hprefix tailTrace_7535693
  have hstable : (prefixWord ++ tailWord_7535693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535693).length < 2 ^ (prefixWord ++ tailWord_7535693).sum := by decide
  have hdescent : baseEnd_7535693 < baseStart_7535693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535696 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2]
def baseStart_7535696 : Nat := 118140960795 + 7535696 * 2 ^ 59
def prefixEnd_7535696 : Nat := 4983230072969 + 3 ^ 40 * 7535696 * 2
def baseEnd_7535696 : Nat := 3869434114163653788443971

theorem tailTrace_7535696 : CollatzResearch.WordTrace tailWord_7535696 prefixEnd_7535696 3869434114163653788443971 := by
  unfold tailWord_7535696
  simp only [CollatzResearch.WordTrace]
  refine ⟨137424706453733930629525471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183232941938311907506033961 137424706453733930629525471)
  ·
    refine ⟨206137059680600895944288207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137424706453733930629525471 206137059680600895944288207)
    ·
      refine ⟨309205589520901343916432311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206137059680600895944288207 309205589520901343916432311)
      ·
        refine ⟨463808384281352015874648467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309205589520901343916432311 463808384281352015874648467)
        ·
          refine ⟨695712576422028023811972701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463808384281352015874648467 695712576422028023811972701)
          ·
            refine ⟨260892216158260508929489763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695712576422028023811972701 260892216158260508929489763)
            ·
              refine ⟨391338324237390763394234645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260892216158260508929489763 391338324237390763394234645)
              ·
                refine ⟨18343983948627692034104749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391338324237390763394234645 18343983948627692034104749)
                ·
                  refine ⟨6878993980735384512789281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18343983948627692034104749 6878993980735384512789281)
                  ·
                    refine ⟨5159245485551538384591961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6878993980735384512789281 5159245485551538384591961)
                    ·
                      refine ⟨3869434114163653788443971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159245485551538384591961 3869434114163653788443971)
                      ·
                        rfl

theorem cell23_7535696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2].length) (baseStart_7535696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535696 prefixEnd_7535696 := by exact prefixLift 7535696
  have htrace : WordTrace (prefixWord ++ tailWord_7535696) baseStart_7535696 baseEnd_7535696 := by
    simpa [prefixWord, tailWord_7535696, baseEnd_7535696] using wordTrace_append hprefix tailTrace_7535696
  have hstable : (prefixWord ++ tailWord_7535696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535696).length < 2 ^ (prefixWord ++ tailWord_7535696).sum := by decide
  have hdescent : baseEnd_7535696 < baseStart_7535696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535730 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_7535730 : Nat := 118140960795 + 7535730 * 2 ^ 59
def prefixEnd_7535730 : Nat := 4983230072969 + 3 ^ 40 * 7535730 * 2
def baseEnd_7535730 : Nat := 3869451572505906655418815

theorem tailTrace_7535730 : CollatzResearch.WordTrace tailWord_7535730 prefixEnd_7535730 3869451572505906655418815 := by
  unfold tailWord_7535730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68712663247336171266447161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183233768659563123377192429 68712663247336171266447161)
  ·
    refine ⟨51534497435502128449835371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68712663247336171266447161 51534497435502128449835371)
    ·
      refine ⟨77301746153253192674753057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51534497435502128449835371 77301746153253192674753057)
      ·
        refine ⟨57976309614939894506064793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77301746153253192674753057 57976309614939894506064793)
        ·
          refine ⟨43482232211204920879548595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57976309614939894506064793 43482232211204920879548595)
          ·
            refine ⟨65223348316807381319322893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43482232211204920879548595 65223348316807381319322893)
            ·
              refine ⟨24458755618802767994746085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65223348316807381319322893 24458755618802767994746085)
              ·
                refine ⟨4586016678525518999014891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24458755618802767994746085 4586016678525518999014891)
                ·
                  refine ⟨6879025017788278498522337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586016678525518999014891 6879025017788278498522337)
                  ·
                    refine ⟨5159268763341208873891753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879025017788278498522337 5159268763341208873891753)
                    ·
                      refine ⟨3869451572505906655418815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159268763341208873891753 3869451572505906655418815)
                      ·
                        rfl

theorem cell23_7535730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_7535730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535730 prefixEnd_7535730 := by exact prefixLift 7535730
  have htrace : WordTrace (prefixWord ++ tailWord_7535730) baseStart_7535730 baseEnd_7535730 := by
    simpa [prefixWord, tailWord_7535730, baseEnd_7535730] using wordTrace_append hprefix tailTrace_7535730
  have hstable : (prefixWord ++ tailWord_7535730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535730).length < 2 ^ (prefixWord ++ tailWord_7535730).sum := by decide
  have hdescent : baseEnd_7535730 < baseStart_7535730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535773 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_7535773 : Nat := 118140960795 + 7535773 * 2 ^ 59
def prefixEnd_7535773 : Nat := 4983230072969 + 3 ^ 40 * 7535773 * 2
def baseEnd_7535773 : Nat := 3869473652174049987181117

theorem tailTrace_7535773 : CollatzResearch.WordTrace tailWord_7535773 prefixEnd_7535773 3869473652174049987181117 := by
  unfold tailWord_7535773
  simp only [CollatzResearch.WordTrace]
  refine ⟨274852221328188903409603973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183234814218792602273069315 274852221328188903409603973)
  ·
    refine ⟨51534791499035419389300745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274852221328188903409603973 51534791499035419389300745)
    ·
      refine ⟨38651093624276564541975559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51534791499035419389300745 38651093624276564541975559)
      ·
        refine ⟨57976640436414846812963339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38651093624276564541975559 57976640436414846812963339)
        ·
          refine ⟨86964960654622270219445009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57976640436414846812963339 86964960654622270219445009)
          ·
            refine ⟨65223720490966702664583757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86964960654622270219445009 65223720490966702664583757)
            ·
              refine ⟨24458895184112513499218909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65223720490966702664583757 24458895184112513499218909)
              ·
                refine ⟨9172085694042192562207091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24458895184112513499218909 9172085694042192562207091)
                ·
                  refine ⟨13758128541063288843310637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172085694042192562207091 13758128541063288843310637)
                  ·
                    refine ⟨5159298202898733316241489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13758128541063288843310637 5159298202898733316241489)
                    ·
                      refine ⟨3869473652174049987181117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159298202898733316241489 3869473652174049987181117)
                      ·
                        rfl

theorem cell23_7535773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_7535773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535773 prefixEnd_7535773 := by exact prefixLift 7535773
  have htrace : WordTrace (prefixWord ++ tailWord_7535773) baseStart_7535773 baseEnd_7535773 := by
    simpa [prefixWord, tailWord_7535773, baseEnd_7535773] using wordTrace_append hprefix tailTrace_7535773
  have hstable : (prefixWord ++ tailWord_7535773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535773).length < 2 ^ (prefixWord ++ tailWord_7535773).sum := by decide
  have hdescent : baseEnd_7535773 < baseStart_7535773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535780 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_7535780 : Nat := 118140960795 + 7535780 * 2 ^ 59
def prefixEnd_7535780 : Nat := 4983230072969 + 3 ^ 40 * 7535780 * 2
def baseEnd_7535780 : Nat := 3869477246538631459793585

theorem tailTrace_7535780 : CollatzResearch.WordTrace tailWord_7535780 prefixEnd_7535780 3869477246538631459793585 := by
  unfold tailWord_7535780
  simp only [CollatzResearch.WordTrace]
  refine ⟨137426238319581771802554397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183234984426109029070072529 137426238319581771802554397)
  ·
    refine ⟨51534839369843164425957899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137426238319581771802554397 51534839369843164425957899)
    ·
      refine ⟨77302259054764746638936849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51534839369843164425957899 77302259054764746638936849)
      ·
        refine ⟨57976694291073559979202637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77302259054764746638936849 57976694291073559979202637)
        ·
          refine ⟨21741260359152584992200989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57976694291073559979202637 21741260359152584992200989)
          ·
            refine ⟨8152972634682219372075371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21741260359152584992200989 8152972634682219372075371)
            ·
              refine ⟨12229458952023329058113057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152972634682219372075371 12229458952023329058113057)
              ·
                refine ⟨9172094214017496793584793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12229458952023329058113057 9172094214017496793584793)
                ·
                  refine ⟨6879070660513122595188595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172094214017496793584793 6879070660513122595188595)
                  ·
                    refine ⟨10318605990769683892782893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6879070660513122595188595 10318605990769683892782893)
                    ·
                      refine ⟨3869477246538631459793585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318605990769683892782893 3869477246538631459793585)
                      ·
                        rfl

theorem cell23_7535780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_7535780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535780 prefixEnd_7535780 := by exact prefixLift 7535780
  have htrace : WordTrace (prefixWord ++ tailWord_7535780) baseStart_7535780 baseEnd_7535780 := by
    simpa [prefixWord, tailWord_7535780, baseEnd_7535780] using wordTrace_append hprefix tailTrace_7535780
  have hstable : (prefixWord ++ tailWord_7535780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535780).length < 2 ^ (prefixWord ++ tailWord_7535780).sum := by decide
  have hdescent : baseEnd_7535780 < baseStart_7535780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535792 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 11]
def baseStart_7535792 : Nat := 118140960795 + 7535792 * 2 ^ 59
def prefixEnd_7535792 : Nat := 4983230072969 + 3 ^ 40 * 7535792 * 2
def baseEnd_7535792 : Nat := 429942600922942823649281

theorem tailTrace_7535792 : CollatzResearch.WordTrace tailWord_7535792 prefixEnd_7535792 429942600922942823649281 := by
  unfold tailWord_7535792
  simp only [CollatzResearch.WordTrace]
  refine ⟨137426457157560034827272815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183235276210080046436363753 137426457157560034827272815)
  ·
    refine ⟨206139685736340052240909223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137426457157560034827272815 206139685736340052240909223)
    ·
      refine ⟨309209528604510078361363835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206139685736340052240909223 309209528604510078361363835)
      ·
        refine ⟨463814292906765117542045753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309209528604510078361363835 463814292906765117542045753)
        ·
          refine ⟨347860719680073838156534315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463814292906765117542045753 347860719680073838156534315)
          ·
            refine ⟨521791079520110757234801473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347860719680073838156534315 521791079520110757234801473)
            ·
              refine ⟨391343309640083067926101105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521791079520110757234801473 391343309640083067926101105)
              ·
                refine ⟨293507482230062300944575829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391343309640083067926101105 293507482230062300944575829)
                ·
                  refine ⟨429942600922942823649281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 293507482230062300944575829 429942600922942823649281)
                  ·
                    rfl

theorem cell23_7535792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_7535792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535792 prefixEnd_7535792 := by exact prefixLift 7535792
  have htrace : WordTrace (prefixWord ++ tailWord_7535792) baseStart_7535792 baseEnd_7535792 := by
    simpa [prefixWord, tailWord_7535792, baseEnd_7535792] using wordTrace_append hprefix tailTrace_7535792
  have hstable : (prefixWord ++ tailWord_7535792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535792).length < 2 ^ (prefixWord ++ tailWord_7535792).sum := by decide
  have hdescent : baseEnd_7535792 < baseStart_7535792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535799 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_7535799 : Nat := 118140960795 + 7535799 * 2 ^ 59
def prefixEnd_7535799 : Nat := 4983230072969 + 3 ^ 40 * 7535799 * 2
def baseEnd_7535799 : Nat := 3869487002671066885455997

theorem tailTrace_7535799 : CollatzResearch.WordTrace tailWord_7535799 prefixEnd_7535799 3869487002671066885455997 := by
  unfold tailWord_7535799
  simp only [CollatzResearch.WordTrace]
  refine ⟨274853169626094709850050451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183235446417396473233366967 274853169626094709850050451)
  ·
    refine ⟨412279754439142064775075677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274853169626094709850050451 412279754439142064775075677)
    ·
      refine ⟨154604907914678274290653379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412279754439142064775075677 154604907914678274290653379)
      ·
        refine ⟨231907361872017411435980069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154604907914678274290653379 231907361872017411435980069)
        ·
          refine ⟨43482630351003264644246263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231907361872017411435980069 43482630351003264644246263)
          ·
            refine ⟨65223945526504896966369395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43482630351003264644246263 65223945526504896966369395)
            ·
              refine ⟨97835918289757345449554093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65223945526504896966369395 97835918289757345449554093)
              ·
                refine ⟨36688469358659004543582785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97835918289757345449554093 36688469358659004543582785)
                ·
                  refine ⟨27516352018994253407687089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36688469358659004543582785 27516352018994253407687089)
                  ·
                    refine ⟨20637264014245690055765317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27516352018994253407687089 20637264014245690055765317)
                    ·
                      refine ⟨3869487002671066885455997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20637264014245690055765317 3869487002671066885455997)
                      ·
                        rfl

theorem cell23_7535799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_7535799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535799 prefixEnd_7535799 := by exact prefixLift 7535799
  have htrace : WordTrace (prefixWord ++ tailWord_7535799) baseStart_7535799 baseEnd_7535799 := by
    simpa [prefixWord, tailWord_7535799, baseEnd_7535799] using wordTrace_append hprefix tailTrace_7535799
  have hstable : (prefixWord ++ tailWord_7535799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535799).length < 2 ^ (prefixWord ++ tailWord_7535799).sum := by decide
  have hdescent : baseEnd_7535799 < baseStart_7535799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535819 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3]
def baseStart_7535819 : Nat := 118140960795 + 7535819 * 2 ^ 59
def prefixEnd_7535819 : Nat := 4983230072969 + 3 ^ 40 * 7535819 * 2
def baseEnd_7535819 : Nat := 3869497272284156807205905

theorem tailTrace_7535819 : CollatzResearch.WordTrace tailWord_7535819 prefixEnd_7535819 3869497272284156807205905 := by
  unfold tailWord_7535819
  simp only [CollatzResearch.WordTrace]
  refine ⟨274853899086022253265778511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183235932724014835510519007 274853899086022253265778511)
  ·
    refine ⟨412280848629033379898667767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274853899086022253265778511 412280848629033379898667767)
    ·
      refine ⟨618421272943550069848001651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412280848629033379898667767 618421272943550069848001651)
      ·
        refine ⟨927631909415325104772002477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618421272943550069848001651 927631909415325104772002477)
        ·
          refine ⟨347861966030746914289500929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927631909415325104772002477 347861966030746914289500929)
          ·
            refine ⟨260896474523060185717125697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347861966030746914289500929 260896474523060185717125697)
            ·
              refine ⟨195672355892295139287844273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260896474523060185717125697 195672355892295139287844273)
              ·
                refine ⟨146754266919221354465883205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195672355892295139287844273 146754266919221354465883205)
                ·
                  refine ⟨27516425047354003962353101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146754266919221354465883205 27516425047354003962353101)
                  ·
                    refine ⟨10318659392757751485882413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27516425047354003962353101 10318659392757751485882413)
                    ·
                      refine ⟨3869497272284156807205905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318659392757751485882413 3869497272284156807205905)
                      ·
                        rfl

theorem cell23_7535819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].length) (baseStart_7535819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535819 prefixEnd_7535819 := by exact prefixLift 7535819
  have htrace : WordTrace (prefixWord ++ tailWord_7535819) baseStart_7535819 baseEnd_7535819 := by
    simpa [prefixWord, tailWord_7535819, baseEnd_7535819] using wordTrace_append hprefix tailTrace_7535819
  have hstable : (prefixWord ++ tailWord_7535819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535819).length < 2 ^ (prefixWord ++ tailWord_7535819).sum := by decide
  have hdescent : baseEnd_7535819 < baseStart_7535819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535839 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 4, 5]
def baseStart_7535839 : Nat := 118140960795 + 7535839 * 2 ^ 59
def prefixEnd_7535839 : Nat := 4983230072969 + 3 ^ 40 * 7535839 * 2
def baseEnd_7535839 : Nat := 1289835847299082242985271

theorem tailTrace_7535839 : CollatzResearch.WordTrace tailWord_7535839 prefixEnd_7535839 1289835847299082242985271 := by
  unfold tailWord_7535839
  simp only [CollatzResearch.WordTrace]
  refine ⟨274854628545949796681506571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183236419030633197787671047 274854628545949796681506571)
  ·
    refine ⟨412281942818924695022259857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274854628545949796681506571 412281942818924695022259857)
    ·
      refine ⟨309211457114193521266694893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412281942818924695022259857 309211457114193521266694893)
      ·
        refine ⟨115954296417822570475010585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309211457114193521266694893 115954296417822570475010585)
        ·
          refine ⟨86965722313366927856257939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115954296417822570475010585 86965722313366927856257939)
          ·
            refine ⟨130448583470050391784386909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86965722313366927856257939 130448583470050391784386909)
            ·
              refine ⟨48918218801268896919145091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130448583470050391784386909 48918218801268896919145091)
              ·
                refine ⟨73377328201903345378717637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48918218801268896919145091 73377328201903345378717637)
                ·
                  refine ⟨13758249037856877258509557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73377328201903345378717637 13758249037856877258509557)
                  ·
                    refine ⟨1289835847299082242985271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13758249037856877258509557 1289835847299082242985271)
                    ·
                      rfl

theorem cell23_7535839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_7535839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535839 prefixEnd_7535839 := by exact prefixLift 7535839
  have htrace : WordTrace (prefixWord ++ tailWord_7535839) baseStart_7535839 baseEnd_7535839 := by
    simpa [prefixWord, tailWord_7535839, baseEnd_7535839] using wordTrace_append hprefix tailTrace_7535839
  have hstable : (prefixWord ++ tailWord_7535839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535839).length < 2 ^ (prefixWord ++ tailWord_7535839).sum := by decide
  have hdescent : baseEnd_7535839 < baseStart_7535839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535889 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7535889 : Nat := 118140960795 + 7535889 * 2 ^ 59
def prefixEnd_7535889 : Nat := 4983230072969 + 3 ^ 40 * 7535889 * 2
def baseEnd_7535889 : Nat := 3869533215929971533330583

theorem tailTrace_7535889 : CollatzResearch.WordTrace tailWord_7535889 prefixEnd_7535889 3869533215929971533330583 := by
  unfold tailWord_7535889
  simp only [CollatzResearch.WordTrace]
  refine ⟨274856452195768655220826721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183237634797179103480551147 274856452195768655220826721)
  ·
    refine ⟨206142339146826491415620041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274856452195768655220826721 206142339146826491415620041)
    ·
      refine ⟨154606754360119868561715031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206142339146826491415620041 154606754360119868561715031)
      ·
        refine ⟨231910131540179802842572547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154606754360119868561715031 231910131540179802842572547)
        ·
          refine ⟨347865197310269704263858821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231910131540179802842572547 347865197310269704263858821)
          ·
            refine ⟨65224724495675569549473529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347865197310269704263858821 65224724495675569549473529)
            ·
              refine ⟨48918543371756677162105147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65224724495675569549473529 48918543371756677162105147)
              ·
                refine ⟨73377815057635015743157721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48918543371756677162105147 73377815057635015743157721)
                ·
                  refine ⟨55033361293226261807368291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73377815057635015743157721 55033361293226261807368291)
                  ·
                    refine ⟨82550041939839392711052437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55033361293226261807368291 82550041939839392711052437)
                    ·
                      refine ⟨3869533215929971533330583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82550041939839392711052437 3869533215929971533330583)
                      ·
                        rfl

theorem cell23_7535889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7535889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535889 prefixEnd_7535889 := by exact prefixLift 7535889
  have htrace : WordTrace (prefixWord ++ tailWord_7535889) baseStart_7535889 baseEnd_7535889 := by
    simpa [prefixWord, tailWord_7535889, baseEnd_7535889] using wordTrace_append hprefix tailTrace_7535889
  have hstable : (prefixWord ++ tailWord_7535889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535889).length < 2 ^ (prefixWord ++ tailWord_7535889).sum := by decide
  have hdescent : baseEnd_7535889 < baseStart_7535889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535937 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7535937 : Nat := 118140960795 + 7535937 * 2 ^ 59
def prefixEnd_7535937 : Nat := 4983230072969 + 3 ^ 40 * 7535937 * 2
def baseEnd_7535937 : Nat := 1289852621000462448510121

theorem tailTrace_7535937 : CollatzResearch.WordTrace tailWord_7535937 prefixEnd_7535937 1289852621000462448510121 := by
  unfold tailWord_7535937
  simp only [CollatzResearch.WordTrace]
  refine ⟨274858202899594759418574065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183238801933063172945716043 274858202899594759418574065)
  ·
    refine ⟨206143652174696069563930549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274858202899594759418574065 206143652174696069563930549)
    ·
      refine ⟨19325967391377756521618489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206143652174696069563930549 19325967391377756521618489)
      ·
        refine ⟨14494475543533317391213867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19325967391377756521618489 14494475543533317391213867)
        ·
          refine ⟨21741713315299976086820801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494475543533317391213867 21741713315299976086820801)
          ·
            refine ⟨16306284986474982065115601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21741713315299976086820801 16306284986474982065115601)
            ·
              refine ⟨12229713739856236548836701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306284986474982065115601 12229713739856236548836701)
              ·
                refine ⟨4586142652446088705813763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12229713739856236548836701 4586142652446088705813763)
                ·
                  refine ⟨6879213978669133058720645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586142652446088705813763 6879213978669133058720645)
                  ·
                    refine ⟨1289852621000462448510121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6879213978669133058720645 1289852621000462448510121)
                    ·
                      rfl

theorem cell23_7535937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7535937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535937 prefixEnd_7535937 := by exact prefixLift 7535937
  have htrace : WordTrace (prefixWord ++ tailWord_7535937) baseStart_7535937 baseEnd_7535937 := by
    simpa [prefixWord, tailWord_7535937, baseEnd_7535937] using wordTrace_append hprefix tailTrace_7535937
  have hstable : (prefixWord ++ tailWord_7535937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535937).length < 2 ^ (prefixWord ++ tailWord_7535937).sum := by decide
  have hdescent : baseEnd_7535937 < baseStart_7535937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535939 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_7535939 : Nat := 118140960795 + 7535939 * 2 ^ 59
def prefixEnd_7535939 : Nat := 4983230072969 + 3 ^ 40 * 7535939 * 2
def baseEnd_7535939 : Nat := 3869558889962696337705353

theorem tailTrace_7535939 : CollatzResearch.WordTrace tailWord_7535939 prefixEnd_7535939 3869558889962696337705353 := by
  unfold tailWord_7535939
  simp only [CollatzResearch.WordTrace]
  refine ⟨274858275845587513760146871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183238850563725009173431247 274858275845587513760146871)
  ·
    refine ⟨412287413768381270640220307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274858275845587513760146871 412287413768381270640220307)
    ·
      refine ⟨618431120652571905960330461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412287413768381270640220307 618431120652571905960330461)
      ·
        refine ⟨231911670244714464735123923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618431120652571905960330461 231911670244714464735123923)
        ·
          refine ⟨347867505367071697102685885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231911670244714464735123923 347867505367071697102685885)
          ·
            refine ⟨130450314512651886413507207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347867505367071697102685885 130450314512651886413507207)
            ·
              refine ⟨195675471768977829620260811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130450314512651886413507207 195675471768977829620260811)
              ·
                refine ⟨293513207653466744430391217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195675471768977829620260811 293513207653466744430391217)
                ·
                  refine ⟨220134905740100058322793413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293513207653466744430391217 220134905740100058322793413)
                  ·
                    refine ⟨41275294826268760935523765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220134905740100058322793413 41275294826268760935523765)
                    ·
                      refine ⟨3869558889962696337705353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41275294826268760935523765 3869558889962696337705353)
                      ·
                        rfl

theorem cell23_7535939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_7535939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535939 prefixEnd_7535939 := by exact prefixLift 7535939
  have htrace : WordTrace (prefixWord ++ tailWord_7535939) baseStart_7535939 baseEnd_7535939 := by
    simpa [prefixWord, tailWord_7535939, baseEnd_7535939] using wordTrace_append hprefix tailTrace_7535939
  have hstable : (prefixWord ++ tailWord_7535939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535939).length < 2 ^ (prefixWord ++ tailWord_7535939).sum := by decide
  have hdescent : baseEnd_7535939 < baseStart_7535939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535953 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_7535953 : Nat := 118140960795 + 7535953 * 2 ^ 59
def prefixEnd_7535953 : Nat := 4983230072969 + 3 ^ 40 * 7535953 * 2
def baseEnd_7535953 : Nat := 3869566078691859282930289

theorem tailTrace_7535953 : CollatzResearch.WordTrace tailWord_7535953 prefixEnd_7535953 3869566078691859282930289 := by
  unfold tailWord_7535953
  simp only [CollatzResearch.WordTrace]
  refine ⟨274858786467536794151156513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183239190978357862767437675 274858786467536794151156513)
  ·
    refine ⟨206144089850652595613367385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274858786467536794151156513 206144089850652595613367385)
    ·
      refine ⟨154608067387989446710025539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206144089850652595613367385 154608067387989446710025539)
      ·
        refine ⟨231912101081984170065038309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154608067387989446710025539 231912101081984170065038309)
        ·
          refine ⟨43483518952872031887194683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231912101081984170065038309 43483518952872031887194683)
          ·
            refine ⟨65225278429308047830792025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43483518952872031887194683 65225278429308047830792025)
            ·
              refine ⟨48918958821981035873094019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65225278429308047830792025 48918958821981035873094019)
              ·
                refine ⟨73378438232971553809641029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48918958821981035873094019 73378438232971553809641029)
                ·
                  refine ⟨13758457168682166339307693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73378438232971553809641029 13758457168682166339307693)
                  ·
                    refine ⟨5159421438255812377240385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13758457168682166339307693 5159421438255812377240385)
                    ·
                      refine ⟨3869566078691859282930289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159421438255812377240385 3869566078691859282930289)
                      ·
                        rfl

theorem cell23_7535953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_7535953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535953 prefixEnd_7535953 := by exact prefixLift 7535953
  have htrace : WordTrace (prefixWord ++ tailWord_7535953) baseStart_7535953 baseEnd_7535953 := by
    simpa [prefixWord, tailWord_7535953, baseEnd_7535953] using wordTrace_append hprefix tailTrace_7535953
  have hstable : (prefixWord ++ tailWord_7535953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535953).length < 2 ^ (prefixWord ++ tailWord_7535953).sum := by decide
  have hdescent : baseEnd_7535953 < baseStart_7535953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535960 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_7535960 : Nat := 118140960795 + 7535960 * 2 ^ 59
def prefixEnd_7535960 : Nat := 4983230072969 + 3 ^ 40 * 7535960 * 2
def baseEnd_7535960 : Nat := 3869569673056440755542757

theorem tailTrace_7535960 : CollatzResearch.WordTrace tailWord_7535960 prefixEnd_7535960 3869569673056440755542757 := by
  unfold tailWord_7535960
  simp only [CollatzResearch.WordTrace]
  refine ⟨137429520889255717173330667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183239361185674289564440889 137429520889255717173330667)
  ·
    refine ⟨206144281333883575759996001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137429520889255717173330667 206144281333883575759996001)
    ·
      refine ⟨154608211000412681819997001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206144281333883575759996001 154608211000412681819997001)
      ·
        refine ⟨115956158250309511364997751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154608211000412681819997001 115956158250309511364997751)
        ·
          refine ⟨173934237375464267047496627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115956158250309511364997751 173934237375464267047496627)
          ·
            refine ⟨260901356063196400571244941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173934237375464267047496627 260901356063196400571244941)
            ·
              refine ⟨97838008523698650214216853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260901356063196400571244941 97838008523698650214216853)
              ·
                refine ⟨4586156649548374228791415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97838008523698650214216853 4586156649548374228791415)
                ·
                  refine ⟨6879234974322561343187123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586156649548374228791415 6879234974322561343187123)
                  ·
                    refine ⟨10318852461483842014780685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6879234974322561343187123 10318852461483842014780685)
                    ·
                      refine ⟨3869569673056440755542757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10318852461483842014780685 3869569673056440755542757)
                      ·
                        rfl

theorem cell23_7535960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_7535960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535960 prefixEnd_7535960 := by exact prefixLift 7535960
  have htrace : WordTrace (prefixWord ++ tailWord_7535960) baseStart_7535960 baseEnd_7535960 := by
    simpa [prefixWord, tailWord_7535960, baseEnd_7535960] using wordTrace_append hprefix tailTrace_7535960
  have hstable : (prefixWord ++ tailWord_7535960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535960).length < 2 ^ (prefixWord ++ tailWord_7535960).sum := by decide
  have hdescent : baseEnd_7535960 < baseStart_7535960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535983 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_7535983 : Nat := 118140960795 + 7535983 * 2 ^ 59
def prefixEnd_7535983 : Nat := 4983230072969 + 3 ^ 40 * 7535983 * 2
def baseEnd_7535983 : Nat := 3869581483111494165555151

theorem tailTrace_7535983 : CollatzResearch.WordTrace tailWord_7535983 prefixEnd_7535983 3869581483111494165555151 := by
  unfold tailWord_7535983
  simp only [CollatzResearch.WordTrace]
  refine ⟨274859880657428109274748603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183239920438285406183165735 274859880657428109274748603)
  ·
    refine ⟨412289820986142163912122905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274859880657428109274748603 412289820986142163912122905)
    ·
      refine ⟨309217365739606622934092179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412289820986142163912122905 309217365739606622934092179)
      ·
        refine ⟨463826048609409934401138269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309217365739606622934092179 463826048609409934401138269)
        ·
          refine ⟨173934768228528725400426851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463826048609409934401138269 173934768228528725400426851)
          ·
            refine ⟨260902152342793088100640277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173934768228528725400426851 260902152342793088100640277)
            ·
              refine ⟨12229788391068426004717513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260902152342793088100640277 12229788391068426004717513)
              ·
                refine ⟨9172341293301319503538135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12229788391068426004717513 9172341293301319503538135)
                ·
                  refine ⟨13758511939951979255307203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172341293301319503538135 13758511939951979255307203)
                  ·
                    refine ⟨20637767909927968882960805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13758511939951979255307203 20637767909927968882960805)
                    ·
                      refine ⟨3869581483111494165555151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20637767909927968882960805 3869581483111494165555151)
                      ·
                        rfl

theorem cell23_7535983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_7535983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535983 prefixEnd_7535983 := by exact prefixLift 7535983
  have htrace : WordTrace (prefixWord ++ tailWord_7535983) baseStart_7535983 baseEnd_7535983 := by
    simpa [prefixWord, tailWord_7535983, baseEnd_7535983] using wordTrace_append hprefix tailTrace_7535983
  have hstable : (prefixWord ++ tailWord_7535983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535983).length < 2 ^ (prefixWord ++ tailWord_7535983).sum := by decide
  have hdescent : baseEnd_7535983 < baseStart_7535983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535986 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7535986 : Nat := 118140960795 + 7535986 * 2 ^ 59
def prefixEnd_7535986 : Nat := 4983230072969 + 3 ^ 40 * 7535986 * 2
def baseEnd_7535986 : Nat := 3869583023553457653817637

theorem tailTrace_7535986 : CollatzResearch.WordTrace tailWord_7535986 prefixEnd_7535986 3869583023553457653817637 := by
  unfold tailWord_7535986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68714997519104310196776953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183239993384278160524738541 68714997519104310196776953)
  ·
    refine ⟨51536248139328232647582715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68714997519104310196776953 51536248139328232647582715)
    ·
      refine ⟨77304372208992348971374073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51536248139328232647582715 77304372208992348971374073)
      ·
        refine ⟨57978279156744261728530555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77304372208992348971374073 57978279156744261728530555)
        ·
          refine ⟨86967418735116392592795833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57978279156744261728530555 86967418735116392592795833)
          ·
            refine ⟨65225564051337294444596875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86967418735116392592795833 65225564051337294444596875)
            ·
              refine ⟨97838346077005941666895313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65225564051337294444596875 97838346077005941666895313)
              ·
                refine ⟨73378759557754456250171485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97838346077005941666895313 73378759557754456250171485)
                ·
                  refine ⟨27517034834157921093814307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73378759557754456250171485 27517034834157921093814307)
                  ·
                    refine ⟨41275552251236881640721461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27517034834157921093814307 41275552251236881640721461)
                    ·
                      refine ⟨3869583023553457653817637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41275552251236881640721461 3869583023553457653817637)
                      ·
                        rfl

theorem cell23_7535986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7535986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535986 prefixEnd_7535986 := by exact prefixLift 7535986
  have htrace : WordTrace (prefixWord ++ tailWord_7535986) baseStart_7535986 baseEnd_7535986 := by
    simpa [prefixWord, tailWord_7535986, baseEnd_7535986] using wordTrace_append hprefix tailTrace_7535986
  have hstable : (prefixWord ++ tailWord_7535986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535986).length < 2 ^ (prefixWord ++ tailWord_7535986).sum := by decide
  have hdescent : baseEnd_7535986 < baseStart_7535986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535996 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7535996 : Nat := 118140960795 + 7535996 * 2 ^ 59
def prefixEnd_7535996 : Nat := 4983230072969 + 3 ^ 40 * 7535996 * 2
def baseEnd_7535996 : Nat := 3869588158360002614692591

theorem tailTrace_7535996 : CollatzResearch.WordTrace tailWord_7535996 prefixEnd_7535996 3869588158360002614692591 := by
  unfold tailWord_7535996
  simp only [CollatzResearch.WordTrace]
  refine ⟨137430177403190506247485921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183240236537587341663314561 137430177403190506247485921)
  ·
    refine ⟨103072633052392879685614441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137430177403190506247485921 103072633052392879685614441)
    ·
      refine ⟨77304474789294659764210831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103072633052392879685614441 77304474789294659764210831)
      ·
        refine ⟨115956712183941989646316247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77304474789294659764210831 115956712183941989646316247)
        ·
          refine ⟨173935068275912984469474371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115956712183941989646316247 173935068275912984469474371)
          ·
            refine ⟨260902602413869476704211557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173935068275912984469474371 260902602413869476704211557)
            ·
              refine ⟨48919237952600526882039667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260902602413869476704211557 48919237952600526882039667)
              ·
                refine ⟨73378856928900790323059501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48919237952600526882039667 73378856928900790323059501)
                ·
                  refine ⟨27517071348337796371147313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73378856928900790323059501 27517071348337796371147313)
                  ·
                    refine ⟨20637803511253347278360485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27517071348337796371147313 20637803511253347278360485)
                    ·
                      refine ⟨3869588158360002614692591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20637803511253347278360485 3869588158360002614692591)
                      ·
                        rfl

theorem cell23_7535996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7535996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7535996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7535996 prefixEnd_7535996 := by exact prefixLift 7535996
  have htrace : WordTrace (prefixWord ++ tailWord_7535996) baseStart_7535996 baseEnd_7535996 := by
    simpa [prefixWord, tailWord_7535996, baseEnd_7535996] using wordTrace_append hprefix tailTrace_7535996
  have hstable : (prefixWord ++ tailWord_7535996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535996).length < 2 ^ (prefixWord ++ tailWord_7535996).sum := by decide
  have hdescent : baseEnd_7535996 < baseStart_7535996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
